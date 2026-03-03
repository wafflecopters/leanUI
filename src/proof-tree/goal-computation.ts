/**
 * Goal computation — replays the proof tree against the real TacticEngine
 * to compute typed hypotheses and goals at each cursor position.
 *
 * This is the bridge between the UI-level proof tree and the structured
 * math editor. The proof tree stores strings (names, labels), while the
 * TacticEngine operates on kernel terms (TTKTerm) with de Bruijn indices.
 *
 * Pipeline:
 * 1. Create TacticEngine from kernel goal type + definitions
 * 2. Walk proof tree root→cursor, applying real tactics (IntrosTactic, etc.)
 * 3. Read MetaVar.ctx and MetaVar.type from focused goal
 * 4. Render to LaTeX via kernelTypeToSurface + ttermToMathNodes
 */

import { TTerm, mkConstTT, mkAppTT, mkVarTT, mkPiTT, mkPropTT, mkHoleTT, mkULitTT } from '../compiler/surface';
import { TTKTerm } from '../compiler/kernel';
import { DefinitionsMap, NamedArgMap, MetaVar } from '../compiler/term';
import { whnf } from '../compiler/whnf';
import { shiftTerm, subst } from '../compiler/subst';
import { SyntaxRegistry } from '../math-editor/syntax-registry';
import { ReverseRegistry, buildReverseRegistry, ttermToMathNodes } from '../math-editor/tt-to-math';
import { mkRow } from '../math-editor/types';
import { renderStaticLatex } from '../math-editor/render';
import { ProofNode, ProofNodeId, CaseNode } from './proof-tree';
import { TacticEngine, createInitialEngine } from '../tactics/tacticsEngine';
import { IntrosTactic } from '../tactics/tactic';
import { UnfoldTactic } from '../tactics/unfold-tactic';

// ============================================================================
// Types
// ============================================================================

export interface TypedHypothesis {
  readonly name: string;
  readonly type: string;  // LaTeX string from structured math renderer
  readonly rawType?: TTerm;  // Raw surface type (for inductive type lookup)
}

export interface TypedProofContext {
  readonly hypotheses: readonly TypedHypothesis[];
  readonly caseLabel?: string;
  readonly caseLabelLatex?: string;
  readonly inductionVar?: string;
  readonly goal: string;  // LaTeX string from structured math renderer
}

/** Info about an inductive type's constructors (surface-level). */
export interface InductiveInfo {
  readonly name: string;
  readonly constructors: ReadonlyArray<{ readonly name: string; readonly type: TTerm }>;
}

/** Map from inductive type name to its info. */
export type InductiveMap = ReadonlyMap<string, InductiveInfo>;

/** Info about a constructor case for generating case nodes. */
export interface ConstructorCaseInfo {
  readonly label: string;
  readonly constructorName: string;
  readonly paramNames: readonly string[];
}

// ============================================================================
// Kernel → Surface conversion
// ============================================================================

/** Collect an application spine: f a1 a2 ... an → { head: f, args: [a1, a2, ..., an] } */
function collectAppSpine(t: TTKTerm): { head: TTKTerm; args: TTKTerm[] } {
  const args: TTKTerm[] = [];
  let head = t;
  while (head.tag === 'App') {
    args.unshift(head.arg);
    head = head.fn;
  }
  return { head, args };
}

/** Look up the NamedArgMap for a constant name in definitions. */
function lookupNamedArgMap(name: string, definitions: DefinitionsMap): NamedArgMap | undefined {
  const termDef = definitions.terms.get(name);
  if (termDef?.namedArgMap) return termDef.namedArgMap;
  const indDef = definitions.inductiveTypes.get(name);
  if (indDef?.namedArgMap) return indDef.namedArgMap;
  const indName = definitions.inductiveNameOfConstructor.get(name);
  if (indName) {
    const parentInd = definitions.inductiveTypes.get(indName);
    if (parentInd) {
      const ctor = parentInd.constructors.find(c => c.name === name);
      if (ctor?.namedArgMap) return ctor.namedArgMap;
    }
  }
  return undefined;
}

/**
 * Convert a kernel TTKTerm to a surface TTerm.
 * Handles the type forms that commonly appear in goals.
 * When definitions are provided, implicit arguments are omitted.
 */
export function kernelTypeToSurface(t: TTKTerm, definitions?: DefinitionsMap): TTerm {
  const prop = mkPropTT();
  switch (t.tag) {
    case 'Var': return mkVarTT(t.index);
    case 'Const': return mkConstTT(t.name);
    case 'App': {
      if (definitions) {
        const { head, args } = collectAppSpine(t);
        if (head.tag === 'Const') {
          const namedArgMap = lookupNamedArgMap(head.name, definitions);
          if (namedArgMap && namedArgMap.size > 0) {
            const implicitPositions = new Set<number>(namedArgMap.values());
            let result: TTerm = mkConstTT(head.name);
            for (let i = 0; i < args.length; i++) {
              if (!implicitPositions.has(i)) {
                result = mkAppTT(result, kernelTypeToSurface(args[i], definitions));
              }
            }
            return result;
          }
        }
      }
      return mkAppTT(kernelTypeToSurface(t.fn, definitions), kernelTypeToSurface(t.arg, definitions));
    }
    case 'Sort': return { tag: 'Sort', level: kernelTypeToSurface(t.level, definitions) } as TTerm;
    case 'ULit': return mkULitTT(t.n);
    case 'Hole': return mkHoleTT(t.id, prop);
    case 'Binder': {
      if (t.binderKind.tag === 'BPi') {
        return mkPiTT(
          kernelTypeToSurface(t.domain, definitions),
          kernelTypeToSurface(t.body, definitions),
          t.name,
        );
      }
      if (t.binderKind.tag === 'BLam') {
        const domain = kernelTypeToSurface(t.domain, definitions);
        const body = kernelTypeToSurface(t.body, definitions);
        return {
          tag: 'Binder',
          binderKind: { tag: 'BLamTT' },
          name: t.name,
          domain,
          body,
        } as TTerm;
      }
      return mkHoleTT('_unsupported_binder', prop);
    }
    case 'Match': {
      return mkHoleTT('_match', prop);
    }
    default: return mkHoleTT(`_unsupported_${t.tag}`, prop);
  }
}

/**
 * Deep normalize a kernel term using WHNF at each level.
 * Needed after UnfoldTactic which replaces constants with lambdas
 * but doesn't beta-reduce the resulting applications.
 * Uses fuel to prevent infinite loops with recursive definitions.
 */
function fullNormalize(term: TTKTerm, definitions: DefinitionsMap, fuel = 50): TTKTerm {
  if (fuel <= 0) return term;

  const reduced = whnf(term, { definitions, fuel: 200 });

  switch (reduced.tag) {
    case 'Var':
    case 'Const':
    case 'Hole':
    case 'Meta':
    case 'ULevel':
    case 'ULit':
    case 'UOmega':
      return reduced;

    case 'Sort':
      return { tag: 'Sort', level: fullNormalize(reduced.level, definitions, fuel - 1) };

    case 'App': {
      const { head, args } = collectAppSpine(reduced);
      const normArgs = args.map(a => fullNormalize(a, definitions, fuel - 1));
      let result: TTKTerm = head;
      for (const a of normArgs) {
        result = { tag: 'App', fn: result, arg: a };
      }
      const re = whnf(result, { definitions, fuel: 200 });
      if (re !== result && re.tag !== 'App') {
        return fullNormalize(re, definitions, fuel - 1);
      }
      return re !== result ? re : result;
    }

    case 'Binder': {
      const domain = fullNormalize(reduced.domain, definitions, fuel - 1);
      const body = fullNormalize(reduced.body, definitions, fuel - 1);
      if (reduced.binderKind.tag === 'BLet') {
        const defVal = fullNormalize(reduced.binderKind.defVal, definitions, fuel - 1);
        return { ...reduced, domain, body, binderKind: { tag: 'BLet', defVal } };
      }
      return { ...reduced, domain, body };
    }

    case 'Annot':
      return fullNormalize(reduced.term, definitions, fuel - 1);

    case 'Match': {
      const scrutinee = fullNormalize(reduced.scrutinee, definitions, fuel - 1);
      const match: TTKTerm = { tag: 'Match', scrutinee, clauses: reduced.clauses };
      const re = whnf(match, { definitions, fuel: 200 });
      if (re.tag !== 'Match') {
        return fullNormalize(re, definitions, fuel - 1);
      }
      return match;
    }
  }
}

/**
 * Normalize a MetaVar's goal type after unfold and update the engine.
 * Returns a new engine with the goal's type replaced by the normalized version.
 */
function normalizeGoalInEngine(engine: TacticEngine, goalId: string): TacticEngine {
  const goal = engine.metaVars.get(goalId);
  if (!goal) return engine;

  const normalized = fullNormalize(goal.type, engine.definitions);
  if (normalized === goal.type) return engine;

  const newMetaVars = new Map(engine.metaVars);
  newMetaVars.set(goalId, { ...goal, type: normalized });
  return engine.withUpdates({ metaVars: newMetaVars });
}

// ============================================================================
// Rendering helpers
// ============================================================================

/** Render a TTerm expression to LaTeX using the structured math editor pipeline. */
function renderTerm(term: TTerm, ctx: string[], rev: ReverseRegistry): string {
  const nodes = ttermToMathNodes(term, rev, ctx);
  return renderStaticLatex(mkRow(nodes));
}

// ============================================================================
// Inductive type helpers (for UI — generating case options)
// ============================================================================

/** Extract the head constant name from a type. */
export function extractTypeHead(type: TTerm): string | null {
  if (type.tag === 'Const') return type.name;
  if (type.tag === 'App') return extractTypeHead(type.fn);
  return null;
}

/**
 * Peel one Pi binder from a surface type (TTerm).
 * Used by peelConstructorParams for UI case generation.
 */
function peelPi(type: TTerm): { name: string; domain: TTerm; body: TTerm; isImplicit: boolean } | null {
  if (type.tag === 'Binder' && type.binderKind.tag === 'BPiTT') {
    return {
      name: type.name,
      domain: type.domain!,
      body: type.body,
      isImplicit: type.named === true,
    };
  }
  if (type.tag === 'MultiBinder' && type.binderKind.tag === 'BPiTT') {
    const firstName = type.names[0];
    const remainingNames = type.names.slice(1);
    const body: TTerm = remainingNames.length > 0
      ? { ...type, names: remainingNames }
      : type.body;
    return {
      name: firstName,
      domain: type.domain,
      body,
      isImplicit: type.named === true,
    };
  }
  return null;
}

/**
 * Peel explicit (non-implicit) Pi binders from a constructor type.
 * Used for generating case node options in the UI.
 */
export function peelConstructorParams(ctorType: TTerm): Array<{ name: string; domain: TTerm }> {
  const params: Array<{ name: string; domain: TTerm }> = [];
  let t = ctorType;
  while (true) {
    const pi = peelPi(t);
    if (!pi) break;
    if (pi.isImplicit) {
      t = pi.body;
      continue;
    }
    params.push({ name: pi.name, domain: pi.domain });
    t = pi.body;
  }
  return params;
}

/**
 * Check if a constructor parameter is recursive (references the inductive type).
 */
function isRecursiveParam(domain: TTerm, inductiveName: string): boolean {
  const head = extractTypeHead(domain);
  return head === inductiveName;
}

/**
 * Build a TTerm for a constructor application with named params.
 */
function buildConstructorApp(ctorName: string, paramNames: readonly string[]): TTerm {
  let app: TTerm = mkConstTT(ctorName);
  for (let i = paramNames.length - 1; i >= 0; i--) {
    app = mkAppTT(app, mkVarTT(i));
  }
  return app;
}

/**
 * Generate ConstructorCaseInfo for each constructor of an inductive type.
 * Used by the UI to create case nodes with proper labels.
 */
export function generateCaseInfos(
  scrutinee: string,
  inductiveInfo: InductiveInfo,
  rev?: ReverseRegistry,
): ConstructorCaseInfo[] {
  return inductiveInfo.constructors.map(ctor => {
    const params = peelConstructorParams(ctor.type);
    const paramNames = params.map((p, i) => {
      return p.name !== '_' ? p.name : `x${i}`;
    });

    let label = `${scrutinee} = ${ctor.name}`;
    if (paramNames.length > 0) {
      label += ' ' + paramNames.join(' ');
    }

    let labelLatex: string | undefined;
    if (rev) {
      const ctorApp = buildConstructorApp(ctor.name, paramNames);
      const ctx = [...paramNames].reverse();
      const rhsLatex = renderTerm(ctorApp, ctx, rev);
      labelLatex = `${scrutinee} = ${rhsLatex}`;
    }

    return {
      label,
      constructorName: ctor.name,
      paramNames,
      labelLatex,
    };
  });
}

// ============================================================================
// TacticEngine replay
// ============================================================================

interface ReplayResult {
  engine: TacticEngine;
  goalId: string;
  caseLabel?: string;
  caseLabelLatex?: string;
  inductionVar?: string;
}

/**
 * Find the de Bruijn index of a variable name in a TTKContext.
 * Returns null if not found.
 */
function findVarIndex(name: string, ctx: ReadonlyArray<{ name: string; type: TTKTerm }>): number | null {
  for (let i = ctx.length - 1; i >= 0; i--) {
    if (ctx[i].name === name) {
      return ctx.length - 1 - i;
    }
  }
  return null;
}

/**
 * Get the head constant name from a (possibly applied) inductive type.
 */
function getInductiveHead(type: TTKTerm): string | null {
  if (type.tag === 'Const') return type.name;
  if (type.tag === 'App') {
    let head: TTKTerm = type;
    while (head.tag === 'App') head = head.fn;
    return head.tag === 'Const' ? head.name : null;
  }
  return null;
}

/**
 * Replace Var(targetIdx) with `replacement` in `term`.
 * Does NOT decrement other variable indices (unlike standard subst).
 * This is used for induction case goals where the scrutinee stays in context.
 */
export function replaceVar(term: TTKTerm, targetIdx: number, replacement: TTKTerm): TTKTerm {
  switch (term.tag) {
    case 'Var':
      return term.index === targetIdx ? replacement : term;
    case 'App': {
      const fn = replaceVar(term.fn, targetIdx, replacement);
      const arg = replaceVar(term.arg, targetIdx, replacement);
      if (fn === term.fn && arg === term.arg) return term;
      return { tag: 'App', fn, arg };
    }
    case 'Binder': {
      // Under a binder, target index shifts up by 1
      const domain = replaceVar(term.domain, targetIdx, replacement);
      const shiftedReplacement = shiftTerm(replacement, 1, 0);
      const body = replaceVar(term.body, targetIdx + 1, shiftedReplacement);
      if (domain === term.domain && body === term.body) return term;
      return { ...term, domain, body };
    }
    case 'Match': {
      const scrutinee = replaceVar(term.scrutinee, targetIdx, replacement);
      let clausesChanged = false;
      const clauses = term.clauses.map(c => {
        // Each clause binds numPatternVars variables
        const numVars = countPatternVars(c.patterns[0]);
        const shiftedRepl = shiftTerm(replacement, numVars, 0);
        const rhs = replaceVar(c.rhs, targetIdx + numVars, shiftedRepl);
        if (rhs !== c.rhs) clausesChanged = true;
        return rhs === c.rhs ? c : { ...c, rhs };
      });
      if (scrutinee === term.scrutinee && !clausesChanged) return term;
      return { tag: 'Match', scrutinee, clauses };
    }
    default:
      return term;
  }
}

/** Count the number of binding variables in a pattern. */
function countPatternVars(pat: import('../compiler/kernel').TTKPattern): number {
  switch (pat.tag) {
    case 'PVar': return 1;
    case 'PWild': return 1;
    case 'PCtor': return pat.args.reduce((sum, a) => sum + countPatternVars(a), 0);
  }
}

/**
 * Compute a case-specific goal by directly substituting the constructor
 * pattern for the scrutinee variable in the goal type.
 *
 * After intros [i, n, f], context is [i:ℕ, n:ℕ, f:ℕ→ℕ] and goal is G(i,n,f).
 * For Zero case: goal becomes G(i,0,f), context extends with nothing.
 * For Succ case: goal becomes G(i,Succ(n'),f), context extends with [n':ℕ, IH:P(n')].
 */
export function computeCaseGoalDirect(
  goal: MetaVar,
  scrutineeIdx: number,
  ctor: { name: string; type: TTKTerm; namedArgMap?: NamedArgMap },
  inductiveName: string,
  definitions: DefinitionsMap,
): MetaVar {
  // Extract type args from scrutinee type for implicit param substitution
  const scrutineeType = goal.ctx[goal.ctx.length - 1 - scrutineeIdx].type;
  const typeArgs = extractTypeArgsFromType(scrutineeType);

  // Count constructor parameters (skip implicit ones)
  const numImplicit = ctor.namedArgMap?.size ?? 0;
  const { params, hasRecursiveParam, recursiveParamLocalIdx } = peelCtorParams(
    ctor.type, numImplicit, typeArgs, inductiveName, definitions
  );

  // Total new context entries: params + (IH if recursive)
  const numNewEntries = params.length + (hasRecursiveParam ? 1 : 0);

  // Build extended context: original ctx + constructor params + optional IH
  const newCtx = [...goal.ctx];
  for (const p of params) {
    newCtx.push({ name: p.name, type: p.type });
  }

  // Build constructor application for substitution:
  // e.g., Succ(n') where n' is at de Bruijn index (numNewEntries - 1 - paramLocalIdx)
  // relative to the NEW context
  let ctorApp: TTKTerm = { tag: 'Const', name: ctor.name };
  const ihOffset = hasRecursiveParam ? 1 : 0;
  for (let i = 0; i < params.length; i++) {
    ctorApp = {
      tag: 'App',
      fn: ctorApp,
      arg: { tag: 'Var', index: (params.length - 1 - i) + ihOffset },
    };
  }

  // Shift goal type to account for new context entries
  const shiftedGoalType = shiftTerm(goal.type, numNewEntries, 0);

  // Replace the scrutinee (now at shifted index) with constructor app
  const shiftedScrutineeIdx = scrutineeIdx + numNewEntries;
  const caseGoalType = replaceVar(shiftedGoalType, shiftedScrutineeIdx, ctorApp);

  // NOTE: Do NOT call fullNormalize here. The substitution Var(n) → Const("Zero")
  // doesn't create beta-redexes. fullNormalize would aggressively unfold definitions
  // like sum → sumStartCount, producing unreadable goals with internal helpers.
  // fullNormalize is only needed after UnfoldTactic (which replaces Const with lambdas).

  // Add induction hypothesis if recursive
  if (hasRecursiveParam && recursiveParamLocalIdx !== null) {
    // IH type: the goal type with scrutinee replaced by the recursive param
    // The recursive param is at index (params.length - 1 - recursiveParamLocalIdx) + 1 (for IH slot)
    // But IH is the LAST entry, so from IH's perspective, recursive param is at
    // (params.length - 1 - recursiveParamLocalIdx) + 1
    const recursiveVarIdx = (params.length - 1 - recursiveParamLocalIdx) + 1;
    const shiftedGoalForIH = shiftTerm(goal.type, numNewEntries, 0);
    const shiftedScrutineeForIH = scrutineeIdx + numNewEntries;
    const ihType = replaceVar(shiftedGoalForIH, shiftedScrutineeForIH, { tag: 'Var', index: recursiveVarIdx });
    newCtx.push({ name: 'IH', type: ihType });
  }

  return {
    ctx: newCtx,
    type: caseGoalType,
    solution: undefined,
    caseTag: ctor.name,
  };
}

/** Extract type arguments from a (possibly applied) type: e.g., List Nat → [Nat] */
function extractTypeArgsFromType(type: TTKTerm): TTKTerm[] {
  const args: TTKTerm[] = [];
  let current = type;
  while (current.tag === 'App') {
    args.unshift(current.arg);
    current = current.fn;
  }
  return args;
}

/** Peel explicit Pi binders from constructor type, substituting implicit params. */
function peelCtorParams(
  ctorType: TTKTerm,
  numImplicit: number,
  typeArgs: TTKTerm[],
  inductiveName: string,
  definitions: DefinitionsMap,
): {
  params: Array<{ name: string; type: TTKTerm }>;
  hasRecursiveParam: boolean;
  recursiveParamLocalIdx: number | null;
} {
  let currentType = ctorType;

  // Substitute type args for implicit params
  for (let i = 0; i < numImplicit; i++) {
    if (currentType.tag === 'Binder' && currentType.binderKind.tag === 'BPi') {
      const arg = typeArgs[i] || { tag: 'Hole' as const, id: '_implicit_' + i };
      currentType = subst(0, arg, currentType.body);
    }
  }

  // Peel explicit params
  const params: Array<{ name: string; type: TTKTerm }> = [];
  let hasRecursiveParam = false;
  let recursiveParamLocalIdx: number | null = null;
  let paramIdx = 0;

  while (currentType.tag === 'Binder' && currentType.binderKind.tag === 'BPi') {
    const name = (currentType.name && currentType.name !== '_')
      ? currentType.name
      : `x${paramIdx}`;

    // Check if recursive
    const domainWhnf = whnf(currentType.domain, { definitions });
    const head = getInductiveHead(domainWhnf);
    if (head === inductiveName) {
      hasRecursiveParam = true;
      recursiveParamLocalIdx = paramIdx;
    }

    params.push({ name, type: currentType.domain });
    paramIdx++;
    currentType = currentType.body;
  }

  return { params, hasRecursiveParam, recursiveParamLocalIdx };
}

/**
 * Search case nodes for cursor when induction can't be applied.
 * Returns the first matching result from case bodies.
 */
function searchCasesForCursor(
  cases: readonly CaseNode[],
  cursorId: ProofNodeId,
  engine: TacticEngine,
  goalId: string,
  scrutinee: string,
): ReplayResult | null {
  for (const c of cases) {
    if (c.id === cursorId) {
      return { engine, goalId, caseLabel: c.label, caseLabelLatex: c.labelLatex, inductionVar: scrutinee };
    }
    const bodyResult = replayProofTree(
      c.body, cursorId, engine,
      c.label, c.labelLatex, scrutinee,
    );
    if (bodyResult) return bodyResult;
  }
  return null;
}

/**
 * Replay the proof tree against a TacticEngine, applying real tactics
 * at each node until we reach the cursor. Returns the engine state
 * at the cursor position.
 */
function replayProofTree(
  node: ProofNode,
  cursorId: ProofNodeId,
  engine: TacticEngine,
  caseLabel?: string,
  caseLabelLatex?: string,
  inductionVar?: string,
): ReplayResult | null {
  const goalId = engine.getFocusedGoalId();
  if (!goalId) return null;

  // Cursor is on this node — return current engine state
  if (node.id === cursorId) {
    return { engine, goalId, caseLabel, caseLabelLatex, inductionVar };
  }

  switch (node.tag) {
    case 'hole':
    case 'exact':
      // Leaf nodes — cursor not here
      return null;

    case 'intros': {
      // Apply IntrosTactic with the given names
      const goal = engine.getFocusedGoal();
      if (!goal) return null;

      const tactic = new IntrosTactic([...node.names]);
      const result = tactic.apply(engine, goal, goalId);

      if (!result.success) {
        // Tactic failed — return current state at cursor if child matches
        if (node.child.id === cursorId) {
          return { engine, goalId, caseLabel, caseLabelLatex, inductionVar };
        }
        return null;
      }

      return replayProofTree(
        node.child, cursorId, result.newEngine,
        caseLabel, caseLabelLatex, inductionVar,
      );
    }

    case 'unfold': {
      // Apply UnfoldTactic (constant replacement) then deep normalize
      // to beta-reduce any resulting (λx => body)(arg) redexes
      const goal = engine.getFocusedGoal();
      if (!goal) return null;

      const tactic = new UnfoldTactic([node.name]);
      const result = tactic.apply(engine, goal, goalId);

      if (!result.success) {
        // Unfold failed — continue with unchanged engine
        return replayProofTree(
          node.child, cursorId, engine,
          caseLabel, caseLabelLatex, inductionVar,
        );
      }

      // Normalize the goal type to reduce beta-redexes from constant unfolding
      const newGoalId = result.newEngine.getFocusedGoalId();
      const normalizedEngine = newGoalId
        ? normalizeGoalInEngine(result.newEngine, newGoalId)
        : result.newEngine;

      return replayProofTree(
        node.child, cursorId, normalizedEngine,
        caseLabel, caseLabelLatex, inductionVar,
      );
    }

    case 'induction': {
      // Direct induction goal computation — bypasses InductionTactic
      // which has a buildMotive bug assuming scrutinee at index 0.
      // Instead, we directly compute case goals by substituting the
      // scrutinee variable with the constructor pattern in the goal type.
      const goal = engine.getFocusedGoal();
      if (!goal) return null;

      // Find scrutinee in context
      const scrutineeIdx = findVarIndex(node.scrutinee, goal.ctx);
      if (scrutineeIdx === null) {
        // Scrutinee not in context — search cases with current engine
        return searchCasesForCursor(node.cases, cursorId, engine, goalId, node.scrutinee);
      }

      // Look up inductive type for constructor info
      const scrutineeType = goal.ctx[goal.ctx.length - 1 - scrutineeIdx].type;
      const scrutineeTypeWhnf = whnf(scrutineeType, { definitions: engine.definitions });
      const inductiveName = getInductiveHead(scrutineeTypeWhnf);
      if (!inductiveName) {
        return searchCasesForCursor(node.cases, cursorId, engine, goalId, node.scrutinee);
      }
      const inductiveDef = engine.definitions.inductiveTypes.get(inductiveName);
      if (!inductiveDef) {
        return searchCasesForCursor(node.cases, cursorId, engine, goalId, node.scrutinee);
      }

      // For each case node, compute case-specific goal
      for (const c of node.cases) {
        // Find matching constructor
        const ctor = inductiveDef.constructors.find(ct => ct.name === c.constructorName);
        if (!ctor) {
          // No matching constructor — use unchanged engine
          if (c.id === cursorId) {
            return { engine, goalId, caseLabel: c.label, caseLabelLatex: c.labelLatex, inductionVar: node.scrutinee };
          }
          const bodyResult = replayProofTree(c.body, cursorId, engine, c.label, c.labelLatex, node.scrutinee);
          if (bodyResult) return bodyResult;
          continue;
        }

        // Compute case-specific goal with proper variable substitution
        const caseGoalId = `${goalId}_case_${c.constructorName}`;
        const caseMeta = computeCaseGoalDirect(
          goal, scrutineeIdx, ctor, inductiveName, engine.definitions
        );

        // Create engine with this case goal
        const caseMetaVars = new Map(engine.metaVars);
        caseMetaVars.set(caseGoalId, caseMeta);
        const caseGoals = [...engine.goals];
        const focusIdx = caseGoals.indexOf(goalId);
        if (focusIdx >= 0) {
          caseGoals[focusIdx] = caseGoalId;
        } else {
          caseGoals.push(caseGoalId);
        }
        const caseEngine = engine.withUpdates({
          metaVars: caseMetaVars,
          goals: caseGoals,
          focusIndex: focusIdx >= 0 ? focusIdx : caseGoals.length - 1,
        });

        // Check cursor on case header
        if (c.id === cursorId) {
          return {
            engine: caseEngine,
            goalId: caseGoalId,
            caseLabel: c.label,
            caseLabelLatex: c.labelLatex,
            inductionVar: node.scrutinee,
          };
        }

        // Recurse into case body
        const bodyResult = replayProofTree(
          c.body, cursorId, caseEngine,
          c.label, c.labelLatex, node.scrutinee,
        );
        if (bodyResult) return bodyResult;
      }
      return null;
    }
  }
}

// ============================================================================
// Core computation
// ============================================================================

/**
 * Compute typed context at cursor position by replaying the proof tree
 * against the real TacticEngine.
 *
 * When kernelType and definitions are provided, uses the real tactic engine
 * for proper goal computation (intro, unfold, induction all work correctly).
 *
 * Falls back to surface-only rendering when kernel type is not available.
 */
export function computeTypedContext(
  root: ProofNode,
  cursorId: ProofNodeId,
  surfaceType: TTerm,
  registry: SyntaxRegistry,
  _inductiveMap?: InductiveMap,
  kernelType?: TTKTerm,
  definitions?: DefinitionsMap,
): TypedProofContext | null {
  const rev = buildReverseRegistry(registry);

  // If we have kernel type + definitions, use the real TacticEngine
  if (kernelType && definitions) {
    return computeWithTacticEngine(root, cursorId, kernelType, definitions, rev);
  }

  // Fallback: surface-only rendering (no tactic engine)
  return computeSurfaceOnly(root, cursorId, surfaceType, rev);
}

/**
 * Compute typed context using the real TacticEngine.
 */
function computeWithTacticEngine(
  root: ProofNode,
  cursorId: ProofNodeId,
  kernelType: TTKTerm,
  definitions: DefinitionsMap,
  rev: ReverseRegistry,
): TypedProofContext | null {
  // Create initial engine with the kernel goal type
  const engine = createInitialEngine(kernelType, [], definitions);

  // Replay the proof tree to find cursor position
  const replay = replayProofTree(root, cursorId, engine);
  if (!replay) return null;

  // Extract focused goal
  const goal = replay.engine.metaVars.get(replay.goalId);
  if (!goal) return null;

  // Zonk the goal type to resolve any solved metas
  const zonkedGoalType = replay.engine.zonkTerm(goal.type, goal.ctx.length);

  // Render hypotheses from MetaVar.ctx
  const hypotheses: TypedHypothesis[] = [];
  for (let i = 0; i < goal.ctx.length; i++) {
    const entry = goal.ctx[i];
    // Build name context for rendering: all entries up to (not including) this one
    const nameCtx: string[] = [];
    for (let j = i - 1; j >= 0; j--) {
      nameCtx.push(goal.ctx[j].name);
    }

    // Convert kernel type to surface, then render
    const surfaceHypType = kernelTypeToSurface(entry.type, definitions);
    const typeLatex = renderTerm(surfaceHypType, nameCtx, rev);

    hypotheses.push({
      name: entry.name,
      type: typeLatex,
      rawType: surfaceHypType,
    });
  }

  // Render goal
  const goalNameCtx: string[] = [];
  for (let j = goal.ctx.length - 1; j >= 0; j--) {
    goalNameCtx.push(goal.ctx[j].name);
  }

  // For exact nodes, show the expression rather than the goal type
  const cursorNode = findNodeById(root, cursorId);
  let goalLatex: string;
  if (cursorNode?.tag === 'exact') {
    goalLatex = cursorNode.expr;
  } else {
    const surfaceGoalType = kernelTypeToSurface(zonkedGoalType, definitions);
    goalLatex = renderTerm(surfaceGoalType, goalNameCtx, rev);
  }

  return {
    hypotheses,
    caseLabel: replay.caseLabel,
    caseLabelLatex: replay.caseLabelLatex,
    inductionVar: replay.inductionVar,
    goal: goalLatex,
  };
}

/**
 * Find a node by ID in the proof tree.
 */
function findNodeById(node: ProofNode, id: ProofNodeId): ProofNode | null {
  if (node.id === id) return node;
  switch (node.tag) {
    case 'hole':
    case 'exact':
      return null;
    case 'intros':
      return findNodeById(node.child, id);
    case 'unfold':
      return findNodeById(node.child, id);
    case 'induction':
      for (const c of node.cases) {
        if (c.id === id) return node; // Case header — return induction node
        const found = findNodeById(c.body, id);
        if (found) return found;
      }
      return null;
  }
}

/**
 * Surface-only fallback: walk the proof tree with surface types only.
 * Used when kernel type is not available.
 */
function computeSurfaceOnly(
  root: ProofNode,
  cursorId: ProofNodeId,
  surfaceType: TTerm,
  rev: ReverseRegistry,
): TypedProofContext | null {
  return walkTreeSurface(root, cursorId, surfaceType, [], [], rev);
}

/**
 * Surface-only tree walk (fallback when no kernel type available).
 * Peels Pi binders manually for intros. No unfold support.
 */
function walkTreeSurface(
  node: ProofNode,
  cursorId: ProofNodeId,
  currentType: TTerm,
  hypotheses: readonly TypedHypothesis[],
  nameCtx: readonly string[],
  rev: ReverseRegistry,
): TypedProofContext | null {
  if (node.id === cursorId) {
    const goal = node.tag === 'exact' ? node.expr : renderTerm(currentType, [...nameCtx], rev);
    return { hypotheses, goal };
  }

  switch (node.tag) {
    case 'hole':
    case 'exact':
      return null;

    case 'intros': {
      let type = currentType;
      const extHyps: TypedHypothesis[] = [...hypotheses];
      const extCtx: string[] = [...nameCtx];

      for (const name of node.names) {
        const pi = peelPi(type);
        if (pi) {
          let current = pi;
          while (current.isImplicit) {
            extCtx.unshift(current.name);
            const next = peelPi(current.body);
            if (!next) break;
            current = next;
          }
          extHyps.push({
            name,
            type: renderTerm(current.domain, extCtx, rev),
            rawType: current.domain,
          });
          extCtx.unshift(name);
          type = current.body;
        } else {
          extHyps.push({ name, type: '?' });
          extCtx.unshift(name);
        }
      }

      return walkTreeSurface(node.child, cursorId, type, extHyps, extCtx, rev);
    }

    case 'unfold':
      // No kernel type — can't unfold, pass through
      return walkTreeSurface(node.child, cursorId, currentType, hypotheses, nameCtx, rev);

    case 'induction': {
      for (const c of node.cases) {
        if (c.id === cursorId) {
          return {
            hypotheses,
            caseLabel: c.label,
            caseLabelLatex: c.labelLatex,
            inductionVar: node.scrutinee,
            goal: renderTerm(currentType, [...nameCtx], rev),
          };
        }
        const result = walkTreeSurface(c.body, cursorId, currentType, hypotheses, nameCtx, rev);
        if (result) {
          return {
            ...result,
            caseLabel: result.caseLabel ?? c.label,
            caseLabelLatex: result.caseLabelLatex ?? c.labelLatex,
            inductionVar: result.inductionVar ?? node.scrutinee,
          };
        }
      }
      return null;
    }
  }
}
