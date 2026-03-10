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

import { TTerm, TPattern, mkConstTT, mkAppTT, mkVarTT, mkPiTT, mkPropTT, mkHoleTT, mkULitTT } from '../compiler/surface';
import { TTKTerm, TTKPattern } from '../compiler/kernel';
import { DefinitionsMap, NamedArgMap, MetaVar, createDefinitionsMap } from '../compiler/term';
import { whnf } from '../compiler/whnf';
import { shiftTerm, subst, betaNormalize } from '../compiler/subst';
import { SyntaxRegistry } from '../math-editor/syntax-registry';
import { ReverseRegistry, buildReverseRegistry, ttermToMathNodes } from '../math-editor/tt-to-math';
import { mkRow } from '../math-editor/types';
import { renderStaticLatex } from '../math-editor/render';
import { ProofNode, ProofNodeId, CaseNode } from './proof-tree';
import { TacticEngine, createInitialEngine } from '../tactics/tacticsEngine';
import { IntrosTactic, ApplyTactic, ExactTactic } from '../tactics/tactic';
import { UnfoldTactic } from '../tactics/unfold-tactic';
import { RewriteTactic } from '../tactics/rewrite-tactic';

// ============================================================================
// Types
// ============================================================================

export interface TypedHypothesis {
  readonly name: string;
  readonly type: string;  // LaTeX string from structured math renderer
  readonly rawType?: TTerm;  // Raw surface type (for inductive type lookup)
}

export type ValidationResult =
  | { readonly status: 'solved' }
  | { readonly status: 'error'; readonly message: string };

export interface TypedProofContext {
  readonly hypotheses: readonly TypedHypothesis[];
  readonly caseLabel?: string;
  readonly caseLabelLatex?: string;
  readonly inductionVar?: string;
  readonly goal: string;  // LaTeX string from structured math renderer
  readonly validation?: ValidationResult;
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

/** Convert a kernel TTKPattern to a surface TPattern. */
function kernelPatternToSurface(p: TTKPattern): TPattern {
  switch (p.tag) {
    case 'PVar': return { tag: 'PVar', name: p.name };
    case 'PWild': return { tag: 'PWild' };
    case 'PCtor': return {
      tag: 'PCtor',
      name: p.name,
      args: p.args.map(a => kernelPatternToSurface(a)),
    };
  }
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
      // Render Match as a case-of application: show scrutinee and clause RHS bodies
      // This arises when unfolding pattern-matching definitions (e.g., unfold minus)
      // where the scrutinee is a variable, so iota-reduction can't fire.
      // Render as: match scrutinee { clause1 | clause2 | ... }
      // For now, render just the scrutinee as a visual indicator.
      const scrut = kernelTypeToSurface(t.scrutinee, definitions);
      // Show each clause RHS
      const clauseTerms = t.clauses.map(c => kernelTypeToSurface(c.rhs, definitions));
      if (clauseTerms.length === 0) return mkHoleTT('_empty_match', prop);
      // Use a simple rendering: first clause that isn't a hole
      // Actually, render as a structured Match TTerm if available,
      // otherwise show scrutinee
      return {
        tag: 'Match',
        scrutinee: scrut,
        clauses: t.clauses.map(c => ({
          patterns: c.patterns.map(p => kernelPatternToSurface(p)),
          rhs: kernelTypeToSurface(c.rhs, definitions),
        })),
      } as TTerm;
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

  // Use empty definitions so fullNormalize only does beta/iota reduction,
  // not delta-reduction of other constants. UnfoldTactic already replaced
  // the target constant with its lambda body — we just need to beta-reduce
  // the resulting (\x => body)(arg) redexes.
  const normalized = fullNormalize(goal.type, createDefinitionsMap());
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
  /** Error from a failed tactic (rewrite, unfold, apply) that preceded the cursor */
  tacticError?: string;
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

/**
 * Remap variables in a term for the restructured induction case context.
 *
 * When performing induction, the scrutinee is REMOVED from context and replaced
 * by constructor parameters. This function adjusts de Bruijn indices in a term
 * (typically the goal type or IH type) to account for this restructuring.
 *
 * Original context: [...far..., scrutinee, ...near...]
 * New context:      [...far..., params..., ...near..., (IH)]
 *
 * Variable mapping (at depth 0):
 *   Var(k) for k < scrutineeIdx  → Var(k + ihOffset)                [near entries shift for IH]
 *   Var(scrutineeIdx)            → ctorApp                           [scrutinee → constructor]
 *   Var(k) for k > scrutineeIdx  → Var(k + numParams - 1 + ihOffset) [far entries shift for params+IH]
 *
 * Under binders, the scrutinee index shifts up by depth.
 */
function remapScrutineeVars(
  term: TTKTerm,
  scrutineeIdx: number,
  ctorApp: TTKTerm,
  numParams: number,
  ihOffset: number,
): TTKTerm {
  function go(t: TTKTerm, depth: number): TTKTerm {
    switch (t.tag) {
      case 'Var': {
        if (t.index < depth) return t; // bound by local binder, unchanged
        const adjustedScrutIdx = scrutineeIdx + depth;
        if (t.index === adjustedScrutIdx) {
          return shiftTerm(ctorApp, depth, 0);
        } else if (t.index < adjustedScrutIdx) {
          // Context var with original idx < scrutineeIdx (near entries)
          return ihOffset === 0 ? t : { tag: 'Var', index: t.index + ihOffset };
        } else {
          // Context var with original idx > scrutineeIdx (far entries)
          const shift = numParams - 1 + ihOffset;
          return shift === 0 ? t : { tag: 'Var', index: t.index + shift };
        }
      }
      case 'App': {
        const fn = go(t.fn, depth);
        const arg = go(t.arg, depth);
        if (fn === t.fn && arg === t.arg) return t;
        return { tag: 'App', fn, arg };
      }
      case 'Binder': {
        const domain = go(t.domain, depth);
        const body = go(t.body, depth + 1);
        if (domain === t.domain && body === t.body) return t;
        return { ...t, domain, body };
      }
      case 'Match': {
        const scrutinee = go(t.scrutinee, depth);
        let changed = scrutinee !== t.scrutinee;
        const clauses = t.clauses.map(c => {
          const numVars = countPatternVars(c.patterns[0]);
          const rhs = go(c.rhs, depth + numVars);
          if (rhs !== c.rhs) changed = true;
          return rhs === c.rhs ? c : { ...c, rhs };
        });
        if (!changed) return t;
        return { tag: 'Match', scrutinee, clauses };
      }
      default:
        return t;
    }
  }
  return go(term, 0);
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
  const s = goal.ctx.length - 1 - scrutineeIdx; // scrutinee array position
  const scrutineeType = goal.ctx[s].type;
  const typeArgs = extractTypeArgsFromType(scrutineeType);

  // Count constructor parameters (skip implicit ones)
  const numImplicit = ctor.namedArgMap?.size ?? 0;
  const { params, hasRecursiveParam, recursiveParamLocalIdx } = peelCtorParams(
    ctor.type, numImplicit, typeArgs, inductiveName, definitions
  );

  const numParams = params.length;
  const ihOffset = hasRecursiveParam ? 1 : 0;
  const netShift = numParams - 1; // replacing 1 scrutinee entry with numParams param entries

  // Build restructured context:
  // [entries_before_scrutinee, ctor_params, entries_after_scrutinee (subst'd), IH]
  // The scrutinee is REMOVED and replaced by ctor params. This ensures params
  // are in scope for entries that depended on the scrutinee (e.g., l : Leq i n
  // becomes l : Leq i Zero in the Zero case, or l : Leq i (Succ n') in Succ).
  const newCtx: Array<{ name: string; type: TTKTerm }> = [];

  // 1. Entries before scrutinee (positions 0..s-1): unchanged
  for (let j = 0; j < s; j++) {
    newCtx.push(goal.ctx[j]);
  }

  // 2. Constructor params (at positions s..s+numParams-1, replacing the scrutinee)
  for (let i = 0; i < numParams; i++) {
    const shiftedType = shiftTerm(params[i].type, s, 0);
    newCtx.push({ name: params[i].name, type: shiftedType });
  }

  // 3. Entries after scrutinee: substitute scrutinee var with ctor app.
  //    Use replaceVar (not subst) FIRST to avoid index collisions,
  //    then shift for the extra params.
  for (let j = s + 1; j < goal.ctx.length; j++) {
    let entryType = goal.ctx[j].type;
    const scrutVarInEntry = j - 1 - s; // scrutinee's de Bruijn index in this entry's type

    // Build ctor app for this entry's scope. After restructuring:
    // - The entry moves from position j to position j+netShift
    // - Params at positions s..s+numParams-1
    // - Last param at Var(j-1-s) = same index as old scrutinee
    // - First param at Var(j-1-s + numParams-1)
    let ctorAppLocal: TTKTerm = { tag: 'Const', name: ctor.name };
    for (let i = 0; i < numParams; i++) {
      ctorAppLocal = {
        tag: 'App',
        fn: ctorAppLocal,
        arg: { tag: 'Var', index: scrutVarInEntry + numParams - 1 - i },
      };
    }

    // Replace the scrutinee var with ctor app (no index shifting)
    entryType = replaceVar(entryType, scrutVarInEntry, ctorAppLocal);

    // Shift vars pointing to entries before scrutinee (index >= j-s after replaceVar)
    // by netShift, because those entries are now further away due to inserted params.
    if (netShift !== 0) {
      entryType = shiftTerm(entryType, netShift, j - s);
    }
    newCtx.push({ name: goal.ctx[j].name, type: entryType });
  }

  // Build goal type using remapScrutineeVars: a custom variable remapping that
  // correctly handles the restructured context (scrutinee removed, params inserted).
  //
  // Original var mapping → new index:
  //   Var(k) for k < scrutineeIdx  → Var(k + ihOffset)              [near entries]
  //   Var(scrutineeIdx)            → ctorApp                         [scrutinee replaced]
  //   Var(k) for k > scrutineeIdx  → Var(k + numParams - 1 + ihOffset) [far entries]

  // Build ctorApp for goal scope with FINAL indices:
  //   param[i] at position s+i → Var(scrutineeIdx + numParams - 1 + ihOffset - i)
  let ctorAppGoal: TTKTerm = { tag: 'Const', name: ctor.name };
  for (let i = 0; i < numParams; i++) {
    ctorAppGoal = {
      tag: 'App',
      fn: ctorAppGoal,
      arg: { tag: 'Var', index: scrutineeIdx + numParams - 1 + ihOffset - i },
    };
  }

  const caseGoalType = remapScrutineeVars(
    goal.type, scrutineeIdx, ctorAppGoal, numParams, ihOffset
  );

  // Add induction hypothesis if recursive
  if (hasRecursiveParam && recursiveParamLocalIdx !== null) {
    // IH type: goal with scrutinee replaced by the recursive param.
    // IH sees entries 0..newCtx.length-2 (everything before IH itself).
    // IH scope depth = newCtx.length - 1 = n + numParams - 2 (without IH's own entry).
    // But IH is about to be pushed, making newCtx.length = n + numParams - 1 + 1.
    // From IH's scope (depth = n + numParams - 1, not counting itself):
    //   param[recursiveParamLocalIdx] at position s + recursiveParamLocalIdx
    //   → Var(scrutineeIdx + numParams - 1 - recursiveParamLocalIdx)
    const recursiveParamRef: TTKTerm = {
      tag: 'Var',
      index: scrutineeIdx + numParams - 1 - recursiveParamLocalIdx,
    };

    // Remap with ihOffset=0 since IH doesn't count itself
    const ihType = remapScrutineeVars(
      goal.type, scrutineeIdx, recursiveParamRef, numParams, 0
    );

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
        // Unfold failed — continue with unchanged engine, propagate error
        const childResult = replayProofTree(
          node.child, cursorId, engine,
          caseLabel, caseLabelLatex, inductionVar,
        );
        if (childResult) {
          childResult.tacticError = `unfold ${node.name}: ${result.error ?? 'failed'}`;
        }
        return childResult;
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

    case 'rewrite': {
      // Apply RewriteTactic with Const(name) as the equality proof
      const goal = engine.getFocusedGoal();
      if (!goal) return null;

      const tactic = new RewriteTactic(
        { tag: 'Const', name: node.name },
        { reverse: node.reverse },
      );
      const result = tactic.apply(engine, goal, goalId);

      if (!result.success) {
        // Rewrite failed — continue with unchanged engine, propagate error
        const childResult = replayProofTree(
          node.child, cursorId, engine,
          caseLabel, caseLabelLatex, inductionVar,
        );
        if (childResult) {
          childResult.tacticError = `rewrite ${node.reverse ? '← ' : ''}${node.name}: ${result.error ?? 'failed'}`;
        }
        return childResult;
      }

      return replayProofTree(
        node.child, cursorId, result.newEngine!,
        caseLabel, caseLabelLatex, inductionVar,
      );
    }

    case 'apply': {
      // Apply ApplyTactic with Const(name) as the function
      const goal = engine.getFocusedGoal();
      if (!goal) return null;

      const tactic = new ApplyTactic({ tag: 'Const', name: node.name });
      const result = tactic.apply(engine, goal, goalId);

      if (!result.success) {
        // Apply failed — search children with unchanged engine
        for (const child of node.children) {
          if (child.id === cursorId) {
            return { engine, goalId, caseLabel, caseLabelLatex, inductionVar };
          }
          const childResult = replayProofTree(
            child, cursorId, engine,
            caseLabel, caseLabelLatex, inductionVar,
          );
          if (childResult) return childResult;
        }
        return null;
      }

      // Apply succeeded — match children to subgoals
      const newEngine = result.newEngine!;
      const baseFocus = newEngine.focusIndex;

      for (let i = 0; i < node.children.length; i++) {
        const child = node.children[i];
        // Focus engine on the i-th subgoal
        const childFocusIdx = baseFocus + i;
        if (childFocusIdx >= newEngine.goals.length) break;

        const childEngine = newEngine.withUpdates({ focusIndex: childFocusIdx });

        if (child.id === cursorId) {
          const childGoalId = childEngine.getFocusedGoalId();
          return {
            engine: childEngine,
            goalId: childGoalId!,
            caseLabel, caseLabelLatex, inductionVar,
          };
        }

        const childResult = replayProofTree(
          child, cursorId, childEngine,
          caseLabel, caseLabelLatex, inductionVar,
        );
        if (childResult) return childResult;
      }
      return null;
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
// Apply subgoal count — used by UI to determine number of children
// ============================================================================

/**
 * Compute how many subgoals `apply <name>` creates at the given cursor position.
 * Returns 1 as fallback if engine replay or tactic application fails.
 */
export function computeApplySubgoalCount(
  root: ProofNode,
  cursorId: ProofNodeId,
  kernelType: TTKTerm,
  definitions: DefinitionsMap,
  name: string,
): number {
  try {
    const engine = createInitialEngine(kernelType, [], definitions);
    const replay = replayProofTree(root, cursorId, engine);
    if (!replay) return 1;

    const goal = replay.engine.metaVars.get(replay.goalId);
    if (!goal) return 1;

    const tactic = new ApplyTactic({ tag: 'Const', name });
    const result = tactic.apply(replay.engine, goal, replay.goalId);
    if (!result.success || !result.newEngine) return 1;

    // Number of new subgoals = new goals count - old goals count + 1
    // (the focused goal was removed and replaced by N new ones)
    const numSubgoals = result.newEngine.goals.length - replay.engine.goals.length + 1;
    return Math.max(1, numSubgoals);
  } catch {
    return 1;
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
 * Validate an exact node by resolving the expression to a kernel term
 * and running ExactTactic to type-check it against the goal.
 */
function validateExactNode(
  expr: string,
  engine: TacticEngine,
  goalId: string,
): ValidationResult {
  const goal = engine.metaVars.get(goalId);
  if (!goal) return { status: 'error', message: 'No goal' };

  // Resolve expression: try as context variable first, then as constant
  const varIdx = findVarIndex(expr, goal.ctx);
  const term: TTKTerm = varIdx !== null
    ? { tag: 'Var', index: varIdx }
    : { tag: 'Const', name: expr };

  const tactic = new ExactTactic(term);
  const result = tactic.apply(engine, goal, goalId);
  if (result.success) {
    return { status: 'solved' };
  }
  return { status: 'error', message: result.error ?? 'Type mismatch' };
}

// ============================================================================
// Rendering helpers (shared by computeWithTacticEngine and replayEntireTree)
// ============================================================================

/** Build a de Bruijn name context for rendering a term at depth `ctx.length`. */
/** Check if a term contains any Hole or Meta (unsolved). */
function containsHoleOrMeta(t: TTKTerm): boolean {
  switch (t.tag) {
    case 'Hole': case 'Meta': return true;
    case 'App': return containsHoleOrMeta(t.fn) || containsHoleOrMeta(t.arg);
    case 'Binder': return containsHoleOrMeta(t.domain) || containsHoleOrMeta(t.body);
    case 'Match': return containsHoleOrMeta(t.scrutinee) || t.clauses.some(c => containsHoleOrMeta(c.rhs));
    default: return false;
  }
}

function buildNameCtx(ctx: ReadonlyArray<{ name: string }>): string[] {
  const nameCtx: string[] = [];
  for (let j = ctx.length - 1; j >= 0; j--) {
    nameCtx.push(ctx[j].name);
  }
  return nameCtx;
}

/** Render hypotheses from a MetaVar's context to TypedHypothesis[]. */
function renderHypotheses(
  ctx: ReadonlyArray<{ name: string; type: TTKTerm }>,
  definitions: DefinitionsMap,
  rev: ReverseRegistry,
): TypedHypothesis[] {
  const hypotheses: TypedHypothesis[] = [];
  for (let i = 0; i < ctx.length; i++) {
    const entry = ctx[i];
    const nameCtx: string[] = [];
    for (let j = i - 1; j >= 0; j--) {
      nameCtx.push(ctx[j].name);
    }
    const normalizedType = betaNormalize(entry.type);
    const surfaceHypType = kernelTypeToSurface(normalizedType, definitions);
    const typeLatex = renderTerm(surfaceHypType, nameCtx, rev);
    hypotheses.push({ name: entry.name, type: typeLatex, rawType: surfaceHypType });
  }
  return hypotheses;
}

/** Render a goal type to LaTeX from a TacticEngine + goal MetaVar. */
export function renderGoalLatex(
  engine: TacticEngine,
  goal: MetaVar,
  definitions: DefinitionsMap,
  rev: ReverseRegistry,
): string {
  const zonked = engine.zonkTerm(goal.type, goal.ctx.length);
  // Beta-normalize to clean up redexes like (\i => i)(0) → 0
  const normalized = betaNormalize(zonked);
  const surface = kernelTypeToSurface(normalized, definitions);
  return renderTerm(surface, buildNameCtx(goal.ctx), rev);
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

  // Render hypotheses and goal using shared helpers
  const hypotheses = renderHypotheses(goal.ctx, definitions, rev);

  // For exact nodes, show the expression and validate it
  const cursorNode = findNodeById(root, cursorId);
  let goalLatex: string;
  let validation: ValidationResult | undefined;
  if (cursorNode?.tag === 'exact') {
    goalLatex = cursorNode.expr;
    validation = validateExactNode(cursorNode.expr, replay.engine, replay.goalId);
  } else {
    goalLatex = renderGoalLatex(replay.engine, goal, definitions, rev);
  }

  // Surface tactic errors (failed rewrite/unfold) as validation errors
  if (!validation && replay.tacticError) {
    validation = { status: 'error', message: replay.tacticError };
  }

  return {
    hypotheses,
    caseLabel: replay.caseLabel,
    caseLabelLatex: replay.caseLabelLatex,
    inductionVar: replay.inductionVar,
    goal: goalLatex,
    validation,
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
    case 'unfold':
    case 'rewrite':
      return findNodeById(node.child, id);
    case 'apply':
      for (const child of node.children) {
        const found = findNodeById(child, id);
        if (found) return found;
      }
      return null;
    case 'induction':
      for (const c of node.cases) {
        if (c.id === id) return node; // Case header — return induction node
        const found = findNodeById(c.body, id);
        if (found) return found;
      }
      return null;
  }
}

// ============================================================================
// Replay Entire Tree — collect goal info at every node
// ============================================================================

export interface NodeGoalInfo {
  readonly goalLatex: string;
  readonly hypotheses: readonly TypedHypothesis[];
  readonly caseLabelLatex?: string;
  readonly validation?: ValidationResult;
  /** For rewrite nodes: the unified equation (lhs = rhs) with all implicit args filled in. */
  readonly unifiedEquationLatex?: string;
  /** For apply nodes: LaTeX of solved explicit args (e.g., "f" in "cong f"). */
  readonly appliedArgsLatex?: string[];
}

/**
 * Replay the entire proof tree, collecting goal info at every node.
 * Unlike replayProofTree (which stops at cursor), this visits all nodes
 * and builds a complete map for prose rendering.
 */
export function replayEntireTree(
  root: ProofNode,
  kernelType: TTKTerm,
  definitions: DefinitionsMap,
  rev: ReverseRegistry,
): Map<ProofNodeId, NodeGoalInfo> {
  const result = new Map<ProofNodeId, NodeGoalInfo>();
  const engine = createInitialEngine(kernelType, [], definitions);

  function recordGoal(nodeId: ProofNodeId, eng: TacticEngine, gId: string, caseLabelLatex?: string): void {
    const goal = eng.metaVars.get(gId);
    if (!goal) return;
    result.set(nodeId, {
      goalLatex: renderGoalLatex(eng, goal, definitions, rev),
      hypotheses: renderHypotheses(goal.ctx, definitions, rev),
      caseLabelLatex,
    });
  }

  function recordExact(nodeId: ProofNodeId, eng: TacticEngine, gId: string, expr: string): void {
    const goal = eng.metaVars.get(gId);
    if (!goal) return;
    const validation = validateExactNode(expr, eng, gId);
    result.set(nodeId, {
      goalLatex: renderGoalLatex(eng, goal, definitions, rev),
      hypotheses: renderHypotheses(goal.ctx, definitions, rev),
      validation,
    });
  }

  function walk(
    node: ProofNode,
    eng: TacticEngine,
    caseLabelLatex?: string,
  ): void {
    const gId = eng.getFocusedGoalId();
    if (!gId) return;

    switch (node.tag) {
      case 'hole': {
        recordGoal(node.id, eng, gId, caseLabelLatex);
        break;
      }

      case 'exact': {
        recordExact(node.id, eng, gId, node.expr);
        break;
      }

      case 'intros': {
        recordGoal(node.id, eng, gId, caseLabelLatex);
        const goal = eng.getFocusedGoal();
        if (!goal) { walk(node.child, eng, caseLabelLatex); break; }
        const tactic = new IntrosTactic([...node.names]);
        const tacResult = tactic.apply(eng, goal, gId);
        walk(node.child, tacResult.success ? tacResult.newEngine! : eng, caseLabelLatex);
        break;
      }

      case 'unfold': {
        recordGoal(node.id, eng, gId, caseLabelLatex);
        const goal = eng.getFocusedGoal();
        if (!goal) { walk(node.child, eng, caseLabelLatex); break; }
        const tactic = new UnfoldTactic([node.name]);
        const tacResult = tactic.apply(eng, goal, gId);
        if (tacResult.success) {
          const newGoalId = tacResult.newEngine!.getFocusedGoalId();
          const normalized = newGoalId
            ? normalizeGoalInEngine(tacResult.newEngine!, newGoalId)
            : tacResult.newEngine!;
          walk(node.child, normalized, caseLabelLatex);
        } else {
          walk(node.child, eng, caseLabelLatex);
        }
        break;
      }

      case 'rewrite': {
        recordGoal(node.id, eng, gId, caseLabelLatex);
        const goal = eng.getFocusedGoal();
        if (!goal) { walk(node.child, eng, caseLabelLatex); break; }
        const tactic = new RewriteTactic(
          { tag: 'Const', name: node.name },
          { reverse: node.reverse },
        );
        const tacResult = tactic.apply(eng, goal, gId);
        // Capture the unified equation and attach it to this node's info
        if (tacResult.success && tacResult.unifiedEquation) {
          const newEngine = tacResult.newEngine!;
          const { lhs: rawLhs, rhs: rawRhs } = tacResult.unifiedEquation;
          // Zonk to resolve metas, then beta-normalize to clean up redexes
          const lhs = betaNormalize(newEngine.zonkTerm(rawLhs, goal.ctx.length));
          const rhs = betaNormalize(newEngine.zonkTerm(rawRhs, goal.ctx.length));
          const nameCtx = buildNameCtx(goal.ctx);
          const lhsSurface = kernelTypeToSurface(lhs, definitions);
          const rhsSurface = kernelTypeToSurface(rhs, definitions);
          const lhsLatex = renderTerm(lhsSurface, nameCtx, rev);
          const rhsLatex = renderTerm(rhsSurface, nameCtx, rev);
          const existing = result.get(node.id);
          if (existing) {
            result.set(node.id, { ...existing, unifiedEquationLatex: `${lhsLatex} = ${rhsLatex}` });
          }
        }
        walk(node.child, tacResult.success ? tacResult.newEngine! : eng, caseLabelLatex);
        break;
      }

      case 'apply': {
        recordGoal(node.id, eng, gId, caseLabelLatex);
        const goal = eng.getFocusedGoal();
        if (!goal) {
          for (const child of node.children) walk(child, eng, caseLabelLatex);
          break;
        }
        const tactic = new ApplyTactic({ tag: 'Const', name: node.name });
        const tacResult = tactic.apply(eng, goal, gId);
        if (!tacResult.success) {
          for (const child of node.children) walk(child, eng, caseLabelLatex);
          break;
        }

        // Extract solved value-level args for prose rendering (e.g., "f" in "cong f")
        // Skip type-level args (whose type is Sort) and unsolved args (subgoals).
        const newEngine = tacResult.newEngine!;
        if (tacResult.solvedArgs) {
          const nameCtx = buildNameCtx(goal.ctx);
          const appliedArgsLatex: string[] = [];
          for (const arg of tacResult.solvedArgs) {
            if (arg.term.tag === 'Hole' || arg.term.tag === 'Meta') continue; // unsolved
            if (arg.type.tag === 'Sort') continue; // type-level arg (e.g., {A : Type})
            try {
              // Zonk to resolve any metas, then beta-normalize
              const zonked = betaNormalize(newEngine.zonkTerm(arg.term, goal.ctx.length));
              const surface = kernelTypeToSurface(zonked, definitions);
              const latex = renderTerm(surface, nameCtx, rev);
              appliedArgsLatex.push(latex);
            } catch {
              // rendering failed — skip
            }
          }
          if (appliedArgsLatex.length > 0) {
            const existing = result.get(node.id);
            if (existing) {
              result.set(node.id, { ...existing, appliedArgsLatex });
            }
          }
        }

        const baseFocus = newEngine.focusIndex;
        for (let i = 0; i < node.children.length; i++) {
          const childFocusIdx = baseFocus + i;
          if (childFocusIdx >= newEngine.goals.length) break;
          const childEngine = newEngine.withUpdates({ focusIndex: childFocusIdx });
          walk(node.children[i], childEngine, caseLabelLatex);
        }
        break;
      }

      case 'induction': {
        recordGoal(node.id, eng, gId, caseLabelLatex);
        const goal = eng.getFocusedGoal();
        if (!goal) break;

        const scrutineeIdx = findVarIndex(node.scrutinee, goal.ctx);
        if (scrutineeIdx === null) {
          // Fallback: record each case with unchanged engine
          for (const c of node.cases) {
            recordGoal(c.id, eng, gId, c.labelLatex);
            walk(c.body, eng, c.labelLatex);
          }
          break;
        }

        const scrutineeType = goal.ctx[goal.ctx.length - 1 - scrutineeIdx].type;
        const scrutineeTypeWhnf = whnf(scrutineeType, { definitions: eng.definitions });
        const inductiveName = getInductiveHead(scrutineeTypeWhnf);
        if (!inductiveName) {
          for (const c of node.cases) {
            recordGoal(c.id, eng, gId, c.labelLatex);
            walk(c.body, eng, c.labelLatex);
          }
          break;
        }
        const inductiveDef = eng.definitions.inductiveTypes.get(inductiveName);
        if (!inductiveDef) {
          for (const c of node.cases) {
            recordGoal(c.id, eng, gId, c.labelLatex);
            walk(c.body, eng, c.labelLatex);
          }
          break;
        }

        for (const c of node.cases) {
          const ctor = inductiveDef.constructors.find(ct => ct.name === c.constructorName);
          if (!ctor) {
            recordGoal(c.id, eng, gId, c.labelLatex);
            walk(c.body, eng, c.labelLatex);
            continue;
          }
          const caseGoalId = `${gId}_case_${c.constructorName}`;
          const caseMeta = computeCaseGoalDirect(goal, scrutineeIdx, ctor, inductiveName, eng.definitions);
          const caseMetaVars = new Map(eng.metaVars);
          caseMetaVars.set(caseGoalId, caseMeta);
          const caseGoals = [...eng.goals];
          const focusIdx = caseGoals.indexOf(gId);
          if (focusIdx >= 0) caseGoals[focusIdx] = caseGoalId;
          else caseGoals.push(caseGoalId);
          const caseEngine = eng.withUpdates({
            metaVars: caseMetaVars,
            goals: caseGoals,
            focusIndex: focusIdx >= 0 ? focusIdx : caseGoals.length - 1,
          });
          recordGoal(c.id, caseEngine, caseGoalId, c.labelLatex);
          walk(c.body, caseEngine, c.labelLatex);
        }
        break;
      }
    }
  }

  walk(root, engine);
  return result;
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
    case 'rewrite':
      // No kernel type — can't process, pass through
      return walkTreeSurface(node.child, cursorId, currentType, hypotheses, nameCtx, rev);

    case 'apply':
      // No kernel type — can't process, pass through each child
      for (const child of node.children) {
        const result = walkTreeSurface(child, cursorId, currentType, hypotheses, nameCtx, rev);
        if (result) return result;
      }
      return null;

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
