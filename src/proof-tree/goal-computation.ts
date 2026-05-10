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

import { TTerm, TPattern, CasePattern, mkConstTT, mkAppTT, mkAppSpineTT, mkVarTT, mkPiTT, mkPropTT, mkHoleTT, mkULitTT } from '../compiler/surface';
import { TTKTerm, TTKPattern, TTKContext, mkConst, mkApp } from '../compiler/kernel';
import { countKernelClauseBindings } from '../compiler/pattern-binders';
import { DefinitionsMap, NamedArgMap, MetaVar, createDefinitionsMap, createNamedArgLookup } from '../compiler/term';
import { inferType, checkType } from '../compiler/checker';
import { elaborateTermInContext, inferTermTypeInContext } from '../compiler/contextual-inference';
import { whnf, fullNormalize } from '../compiler/whnf';
import { shiftTerm, subst, betaNormalize } from '../compiler/subst';
import { SyntaxRegistry } from '../math-editor/syntax-registry';
import { ReverseRegistry, buildReverseRegistry, ttermToMathNodes, SubtermAnnotator } from '../math-editor/tt-to-math';
import { mkRow } from '../math-editor/types';
import { renderStaticLatex } from '../math-editor/render';
import { ProofNode, ProofNodeId, CaseNode, isCursorInSubtree } from './proof-tree';
import { TacticEngine, createInitialEngine } from '../tactics/tacticsEngine';
import { IntrosTactic, ApplyTactic, ExactTactic } from '../tactics/tactic';
import { UnfoldTactic } from '../tactics/unfold-tactic';
import { FoldTactic } from '../tactics/fold-tactic';
import { RewriteTactic } from '../tactics/rewrite-tactic';
import { HaveTactic } from '../tactics/have-tactic';
import { ConstructorTactic } from '../tactics/constructor-tactic';
import { proposeVarName, freshenName } from './propose-var-name';

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
  /** Kernel-level goal info for interactive rendering (available when using TacticEngine). */
  readonly kernelGoal?: {
    readonly engine: TacticEngine;
    readonly goal: MetaVar;
    readonly definitions: DefinitionsMap;
    readonly rev: ReverseRegistry;
  };
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
      namedArgs: p.namedArgs?.map(na => ({
        name: na.name,
        pattern: kernelPatternToSurface(na.pattern),
      })),
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
          // @ofNat coercion fold: a fully-applied registered @ofNat function
          // wrapping a NatLit is just the literal at the display level.
          // \`realOfNat R (NatLit 1)\` → \`1\`, hiding the kernel coercion that
          // makes \`1 : Carrier R\` work.
          const ofNatReg = definitions.ofNatByTargetHead;
          if (ofNatReg && [...ofNatReg.values()].includes(head.name)) {
            const last = args[args.length - 1];
            if (last && last.tag === 'NatLit') {
              return { tag: 'NatLit', value: last.value } as TTerm;
            }
          }
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
    case 'NatLit': return { tag: 'NatLit', value: t.value } as TTerm;
    case 'Hole': return mkHoleTT(t.id, prop);
    case 'Meta': return mkHoleTT(t.id, prop);
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
          namedPatterns: c.namedPatterns?.map(np => ({
            name: np.name,
            pattern: kernelPatternToSurface(np.pattern),
          })),
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

/**
 * Collect the App spine: App(App(f, a), b) → { head: f, args: [a, b] }
 */
function collectSpine(term: TTKTerm): { head: TTKTerm; args: TTKTerm[] } {
  const args: TTKTerm[] = [];
  let current = term;
  while (current.tag === 'App') {
    args.unshift(current.arg);
    current = current.fn;
  }
  return { head: current, args };
}

function rebuildApp(head: TTKTerm, args: TTKTerm[]): TTKTerm {
  let result = head;
  for (const arg of args) {
    result = { tag: 'App', fn: result, arg };
  }
  return result;
}

/**
 * Prepare Match terms for iota-reduction by WHNF-ing critical positions
 * with real definitions, without delta-reducing other constants.
 *
 * Handles two patterns:
 * 1. Single-scrutinee: `Match(Const("one"), ...)` → whnf scrutinee
 * 2. Multi-arg (Hole scrutinee): `App(App(Match(Hole, ...), one), one)`
 *    → whnf each applied arg to expose constructors
 */
function prepareMatchesForIota(term: TTKTerm, definitions: DefinitionsMap): TTKTerm {
  switch (term.tag) {
    case 'Match': {
      const scrut = prepareMatchesForIota(term.scrutinee, definitions);
      const whnfScrut = (scrut.tag === 'Const') ? whnf(scrut, { definitions }) : scrut;
      const newClauses = term.clauses.map(c => ({
        ...c,
        rhs: prepareMatchesForIota(c.rhs, definitions),
      }));
      if (whnfScrut === term.scrutinee && newClauses.every((c, i) => c.rhs === term.clauses[i].rhs))
        return term;
      return { ...term, scrutinee: whnfScrut, clauses: newClauses };
    }
    case 'App': {
      // Check for multi-arg Match pattern: App(App(Match(Hole, ...), arg1), arg2)
      const { head, args } = collectSpine(term);
      if (head.tag === 'Match' && head.scrutinee.tag === 'Hole') {
        // WHNF each arg with real definitions to expose constructors
        const newArgs = args.map(a => {
          const prepared = prepareMatchesForIota(a, definitions);
          // Only whnf Const args (value aliases like `one`, `two`)
          if (prepared.tag === 'Const') return whnf(prepared, { definitions });
          // Also handle App(Const("Succ"), Const("Zero")) etc. already reduced
          return prepared;
        });
        const newHead = prepareMatchesForIota(head, definitions);
        const changed = newHead !== head || newArgs.some((a, i) => a !== args[i]);
        return changed ? rebuildApp(newHead, newArgs) : term;
      }
      // Regular App — just recurse
      const newFn = prepareMatchesForIota(term.fn, definitions);
      const newArg = prepareMatchesForIota(term.arg, definitions);
      if (newFn === term.fn && newArg === term.arg) return term;
      return { ...term, fn: newFn, arg: newArg };
    }
    case 'Binder': {
      const newDomain = prepareMatchesForIota(term.domain, definitions);
      const newBody = prepareMatchesForIota(term.body, definitions);
      if (newDomain === term.domain && newBody === term.body) return term;
      return { ...term, domain: newDomain, body: newBody };
    }
    default:
      return term;
  }
}

/**
 * Build a map from (constructorName, fieldPosition) → projectionName.
 * Used to fold projection-like Match expressions back to their Const form.
 *
 * A projection value looks like: λ params... λ r. match r { Ctor(_, _, PVar, _, ...) => Var(0) }
 * where only one pattern arg is PVar (the projected field) and the rest are PWild.
 */
export function buildProjectionFoldMap(definitions: DefinitionsMap): Map<string, Map<number, string>> {
  const map = new Map<string, Map<number, string>>();
  for (const [name, def] of definitions.terms) {
    if (!name.includes('.') || !def.value) continue;
    // Strip lambda binders to find the innermost body
    let body = def.value;
    while (body.tag === 'Binder' && body.binderKind.tag === 'BLam') {
      body = body.body;
    }
    // Must be Match(Var(0), [single clause]) — matching on the record arg
    if (body.tag !== 'Match' || body.scrutinee.tag !== 'Var' || body.scrutinee.index !== 0) continue;
    if (body.clauses.length !== 1) continue;
    const clause = body.clauses[0];
    if (clause.patterns.length !== 1 || clause.patterns[0].tag !== 'PCtor') continue;
    const pctor = clause.patterns[0];
    // RHS must be Var(0) — the single PVar binding
    if (clause.rhs.tag !== 'Var' || clause.rhs.index !== 0) continue;
    // Find the PVar position (exactly one PVar expected)
    let pvarFieldPos = -1;
    let pvarCount = 0;
    for (let i = 0; i < pctor.args.length; i++) {
      if (pctor.args[i].tag === 'PVar') {
        pvarFieldPos = i;
        pvarCount++;
      }
    }
    if (pvarCount !== 1 || pvarFieldPos < 0) continue;
    // Register: (ctorName, fieldPosition) → projectionName
    let ctorMap = map.get(pctor.name);
    if (!ctorMap) {
      ctorMap = new Map();
      map.set(pctor.name, ctorMap);
    }
    ctorMap.set(pvarFieldPos, name);
  }
  return map;
}

/**
 * Fold projection-like Match expressions back to their Const projection form.
 *
 * When erw (enhanced rewrite) unfolds definitions, record projections become
 * Match(scrutinee, [Clause([PCtor(ctor, ...PWild, PVar, PWild...)], Var(0))]).
 * These can't be iota-reduced when the scrutinee is a variable.
 * This function replaces them with App(Const(projName), scrutinee).
 */
export function foldProjectionMatches(
  term: TTKTerm,
  projMap: Map<string, Map<number, string>>,
): TTKTerm {
  switch (term.tag) {
    case 'Match': {
      // First, recursively fold sub-terms
      const foldedScrutinee = foldProjectionMatches(term.scrutinee, projMap);
      const foldedClauses = term.clauses.map(c => ({
        ...c,
        rhs: foldProjectionMatches(c.rhs, projMap),
      }));
      // Check if this Match is a projection pattern
      if (foldedClauses.length === 1) {
        const clause = foldedClauses[0];
        if (clause.patterns.length === 1 && clause.patterns[0].tag === 'PCtor') {
          const pctor = clause.patterns[0];
          if (clause.rhs.tag === 'Var' && clause.rhs.index === 0) {
            // Find PVar position
            let pvarPos = -1;
            let pvarCount = 0;
            for (let i = 0; i < pctor.args.length; i++) {
              if (pctor.args[i].tag === 'PVar') { pvarPos = i; pvarCount++; }
            }
            if (pvarCount === 1 && pvarPos >= 0) {
              const ctorMap = projMap.get(pctor.name);
              if (ctorMap) {
                const projName = ctorMap.get(pvarPos);
                if (projName) {
                  return mkApp(mkConst(projName), foldedScrutinee);
                }
              }
            }
          }
        }
      }
      // Not a projection — return with folded sub-terms
      const changed = foldedScrutinee !== term.scrutinee ||
        foldedClauses.some((c, i) => c.rhs !== term.clauses[i].rhs);
      return changed ? { ...term, scrutinee: foldedScrutinee, clauses: foldedClauses } : term;
    }
    case 'App': {
      const newFn = foldProjectionMatches(term.fn, projMap);
      const newArg = foldProjectionMatches(term.arg, projMap);
      if (newFn === term.fn && newArg === term.arg) return term;
      return { ...term, fn: newFn, arg: newArg };
    }
    case 'Binder': {
      const newDomain = foldProjectionMatches(term.domain, projMap);
      const newBody = foldProjectionMatches(term.body, projMap);
      if (newDomain === term.domain && newBody === term.body) return term;
      return { ...term, domain: newDomain, body: newBody };
    }
    default:
      return term;
  }
}

// ============================================================================
// Alias folding — fold delta-expanded projections back to their alias names
// ============================================================================

/**
 * Info for folding a projection application back to its alias.
 * E.g., CompleteOrderedField.mul(Carrier(R), field(R), a, b) → rmul(R, a, b)
 */
interface AliasFoldExtractionEntry {
  numFixedArgs: number;
  /** For each lambda variable (0..numLambdas-1), how to extract it from actual args. */
  lambdaExtractions: Array<{ fixedArgIndex: number; path: readonly ('fn' | 'arg')[] }>;
  /**
   * Cross-validation paths: for each lambda var, all the OTHER positions where it can
   * also be extracted. Used to verify that a match is genuine (not a false positive from
   * type params being structurally similar to the scrutinee).
   */
  crossValidations: Array<Array<{ fixedArgIndex: number; path: readonly ('fn' | 'arg')[] }>>;
  /** Head-const names for each fixed arg (used to verify structure before extraction).
   *  When the full-form extraction has fixedArgs = [Carrier(R), DPair.snd(R)], the
   *  heads are ['Carrier', 'DPair.snd']. At fold time we check that the actual term's
   *  head matches — this prevents `rone(R)` from being falsely matched against the
   *  `DPair.snd(R)` pattern (they have the same `.arg` extraction path but different heads). */
  fixedArgHeads?: readonly (string | undefined)[];
}

interface AliasFoldInfo {
  aliasName: string;
  /**
   * Extraction entries to try, in order. The first one where the term has
   * enough args and all lambda vars can be extracted wins.
   *
   * Typically has 1 entry for non-projection heads, or 2 entries for projection
   * heads: [projectionShortForm, fullForm] — where the short form has numFixedArgs=1
   * (just the scrutinee, as produced by foldProjectionMatches) and the full form has
   * all universe/type params.
   */
  extractions: AliasFoldExtractionEntry[];
}

/**
 * Find the path to Var(varIndex) in a kernel term.
 * Returns a sequence of 'fn'/'arg' selectors, or null if not found.
 */
function findVarPath(term: TTKTerm, varIndex: number): ('fn' | 'arg')[] | null {
  if (term.tag === 'Var' && term.index === varIndex) return [];
  if (term.tag === 'App') {
    const argPath = findVarPath(term.arg, varIndex);
    if (argPath) return ['arg', ...argPath];
    const fnPath = findVarPath(term.fn, varIndex);
    if (fnPath) return ['fn', ...fnPath];
  }
  return null;
}

/** Extract a subterm from a kernel term by following a path of fn/arg selectors. */
function extractByPath(term: TTKTerm, path: readonly ('fn' | 'arg')[]): TTKTerm | null {
  let current = term;
  for (const step of path) {
    if (current.tag !== 'App') return null;
    current = step === 'fn' ? current.fn : current.arg;
  }
  return current;
}

/**
 * Build a map from projection name → alias info for folding delta-expanded projections.
 *
 * Scans definitions for aliases like:
 *   rmul {R} = CompleteOrderedField.mul (field R)
 * where the value (after stripping lambdas) is a partial application of a projection.
 *
 * This allows folding CompleteOrderedField.mul(field(R), a, b) back to rmul(R, a, b),
 * which then renders using the notation for rmul (e.g., a · b).
 *
 * When `projMap` is provided, the function accounts for the fact that `foldProjectionMatches`
 * reduces projection applications to short form: `ProjName(scrutinee)` with just 1 arg
 * (the scrutinee), dropping universe/type params. Without this adjustment, the alias map
 * would expect the full compiled form (with all params) and fail to match the short form.
 */
export function buildAliasFoldMap(
  definitions: DefinitionsMap,
  projMap?: Map<string, Map<number, string>>,
): Map<string, AliasFoldInfo> {
  // Build set of known projection names from projMap so we know which heads
  // will appear in short form (just the scrutinee) after foldProjectionMatches.
  const projectionNames = new Set<string>();
  if (projMap) {
    for (const [, ctorMap] of projMap) {
      for (const [, projName] of ctorMap) {
        projectionNames.add(projName);
      }
    }
  }

  const map = new Map<string, AliasFoldInfo>();
  for (const [name, def] of definitions.terms) {
    // Only consider non-projection definitions (aliases don't contain '.')
    if (name.includes('.') || !def.value) continue;

    // Strip lambda binders to find the body
    let body = def.value;
    let numBindings = 0;
    while (body.tag === 'Binder' && body.binderKind.tag === 'BLam') {
      body = body.body;
      numBindings++;
    }
    // Also handle pattern-matching form: Match(Hole, [single clause with all PVar])
    // This is how pattern-matching defs like `radd {R} = ...` compile.
    if (body.tag === 'Match' && body.scrutinee.tag === 'Hole' &&
        body.clauses.length === 1) {
      const clause = body.clauses[0];
      if (clause.patterns.every(p => p.tag === 'PVar')) {
        numBindings += clause.patterns.length;
        body = clause.rhs;
      }
    }
    if (numBindings === 0) continue;

    // Body must be a partial application of a projection (name with '.')
    const { head, args: fixedArgs } = collectAppSpine(body);
    if (head.tag !== 'Const' || !head.name.includes('.') || fixedArgs.length === 0) continue;

    // Helper: try to build extraction info from a given set of fixed args
    function tryBuildExtractions(
      effectiveArgs: TTKTerm[],
    ): AliasFoldExtractionEntry | null {
      const lambdaExtractions: AliasFoldExtractionEntry['lambdaExtractions'] = [];
      const crossValidations: AliasFoldExtractionEntry['crossValidations'] = [];
      for (let k = 0; k < numBindings; k++) {
        const allPaths: Array<{ fixedArgIndex: number; path: ('fn' | 'arg')[] }> = [];
        for (let fi = 0; fi < effectiveArgs.length; fi++) {
          const path = findVarPath(effectiveArgs[fi], k);
          if (path) {
            allPaths.push({ fixedArgIndex: fi, path });
          }
        }
        if (allPaths.length === 0) return null;
        // Primary extraction: first occurrence
        lambdaExtractions.push(allPaths[0]);
        // Cross-validations: all OTHER occurrences
        crossValidations.push(allPaths.slice(1));
      }
      // Record each fixed arg's head Const so we can verify structure at fold time.
      const fixedArgHeads = effectiveArgs.map(a => {
        let h = a;
        while (h.tag === 'App') h = h.fn;
        return h.tag === 'Const' ? h.name : undefined;
      });
      return { numFixedArgs: effectiveArgs.length, lambdaExtractions, crossValidations, fixedArgHeads };
    }

    // Build extraction entries. For projection heads, we need both:
    // 1. Short form (after foldProjectionMatches): ProjName(scrutinee) — just the last arg
    // 2. Full form (when Consts haven't been delta-expanded): ProjName(u1, u2, ..., scrutinee)
    const extractions: AliasFoldExtractionEntry[] = [];

    // Always try the full form first (more specific — avoids false matches on type params)
    const fullEntry = tryBuildExtractions(fixedArgs);
    if (fullEntry) extractions.push(fullEntry);

    // For projection heads, also add the short form (after foldProjectionMatches,
    // projections appear as ProjName(scrutinee) with just the last arg).
    // The short form is tried after the full form so it doesn't accidentally match
    // type params in unexpanded terms.
    const isProjectionHead = projectionNames.has(head.name);
    if (isProjectionHead && fixedArgs.length > 1) {
      const shortEntry = tryBuildExtractions([fixedArgs[fixedArgs.length - 1]]);
      if (shortEntry) extractions.push(shortEntry);
    }

    if (extractions.length === 0) continue;

    // First alias wins (don't overwrite)
    if (!map.has(head.name)) {
      map.set(head.name, { aliasName: name, extractions });
    }
  }
  return map;
}

/**
 * Fold delta-expanded projection applications back to their alias names.
 *
 * E.g., CompleteOrderedField.mul(Carrier(R), field(R), a, b)
 *     → rmul(R, a, b)
 *
 * Applied after foldProjectionMatches (which handles Match → Const folding).
 */
export function foldAliases(term: TTKTerm, aliasMap: Map<string, AliasFoldInfo>): TTKTerm {
  switch (term.tag) {
    case 'App': {
      // First try alias matching on the FULL spine BEFORE recursion.
      // This prevents premature matching at inner App nodes (e.g., matching
      // COF.add(Carrier(R)) as radd(R) instead of waiting for the full
      // COF.add(Carrier(R), field(R), x, y) → radd(R, x, y)).
      const { head: rawHead, args: rawArgs } = collectAppSpine(term);
      if (rawHead.tag === 'Const') {
        const alias = aliasMap.get(rawHead.name);
        if (alias) {
          for (const entry of alias.extractions) {
            if (rawArgs.length < entry.numFixedArgs) continue;

            // Recurse into ALL args first (needed for inner alias folding,
            // e.g., DPair.snd(R) → field(R) inside the args)
            const foldedArgs = rawArgs.map(a => foldAliases(a, aliasMap));

            // Verify that each fixed arg's head structure matches the expected pattern.
            // Without this, `rone(R)` can falsely match a `DPair.snd(R)` pattern
            // (same .arg extraction path, different head), causing the fold to consume
            // too many args — e.g., `radd(R, 1)` instead of `radd(R, 1, 1)`.
            if (entry.fixedArgHeads) {
              let headMismatch = false;
              for (let fi = 0; fi < entry.numFixedArgs && !headMismatch; fi++) {
                const expectedHead = entry.fixedArgHeads[fi];
                if (expectedHead !== undefined) {
                  let actualHead: TTKTerm = foldedArgs[fi];
                  while (actualHead.tag === 'App') actualHead = actualHead.fn;
                  if (actualHead.tag !== 'Const' || actualHead.name !== expectedHead) {
                    headMismatch = true;
                  }
                }
              }
              if (headMismatch) continue;
            }

            // Extract lambda-bound values from fixed args
            const lambdaValues: TTKTerm[] = [];
            let extractionFailed = false;
            for (const extraction of entry.lambdaExtractions) {
              const value = extractByPath(foldedArgs[extraction.fixedArgIndex], extraction.path);
              if (!value) { extractionFailed = true; break; }
              lambdaValues.push(value);
            }
            if (extractionFailed) continue;

            // Cross-validate: verify that each lambda var extracts to the SAME value
            // from all other fixed arg positions where it appears.
            let crossCheckFailed = false;
            for (let k = 0; k < lambdaValues.length && !crossCheckFailed; k++) {
              for (const cv of entry.crossValidations[k]) {
                const cvValue = extractByPath(foldedArgs[cv.fixedArgIndex], cv.path);
                if (!cvValue || !ttermStructEqual(cvValue, lambdaValues[k])) {
                  crossCheckFailed = true;
                  break;
                }
              }
            }
            if (crossCheckFailed) continue;

            // Rebuild: alias(lambdaValues..., remainingArgs...)
            const remainingArgs = foldedArgs.slice(entry.numFixedArgs);
            let result: TTKTerm = mkConst(alias.aliasName);
            for (const v of lambdaValues) result = mkApp(result, v);
            for (const a of remainingArgs) result = mkApp(result, a);
            return result;
          }
        }
      }

      // No alias matched — recurse into subterms normally
      const newFn = foldAliases(term.fn, aliasMap);
      const newArg = foldAliases(term.arg, aliasMap);
      if (newFn === term.fn && newArg === term.arg) return term;
      return { ...term, fn: newFn, arg: newArg };
    }
    case 'Binder': {
      const newDomain = foldAliases(term.domain, aliasMap);
      const newBody = foldAliases(term.body, aliasMap);
      if (newDomain === term.domain && newBody === term.body) return term;
      return { ...term, domain: newDomain, body: newBody };
    }
    case 'Match': {
      const newScrutinee = foldAliases(term.scrutinee, aliasMap);
      const newClauses = term.clauses.map(c => ({
        ...c,
        rhs: foldAliases(c.rhs, aliasMap),
      }));
      const changed = newScrutinee !== term.scrutinee ||
        newClauses.some((c, i) => c.rhs !== term.clauses[i].rhs);
      return changed ? { ...term, scrutinee: newScrutinee, clauses: newClauses } : term;
    }
    default:
      return term;
  }
}

/**
 * Fold simple wrapper definitions back to their names.
 * Handles definitions like `rtwo R = radd R (rone R) (rone R)` — after alias folding,
 * the term still contains `radd(R, rone(R), rone(R))` which should fold back to `rtwo(R)`.
 *
 * Builds a map of (body structure key → definition name) for definitions whose
 * bodies are simple applications (no lambdas/matches in the body).
 */
let _simpleWrapperCache: { defs: DefinitionsMap; map: Map<string, { name: string; numArgs: number }> } | null = null;

function buildSimpleWrapperMap(definitions: DefinitionsMap): Map<string, { name: string; numArgs: number }> {
  if (_simpleWrapperCache?.defs === definitions) return _simpleWrapperCache.map;
  const map = new Map<string, { name: string; numArgs: number }>();
  for (const [name, def] of definitions.terms) {
    if (name.includes('.') || !def.value) continue;
    // Strip lambda binders
    let body = def.value;
    let numArgs = 0;
    while (body.tag === 'Binder' && body.binderKind.tag === 'BLam') { body = body.body; numArgs++; }
    // Handle pattern-matching form
    if (body.tag === 'Match' && body.clauses.length === 1 && body.clauses[0].patterns.every(p => p.tag === 'PVar')) {
      numArgs += body.clauses[0].patterns.length;
      body = body.clauses[0].rhs;
    }
    if (numArgs === 0) continue;
    // Body must be a simple application (no Binders, no Matches in args)
    const { head, args } = collectAppSpine(body);
    if (head.tag !== 'Const') continue;
    // Skip if body contains complex terms (lambdas, matches)
    const isSimple = args.every(a => a.tag === 'Var' || a.tag === 'Const' || a.tag === 'App');
    if (!isSimple) continue;
    // Build a structural key from the body
    const key = termStructKey(body, numArgs);
    if (key) map.set(key, { name, numArgs });
  }
  _simpleWrapperCache = { defs: definitions, map };
  return map;
}

/** Build a structural key for a term, normalizing Var indices relative to lambda depth. */
function termStructKey(t: TTKTerm, _depth: number): string | null {
  switch (t.tag) {
    case 'Var': return `V${t.index}`;
    case 'Const': return `C:${t.name}`;
    case 'App': {
      const fnKey = termStructKey(t.fn, _depth);
      const argKey = termStructKey(t.arg, _depth);
      if (!fnKey || !argKey) return null;
      return `(${fnKey} ${argKey})`;
    }
    default: return null;
  }
}

function foldSimpleWrappers(term: TTKTerm, definitions: DefinitionsMap): TTKTerm {
  const wrapperMap = buildSimpleWrapperMap(definitions);
  if (wrapperMap.size === 0) return term;

  function fold(t: TTKTerm): TTKTerm {
    // Try to match the current application spine against a wrapper definition
    if (t.tag === 'App') {
      const { head, args: spineArgs } = collectAppSpine(t);
      if (head.tag === 'Const') {
        // Check each suffix of the spine to see if it matches a wrapper body
        for (let startIdx = 0; startIdx <= spineArgs.length; startIdx++) {
          const subArgs = spineArgs.slice(startIdx);
          // Build app of head + subArgs with Var indices shifted
          let subTerm: TTKTerm = head;
          for (const a of subArgs) subTerm = { tag: 'App', fn: subTerm, arg: a };
          // Build key
          const key = termStructKey(subTerm, 0);
          if (key) {
            const wrapper = wrapperMap.get(key);
            if (wrapper && wrapper.numArgs === spineArgs.length - startIdx) {
              // Found a match! Build the folded application: wrapper(prefix_args)
              let result: TTKTerm = { tag: 'Const', name: wrapper.name };
              for (let i = 0; i < startIdx; i++) {
                result = { tag: 'App', fn: result, arg: fold(spineArgs[i]) };
              }
              return result;
            }
          }
        }
      }
    }
    // Recurse into subterms
    switch (t.tag) {
      case 'App': return { ...t, fn: fold(t.fn), arg: fold(t.arg) };
      case 'Binder': return { ...t, domain: fold(t.domain), body: fold(t.body) };
      default: return t;
    }
  }
  return fold(term);
}

/**
 * Delta-reduce (unfold) applications of constants marked with `@syntax @unfold`.
 * Only unfolds at the HEAD of an application spine — does not unfold inside args
 * unless those args themselves have unfold-marked heads.
 *
 * The definition's value is typically a lambda chain:
 *   \arg0 => \arg1 => ... => body
 * We substitute the application's args into the body and beta-normalize.
 */
export function unfoldTransparent(
  term: TTKTerm,
  definitions: DefinitionsMap,
  unfoldNames: Set<string>,
): TTKTerm {
  if (unfoldNames.size === 0) return term;

  switch (term.tag) {
    case 'App': {
      const { head, args } = collectAppSpine(term);
      if (head.tag === 'Const' && unfoldNames.has(head.name)) {
        const defn = definitions.terms.get(head.name);
        if (defn?.value) {
          // Single-step delta reduction: substitute args into this definition only.
          // Use an isolated definitions map containing ONLY this constant, so whnf
          // doesn't aggressively unfold other constants (field, Carrier, rlt, etc.)
          const isolatedDefs = createDefinitionsMap();
          isolatedDefs.terms.set(head.name, defn);
          let body: TTKTerm = head;
          for (const arg of args) {
            body = mkApp(body, arg);
          }
          const reduced = whnf(body, { definitions: isolatedDefs });
          // Recurse in case the unfolded body contains more unfold-marked constants
          return unfoldTransparent(reduced, definitions, unfoldNames);
        }
      }
      // No unfold match — recurse into subterms
      const newFn = unfoldTransparent(term.fn, definitions, unfoldNames);
      const newArg = unfoldTransparent(term.arg, definitions, unfoldNames);
      if (newFn === term.fn && newArg === term.arg) return term;
      return { ...term, fn: newFn, arg: newArg };
    }
    case 'Binder': {
      const newDomain = unfoldTransparent(term.domain, definitions, unfoldNames);
      const newBody = unfoldTransparent(term.body, definitions, unfoldNames);
      if (newDomain === term.domain && newBody === term.body) return term;
      return { ...term, domain: newDomain, body: newBody };
    }
    case 'Match': {
      const newScrutinee = unfoldTransparent(term.scrutinee, definitions, unfoldNames);
      const newClauses = term.clauses.map(c => ({
        ...c,
        rhs: unfoldTransparent(c.rhs, definitions, unfoldNames),
      }));
      const changed = newScrutinee !== term.scrutinee ||
        newClauses.some((c, i) => c.rhs !== term.clauses[i].rhs);
      return changed ? { ...term, scrutinee: newScrutinee, clauses: newClauses } : term;
    }
    default:
      return term;
  }
}

/**
 * Normalize a MetaVar's goal type after unfold and update the engine.
 * Returns a new engine with the goal's type replaced by the normalized version.
 *
 * Two-step approach:
 * 1. prepareMatchesForIota: WHNF Match scrutinees and multi-arg Match applied args
 *    with real definitions to expose constructors (e.g., `one` → `Succ(Zero)`)
 * 2. fullNormalize with empty definitions: beta+iota only, no delta on other constants
 */
function normalizeGoalInEngine(engine: TacticEngine, goalId: string): TacticEngine {
  const goal = engine.metaVars.get(goalId);
  if (!goal) return engine;

  const prepared = prepareMatchesForIota(goal.type, engine.definitions);
  const normalized = fullNormalize(prepared, createDefinitionsMap());
  if (normalized === goal.type) return engine;

  const newMetaVars = new Map(engine.metaVars);
  newMetaVars.set(goalId, { ...goal, type: normalized });
  return engine.withUpdates({ metaVars: newMetaVars });
}

// ============================================================================
// Rendering helpers
// ============================================================================

/**
 * Heuristic: is this goal type a VALUE type (need to provide a value) rather
 * than a PROPOSITION (need to prove a statement)?
 *
 * Used by the prose renderer to choose phrasing:
 *   - Value type: "We need a value of type ℝ.  Use δF."
 *   - Proposition: "We must show 0 < δF.  The result follows from posF."
 *
 * Detection strategy:
 *   - Known proposition-formers (Equal, rlt, rle, Not, And, Or, Iff, ...)
 *     → proposition
 *   - Known value-type constructors (Nat, Bool, Real, Carrier, List, Vec, ...)
 *     → value type
 *   - Sort / Type → value type (we're picking a type)
 *   - Pi chain → follow to the return type and classify that
 *   - Unknown Const heads → default to PROPOSITION (safer — prop-like
 *     wording is always grammatical; value-type wording only works when
 *     we're confident).
 */
const PROPOSITION_HEADS = new Set([
  'Equal', 'Eq',
  'rlt', 'rle', 'rgt', 'rge', 'rne',
  'lt', 'le', 'gt', 'ge', 'ne',
  'Not', 'Void', 'Iff', 'Implies',
]);

const VALUE_TYPE_HEADS = new Set([
  'Nat', 'Int', 'Bool', 'Real',
  'Carrier',
  'List', 'Vec', 'Array',
  'String', 'Char', 'Float', 'Double',
  'Unit', 'Empty',
]);

export function isValueTypeGoal(term: TTKTerm): boolean {
  if (!term) return false;
  // Sort (Type, Prop itself as a value) — picking a type counts as value-like
  if (term.tag === 'Sort') return true;
  // Pi type: recurse into the return type
  if (term.tag === 'Binder' && term.binderKind.tag === 'BPi') {
    let body: TTKTerm = term.body;
    while (body.tag === 'Binder' && body.binderKind.tag === 'BPi') body = body.body;
    return isValueTypeGoal(body);
  }
  // Walk the App spine to the head
  let head: TTKTerm = term;
  while (head.tag === 'App') head = head.fn;
  if (head.tag === 'Const') {
    if (PROPOSITION_HEADS.has(head.name)) return false;
    if (VALUE_TYPE_HEADS.has(head.name)) return true;
  }
  // Meta / Hole / unknown head → conservative default: proposition
  return false;
}

/** Render a TTerm expression to LaTeX using the structured math editor pipeline. */
export function renderTerm(term: TTerm, ctx: string[], rev: ReverseRegistry): string {
  const nodes = ttermToMathNodes(term, rev, ctx);
  return renderStaticLatex(mkRow(nodes));
}

/** Convert a CasePattern to a synthetic TTerm, so the math pipeline can
 *  render it through the @syntax registry. Pattern variables become Const
 *  nodes (their names render as plain symbols); constructor patterns become
 *  Const-headed applications (which the registry matches via `nameToEntry`). */
function casePatternToTTerm(p: CasePattern): TTerm {
  if (p.tag === 'var') return mkConstTT(p.name);
  return mkAppSpineTT(mkConstTT(p.constructor), p.params.map(casePatternToTTerm));
}

/** Render a branch's nested pattern list as a LaTeX label, respecting any
 *  `@syntax` entries defined for the constructors involved. Used by the
 *  replay layer to replace the static labelLatex stored on CaseNodes. */
function renderNestedCaseLabelLatex(
  ctorName: string,
  patterns: readonly CasePattern[],
  rev: ReverseRegistry,
): string {
  const term = mkAppSpineTT(mkConstTT(ctorName), patterns.map(casePatternToTTerm));
  const nodes = ttermToMathNodes(term, rev, []);
  return renderStaticLatex(mkRow(nodes));
}

/** Resolve a case node's display label. When the case has `casePatterns`
 *  (set for nested-pattern branches) AND a registry is available, render
 *  through the @syntax registry. Otherwise fall back to the static
 *  `labelLatex` set at tree-build time. `rev` is optional so cursor-replay
 *  functions (which don't need registry-aware labels) can reuse this
 *  helper without threading `rev` through every call site. */
function caseLabelLatexOf(c: CaseNode, rev?: ReverseRegistry): string | undefined {
  if (rev && c.casePatterns && c.casePatterns.length > 0 && c.constructorName) {
    return renderNestedCaseLabelLatex(c.constructorName, c.casePatterns, rev);
  }
  return c.labelLatex;
}

/**
 * Render a suffices "by" proof expression through the math pipeline.
 */
function renderByProofExpr(
  byProof: ProofNode,
  engine: TacticEngine,
  goalId: string,
  definitions: DefinitionsMap,
  rev: ReverseRegistry,
  projMap?: Map<string, Map<number, string>>,
  aliasMap?: Map<string, AliasFoldInfo>,
): string | undefined {
  const expr = extractByExprFromTree(byProof);
  if (!expr) return undefined;
  const goal = engine.metaVars.get(goalId);
  if (!goal) return undefined;
  return renderProofExpr(expr, goal, definitions, rev, projMap, aliasMap);
}

/**
 * Render a proof expression string through the math pipeline.
 * Parses the string in the given goal's context and renders via the structured math renderer.
 */
function renderProofExpr(
  expr: string,
  goal: MetaVar,
  definitions: DefinitionsMap,
  rev: ReverseRegistry,
  projMap?: Map<string, Map<number, string>>,
  aliasMap?: Map<string, AliasFoldInfo>,
): string | undefined {
  const term = parseExactExpr(expr, goal.ctx, definitions);
  if (!term) return undefined;
  const pm = projMap ?? buildProjectionFoldMap(definitions);
  const am = aliasMap ?? buildAliasFoldMap(definitions, pm);
  let folded = foldProjectionMatches(term, pm);
  folded = foldAliases(folded, am);
  // Unfold @syntax @unfold-marked constants
  if (rev.unfoldNames.size > 0) {
    folded = unfoldTransparent(folded, definitions, rev.unfoldNames);
  }
  const surface = kernelTypeToSurface(folded, definitions);
  return renderTerm(surface, buildNameCtx(goal.ctx), rev);
}

/** Extract the exact expression string from a byProof subtree. */
function extractByExprFromTree(node: ProofNode): string | undefined {
  switch (node.tag) {
    case 'exact': return node.expr;
    case 'intros': return extractByExprFromTree(node.child);
    case 'have': return extractByExprFromTree(node.child);
    default: return undefined;
  }
}

/** Render a surface term to LaTeX with subterm annotations via the annotate callback. */
export function renderTermAnnotated(term: TTerm, ctx: string[], rev: ReverseRegistry, annotate: SubtermAnnotator): string {
  const nodes = ttermToMathNodes(term, rev, ctx, annotate);
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
  contextNames?: readonly string[],
): ConstructorCaseInfo[] {
  return inductiveInfo.constructors.map(ctor => {
    const usedNames = new Set(contextNames ?? []);
    const paramNames: string[] = [];
    // Peel constructor type, building de Bruijn context incrementally
    // so Var references in each param's domain resolve correctly
    const binderNames: string[] = []; // peeling order (outermost first)
    let ctorBody = ctor.type;
    while (true) {
      const pi = peelPi(ctorBody);
      if (!pi) break;
      if (pi.isImplicit) {
        binderNames.push(pi.name);
        ctorBody = pi.body;
        continue;
      }
      // De Bruijn ctx at this point: binders peeled so far, reversed
      const ctx = [...binderNames].reverse();
      let name: string;
      if (pi.name !== '_') {
        name = freshenName(pi.name, usedNames);
      } else {
        name = proposeVarName(pi.domain, usedNames, rev, ctx);
      }
      usedNames.add(name);
      paramNames.push(name);
      binderNames.push(pi.name);
      ctorBody = pi.body;
    }

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
 * Tokenize an exact expression string into a flat array of tokens.
 * Handles parentheses and whitespace-separated identifiers.
 */
function tokenizeExactExpr(expr: string): string[] {
  const tokens: string[] = [];
  let i = 0;
  while (i < expr.length) {
    if (expr[i] === ' ' || expr[i] === '\t') { i++; continue; }
    if (expr[i] === '(' || expr[i] === ')') {
      tokens.push(expr[i]);
      i++;
      continue;
    }
    let j = i;
    while (j < expr.length && expr[j] !== ' ' && expr[j] !== '\t' && expr[j] !== '(' && expr[j] !== ')') j++;
    tokens.push(expr.slice(i, j));
    i = j;
  }
  return tokens;
}

/**
 * Parse an exact expression into a TTKTerm.
 * Supports: single names, function application (f x y), parenthesized groups.
 * Names are resolved as context variables first, then as constants.
 * When definitions are provided, implicit argument Holes are inserted automatically.
 */
export function parseExactExpr(
  expr: string,
  ctx: ReadonlyArray<{ name: string; type: TTKTerm }>,
  definitions?: DefinitionsMap,
): TTKTerm | null {
  const tokens = tokenizeExactExpr(expr);
  if (tokens.length === 0) return null;

  const namedArgLookup = definitions ? createNamedArgLookup(definitions) : undefined;

  let pos = 0;

  // Stack of local binder names for resolving Var references inside lambdas
  const localBinderNames: string[] = [];

  function parseAtom(): TTKTerm | null {
    if (pos >= tokens.length) return null;
    if (tokens[pos] === '(') {
      pos++; // skip '('
      const inner = parseApp();
      if (pos < tokens.length && tokens[pos] === ')') pos++; // skip ')'
      return inner;
    }
    if (tokens[pos] === ')') return null;
    // Lambda: fun name => body
    if (tokens[pos] === 'fun') {
      pos++; // skip 'fun'
      const binderName = pos < tokens.length ? tokens[pos++] : '_';
      if (pos < tokens.length && tokens[pos] === '=>') pos++; // skip '=>'
      localBinderNames.push(binderName);
      const body = parseApp();
      localBinderNames.pop();
      if (!body) return null;
      return {
        tag: 'Binder',
        binderKind: { tag: 'BLam' },
        name: binderName,
        domain: { tag: 'Hole', id: '_lam_domain' },
        body,
      };
    }
    const name = tokens[pos++];
    // Numeric literal: pure non-negative digit run becomes a NatLit (BigInt)
    if (/^\d+$/.test(name)) {
      return { tag: 'NatLit', value: BigInt(name) };
    }
    // Check local lambda binders first (innermost first)
    for (let i = localBinderNames.length - 1; i >= 0; i--) {
      if (localBinderNames[i] === name) {
        return { tag: 'Var', index: localBinderNames.length - 1 - i };
      }
    }
    // Then check goal context (shifted by number of local binders)
    const varIdx = findVarIndex(name, ctx);
    if (varIdx !== null) return { tag: 'Var', index: varIdx + localBinderNames.length };
    // For constants, insert Holes for implicit args (matching elaboration behavior)
    let result: TTKTerm = { tag: 'Const', name };
    if (namedArgLookup) {
      const namedArgs = namedArgLookup(name);
      if (namedArgs) {
        for (const [paramName] of namedArgs) {
          result = { tag: 'App', fn: result, arg: { tag: 'Hole', id: '_implicit_' + paramName } };
        }
      }
    }
    return result;
  }

  function parseApp(): TTKTerm | null {
    let result = parseAtom();
    if (!result) return null;
    while (pos < tokens.length && tokens[pos] !== ')' && tokens[pos] !== '=>') {
      const arg = parseAtom();
      if (!arg) break;
      result = { tag: 'App', fn: result, arg };
    }
    return result;
  }

  const result = parseApp();
  if (result && pos < tokens.length) return null; // leftover tokens = parse error
  return result;
}

/**
 * Elaborate a parsed type term to resolve Holes (implicit args) into real terms.
 * parseExactExpr inserts Hole("_implicit_X") for implicit args — these need to
 * be resolved by the type checker so that unification/apply can work against them.
 */
export function elaborateType(
  term: TTKTerm,
  ctx: ReadonlyArray<{ name: string; type: TTKTerm }>,
  definitions: DefinitionsMap,
  _metaVars?: Map<string, MetaVar>,
): TTKTerm {
  return elaborateTermInContext({
    term,
    context: [...ctx],
    definitions,
  });
}

function extendGoalForComplexScrutinee(
  engine: TacticEngine,
  goal: MetaVar,
  goalId: string,
  parsedScrutinee: TTKTerm,
): { engine: TacticEngine; goal: MetaVar; goalId: string; scrutineeIdx: number } | null {
  try {
    const inferredType = inferTermTypeInContext({
      term: parsedScrutinee,
      context: goal.ctx,
      definitions: engine.definitions,
      metaVars: engine.metaVars,
      constraints: engine.constraints,
    });
    const extCtx = [...goal.ctx, { name: '_scrut', type: inferredType }];
    const extGoalType = shiftTerm(goal.type, 1, 0);
    const tempGoalId = goalId + '_cases_temp';
    const tempMeta: MetaVar = { ctx: extCtx, type: extGoalType, solution: undefined };
    const tempMetaVars = new Map(engine.metaVars);
    tempMetaVars.set(tempGoalId, tempMeta);
    const tempGoals = engine.goals.map(g => g === goalId ? tempGoalId : g);
    return {
      engine: engine.withUpdates({ metaVars: tempMetaVars, goals: tempGoals }),
      goal: tempMeta,
      goalId: tempGoalId,
      scrutineeIdx: 0,
    };
  } catch {
    return null;
  }
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
        const numVars = countKernelClauseBindings(c);
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
          const numVars = countKernelClauseBindings(c);
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

/**
 * Structural equality check for TTKTerms (no normalization).
 * Used for comparing type args during index unification.
 */
function ttermStructEqual(a: TTKTerm, b: TTKTerm): boolean {
  if (a === b) return true;
  if (a.tag !== b.tag) return false;
  switch (a.tag) {
    case 'Var': return b.tag === 'Var' && a.index === b.index;
    case 'Const': return b.tag === 'Const' && a.name === b.name;
    case 'App':
      return b.tag === 'App' && ttermStructEqual(a.fn, b.fn) && ttermStructEqual(a.arg, b.arg);
    case 'Binder':
      return b.tag === 'Binder' && a.binderKind.tag === (b as any).binderKind.tag
        && ttermStructEqual(a.domain, (b as any).domain) && ttermStructEqual(a.body, (b as any).body);
    default: return false;
  }
}

/**
 * Index unification for indexed inductive types (e.g., Equal).
 *
 * When case-splitting on a scrutinee of type `I params indices`, a constructor
 * like `refl : {A} -> {a : A} -> Equal A a a` constrains the indices.
 * For `eq : Equal A x y` in the `refl` case, the constructor forces y = x.
 *
 * This function detects such index constraints and applies substitutions to
 * the goal, removing the unified variables from the context.
 *
 * Returns the modified goal and adjusted scrutineeIdx.
 */
function applyIndexUnification(
  goal: MetaVar,
  scrutineeIdx: number,
  ctorType: TTKTerm,
  numImplicit: number,
  typeArgs: TTKTerm[],
): { goal: MetaVar; scrutineeIdx: number } {
  // Compute constructor return type by substituting implicits and peeling explicit params
  let returnType = ctorType;
  for (let i = 0; i < numImplicit; i++) {
    if (returnType.tag === 'Binder' && returnType.binderKind.tag === 'BPi') {
      const arg = typeArgs[i] || { tag: 'Hole' as const, id: '_implicit_' + i };
      returnType = subst(0, arg, returnType.body);
    }
  }
  let numExplicit = 0;
  while (returnType.tag === 'Binder' && returnType.binderKind.tag === 'BPi') {
    returnType = returnType.body;
    numExplicit++;
  }

  // For constructors with explicit params, the return type may reference those
  // params directly in its indices (e.g., Wrap n, Vec A (Succ n)). Cases that
  // don't mention explicit params can be unified eagerly here; constructor-param
  // references are deferred until the constructor params are in scope.
  const ctorRetArgs = extractTypeArgsFromType(returnType);

  const s = goal.ctx.length - 1 - scrutineeIdx;

  // Find index mismatches: positions where scrutinee type arg differs from constructor return type arg
  // Only handle cases where the scrutinee arg is a simple Var (can be substituted away)
  interface IndexSubst {
    scrVarIdx: number;   // De Bruijn index in scrutinee's type scope
    ctxArrayPos: number; // Position in goal.ctx array
    replacement: TTKTerm; // Replacement term in scrutinee's type scope
  }
  const substs: IndexSubst[] = [];

  for (let i = 0; i < Math.min(typeArgs.length, ctorRetArgs.length); i++) {
    const scrArg = typeArgs[i];
    let ctorArg = ctorRetArgs[i];

    // Skip if constructor return type arg references explicit params
    if (numExplicit > 0 && containsVarBelow(ctorArg, numExplicit)) continue;

    // Shift constructor return type arg from (scrScope + numExplicit) to scrScope
    if (numExplicit > 0) {
      ctorArg = shiftTerm(ctorArg, -numExplicit, 0);
    }

    if (scrArg.tag === 'Var' && !ttermStructEqual(scrArg, ctorArg)) {
      const ctxArrayPos = s - 1 - scrArg.index;
      if (ctxArrayPos >= 0 && ctxArrayPos < goal.ctx.length && ctxArrayPos !== s) {
        substs.push({ scrVarIdx: scrArg.index, ctxArrayPos, replacement: ctorArg });
      }
    }
  }

  if (substs.length === 0) return { goal, scrutineeIdx };

  // Sort by ctxArrayPos descending so removals from the end don't shift earlier positions
  substs.sort((a, b) => b.ctxArrayPos - a.ctxArrayPos);

  let currentGoal = goal;
  let currentScrutIdx = scrutineeIdx;

  for (const sub of substs) {
    const n = currentGoal.ctx.length;
    const s_cur = n - 1 - currentScrutIdx;
    const ap = sub.ctxArrayPos;
    // Recompute: the variable being removed is at de Bruijn index (n - 1 - ap) in the goal
    const goalVarIdx = n - 1 - ap;

    // Convert replacement from scrutinee's type scope to goal scope.
    // scrScope Var(v) maps to goalScope Var(v + currentScrutIdx + 1)
    const repInGoalScope = shiftTerm(sub.replacement, currentScrutIdx + 1, 0);

    // For subst: replacement must be in the scope AFTER removing goalVarIdx.
    // After removal, Var(k) for k > goalVarIdx shifts to Var(k-1).
    // So adjust the replacement accordingly.
    const adjRep = shiftTerm(repInGoalScope, -1, goalVarIdx);

    // Apply substitution to goal type
    const newGoalType = subst(goalVarIdx, adjRep, currentGoal.type);

    // Apply substitution to context entries
    const newCtx: Array<{ name: string; type: TTKTerm }> = [];
    for (let j = 0; j < n; j++) {
      if (j === ap) continue; // remove the unified variable

      const entry = currentGoal.ctx[j];
      if (j > ap) {
        // This entry references the removed variable.
        // In entry j's type scope, the removed variable is at de Bruijn index (j - 1 - ap).
        const varInEntry = j - 1 - ap;

        // Convert replacement from scrScope to entry j's type scope:
        // scrScope has s_cur entries, entry j has j entries.
        // scrScope Var(v) → entry scope Var(v + (j - s_cur))
        const repInEntry = shiftTerm(sub.replacement, j - s_cur, 0);
        const adjRepEntry = shiftTerm(repInEntry, -1, varInEntry);
        const newType = subst(varInEntry, adjRepEntry, entry.type);
        newCtx.push({ name: entry.name, type: newType });
      } else {
        newCtx.push(entry);
      }
    }

    // Adjust scrutineeIdx: if we removed an entry AFTER the scrutinee in the array
    // (i.e., BEFORE it in de Bruijn order), the scrutinee's de Bruijn index decreases.
    if (ap > s_cur) {
      currentScrutIdx = currentScrutIdx - 1;
    }
    // If ap < s_cur: both array position and length decrease by 1, so de Bruijn is unchanged.

    currentGoal = { ...currentGoal, ctx: newCtx, type: newGoalType };
  }

  return { goal: currentGoal, scrutineeIdx: currentScrutIdx };
}

interface GoalScopeIndexSubst {
  ctxArrayPos: number;
  replacement: TTKTerm;
}

function applyGoalScopeIndexSubstitutions(
  goal: MetaVar,
  substs: GoalScopeIndexSubst[],
): MetaVar {
  if (substs.length === 0) return goal;

  const sorted = [...substs].sort((a, b) => b.ctxArrayPos - a.ctxArrayPos);
  let currentGoal = goal;

  for (const sub of sorted) {
    const n = currentGoal.ctx.length;
    const ap = sub.ctxArrayPos;
    const goalVarIdx = n - 1 - ap;
    const adjRep = shiftTerm(sub.replacement, -1, goalVarIdx);
    const newGoalType = subst(goalVarIdx, adjRep, currentGoal.type);

    const newCtx: Array<{ name: string; type: TTKTerm }> = [];
    for (let j = 0; j < n; j++) {
      if (j === ap) continue;

      const entry = currentGoal.ctx[j];
      if (j > ap) {
        const varInEntry = j - 1 - ap;
        const repInEntry = shiftTerm(sub.replacement, j - n, 0);
        const adjRepEntry = shiftTerm(repInEntry, -1, varInEntry);
        newCtx.push({
          name: entry.name,
          type: subst(varInEntry, adjRepEntry, entry.type),
        });
      } else {
        newCtx.push(entry);
      }
    }

    currentGoal = { ...currentGoal, ctx: newCtx, type: newGoalType };
  }

  return currentGoal;
}

function remapCtorReturnArgToGoalScope(
  term: TTKTerm,
  numExplicit: number,
  scrutineeIdx: number,
  numParams: number,
  ihOffset: number,
): TTKTerm {
  switch (term.tag) {
    case 'Var':
      if (term.index < numExplicit) {
        return { tag: 'Var', index: scrutineeIdx + numParams - 1 + ihOffset - term.index };
      }
      return {
        tag: 'Var',
        index: term.index - numExplicit + scrutineeIdx + numParams + ihOffset,
      };
    case 'App':
      return {
        tag: 'App',
        fn: remapCtorReturnArgToGoalScope(term.fn, numExplicit, scrutineeIdx, numParams, ihOffset),
        arg: remapCtorReturnArgToGoalScope(term.arg, numExplicit, scrutineeIdx, numParams, ihOffset),
      };
    case 'Binder': {
      const domain = remapCtorReturnArgToGoalScope(term.domain, numExplicit, scrutineeIdx, numParams, ihOffset);
      const body = remapCtorReturnArgToGoalScope(term.body, numExplicit, scrutineeIdx + 1, numParams, ihOffset);
      return {
        tag: 'Binder',
        name: term.name,
        binderKind: term.binderKind,
        domain,
        body,
      };
    }
    case 'Annot':
      return {
        tag: 'Annot',
        term: remapCtorReturnArgToGoalScope(term.term, numExplicit, scrutineeIdx, numParams, ihOffset),
        type: remapCtorReturnArgToGoalScope(term.type, numExplicit, scrutineeIdx, numParams, ihOffset),
      };
    case 'Match':
      return {
        tag: 'Match',
        scrutinee: remapCtorReturnArgToGoalScope(term.scrutinee, numExplicit, scrutineeIdx, numParams, ihOffset),
        clauses: term.clauses.map(clause => ({
          ...clause,
          rhs: remapCtorReturnArgToGoalScope(
            clause.rhs,
            numExplicit,
            scrutineeIdx + countKernelClauseBindings(clause),
            numParams,
            ihOffset,
          ),
        })),
      };
    default:
      return term;
  }
}

/** Check if a term contains any Var with index < threshold. */
function containsVarBelow(term: TTKTerm, threshold: number): boolean {
  switch (term.tag) {
    case 'Var': return term.index < threshold;
    case 'App': return containsVarBelow(term.fn, threshold) || containsVarBelow(term.arg, threshold);
    case 'Binder': return containsVarBelow(term.domain, threshold) || containsVarBelow(term.body, threshold + 1);
    default: return false;
  }
}

/**
 * Compute a case-specific goal by directly substituting the constructor
 * pattern for the scrutinee variable in the goal type.
 *
 * After intros [i, n, f], context is [i:ℕ, n:ℕ, f:ℕ→ℕ] and goal is G(i,n,f).
 * For Zero case: goal becomes G(i,0,f), context extends with nothing.
 * For Succ case: goal becomes G(i,Succ(n'),f), context extends with [n':ℕ, IH:P(n')].
 *
 * For indexed inductive types (e.g., Equal), also performs index unification:
 * the constructor's return type constrains index positions, and variables at
 * those positions are substituted and removed from the context.
 */
export function computeCaseGoalDirect(
  goal: MetaVar,
  scrutineeIdx: number,
  ctor: { name: string; type: TTKTerm; namedArgMap?: NamedArgMap },
  inductiveName: string,
  definitions: DefinitionsMap,
  userParamNames?: readonly string[],
): MetaVar {
  // --- Index unification (preprocessing) ---
  // For indexed inductive types, the constructor constrains index values.
  // E.g., refl : Equal A a a constrains both index positions to be equal.
  // We detect and apply these substitutions before the main restructuring.
  const numImplicit = ctor.namedArgMap?.size ?? 0;
  const s_orig = goal.ctx.length - 1 - scrutineeIdx;
  const scrutineeTypeOrig = goal.ctx[s_orig].type;
  const typeArgsOrig = extractTypeArgsFromType(scrutineeTypeOrig);

  const unified = applyIndexUnification(goal, scrutineeIdx, ctor.type, numImplicit, typeArgsOrig);

  // Use the unified goal and adjusted scrutineeIdx for the rest
  const uGoal = unified.goal;
  const uScrutIdx = unified.scrutineeIdx;

  // Extract type args from (possibly modified) scrutinee type
  const s = uGoal.ctx.length - 1 - uScrutIdx; // scrutinee array position
  const scrutineeType = uGoal.ctx[s].type;
  const typeArgs = extractTypeArgsFromType(scrutineeType);

  // Count constructor parameters (skip implicit ones) — numImplicit already computed above
  const { params, hasRecursiveParam, recursiveParamLocalIdx } = peelCtorParams(
    ctor.type, numImplicit, typeArgs, inductiveName, definitions, userParamNames
  );
  let ctorReturnType = ctor.type;
  for (let i = 0; i < numImplicit; i++) {
    if (ctorReturnType.tag === 'Binder' && ctorReturnType.binderKind.tag === 'BPi') {
      const arg = typeArgs[i] || { tag: 'Hole' as const, id: '_implicit_' + i };
      ctorReturnType = subst(0, arg, ctorReturnType.body);
    }
  }
  let numExplicit = 0;
  while (ctorReturnType.tag === 'Binder' && ctorReturnType.binderKind.tag === 'BPi') {
    ctorReturnType = ctorReturnType.body;
    numExplicit++;
  }
  const ctorRetArgs = extractTypeArgsFromType(ctorReturnType);

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
    newCtx.push(uGoal.ctx[j]);
  }

  // 2. Constructor params (at positions s..s+numParams-1, replacing the scrutinee)
  // After peelCtorParams substitutes implicit type args (from the scrutinee's scope
  // at depth s), the param types already have correct de Bruijn indices for depth s.
  // No additional shift is needed — shifting would double the offset.
  for (let i = 0; i < numParams; i++) {
    newCtx.push({ name: params[i].name, type: params[i].type });
  }

  // 3. Entries after scrutinee: substitute scrutinee var with ctor app.
  //    Use replaceVar (not subst) FIRST to avoid index collisions,
  //    then shift for the extra params.
  for (let j = s + 1; j < uGoal.ctx.length; j++) {
    let entryType = uGoal.ctx[j].type;
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
    newCtx.push({ name: uGoal.ctx[j].name, type: entryType });
  }

  // Build goal type using remapScrutineeVars: a custom variable remapping that
  // correctly handles the restructured context (scrutinee removed, params inserted).
  //
  // Original var mapping → new index:
  //   Var(k) for k < uScrutIdx  → Var(k + ihOffset)              [near entries]
  //   Var(uScrutIdx)            → ctorApp                         [scrutinee replaced]
  //   Var(k) for k > uScrutIdx  → Var(k + numParams - 1 + ihOffset) [far entries]

  // Build ctorApp for goal scope with FINAL indices:
  //   param[i] at position s+i → Var(uScrutIdx + numParams - 1 + ihOffset - i)
  let ctorAppGoal: TTKTerm = { tag: 'Const', name: ctor.name };
  for (let i = 0; i < numParams; i++) {
    ctorAppGoal = {
      tag: 'App',
      fn: ctorAppGoal,
      arg: { tag: 'Var', index: uScrutIdx + numParams - 1 + ihOffset - i },
    };
  }

  const caseGoalType = remapScrutineeVars(
    uGoal.type, uScrutIdx, ctorAppGoal, numParams, ihOffset
  );

  // Add induction hypothesis if recursive
  if (hasRecursiveParam && recursiveParamLocalIdx !== null) {
    // IH type: goal with scrutinee replaced by the recursive param.
    // IH sees entries 0..newCtx.length-2 (everything before IH itself).
    // IH scope depth = newCtx.length - 1 = n + numParams - 2 (without IH's own entry).
    // But IH is about to be pushed, making newCtx.length = n + numParams - 1 + 1.
    // From IH's scope (depth = n + numParams - 1, not counting itself):
    //   param[recursiveParamLocalIdx] at position s + recursiveParamLocalIdx
    //   → Var(uScrutIdx + numParams - 1 - recursiveParamLocalIdx)
    const recursiveParamRef: TTKTerm = {
      tag: 'Var',
      index: uScrutIdx + numParams - 1 - recursiveParamLocalIdx,
    };

    // Remap with ihOffset=0 since IH doesn't count itself
    const ihType = remapScrutineeVars(
      uGoal.type, uScrutIdx, recursiveParamRef, numParams, 0
    );

    // Use user-provided IH name if available (comes after constructor params in userParamNames)
    const ihName = userParamNames?.[numParams] ?? 'IH';
    newCtx.push({ name: ihName, type: ihType });
  }

  let resultGoal: MetaVar = {
    ctx: newCtx,
    type: caseGoalType,
    solution: undefined,
    caseTag: ctor.name,
  };

  const deferredIndexSubsts: GoalScopeIndexSubst[] = [];
  for (let i = 0; i < Math.min(typeArgs.length, ctorRetArgs.length); i++) {
    const scrArg = typeArgs[i];
    if (scrArg.tag !== 'Var') continue;

    const ctorArg = ctorRetArgs[i];
    if (!containsVarBelow(ctorArg, numExplicit)) continue;

    const replacement = remapCtorReturnArgToGoalScope(
      ctorArg,
      numExplicit,
      uScrutIdx,
      numParams,
      ihOffset,
    );
    if (ttermStructEqual(scrArg, replacement)) continue;

    deferredIndexSubsts.push({
      ctxArrayPos: s - 1 - scrArg.index,
      replacement,
    });
  }

  resultGoal = applyGoalScopeIndexSubstitutions(resultGoal, deferredIndexSubsts);

  return resultGoal;
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
  userParamNames?: readonly string[],
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
    const userName = userParamNames?.[paramIdx];
    const name = (userName && userName !== '_')
      ? userName
      : (currentType.name && currentType.name !== '_')
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
 * Resolve a name against the goal context. If the name matches a hypothesis,
 * return a Var term with the correct de Bruijn index. Otherwise return Const.
 */
function resolveNameInGoal(name: string, goal: MetaVar): TTKTerm {
  // Search context from most recent (innermost) to oldest (outermost)
  for (let i = goal.ctx.length - 1; i >= 0; i--) {
    if (goal.ctx[i].name === name) {
      return { tag: 'Var', index: goal.ctx.length - 1 - i };
    }
  }
  return { tag: 'Const', name };
}

/**
 * Tokenize a parenthesized expression string, respecting nested parens.
 * E.g. "addComm (field R) a" → ["addComm", "(field R)", "a"]
 */
function tokenizeExpr(s: string): string[] {
  const tokens: string[] = [];
  let depth = 0;
  let start = 0;
  for (let i = 0; i < s.length; i++) {
    if (s[i] === '(') depth++;
    else if (s[i] === ')') depth--;
    else if (s[i] === ' ' && depth === 0) {
      if (i > start) tokens.push(s.slice(start, i));
      start = i + 1;
    }
  }
  if (start < s.length) tokens.push(s.slice(start));
  return tokens;
}

/**
 * Resolve an expression string (from surfaceTermToString) against the goal context.
 * Handles parenthesized applications like "(addComm (field R) (rzero R) a)"
 * and simple names like "plusComm". Inserts Hole placeholders at implicit
 * argument positions using the namedArgMap from definitions.
 */
function resolveExprInGoal(expr: string, goal: MetaVar, definitions?: DefinitionsMap): TTKTerm {
  expr = expr.trim();

  // Var format from surfaceTermToString: v0, v1, ...
  if (/^v\d+$/.test(expr)) {
    return { tag: 'Var', index: parseInt(expr.slice(1)) };
  }

  // Parenthesized expression: (head arg1 arg2 ...)
  if (expr.startsWith('(') && expr.endsWith(')')) {
    const inner = expr.slice(1, -1).trim();

    // Lambda: (fun name => body) or legacy (\name => body)
    const isFunLambda = inner.startsWith('fun ');
    const isBackslashLambda = inner.startsWith('\\');
    if (isFunLambda || isBackslashLambda) {
      const arrowIdx = inner.indexOf('=>');
      if (arrowIdx !== -1) {
        const binderName = isFunLambda
          ? inner.slice(4, arrowIdx).trim()   // skip "fun "
          : inner.slice(1, arrowIdx).trim();  // skip "\"
        // Extend goal context with lambda binder so name resolution inside the
        // body produces correctly shifted de Bruijn indices (e.g., "a" at index 3
        // in the outer context becomes index 4 inside the lambda body).
        const bodyGoal: MetaVar = {
          ...goal,
          ctx: [...goal.ctx, { name: binderName, type: { tag: 'Hole', id: '_' } }],
        };
        const body = resolveExprInGoal(inner.slice(arrowIdx + 2).trim(), bodyGoal, definitions);
        return {
          tag: 'Binder',
          name: '_',
          binderKind: { tag: 'BLam' },
          domain: { tag: 'Hole', id: '_' },
          body,
        };
      }
    }

    // Application: (f a b c) → App(App(App(f, a), b), c)
    const tokens = tokenizeExpr(inner);
    if (tokens.length === 0) return { tag: 'Const', name: expr };

    const head = resolveExprInGoal(tokens[0], goal, definitions);
    const userArgs = tokens.slice(1).map(t => resolveExprInGoal(t, goal, definitions));

    // Insert Holes at implicit positions if the head has a namedArgMap
    const resolvedArgs = insertImplicitHoles(head, userArgs, definitions);

    let result = head;
    for (const arg of resolvedArgs) {
      result = { tag: 'App', fn: result, arg };
    }
    return result;
  }

  // Simple name — resolve against context
  return resolveNameInGoal(expr, goal);
}

/**
 * Insert Hole placeholders at implicit argument positions.
 * If the head is Const and has a namedArgMap in definitions, implicit positions
 * get Holes and user args fill explicit positions.
 */
function insertImplicitHoles(head: TTKTerm, userArgs: TTKTerm[], definitions?: DefinitionsMap): TTKTerm[] {
  if (!definitions || head.tag !== 'Const') return userArgs;

  const lookup = createNamedArgLookup(definitions);
  const namedArgMap = lookup(head.name);
  if (!namedArgMap || namedArgMap.size === 0) return userArgs;

  const implicitPositions = new Set(namedArgMap.values());
  const result: TTKTerm[] = [];
  let userIdx = 0;
  let pos = 0;
  while (userIdx < userArgs.length) {
    if (implicitPositions.has(pos)) {
      result.push({ tag: 'Hole', id: `_implicit${pos}` });
    } else {
      result.push(userArgs[userIdx]);
      userIdx++;
    }
    pos++;
  }
  return result;
}

/**
 * Trace-based cursor replay: walk the proof tree advancing through the
 * pre-computed trace until we reach the cursor node. Returns the engine
 * state at the cursor position without re-running any tactics.
 */
function replayProofTreeFromTrace(
  root: ProofNode,
  cursorId: ProofNodeId,
  initialEngine: TacticEngine,
  trace: import('../tactics/tactic-session').TacticStepTrace[],
): ReplayResult | null {
  let traceIdx = 0;

  function walk(
    node: ProofNode | undefined,
    currentEngine: TacticEngine,
    caseLabel?: string,
    caseLabelLatex?: string,
    inductionVar?: string,
  ): ReplayResult | null {
    if (!node) return null;  // Defensive: handle undefined nodes gracefully
    const goalId = currentEngine.getFocusedGoalId();
    if (!goalId) return null;

    // Cursor found — return current engine state
    if (node.id === cursorId) {
      return { engine: currentEngine, goalId, caseLabel, caseLabelLatex, inductionVar };
    }

    switch (node.tag) {
      case 'hole':
      case 'exact':
        return null; // leaf — cursor not here

      case 'intros':
      case 'unfold':
      case 'fold':
      case 'rewrite':
      case 'have':
      case 'suffices': {
        const step = traceIdx < trace.length ? trace[traceIdx++] : undefined;
        const nextEngine = step?.engineAfter ?? currentEngine;
        if (node.child.id === cursorId) {
          return { engine: nextEngine, goalId: nextEngine.getFocusedGoalId() ?? goalId, caseLabel, caseLabelLatex, inductionVar, tacticError: step?.error };
        }
        return walk(node.child, nextEngine, caseLabel, caseLabelLatex, inductionVar);
      }

      case 'apply': {
        const step = traceIdx < trace.length ? trace[traceIdx++] : undefined;
        const nextEngine = step?.engineAfter ?? currentEngine;
        const baseFocus = nextEngine.focusIndex;
        for (let i = 0; i < node.children.length; i++) {
          const childFocusIdx = baseFocus + i;
          if (childFocusIdx >= nextEngine.goals.length) break;
          const childEngine = nextEngine.withUpdates({ focusIndex: childFocusIdx });
          const childGoalId = childEngine.getFocusedGoalId();
          if (node.children[i].id === cursorId) {
            return { engine: childEngine, goalId: childGoalId ?? goalId, caseLabel, caseLabelLatex, inductionVar };
          }
          const result = walk(node.children[i], childEngine, caseLabel, caseLabelLatex, inductionVar);
          if (result) return result;
        }
        return null;
      }

      case 'induction': {
        const step = traceIdx < trace.length ? trace[traceIdx++] : undefined;
        const afterCasesEngine = step?.engineAfter ?? currentEngine;

        for (const c of node.cases) {
          const matchIdx = afterCasesEngine.goals.findIndex(g => {
            const meta = afterCasesEngine.metaVars.get(g);
            return meta?.caseTag === c.constructorName;
          });
          if (matchIdx >= 0) {
            const caseEngine = afterCasesEngine.withUpdates({ focusIndex: matchIdx });
            if (c.id === cursorId) {
              return { engine: caseEngine, goalId: caseEngine.getFocusedGoalId() ?? goalId, caseLabel: c.label, caseLabelLatex: c.labelLatex, inductionVar: node.scrutinee };
            }
            const result = walk(c.body, caseEngine, c.label, c.labelLatex, node.scrutinee);
            if (result) return result;
          } else {
            if (c.id === cursorId) {
              return { engine: afterCasesEngine, goalId, caseLabel: c.label, caseLabelLatex: c.labelLatex, inductionVar: node.scrutinee };
            }
            const result = walk(c.body, afterCasesEngine, c.label, c.labelLatex, node.scrutinee);
            if (result) return result;
          }
        }
        return null;
      }

      case 'simp': {
        for (const _step of node.steps) {
          if (traceIdx < trace.length) traceIdx++;
        }
        const step = traceIdx < trace.length ? trace[traceIdx++] : undefined;
        const nextEngine = step?.engineAfter ?? currentEngine;
        if (node.child.id === cursorId) {
          return { engine: nextEngine, goalId: nextEngine.getFocusedGoalId() ?? goalId, caseLabel, caseLabelLatex, inductionVar };
        }
        return walk(node.child, nextEngine, caseLabel, caseLabelLatex, inductionVar);
      }
    }
  }

  return walk(root, initialEngine);
}

/**
 * Replay the proof tree against a TacticEngine, applying real tactics
 * at each node until we reach the cursor. Returns the engine state
 * at the cursor position.
 */
function replayProofTree(
  node: ProofNode | undefined,
  cursorId: ProofNodeId,
  engine: TacticEngine,
  caseLabel?: string,
  caseLabelLatex?: string,
  inductionVar?: string,
): ReplayResult | null {
  if (!node) return null;  // Defensive: handle undefined nodes gracefully
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

      const tactic = new UnfoldTactic([node.name], node.occurrence);
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

    case 'fold': {
      // Apply FoldTactic — replace definition body occurrences with Const(name)
      const goal = engine.getFocusedGoal();
      if (!goal) return null;

      const tactic = new FoldTactic([node.name], node.occurrence);
      const result = tactic.apply(engine, goal, goalId);

      if (!result.success) {
        const childResult = replayProofTree(
          node.child, cursorId, engine,
          caseLabel, caseLabelLatex, inductionVar,
        );
        if (childResult) {
          childResult.tacticError = `fold ${node.name}: ${result.error ?? 'failed'}`;
        }
        return childResult;
      }

      return replayProofTree(
        node.child, cursorId, result.newEngine,
        caseLabel, caseLabelLatex, inductionVar,
      );
    }

    case 'rewrite': {
      // Apply RewriteTactic — resolve name against context first (for hypotheses like IH)
      const goal = engine.getFocusedGoal();
      if (!goal) return null;

      const tactic = new RewriteTactic(
        resolveExprInGoal(node.name, goal, engine.definitions),
        { reverse: node.reverse, enhanced: node.enhanced, occurrences: node.occurrences && node.occurrences.length > 0 ? [...node.occurrences] : undefined, targetHead: node.targetHead },
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
      // Apply ApplyTactic — resolve name against context first (for hypotheses)
      const goal = engine.getFocusedGoal();
      if (!goal) return null;

      const tactic = node.name === 'constructor'
        ? new ConstructorTactic()
        : new ApplyTactic(resolveExprInGoal(node.name, goal, engine.definitions));
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

      // Apply succeeded — match children to subgoals.
      // Accumulate engine state across children so that solving child 0
      // (e.g., exact 1) propagates the meta solution to child 1's goal type
      // (showing 0 ≤ 1 instead of 0 ≤ □).
      let currentEngine = result.newEngine!;
      const baseFocus = currentEngine.focusIndex;

      for (let i = 0; i < node.children.length; i++) {
        const child = node.children[i];
        const childFocusIdx = baseFocus + i;
        if (childFocusIdx >= currentEngine.goals.length) break;

        const childEngine = currentEngine.withUpdates({ focusIndex: childFocusIdx });
        const childGoalId = childEngine.getFocusedGoalId();

        if (child.id === cursorId) {
          return {
            engine: childEngine,
            goalId: childGoalId!,
            caseLabel, caseLabelLatex, inductionVar,
          };
        }

        // Check if cursor is inside this child's subtree
        if (isCursorInSubtree(child, cursorId)) {
          const childResult = replayProofTree(
            child, cursorId, childEngine,
            caseLabel, caseLabelLatex, inductionVar,
          );
          if (childResult) return childResult;
        } else {
          // Cursor is NOT in this child — replay it to propagate meta solutions
          // to subsequent sibling goals (e.g., exact 1 solves ?a → siblings show 0≤1 not 0≤□)
          // Only update metaVars (NOT goals list, since ExactTactic removes the solved goal
          // and that would break focus indices for subsequent children).
          if (child.tag === 'exact' && childGoalId) {
            const goal = childEngine.getFocusedGoal();
            if (goal) {
              const term = parseExactExpr(child.expr, goal.ctx, childEngine.definitions);
              if (term) {
                try {
                  const er = new ExactTactic(term).apply(childEngine, goal, childGoalId);
                  if (er.success) {
                    // Propagate ONLY metaVars (solutions), keep original goals list
                    currentEngine = currentEngine.withUpdates({ metaVars: er.newEngine.metaVars });
                  }
                } catch { /* ignore */ }
              }
            }
          }
        }
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

      // Find scrutinee in context or infer from expression
      let scrutineeIdx = findVarIndex(node.scrutinee, goal.ctx);
      let effectiveGoal = goal;
      let effectiveEngine = engine;
      let effectiveGoalId = goalId;

      // If scrutinee is a complex expression (not in context), try to parse and infer its type
      if (scrutineeIdx === null) {
        const parsedScrutinee = parseExactExpr(node.scrutinee, goal.ctx, engine.definitions);
        if (parsedScrutinee) {
          const extended = extendGoalForComplexScrutinee(engine, goal, goalId, parsedScrutinee);
          if (extended) {
            effectiveEngine = extended.engine;
            effectiveGoal = extended.goal;
            effectiveGoalId = extended.goalId;
            scrutineeIdx = extended.scrutineeIdx;
          }
        }
      }

      if (scrutineeIdx === null) {
        return searchCasesForCursor(node.cases, cursorId, engine, goalId, node.scrutinee);
      }

      // Look up inductive type for constructor info
      const scrutineeType = effectiveGoal.ctx[effectiveGoal.ctx.length - 1 - scrutineeIdx].type;
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
        const caseGoalId = `${effectiveGoalId}_case_${c.constructorName}`;
        const caseMeta = computeCaseGoalDirect(
          effectiveGoal, scrutineeIdx, ctor, inductiveName, effectiveEngine.definitions,
          c.constructorParamNames
        );

        // Create engine with this case goal
        const caseMetaVars = new Map(effectiveEngine.metaVars);
        caseMetaVars.set(caseGoalId, caseMeta);
        const caseGoals = [...effectiveEngine.goals];
        const focusIdx = caseGoals.indexOf(effectiveGoalId);
        if (focusIdx >= 0) {
          caseGoals[focusIdx] = caseGoalId;
        } else {
          caseGoals.push(caseGoalId);
        }
        const caseEngine = effectiveEngine.withUpdates({
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

    case 'simp': {
      // Replay each step sequentially, then recurse into child
      let currentEngine = engine;
      for (const step of node.steps) {
        const stepGoalId = currentEngine.getFocusedGoalId();
        const stepGoal = currentEngine.getFocusedGoal();
        if (!stepGoalId || !stepGoal) break;

        if (step.tag === 'rewrite') {
          const tactic = new RewriteTactic(
            resolveExprInGoal(step.name, stepGoal, currentEngine.definitions),
            { reverse: step.reverse, enhanced: step.enhanced, occurrences: step.occurrences && step.occurrences.length > 0 ? [...step.occurrences] : undefined, targetHead: step.targetHead },
          );
          const result = tactic.apply(currentEngine, stepGoal, stepGoalId);
          if (result.success) {
            currentEngine = result.newEngine!;
          }
        } else if (step.tag === 'unfold') {
          const tactic = new UnfoldTactic([step.name]);
          const result = tactic.apply(currentEngine, stepGoal, stepGoalId);
          if (result.success) {
            const newId = result.newEngine.getFocusedGoalId();
            currentEngine = newId
              ? normalizeGoalInEngine(result.newEngine, newId)
              : result.newEngine;
          }
        }
      }

      return replayProofTree(
        node.child, cursorId, currentEngine,
        caseLabel, caseLabelLatex, inductionVar,
      );
    }

    case 'have': {
      const goal = engine.getFocusedGoal();
      if (!goal) return null;

      // Interactive proof subtree: proofTree proves typeExpr, then child gets h : T in context
      if (node.proofTree && node.typeExpr) {
        // Parse typeExpr in the current goal context (implicit args are re-inserted as Holes
        // by parseExactExpr, then resolved by elaborateType via checkType)
        const raw = parseExactExpr(node.typeExpr, goal.ctx, engine.definitions);
        const typeTerm = raw ? elaborateType(raw, goal.ctx, engine.definitions) : null;
        if (!typeTerm) {
          return replayProofTree(node.child, cursorId, engine, caseLabel, caseLabelLatex, inductionVar);
        }

        // Create a subgoal for the proofTree with goal type = typeExpr
        const proofGoalId = goalId + '_have_proof';
        const proofMeta: MetaVar = { ctx: goal.ctx, type: typeTerm, solution: undefined };
        const proofMetaVars = new Map(engine.metaVars);
        proofMetaVars.set(proofGoalId, proofMeta);
        const proofGoals = engine.goals.map(g => g === goalId ? proofGoalId : g);
        const proofEngine = engine.withUpdates({ metaVars: proofMetaVars, goals: proofGoals });

        // If cursor is in the proofTree subtree, replay there
        if (isCursorInSubtree(node.proofTree, cursorId)) {
          return replayProofTree(node.proofTree, cursorId, proofEngine, caseLabel, caseLabelLatex, inductionVar);
        }

        // Cursor is in child — extend context with h : T
        const newCtx = [...goal.ctx, { name: node.name, type: typeTerm }];
        const newGoalType = shiftTerm(goal.type, 1, 0);
        const childGoalId = goalId + '_have_cont';
        const childMeta: MetaVar = { ctx: newCtx, type: newGoalType, solution: undefined };
        const childMetaVars = new Map(engine.metaVars);
        childMetaVars.set(childGoalId, childMeta);
        const childGoals = engine.goals.map(g => g === goalId ? childGoalId : g);
        const childEngine = engine.withUpdates({ metaVars: childMetaVars, goals: childGoals });

        if (node.child.id === cursorId) {
          return { engine: childEngine, goalId: childGoalId, caseLabel, caseLabelLatex, inductionVar };
        }
        return replayProofTree(node.child, cursorId, childEngine, caseLabel, caseLabelLatex, inductionVar);
      }

      // Flat expression mode: Apply HaveTactic — parse proof expression, infer type, extend context
      const proofTerm = parseExactExpr(node.expr, goal.ctx, engine.definitions);
      if (!proofTerm) {
        // Parse failed — continue with unchanged engine
        if (node.child.id === cursorId) {
          return { engine, goalId, caseLabel, caseLabelLatex, inductionVar };
        }
        return replayProofTree(
          node.child, cursorId, engine,
          caseLabel, caseLabelLatex, inductionVar,
        );
      }

      // Use Hole as type — HaveTactic will infer it
      const holeType: TTKTerm = { tag: 'Hole', id: '_have_type' };
      const tactic = new HaveTactic(node.name, holeType, proofTerm);
      const result = tactic.apply(engine, goal, goalId);

      if (!result.success) {
        // Tactic failed — continue with unchanged engine, propagate error
        const childResult = replayProofTree(
          node.child, cursorId, engine,
          caseLabel, caseLabelLatex, inductionVar,
        );
        if (childResult) {
          childResult.tacticError = `have ${node.name}: ${result.error ?? 'failed'}`;
        }
        return childResult;
      }

      return replayProofTree(
        node.child, cursorId, result.newEngine,
        caseLabel, caseLabelLatex, inductionVar,
      );
    }

    case 'suffices': {
      // Parse the suffices type, create a new goal with that type
      const goal = engine.getFocusedGoal();
      if (!goal) return null;

      const typeTerm = parseExactExpr(node.typeExpr, goal.ctx, engine.definitions);
      if (!typeTerm) {
        if (node.child.id === cursorId) {
          return { engine, goalId, caseLabel, caseLabelLatex, inductionVar };
        }
        return replayProofTree(node.child, cursorId, engine, caseLabel, caseLabelLatex, inductionVar);
      }

      // Create new goal with the suffices type
      const newGoalId = goalId + '_suffices';
      const newMeta: MetaVar = { ctx: goal.ctx, type: typeTerm, solution: undefined };
      const newMetaVars = new Map(engine.metaVars);
      newMetaVars.set(newGoalId, newMeta);
      const newGoals = engine.goals.map(g => g === goalId ? newGoalId : g);
      const newEngine = engine.withUpdates({ metaVars: newMetaVars, goals: newGoals });

      if (node.child.id === cursorId) {
        return { engine: newEngine, goalId: newGoalId, caseLabel, caseLabelLatex, inductionVar };
      }
      return replayProofTree(node.child, cursorId, newEngine, caseLabel, caseLabelLatex, inductionVar);
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
/**
 * Replay the proof tree to the cursor position and return the TacticEngine.
 * Used by simp and other meta-tactics that need the engine state.
 */
export function replayToEngine(
  root: ProofNode,
  cursorId: ProofNodeId,
  kernelType: TTKTerm,
  definitions: DefinitionsMap,
): TacticEngine | null {
  const engine = createInitialEngine(kernelType, [], definitions);
  const replay = replayProofTree(root, cursorId, engine);
  return replay?.engine ?? null;
}

export function computeTypedContext(
  root: ProofNode,
  cursorId: ProofNodeId,
  surfaceType: TTerm,
  registry: SyntaxRegistry,
  _inductiveMap?: InductiveMap,
  kernelType?: TTKTerm,
  definitions?: DefinitionsMap,
  tacticTrace?: import('../tactics/tactic-session').TacticStepTrace[],
): TypedProofContext | null {
  const rev = buildReverseRegistry(registry);

  // If we have kernel type + definitions, use the real TacticEngine
  if (kernelType && definitions) {
    return computeWithTacticEngine(root, cursorId, kernelType, definitions, rev, tacticTrace);
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

  // Parse expression (supports application, parens, name resolution, and implicit arg insertion)
  const term = parseExactExpr(expr, goal.ctx, engine.definitions);
  if (!term) {
    return { status: 'error', message: `Cannot parse expression: ${expr}` };
  }

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

export function buildNameCtx(ctx: ReadonlyArray<{ name: string }>): string[] {
  const nameCtx: string[] = [];
  for (let j = ctx.length - 1; j >= 0; j--) {
    nameCtx.push(ctx[j].name);
  }
  return nameCtx;
}

/** Render hypotheses from a MetaVar's context to TypedHypothesis[]. */
/** Cosmetic zonk for stale implicit-arg metas.
 *
 *  Some tactics (notably `cases` on a scrutinee like `Limit.eps_delta limF ε h`)
 *  leave metas named `_implicit_<paramName>` unsolved in the engine's metavar
 *  map — they were created during parseExactExpr for Const's implicit args
 *  but never got unified because constraint solving isn't run between tactics.
 *
 *  These metas are SEMANTICALLY references to the outer context variable with
 *  the matching name. At display time, resolve them to a Var pointing at that
 *  context entry so the user sees `Carrier(R)` instead of `Carrier(□)`.
 *
 *  `hypIndex` is the index of the hypothesis being rendered; its context is
 *  `ctx[0..hypIndex-1]`, and de Bruijn Var indices run from 0 (closest) to
 *  hypIndex-1 (furthest).
 */
function cosmeticZonkImplicitMetas(
  term: TTKTerm,
  ctx: ReadonlyArray<{ name: string }>,
  hypIndex: number,
  depth: number = 0,
): TTKTerm {
  if (!term) return term;
  if (term.tag === 'Meta' && term.id.startsWith('_implicit_')) {
    // Strip any fresh-meta suffixes. `elaborate-tactic-arg` appends `_<N>`
    // per Const-occurrence to keep implicit-arg metas unique; the elaborator
    // may further add `$<N>` as a freshening marker.
    const paramName = term.id
      .substring('_implicit_'.length)
      .replace(/\$\d+$/, '')
      .replace(/_\d+$/, '');
    // Search the hypothesis's context (entries 0..hypIndex-1) for a matching name.
    // Innermost match wins so we shadow correctly.
    for (let i = hypIndex - 1; i >= 0; i--) {
      if (ctx[i].name === paramName) {
        // Var index in the hypothesis's frame: the entry at ctx[i] is
        // (hypIndex - 1 - i) positions away from the innermost binder.
        // Under `depth` additional binders (inside Pi/Lam bodies), shift up.
        return { tag: 'Var', index: (hypIndex - 1 - i) + depth };
      }
    }
    return term;
  }
  switch (term.tag) {
    case 'App':
      return {
        tag: 'App',
        fn: cosmeticZonkImplicitMetas(term.fn, ctx, hypIndex, depth),
        arg: cosmeticZonkImplicitMetas(term.arg, ctx, hypIndex, depth),
      };
    case 'Binder':
      return {
        ...term,
        domain: cosmeticZonkImplicitMetas(term.domain, ctx, hypIndex, depth),
        body: cosmeticZonkImplicitMetas(term.body, ctx, hypIndex, depth + 1),
      };
    default:
      return term;
  }
}

function renderHypotheses(
  ctx: ReadonlyArray<{ name: string; type: TTKTerm }>,
  definitions: DefinitionsMap,
  rev: ReverseRegistry,
  projMap?: Map<string, Map<number, string>>,
  aliasMap?: Map<string, AliasFoldInfo>,
  engine?: TacticEngine,
): TypedHypothesis[] {
  const pm = projMap ?? buildProjectionFoldMap(definitions);
  const am = aliasMap ?? buildAliasFoldMap(definitions, pm);
  const hypotheses: TypedHypothesis[] = [];
  for (let i = 0; i < ctx.length; i++) {
    const entry = ctx[i];
    // Skip internal desugaring placeholders. `_nested*` entries are inserted
    // by nested-case-pattern desugaring (`| MkDPair a (MkPair b c) =>` becomes
    // `| MkDPair a _nested0 => cases _nested0 with | MkPair b c => ...`) and
    // the user should never see them in the hypothesis panel — the useful
    // content is in the subsequent destructured entries.
    if (entry.name.startsWith('_nested')) continue;
    const nameCtx: string[] = [];
    for (let j = i - 1; j >= 0; j--) {
      nameCtx.push(ctx[j].name);
    }
    // Zonk before rendering — solved metas must be substituted so they don't
    // appear as Holes (gray squares) in the UI.  Depth = i because hypothesis i
    // was formed in the context of entries 0..i-1.
    const zonked = engine ? engine.zonkTerm(entry.type, i) : entry.type;
    // Resolve stale `_implicit_*` metas to the matching outer ctx var.
    const cosmeticZonked = cosmeticZonkImplicitMetas(zonked, ctx, i);
    const normalizedType = betaNormalize(cosmeticZonked);
    let folded = foldProjectionMatches(normalizedType, pm);
    folded = foldAliases(folded, am);
    // Unfold @syntax @unfold-marked constants
    if (rev.unfoldNames.size > 0) {
      folded = unfoldTransparent(folded, definitions, rev.unfoldNames);
    }
    const surfaceHypType = kernelTypeToSurface(folded, definitions);
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
  projMap?: Map<string, Map<number, string>>,
  aliasMap?: Map<string, AliasFoldInfo>,
): string {
  const zonked = engine.zonkTerm(goal.type, goal.ctx.length);
  const pm = projMap ?? buildProjectionFoldMap(definitions);
  const am = aliasMap ?? buildAliasFoldMap(definitions, pm);
  // 1. Prepare Match scrutinees for iota-reduction by WHNF-ing with real definitions
  //    (e.g., `match one { ... }` → `match Succ(Zero) { ... }` so iota fires)
  const prepared = prepareMatchesForIota(zonked, definitions);
  // 2. Full-normalize (beta + iota) to reduce redexes like (\i => i)(0) → 0
  //    and Match expressions from unfold (e.g., match Zero { ... } → result)
  const normalized = fullNormalize(prepared, createDefinitionsMap());
  // 3. Fold projection-like Match expressions back to Const form
  //    (e.g., match x { MkR fields => field_i } → R.field_i(x))
  let term = foldProjectionMatches(normalized, pm);
  // 4. Fold delta-expanded projections back to alias names
  //    (e.g., CompleteOrderedField.mul(Carrier(R), field(R), a, b) → rmul(R, a, b))
  term = foldAliases(term, am);
  // 5. Fold simple wrapper definitions back (e.g., radd(R, rone(R), rone(R)) → rtwo(R))
  term = foldSimpleWrappers(term, definitions);
  // 6. Unfold @syntax @unfold-marked constants (e.g., EpsDeltaWitness → Pair(...))
  if (rev.unfoldNames.size > 0) {
    term = unfoldTransparent(term, definitions, rev.unfoldNames);
  }
  const surface = kernelTypeToSurface(term, definitions);
  return renderTerm(surface, buildNameCtx(goal.ctx), rev);
}

/** Render a kernel subterm to LaTeX (for previewing what a subterm becomes after a tactic). */
export function renderSubtermLatex(
  term: TTKTerm,
  ctx: TTKContext,
  definitions: DefinitionsMap,
  rev: ReverseRegistry,
  projMap?: Map<string, Map<number, string>>,
  aliasMap?: Map<string, AliasFoldInfo>,
): string {
  const prepared = prepareMatchesForIota(term, definitions);
  const normalized = fullNormalize(prepared, createDefinitionsMap());
  const pm = projMap ?? buildProjectionFoldMap(definitions);
  let folded = foldProjectionMatches(normalized, pm);
  const am = aliasMap ?? buildAliasFoldMap(definitions, pm);
  folded = foldAliases(folded, am);
  // Fold simple wrapper definitions back
  folded = foldSimpleWrappers(folded, definitions);
  // Unfold @syntax @unfold-marked constants
  if (rev.unfoldNames.size > 0) {
    folded = unfoldTransparent(folded, definitions, rev.unfoldNames);
  }
  const surface = kernelTypeToSurface(folded, definitions);
  return renderTerm(surface, buildNameCtx(ctx), rev);
}

/**
 * Render a UnifiedEquation (lhs/rhs kernel terms) to LaTeX string "lhs = rhs".
 * Shared by both trace-based and walk-based replay paths.
 */
function renderUnifiedEquationLatex(
  equation: import('../tactics/tactic').UnifiedEquation,
  engine: TacticEngine,
  goalCtx: ReadonlyArray<{ name: string; type: TTKTerm }>,
  definitions: DefinitionsMap,
  rev: ReverseRegistry,
  projMap: Map<string, Map<number, string>>,
  aliasMap: Map<string, AliasFoldInfo>,
): string {
  const { lhs: rawLhs, rhs: rawRhs } = equation;
  // Zonk, normalize (beta + iota), fold projections back to Const form
  const lhsZonked = engine.zonkTerm(rawLhs, goalCtx.length);
  const rhsZonked = engine.zonkTerm(rawRhs, goalCtx.length);
  const lhsNorm = fullNormalize(prepareMatchesForIota(betaNormalize(lhsZonked), definitions), createDefinitionsMap());
  const rhsNorm = fullNormalize(prepareMatchesForIota(betaNormalize(rhsZonked), definitions), createDefinitionsMap());
  let lhs = foldProjectionMatches(lhsNorm, projMap);
  let rhs = foldProjectionMatches(rhsNorm, projMap);
  lhs = foldAliases(lhs, aliasMap);
  rhs = foldAliases(rhs, aliasMap);
  // Unfold @syntax @unfold-marked constants
  if (rev.unfoldNames.size > 0) {
    lhs = unfoldTransparent(lhs, definitions, rev.unfoldNames);
    rhs = unfoldTransparent(rhs, definitions, rev.unfoldNames);
  }
  const nameCtx = buildNameCtx(goalCtx);
  const lhsSurface = kernelTypeToSurface(lhs, definitions);
  const rhsSurface = kernelTypeToSurface(rhs, definitions);
  const lhsLatex = renderTerm(lhsSurface, nameCtx, rev);
  const rhsLatex = renderTerm(rhsSurface, nameCtx, rev);
  return `${lhsLatex} = ${rhsLatex}`;
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
  tacticTrace?: import('../tactics/tactic-session').TacticStepTrace[],
): TypedProofContext | null {
  // Create initial engine with the kernel goal type
  const engine = createInitialEngine(kernelType, [], definitions);

  // Fast path: use trace to find engine at cursor without replaying
  let replay: ReplayResult | null = null;
  if (tacticTrace && tacticTrace.length > 0) {
    replay = replayProofTreeFromTrace(root, cursorId, engine, tacticTrace);
  }
  // Fallback: replay tactics
  if (!replay) {
    replay = replayProofTree(root, cursorId, engine);
  }
  if (!replay) return null;

  // Use the FINAL trace engine's metaVars when available. Branch
  // renames (e.g., `_arg0` → `hle`) happen inside tactic-session's
  // applyCaseBranches AFTER the enclosing cases tactic fires, so the
  // trace engine at the cursor may still have the old name. The final
  // engine has all renames applied.
  const finalMetaVars = (tacticTrace && tacticTrace.length > 0)
    ? tacticTrace[tacticTrace.length - 1].engineAfter.metaVars
    : replay.engine.metaVars;
  const goal = finalMetaVars.get(replay.goalId) ?? replay.engine.metaVars.get(replay.goalId);
  if (!goal) return null;

  // Render hypotheses and goal using shared helpers.  Pass a zonk
  // engine that has the final metaVars so solved metas from later
  // tactics and branch renames are both visible.
  const zonkEngine = replay.engine.withUpdates({ metaVars: finalMetaVars });
  const hypotheses = renderHypotheses(goal.ctx, definitions, rev, undefined, undefined, zonkEngine);

  // For exact nodes, show the expression and validate it
  const cursorNode = findNodeById(root, cursorId);
  let goalLatex: string;
  let validation: ValidationResult | undefined;
  if (cursorNode?.tag === 'exact') {
    goalLatex = cursorNode.expr;
    // If we used the trace path, check the trace for exact validation
    if (tacticTrace && tacticTrace.length > 0) {
      // Find the trace entry for this exact — it's the last entry (exact is terminal)
      const exactEntry = tacticTrace.find(s => s.tacticName === 'exact' || s.tacticName === 'reflexivity');
      if (exactEntry && !exactEntry.error) {
        validation = { status: 'solved' };
      } else if (exactEntry?.error) {
        validation = { status: 'error', message: exactEntry.error };
      } else {
        validation = validateExactNode(cursorNode.expr, replay.engine, replay.goalId);
      }
    } else {
      validation = validateExactNode(cursorNode.expr, replay.engine, replay.goalId);
    }
  } else {
    goalLatex = renderGoalLatex(replay.engine, goal, definitions, rev);
  }

  // Surface tactic errors (failed rewrite/unfold) as validation errors
  if (!validation && replay.tacticError) {
    validation = { status: 'error', message: replay.tacticError };
  }

  // Generate caseLabelLatex using the real renderer when missing
  let caseLabelLatex = replay.caseLabelLatex;
  if (!caseLabelLatex && replay.caseLabel) {
    const caseInfo = findCaseAncestor(root, cursorId);
    if (caseInfo) {
      const paramNames = caseInfo.caseNode.constructorParamNames ?? [];
      const ctorApp = buildConstructorApp(caseInfo.caseNode.constructorName!, [...paramNames]);
      const ctx = [...paramNames].reverse();
      const rhsLatex = renderTerm(ctorApp, ctx, rev);
      const scrutineeName = caseInfo.scrutinee;
      caseLabelLatex = `${renderTerm(mkVarTT(0), [scrutineeName], rev)} = ${rhsLatex}`;
    }
  }

  return {
    hypotheses,
    caseLabel: replay.caseLabel,
    caseLabelLatex,
    inductionVar: replay.inductionVar,
    goal: goalLatex,
    validation,
    kernelGoal: {
      engine: replay.engine,
      goal,
      definitions,
      rev,
    },
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
    case 'fold':
    case 'rewrite':
    case 'have':
    case 'suffices':
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
    case 'simp': {
      for (const step of node.steps) {
        const found = findNodeById(step, id);
        if (found) return found;
      }
      return findNodeById(node.child, id);
    }
  }
}

/**
 * Find the CaseNode ancestor that contains the given cursor ID,
 * plus its scrutinee name from the parent InductionNode.
 */
function findCaseAncestor(
  node: ProofNode, targetId: ProofNodeId,
): { caseNode: CaseNode; scrutinee: string } | null {
  switch (node.tag) {
    case 'hole':
    case 'exact':
      return null;
    case 'intros':
    case 'unfold':
    case 'fold':
    case 'rewrite':
    case 'have':
    case 'suffices':
      return findCaseAncestor(node.child, targetId);
    case 'apply':
      for (const child of node.children) {
        const found = findCaseAncestor(child, targetId);
        if (found) return found;
      }
      return null;
    case 'induction':
      for (const c of node.cases) {
        if (c.id === targetId || containsNodeId(c.body, targetId)) {
          return c.constructorName ? { caseNode: c, scrutinee: node.scrutinee } : null;
        }
      }
      return null;
    case 'simp':
      for (const step of node.steps) {
        const found = findCaseAncestor(step, targetId);
        if (found) return found;
      }
      return findCaseAncestor(node.child, targetId);
  }
}

function containsNodeId(node: ProofNode, id: ProofNodeId): boolean {
  return findNodeById(node, id) !== null;
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
  /** Error message when this tactic (unfold/rewrite/apply) failed. */
  readonly tacticError?: string;
  /** For suffices nodes: LaTeX of the "by" proof expression, rendered through math pipeline. */
  readonly sufficesByLatex?: string;
  /** For exact/have nodes: LaTeX of the proof expression, rendered through math pipeline. */
  readonly proofExprLatex?: string;
  /** For induction/cases nodes: LaTeX of the scrutinee, rendered through math pipeline. */
  readonly scrutineeLatex?: string;
  /** True when the goal type is a VALUE type (like ℝ, Nat, List A) rather
   *  than a proposition. Used by the prose renderer to switch phrasing:
   *  "We need a value of type ℝ. Use δF." vs
   *  "We must show 0 < δF. The result follows from posF." */
  readonly isValueType?: boolean;
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
  tacticTrace?: import('../tactics/tactic-session').TacticStepTrace[],
): Map<ProofNodeId, NodeGoalInfo> {
  // Fast path: use pre-computed trace from compilation
  if (tacticTrace && tacticTrace.length > 0) {
    return replayEntireTreeFromTrace(root, kernelType, definitions, rev, tacticTrace);
  }
  // Fallback: re-run tactics (for interactive editing or when trace unavailable)
  return replayEntireTreeViaWalk(root, kernelType, definitions, rev);
}

function replayEntireTreeFromTrace(
  root: ProofNode,
  kernelType: TTKTerm,
  definitions: DefinitionsMap,
  rev: ReverseRegistry,
  trace: import('../tactics/tactic-session').TacticStepTrace[],
): Map<ProofNodeId, NodeGoalInfo> {
  const result = new Map<ProofNodeId, NodeGoalInfo>();
  const projMap = buildProjectionFoldMap(definitions);
  const aliasMap = buildAliasFoldMap(definitions, projMap);
  const initialEngine = createInitialEngine(kernelType, [], definitions);

  // The final trace entry has the most complete metaVars map — all implicit
  // arg metas have been solved by that point. Using it for hypothesis
  // zonking at intermediate steps avoids rendering unsolved-yet-to-be-solved
  // metas as ugly □ holes (e.g., `fst : Carrier(□)` instead of `Carrier(R)`
  // when `_implicit_R` is solved by a later tactic).
  const finalMetaVars = trace.length > 0
    ? trace[trace.length - 1].engineAfter.metaVars
    : initialEngine.metaVars;

  /** Wrap an engine with the final metaVars map so zonking sees all
   *  solutions that will eventually be known, not just the ones fixed
   *  at this step. Context/goal IDs are preserved; only the solution
   *  map changes. */
  function withFinalMetas(eng: TacticEngine): TacticEngine {
    return eng.withUpdates({ metaVars: finalMetaVars });
  }

  function recordFromEngine(nodeId: ProofNodeId, eng: TacticEngine, gId: string, caseLabelLatex?: string, validation?: ValidationResult): void {
    const zonkEng = withFinalMetas(eng);
    // Look up the goal from the final metaVars so any post-cases renames
    // (applied by tactic-session.applyCaseBranches inside branch bodies) are
    // visible when rendering case-branch headers captured from the pre-rename
    // `engineAfter` of the enclosing cases tactic.
    const goal = zonkEng.metaVars.get(gId) ?? eng.metaVars.get(gId);
    if (!goal) return;
    const zonkedGoalType = zonkEng.zonkTerm(goal.type, goal.ctx.length);
    result.set(nodeId, {
      goalLatex: renderGoalLatex(zonkEng, goal, definitions, rev, projMap, aliasMap),
      hypotheses: renderHypotheses(goal.ctx, definitions, rev, projMap, aliasMap, zonkEng),
      caseLabelLatex,
      validation,
      isValueType: isValueTypeGoal(zonkedGoalType),
    });
  }

  /** Fill in proofExprLatex for exact descendants that the trace walk missed.
   *  This happens when exact nodes are inside nested constructor+focus bullets
   *  — the FocusTactic wraps the entire inner sequence into one trace step,
   *  so the per-node walk can't descend into them.
   *
   *  Uses the PARENT goal context (which has the full branch variables) to
   *  parse and render the exact expressions. */
  function fillMissingProofExprs(root: ProofNode, parentGoal: MetaVar): void {
    function visit(n: ProofNode): void {
      if (n.tag === 'exact') {
        const existing = result.get(n.id);
        if (!existing || !existing.proofExprLatex) {
          const latex = renderProofExpr(n.expr, parentGoal, definitions, rev, projMap, aliasMap);
          if (latex) {
            if (existing) {
              result.set(n.id, { ...existing, proofExprLatex: latex });
            } else {
              // Create a minimal entry for nodes the trace walk never visited
              result.set(n.id, {
                goalLatex: '',
                hypotheses: [],
                proofExprLatex: latex,
              });
            }
          }
        }
      }
      if ('child' in n && (n as any).child) visit((n as any).child);
      if ('children' in n && (n as any).children) for (const c of (n as any).children) visit(c);
      if ('cases' in n && (n as any).cases) for (const c of (n as any).cases) visit(c.body);
    }
    visit(root);
  }

  // Walk the proof tree in the same order as the trace, advancing a cursor through the trace.
  let traceIdx = 0;

  function walkTrace(node: ProofNode | undefined, currentEngine: TacticEngine, caseLabelLatex?: string): void {
    if (!node) return;  // Defensive: handle undefined nodes gracefully
    const gId = currentEngine.getFocusedGoalId();
    if (!gId) return;

    switch (node.tag) {
      case 'hole':
        recordFromEngine(node.id, currentEngine, gId, caseLabelLatex);
        break;

      case 'exact': {
        // The trace already validated this exact — check if it succeeded
        const exactStep = traceIdx < trace.length ? trace[traceIdx++] : undefined;
        let validation: ValidationResult | undefined;
        if (exactStep && !exactStep.error) {
          validation = { status: 'solved' };
        } else if (exactStep?.error) {
          validation = { status: 'error', message: exactStep.error };
        } else {
          validation = validateExactNode(node.expr, currentEngine, gId);
        }
        recordFromEngine(node.id, currentEngine, gId, caseLabelLatex, validation);
        // Render the proof expression through the math pipeline
        const exactGoal = currentEngine.metaVars.get(gId);
        if (exactGoal) {
          const exprLatex = renderProofExpr(node.expr, exactGoal, definitions, rev, projMap, aliasMap);
          if (exprLatex) {
            const existing = result.get(node.id);
            if (existing) result.set(node.id, { ...existing, proofExprLatex: exprLatex });
          }
        }
        break;
      }

      case 'intros':
      case 'unfold':
      case 'fold': {
        recordFromEngine(node.id, currentEngine, gId, caseLabelLatex);
        const step = traceIdx < trace.length ? trace[traceIdx++] : undefined;
        const nextEngine = step?.engineAfter ?? currentEngine;
        if (step?.error) {
          const existing = result.get(node.id);
          if (existing) result.set(node.id, { ...existing, tacticError: step.error });
        }
        walkTrace(node.child, nextEngine, caseLabelLatex);
        break;
      }
      case 'rewrite': {
        recordFromEngine(node.id, currentEngine, gId, caseLabelLatex);
        const step = traceIdx < trace.length ? trace[traceIdx++] : undefined;
        const nextEngine = step?.engineAfter ?? currentEngine;
        if (step?.error) {
          const existing = result.get(node.id);
          if (existing) result.set(node.id, { ...existing, tacticError: step.error });
        }
        // Render the unified equation from the trace
        if (step?.unifiedEquation && !step.error) {
          const goal = currentEngine.metaVars.get(gId);
          if (goal) {
            const eqLatex = renderUnifiedEquationLatex(
              step.unifiedEquation, nextEngine, goal.ctx,
              definitions, rev, projMap, aliasMap,
            );
            const existing = result.get(node.id);
            if (existing) result.set(node.id, { ...existing, unifiedEquationLatex: eqLatex });
          }
        }
        walkTrace(node.child, nextEngine, caseLabelLatex);
        break;
      }
      case 'have': {
        recordFromEngine(node.id, currentEngine, gId, caseLabelLatex);

        // Interactive proof subtree mode — no trace step to consume
        if (node.proofTree && (node.typeKernel || node.typeExpr)) {
          const haveGoal = currentEngine.metaVars.get(gId);
          if (haveGoal) {
            let typeTerm = node.typeKernel ?? null;
            if (!typeTerm && node.typeExpr) {
              const raw = parseExactExpr(node.typeExpr, haveGoal.ctx, definitions);
              if (raw) typeTerm = elaborateType(raw, haveGoal.ctx, definitions, currentEngine.metaVars);
            }
            if (typeTerm) {
              // Walk proofTree with subgoal
              const proofGoalId = gId + '_have_proof';
              const proofMeta: MetaVar = { ctx: haveGoal.ctx, type: typeTerm, solution: undefined };
              const proofMetaVars = new Map(currentEngine.metaVars);
              proofMetaVars.set(proofGoalId, proofMeta);
              const proofGoals = currentEngine.goals.map(g => g === gId ? proofGoalId : g);
              const proofEngine = currentEngine.withUpdates({ metaVars: proofMetaVars, goals: proofGoals });
              walkTrace(node.proofTree, proofEngine, caseLabelLatex);

              // Walk child with h : T
              const newCtx = [...haveGoal.ctx, { name: node.name, type: typeTerm }];
              const newGoalType = shiftTerm(haveGoal.type, 1, 0);
              const childGoalId = gId + '_have_cont';
              const childMeta: MetaVar = { ctx: newCtx, type: newGoalType, solution: undefined };
              const childMetaVars = new Map(currentEngine.metaVars);
              childMetaVars.set(childGoalId, childMeta);
              const childGoals = currentEngine.goals.map(g => g === gId ? childGoalId : g);
              const childEngine = currentEngine.withUpdates({ metaVars: childMetaVars, goals: childGoals });
              walkTrace(node.child, childEngine, caseLabelLatex);
              break;
            }
          }
        }

        // Flat expression mode
        if (node.expr.trim() !== '?') {
          const haveGoal = currentEngine.metaVars.get(gId);
          if (haveGoal) {
            const haveLatex = renderProofExpr(node.expr, haveGoal, definitions, rev, projMap, aliasMap);
            if (haveLatex) {
              const existing = result.get(node.id);
              if (existing) result.set(node.id, { ...existing, proofExprLatex: haveLatex });
            }
          }
        }
        const step = traceIdx < trace.length ? trace[traceIdx++] : undefined;
        const nextEngine = step?.engineAfter ?? currentEngine;
        if (step?.error) {
          const existing = result.get(node.id);
          if (existing) result.set(node.id, { ...existing, tacticError: step.error });
        }
        walkTrace(node.child, nextEngine, caseLabelLatex);
        break;
      }
      case 'suffices': {
        recordFromEngine(node.id, currentEngine, gId, caseLabelLatex);
        const step = traceIdx < trace.length ? trace[traceIdx++] : undefined;
        const nextEngine = step?.engineAfter ?? currentEngine;
        if (step?.error) {
          const existing = result.get(node.id);
          if (existing) result.set(node.id, { ...existing, tacticError: step.error });
        }
        // Render the byProof expression through the math pipeline
        if (node.byProof) {
          const byLatex = renderByProofExpr(node.byProof, currentEngine, gId, definitions, rev, projMap, aliasMap);
          if (byLatex) {
            const existing = result.get(node.id);
            if (existing) result.set(node.id, { ...existing, sufficesByLatex: byLatex });
          }
        }
        walkTrace(node.child, nextEngine, caseLabelLatex);
        break;
      }

      case 'apply': {
        recordFromEngine(node.id, currentEngine, gId, caseLabelLatex);
        // Advance trace cursor
        const step = traceIdx < trace.length ? trace[traceIdx++] : undefined;
        const nextEngine = step?.engineAfter ?? currentEngine;
        if (step?.error) {
          const existing = result.get(node.id);
          if (existing) result.set(node.id, { ...existing, tacticError: step.error });
        }
        // Walk children (subgoals from apply), propagating sibling solutions
        let traceEng = nextEngine;
        const baseFocus = nextEngine.focusIndex;
        for (let i = 0; i < node.children.length; i++) {
          const childFocusIdx = baseFocus + i;
          if (childFocusIdx >= traceEng.goals.length) break;
          const childEngine = traceEng.withUpdates({ focusIndex: childFocusIdx });
          walkTrace(node.children[i], childEngine, caseLabelLatex);
          // Propagate exact solutions to subsequent siblings
          const child = node.children[i];
          if (child.tag === 'exact') {
            const cGoalId = childEngine.getFocusedGoalId();
            const cGoal = cGoalId ? childEngine.getFocusedGoal() : null;
            if (cGoal && cGoalId) {
              const term = parseExactExpr(child.expr, cGoal.ctx, definitions);
              if (term) {
                try {
                  const er = new ExactTactic(term).apply(childEngine, cGoal, cGoalId);
                  if (er.success) traceEng = traceEng.withUpdates({ metaVars: er.newEngine.metaVars });
                } catch { /* ignore */ }
              }
            }
          }
        }
        // Fill in proofExprLatex for any exact descendants that the trace
        // walk couldn't reach (e.g., inner exacts inside nested constructor
        // + focus bullets, where the trace has a single step for the whole
        // focus block). Uses the PARENT goal context (before the apply) so
        // branch variables (δF, posF, etc.) are in scope for parsing.
        const parentGoal = withFinalMetas(currentEngine).metaVars.get(gId);
        if (parentGoal) fillMissingProofExprs(node, parentGoal);
        break;
      }

      case 'induction': {
        recordFromEngine(node.id, currentEngine, gId, caseLabelLatex);
        // Render scrutinee through math pipeline
        const indGoal = currentEngine.metaVars.get(gId);
        if (indGoal) {
          const scrLatex = renderProofExpr(node.scrutinee, indGoal, definitions, rev, projMap, aliasMap);
          if (scrLatex) {
            const existing = result.get(node.id);
            if (existing) result.set(node.id, { ...existing, scrutineeLatex: scrLatex });
          }
        }
        // Cases/induction: trace has steps for the base tactic + each branch's tactics
        // Advance past the base cases/induction tactic
        const step = traceIdx < trace.length ? trace[traceIdx++] : undefined;
        const afterCasesEngine = step?.engineAfter ?? currentEngine;

        for (const c of node.cases) {
          // Find the goal with matching caseTag in the engine after cases
          const matchIdx = afterCasesEngine.goals.findIndex(g => {
            const meta = afterCasesEngine.metaVars.get(g);
            return meta?.caseTag === c.constructorName;
          });
          const resolvedLabel = caseLabelLatexOf(c, rev);
          if (matchIdx >= 0) {
            const caseEngine = afterCasesEngine.withUpdates({ focusIndex: matchIdx });
            const caseGoalId = caseEngine.getFocusedGoalId();
            if (caseGoalId) {
              recordFromEngine(c.id, caseEngine, caseGoalId, resolvedLabel);
            }
            walkTrace(c.body, caseEngine, resolvedLabel);
          } else {
            // Fallback: use current engine
            recordFromEngine(c.id, afterCasesEngine, gId, resolvedLabel);
            walkTrace(c.body, afterCasesEngine, resolvedLabel);
          }
        }
        break;
      }

      case 'simp': {
        recordFromEngine(node.id, currentEngine, gId, caseLabelLatex);
        // Simp has multiple rewrite steps — each is a trace entry
        for (const _step of node.steps) {
          if (traceIdx < trace.length) traceIdx++; // advance past each simp sub-step
        }
        // After simp, advance past the simp tactic itself
        const step = traceIdx < trace.length ? trace[traceIdx++] : undefined;
        const nextEngine = step?.engineAfter ?? currentEngine;
        walkTrace(node.child, nextEngine, caseLabelLatex);
        break;
      }
    }
  }

  walkTrace(root, initialEngine);
  return result;
}

function replayEntireTreeViaWalk(
  root: ProofNode,
  kernelType: TTKTerm,
  definitions: DefinitionsMap,
  rev: ReverseRegistry,
): Map<ProofNodeId, NodeGoalInfo> {
  const result = new Map<ProofNodeId, NodeGoalInfo>();
  const engine = createInitialEngine(kernelType, [], definitions);
  const projMap = buildProjectionFoldMap(definitions);
  const aliasMap = buildAliasFoldMap(definitions, projMap);

  function recordGoal(nodeId: ProofNodeId, eng: TacticEngine, gId: string, caseLabelLatex?: string): void {
    const goal = eng.metaVars.get(gId);
    if (!goal) return;
    const zonkedGoalType = eng.zonkTerm(goal.type, goal.ctx.length);
    result.set(nodeId, {
      goalLatex: renderGoalLatex(eng, goal, definitions, rev, projMap, aliasMap),
      hypotheses: renderHypotheses(goal.ctx, definitions, rev, projMap, aliasMap, eng),
      caseLabelLatex,
      isValueType: isValueTypeGoal(zonkedGoalType),
    });
  }

  function recordExact(nodeId: ProofNodeId, eng: TacticEngine, gId: string, expr: string): void {
    const goal = eng.metaVars.get(gId);
    if (!goal) return;
    const validation = validateExactNode(expr, eng, gId);
    result.set(nodeId, {
      goalLatex: renderGoalLatex(eng, goal, definitions, rev, projMap, aliasMap),
      hypotheses: renderHypotheses(goal.ctx, definitions, rev, projMap, aliasMap, eng),
      validation,
    });
  }

  function walk(
    node: ProofNode | undefined,
    eng: TacticEngine,
    caseLabelLatex?: string,
  ): void {
    if (!node) return;  // Defensive: handle undefined nodes gracefully
    const gId = eng.getFocusedGoalId();
    if (!gId) return;

    switch (node.tag) {
      case 'hole': {
        recordGoal(node.id, eng, gId, caseLabelLatex);
        break;
      }

      case 'exact': {
        recordExact(node.id, eng, gId, node.expr);
        // Render the exact proof expression through the math pipeline
        const exactGoal = eng.metaVars.get(gId);
        if (exactGoal) {
          const exprLatex = renderProofExpr(node.expr, exactGoal, definitions, rev, projMap, aliasMap);
          if (exprLatex) {
            const existing = result.get(node.id);
            if (existing) result.set(node.id, { ...existing, proofExprLatex: exprLatex });
          }
        }
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
        const tactic = new UnfoldTactic([node.name], node.occurrence);
        const tacResult = tactic.apply(eng, goal, gId);
        if (tacResult.success) {
          const newGoalId = tacResult.newEngine!.getFocusedGoalId();
          const normalized = newGoalId
            ? normalizeGoalInEngine(tacResult.newEngine!, newGoalId)
            : tacResult.newEngine!;
          walk(node.child, normalized, caseLabelLatex);
        } else {
          // Tag the node with error info
          const existing = result.get(node.id);
          if (existing) result.set(node.id, { ...existing, tacticError: tacResult.error });
          walk(node.child, eng, caseLabelLatex);
        }
        break;
      }

      case 'fold': {
        recordGoal(node.id, eng, gId, caseLabelLatex);
        const goal = eng.getFocusedGoal();
        if (!goal) { walk(node.child, eng, caseLabelLatex); break; }
        const foldTactic = new FoldTactic([node.name], node.occurrence);
        const foldResult = foldTactic.apply(eng, goal, gId);
        if (foldResult.success) {
          walk(node.child, foldResult.newEngine!, caseLabelLatex);
        } else {
          const existing = result.get(node.id);
          if (existing) result.set(node.id, { ...existing, tacticError: foldResult.error });
          walk(node.child, eng, caseLabelLatex);
        }
        break;
      }

      case 'rewrite': {
        recordGoal(node.id, eng, gId, caseLabelLatex);
        const goal = eng.getFocusedGoal();
        if (!goal) { walk(node.child, eng, caseLabelLatex); break; }
        const tactic = new RewriteTactic(
          resolveExprInGoal(node.name, goal, eng.definitions),
          { reverse: node.reverse, enhanced: node.enhanced, occurrences: node.occurrences && node.occurrences.length > 0 ? [...node.occurrences] : undefined, targetHead: node.targetHead },
        );
        const tacResult = tactic.apply(eng, goal, gId);
        // Capture the unified equation and attach it to this node's info
        if (tacResult.success && tacResult.unifiedEquation) {
          const eqLatex = renderUnifiedEquationLatex(
            tacResult.unifiedEquation, tacResult.newEngine!, goal.ctx,
            definitions, rev, projMap, aliasMap,
          );
          const existing = result.get(node.id);
          if (existing) {
            result.set(node.id, { ...existing, unifiedEquationLatex: eqLatex });
          }
        }
        if (!tacResult.success) {
          const existing = result.get(node.id);
          if (existing) result.set(node.id, { ...existing, tacticError: tacResult.error });
        }
        walk(node.child, tacResult.success ? tacResult.newEngine! : eng, caseLabelLatex);
        break;
      }

      case 'have': {
        recordGoal(node.id, eng, gId, caseLabelLatex);
        const goal = eng.getFocusedGoal();
        if (!goal) { walk(node.child, eng, caseLabelLatex); break; }

        // Interactive proof subtree mode
        if (node.proofTree && (node.typeKernel || node.typeExpr)) {
          let typeTerm = node.typeKernel ?? null;
          if (!typeTerm && node.typeExpr) {
            const raw = parseExactExpr(node.typeExpr, goal.ctx, eng.definitions);
            if (raw) typeTerm = elaborateType(raw, goal.ctx, eng.definitions, eng.metaVars);
          }
          if (typeTerm) {
            // Walk proofTree with a subgoal of type typeExpr
            const proofGoalId = gId + '_have_proof';
            const proofMeta: MetaVar = { ctx: goal.ctx, type: typeTerm, solution: undefined };
            const proofMetaVars = new Map(eng.metaVars);
            proofMetaVars.set(proofGoalId, proofMeta);
            const proofGoals = eng.goals.map(g => g === gId ? proofGoalId : g);
            const proofEngine = eng.withUpdates({ metaVars: proofMetaVars, goals: proofGoals });
            walk(node.proofTree, proofEngine, caseLabelLatex);

            // Walk child with h : T in context
            const newCtx = [...goal.ctx, { name: node.name, type: typeTerm }];
            const newGoalType = shiftTerm(goal.type, 1, 0);
            const childGoalId = gId + '_have_cont';
            const childMeta: MetaVar = { ctx: newCtx, type: newGoalType, solution: undefined };
            const childMetaVars = new Map(eng.metaVars);
            childMetaVars.set(childGoalId, childMeta);
            const childGoals = eng.goals.map(g => g === gId ? childGoalId : g);
            const childEngine = eng.withUpdates({ metaVars: childMetaVars, goals: childGoals });
            walk(node.child, childEngine, caseLabelLatex);
            break;
          }
        }

        // Flat expression mode
        if (node.expr.trim() !== '?') {
          const haveExprLatex = renderProofExpr(node.expr, goal, definitions, rev, projMap, aliasMap);
          if (haveExprLatex) {
            const existing = result.get(node.id);
            if (existing) result.set(node.id, { ...existing, proofExprLatex: haveExprLatex });
          }
        }
        const proofTerm = parseExactExpr(node.expr, goal.ctx, eng.definitions);
        if (!proofTerm) { walk(node.child, eng, caseLabelLatex); break; }
        const haveTactic = new HaveTactic(node.name, { tag: 'Hole', id: '_have_type' }, proofTerm);
        const haveResult = haveTactic.apply(eng, goal, gId);
        walk(node.child, haveResult.success ? haveResult.newEngine! : eng, caseLabelLatex);
        break;
      }

      case 'suffices': {
        recordGoal(node.id, eng, gId, caseLabelLatex);
        const goal = eng.getFocusedGoal();
        if (!goal) { walk(node.child, eng, caseLabelLatex); break; }
        const typeTerm = parseExactExpr(node.typeExpr, goal.ctx, eng.definitions);
        if (!typeTerm) { walk(node.child, eng, caseLabelLatex); break; }
        // Render the byProof expression through the math pipeline
        if (node.byProof) {
          const byLatex = renderByProofExpr(node.byProof, eng, gId, definitions, rev, projMap, aliasMap);
          if (byLatex) {
            const existing = result.get(node.id);
            if (existing) result.set(node.id, { ...existing, sufficesByLatex: byLatex });
          }
        }
        // Create new goal with the suffices type
        const suffGoalId = gId + '_suffices';
        const suffMeta: MetaVar = { ctx: goal.ctx, type: typeTerm, solution: undefined };
        const suffMetaVars = new Map(eng.metaVars);
        suffMetaVars.set(suffGoalId, suffMeta);
        const suffGoals = eng.goals.map(g => g === gId ? suffGoalId : g);
        const suffEngine = eng.withUpdates({ metaVars: suffMetaVars, goals: suffGoals });
        walk(node.child, suffEngine, caseLabelLatex);
        break;
      }

      case 'apply': {
        recordGoal(node.id, eng, gId, caseLabelLatex);
        const goal = eng.getFocusedGoal();
        if (!goal) {
          for (const child of node.children) walk(child, eng, caseLabelLatex);
          break;
        }
        const tactic = node.name === 'constructor'
          ? new ConstructorTactic()
          : new ApplyTactic(resolveExprInGoal(node.name, goal, eng.definitions));
        const tacResult = tactic.apply(eng, goal, gId);
        if (!tacResult.success) {
          const existing = result.get(node.id);
          if (existing) result.set(node.id, { ...existing, tacticError: tacResult.error });
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
              // Zonk to resolve any metas, beta-normalize, fold projections + aliases
              const zonked = betaNormalize(newEngine.zonkTerm(arg.term, goal.ctx.length));
              let folded = foldProjectionMatches(zonked, projMap);
              folded = foldAliases(folded, aliasMap);
              // Unfold @syntax @unfold-marked constants
              if (rev.unfoldNames.size > 0) {
                folded = unfoldTransparent(folded, definitions, rev.unfoldNames);
              }
              const surface = kernelTypeToSurface(folded, definitions);
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

        let currentEng = newEngine;
        const baseFocus = newEngine.focusIndex;
        for (let i = 0; i < node.children.length; i++) {
          const childFocusIdx = baseFocus + i;
          if (childFocusIdx >= currentEng.goals.length) break;
          const childEngine = currentEng.withUpdates({ focusIndex: childFocusIdx });
          walk(node.children[i], childEngine, caseLabelLatex);
          // Propagate meta solutions from this child to subsequent siblings
          // (e.g., exact 1 solves ?a → sibling goals show 0≤1 not 0≤□)
          const child = node.children[i];
          if (child.tag === 'exact') {
            const childGoalId = childEngine.getFocusedGoalId();
            const childGoal = childGoalId ? childEngine.getFocusedGoal() : null;
            if (childGoal && childGoalId) {
              const term = parseExactExpr(child.expr, childGoal.ctx, childEngine.definitions);
              if (term) {
                try {
                  const er = new ExactTactic(term).apply(childEngine, childGoal, childGoalId);
                  if (er.success) {
                    currentEng = currentEng.withUpdates({ metaVars: er.newEngine.metaVars });
                  }
                } catch { /* ignore */ }
              }
            }
          }
        }
        break;
      }

      case 'induction': {
        recordGoal(node.id, eng, gId, caseLabelLatex);
        const goal = eng.getFocusedGoal();
        if (!goal) break;
        // Render scrutinee through math pipeline
        {
          const scrLatex = renderProofExpr(node.scrutinee, goal, definitions, rev, projMap, aliasMap);
          if (scrLatex) {
            const existing = result.get(node.id);
            if (existing) result.set(node.id, { ...existing, scrutineeLatex: scrLatex });
          }
        }

        let scrutineeIdx: number | null = findVarIndex(node.scrutinee, goal.ctx);
        let effGoal = goal;
        let effEng = eng;
        let effGId = gId;

        // If scrutinee is a complex expression (not in context), try to parse and infer its type
        if (scrutineeIdx === null) {
          const parsedScrutinee = parseExactExpr(node.scrutinee, goal.ctx, eng.definitions);
          if (parsedScrutinee) {
            const extended = extendGoalForComplexScrutinee(eng, goal, gId, parsedScrutinee);
            if (extended) {
              effEng = extended.engine;
              effGoal = extended.goal;
              effGId = extended.goalId;
              scrutineeIdx = extended.scrutineeIdx;
            }
          }
        }

        if (scrutineeIdx === null) {
          for (const c of node.cases) {
            const resolved = caseLabelLatexOf(c, rev);
            recordGoal(c.id, eng, gId, resolved);
            walk(c.body, eng, resolved);
          }
          break;
        }

        const scrutineeType = effGoal.ctx[effGoal.ctx.length - 1 - scrutineeIdx].type;
        const scrutineeTypeWhnf = whnf(scrutineeType, { definitions: eng.definitions });
        const inductiveName = getInductiveHead(scrutineeTypeWhnf);
        if (!inductiveName) {
          for (const c of node.cases) {
            const resolved = caseLabelLatexOf(c, rev);
            recordGoal(c.id, eng, gId, resolved);
            walk(c.body, eng, resolved);
          }
          break;
        }
        const inductiveDef = eng.definitions.inductiveTypes.get(inductiveName);
        if (!inductiveDef) {
          for (const c of node.cases) {
            const resolved = caseLabelLatexOf(c, rev);
            recordGoal(c.id, eng, gId, resolved);
            walk(c.body, eng, resolved);
          }
          break;
        }

        for (const c of node.cases) {
          const resolved = caseLabelLatexOf(c, rev);
          const ctor = inductiveDef.constructors.find(ct => ct.name === c.constructorName);
          if (!ctor) {
            recordGoal(c.id, eng, gId, resolved);
            walk(c.body, eng, resolved);
            continue;
          }
          const caseGoalId = `${effGId}_case_${c.constructorName}`;
          const caseMeta = computeCaseGoalDirect(effGoal, scrutineeIdx!, ctor, inductiveName, effEng.definitions, c.constructorParamNames);
          const caseMetaVars = new Map(effEng.metaVars);
          caseMetaVars.set(caseGoalId, caseMeta);
          const caseGoals = [...effEng.goals];
          const focusIdx = caseGoals.indexOf(effGId);
          if (focusIdx >= 0) caseGoals[focusIdx] = caseGoalId;
          else caseGoals.push(caseGoalId);
          const caseEngine = effEng.withUpdates({
            metaVars: caseMetaVars,
            goals: caseGoals,
            focusIndex: focusIdx >= 0 ? focusIdx : caseGoals.length - 1,
          });
          recordGoal(c.id, caseEngine, caseGoalId, resolved);
          walk(c.body, caseEngine, resolved);
        }
        break;
      }

      case 'simp': {
        recordGoal(node.id, eng, gId, caseLabelLatex);
        let currentEngine = eng;
        // Replay each step
        for (const step of node.steps) {
          const stepGoalId = currentEngine.getFocusedGoalId();
          const stepGoal = currentEngine.getFocusedGoal();
          if (!stepGoalId || !stepGoal) break;

          recordGoal(step.id, currentEngine, stepGoalId, caseLabelLatex);

          if (step.tag === 'rewrite') {
            const tactic = new RewriteTactic(
              resolveExprInGoal(step.name, stepGoal, currentEngine.definitions),
              { reverse: step.reverse, enhanced: step.enhanced, occurrences: step.occurrences && step.occurrences.length > 0 ? [...step.occurrences] : undefined, targetHead: step.targetHead },
            );
            const stepResult = tactic.apply(currentEngine, stepGoal, stepGoalId);
            if (stepResult.success) {
              currentEngine = stepResult.newEngine!;
            }
          } else if (step.tag === 'unfold') {
            const tactic = new UnfoldTactic([step.name]);
            const stepResult = tactic.apply(currentEngine, stepGoal, stepGoalId);
            if (stepResult.success) {
              const newId = stepResult.newEngine.getFocusedGoalId();
              currentEngine = newId
                ? normalizeGoalInEngine(stepResult.newEngine, newId)
                : stepResult.newEngine;
            }
          }
        }
        walk(node.child, currentEngine, caseLabelLatex);
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
    case 'fold':
    case 'rewrite':
    case 'have':
    case 'suffices':
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
            caseLabelLatex: caseLabelLatexOf(c, rev),
            inductionVar: node.scrutinee,
            goal: renderTerm(currentType, [...nameCtx], rev),
          };
        }
        const result = walkTreeSurface(c.body, cursorId, currentType, hypotheses, nameCtx, rev);
        if (result) {
          return {
            ...result,
            caseLabel: result.caseLabel ?? c.label,
            caseLabelLatex: result.caseLabelLatex ?? caseLabelLatexOf(c, rev),
            inductionVar: result.inductionVar ?? node.scrutinee,
          };
        }
      }
      return null;
    }

    case 'simp':
      // No kernel type — pass through to child
      return walkTreeSurface(node.child, cursorId, currentType, hypotheses, nameCtx, rev);
  }
}
