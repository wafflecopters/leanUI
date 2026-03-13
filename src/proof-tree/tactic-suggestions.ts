/**
 * Tactic Suggestion System
 *
 * Computes suggested tactics based on what the user has selected
 * in the interactive goal view. Pure functions — no React dependency.
 */

import { GoalPath, GoalBinderInfo, InteractiveGoal } from './interactive-goal';
import { TTKTerm } from '../compiler/kernel';
import { DefinitionsMap, MetaVar } from '../compiler/term';
import { TacticEngine } from '../tactics/tacticsEngine';
import { ExactTactic } from '../tactics/tactic';
import { RewriteTactic } from '../tactics/rewrite-tactic';

// ============================================================================
// Types
// ============================================================================

export interface TacticSuggestion {
  readonly id: string;
  readonly label: string;
  /** Optional LaTeX version of the label for rich rendering. */
  readonly labelLatex?: string;
  readonly description: string;
  /** For intro tactics: proposed variable names (editable by user). */
  readonly proposedNames?: readonly string[];
}

/** Escape a name for use in LaTeX (wrap multi-char names in \text{}). */
function texEscape(name: string): string {
  if (name.length === 1) return name;
  return `\\text{${name}}`;
}

// ============================================================================
// Main entry point
// ============================================================================

/**
 * Compute tactic suggestions based on the selected goal path.
 * Returns an empty array if nothing is selected or no suggestions apply.
 */
export function computeTacticSuggestions(
  selectedPath: GoalPath | null,
  goal: InteractiveGoal,
  definitions?: DefinitionsMap,
  kernelGoal?: KernelGoalInfo,
): readonly TacticSuggestion[] {
  if (!selectedPath) return [];

  const suggestions: TacticSuggestion[] = [];

  // Try `exact refl` — only when clicking on an Equal(...) subterm
  if (kernelGoal) {
    const subtermInfo = goal.subtermMap.get(selectedPath);
    if (subtermInfo?.headName === 'Equal') {
      const { engine, goal: metaGoal } = kernelGoal;
      const goalId = engine.getFocusedGoalId();
      if (goalId) {
        try {
          const reflTactic = new ExactTactic({ tag: 'Const', name: 'refl' });
          const result = reflTactic.apply(engine, metaGoal, goalId);
          if (result.success) {
            suggestions.push({
              id: 'exact-refl',
              label: 'refl',
              labelLatex: '\\textbf{refl}',
              description: 'Both sides are equal — close with refl',
            });
          }
        } catch { /* refl doesn't apply */ }
      }
    }
  }

  // Check if a Pi binder is selected (path = "goal-N" where N is a valid binder index)
  const binderMatch = selectedPath.match(/^goal-(\d+)$/);
  if (binderMatch && goal.binders.length > 0) {
    const binderIndex = parseInt(binderMatch[1], 10);
    if (binderIndex >= 0 && binderIndex < goal.binders.length) {
      suggestions.push(...computeBinderSuggestions(binderIndex, goal));
    }
  }

  // Check subterm-level suggestions
  if (definitions) {
    const subtermInfo = goal.subtermMap.get(selectedPath);
    if (subtermInfo) {
      // Unfold: selected subterm is an App of a term definition (not inductive type or constructor)
      if (subtermInfo.isAppOfConst && subtermInfo.headName) {
        const name = subtermInfo.headName;
        if (definitions.terms.has(name)
          && !definitions.inductiveTypes.has(name)
          && !definitions.inductiveNameOfConstructor.has(name)) {
          suggestions.push({
            id: `unfold-${name}`,
            label: `Unfold ${name}`,
            labelLatex: `\\text{Unfold } \\textbf{${texEscape(name)}}`,
            description: `Unfold the definition of ${name}`,
          });
        }
      }

      // Induction: selected subterm is a Var whose type is an inductive type
      if (subtermInfo.varName) {
        const typeHead = goal.contextVarTypes.get(subtermInfo.varName);
        if (typeHead && definitions.inductiveTypes.has(typeHead)) {
          suggestions.push({
            id: `induction-${subtermInfo.varName}`,
            label: `Induction on ${subtermInfo.varName}`,
            labelLatex: `\\text{Induction on } ${texEscape(subtermInfo.varName)}`,
            description: `Case split / induction on ${subtermInfo.varName} : ${typeHead}`,
          });
        }
      }
    }
  }

  return suggestions;
}

// ============================================================================
// Binder suggestions (intro)
// ============================================================================

function computeBinderSuggestions(
  selectedIndex: number,
  goal: InteractiveGoal,
): TacticSuggestion[] {
  const { binders } = goal;
  const suggestions: TacticSuggestion[] = [];

  // Collect explicit binders up to and including the selected one
  const upToSelected = collectExplicitBinders(binders, 0, selectedIndex);

  if (upToSelected.length > 0) {
    const names = upToSelected.map(proposeName);
    const introLabel = upToSelected.length === 1 ? 'Intro' : 'Intro up to here';
    suggestions.push({
      id: 'intro-up-to',
      label: introLabel,
      labelLatex: `\\text{${introLabel}}`,
      description: `Introduce: ${names.join(', ')}`,
      proposedNames: names,
    });
  }

  // "Intro all" — all explicit binders
  const allExplicit = collectExplicitBinders(binders, 0, binders.length - 1);
  if (allExplicit.length > upToSelected.length) {
    const allNames = allExplicit.map(proposeName);
    suggestions.push({
      id: 'intro-all',
      label: 'Intro all',
      labelLatex: '\\text{Intro all}',
      description: `Introduce: ${allNames.join(', ')}`,
      proposedNames: allNames,
    });
  }

  return suggestions;
}

/** Collect explicit (non-implicit) binders from index `from` to `to` (inclusive). */
function collectExplicitBinders(
  binders: readonly GoalBinderInfo[],
  from: number,
  to: number,
): GoalBinderInfo[] {
  const result: GoalBinderInfo[] = [];
  for (let i = from; i <= to && i < binders.length; i++) {
    if (!binders[i].isImplicit) {
      result.push(binders[i]);
    }
  }
  return result;
}

/** Propose a name for a binder. Uses the binder name if meaningful, else 'x'. */
function proposeName(binder: GoalBinderInfo): string {
  if (binder.name && binder.name !== '_') return binder.name;
  return 'x';
}

// ============================================================================
// Rewrite suggestions (async — scans hypotheses and tries rewrites)
// ============================================================================

export interface RewriteSuggestion extends TacticSuggestion {
  readonly rewriteName: string;
  readonly reverse: boolean;
  readonly occurrences: readonly number[];
}

/** Kernel-level goal info needed for rewrite suggestions. */
export interface KernelGoalInfo {
  readonly engine: TacticEngine;
  readonly goal: MetaVar;
  readonly definitions: DefinitionsMap;
}

/**
 * Extract type param, LHS and RHS from an equality type (kernel-level).
 * Recognizes both bare `Equal A lhs rhs` and Pi-typed equalities like
 * `(x : Nat) -> Equal (f x) (g x)` (peels all leading Pi binders).
 */
function extractEqualityArgs(type: TTKTerm): { typeA: TTKTerm; lhs: TTKTerm; rhs: TTKTerm } | null {
  // Peel leading Pi binders to reach the equality body
  let body = type;
  while (body.tag === 'Binder' && body.binderKind.tag === 'BPi') {
    body = body.body;
  }
  if (body.tag !== 'App') return null;
  const args: TTKTerm[] = [];
  let current: TTKTerm = body;
  while (current.tag === 'App') {
    args.unshift(current.arg);
    current = current.fn;
  }
  if (current.tag !== 'Const' || current.name !== 'Equal') return null;
  if (args.length < 2) return null;
  const rhs = args[args.length - 1];
  const lhs = args[args.length - 2];
  const typeA = args.length >= 3
    ? args[args.length - 3]
    : { tag: 'Hole' as const, id: '_rw_type' };
  return { typeA, lhs, rhs };
}

/** Get the head constant name, peeling through Apps AND Vars (ignore var-headed apps). */
function getKernelHeadNameDeep(term: TTKTerm): string | null {
  let current = term;
  while (current.tag === 'App') current = current.fn;
  return current.tag === 'Const' ? current.name : null;
}

/** Get the head constant name of a kernel term's App chain. */
function getKernelHeadName(term: TTKTerm): string | null {
  let current = term;
  while (current.tag === 'App') current = current.fn;
  return current.tag === 'Const' ? current.name : null;
}

/**
 * Try a single rewrite attempt. Returns a RewriteSuggestion if successful, null otherwise.
 */
function tryRewrite(
  engine: TacticEngine,
  goal: MetaVar,
  goalId: string,
  proofTerm: TTKTerm,
  hypName: string,
  reverse: boolean,
  occurrences: number[],
): RewriteSuggestion | null {
  try {
    const opts = occurrences.length > 0 ? { reverse, occurrences } : { reverse };
    const tactic = new RewriteTactic(proofTerm, opts);
    const result = tactic.apply(engine, goal, goalId);
    if (!result.success) return null;
    const arrow = reverse ? '\\leftarrow' : '';
    const occDesc = occurrences.length > 0 ? ` at occurrence ${occurrences.join(', ')}` : '';
    return {
      id: `rewrite-${reverse ? 'rev-' : ''}${hypName}-occ${occurrences.join(',')}`,
      label: `rw${reverse ? '\u2190' : ''} ${hypName}`,
      labelLatex: `\\text{rw}${arrow}\\; \\textbf{${texEscape(hypName)}}`,
      description: `Rewrite${reverse ? ' (reverse)' : ''} using ${hypName}${occDesc}`,
      rewriteName: hypName,
      reverse,
      occurrences,
    };
  } catch {
    return null;
  }
}

/** Progress report for incremental rewrite suggestion computation. */
export interface RewriteProgress {
  readonly checked: number;
  readonly total: number;
  readonly suggestions: readonly RewriteSuggestion[];
  readonly done: boolean;
}


/**
 * Collect candidate equalities from hypotheses and definitions.
 * Each candidate is a { proofTerm, name, reverse } triple ready to try.
 *
 * When `selectedHead` is provided, filters by equality head constant (fast path).
 * When `broadSearch` is true, collects ALL equalities (for Var selections where
 * head-based filtering isn't possible).
 */
function collectRewriteCandidates(
  metaGoal: MetaVar,
  definitions: DefinitionsMap,
  filter: { selectedHead: string } | { broadSearch: true },
): Array<{ proofTerm: TTKTerm; name: string; reverse: boolean }> {
  const candidates: Array<{ proofTerm: TTKTerm; name: string; reverse: boolean }> = [];
  const headFilter = 'selectedHead' in filter ? filter.selectedHead : null;

  // Scan hypotheses (goal context) for equality types
  const ctx = metaGoal.ctx;
  for (let i = 0; i < ctx.length; i++) {
    const entry = ctx[i];
    const eqArgs = extractEqualityArgs(entry.type);
    if (!eqArgs) continue;

    const debruijnIdx = ctx.length - 1 - i;
    const proofTerm: TTKTerm = { tag: 'Var', index: debruijnIdx };

    if (headFilter) {
      const lhsHead = getKernelHeadName(eqArgs.lhs);
      if (lhsHead === headFilter) candidates.push({ proofTerm, name: entry.name, reverse: false });
      const rhsHead = getKernelHeadName(eqArgs.rhs);
      if (rhsHead === headFilter) candidates.push({ proofTerm, name: entry.name, reverse: true });
    } else {
      // Broad search: try both directions
      candidates.push({ proofTerm, name: entry.name, reverse: false });
      candidates.push({ proofTerm, name: entry.name, reverse: true });
    }
  }

  // Scan named term definitions for equalities
  for (const [name, termDef] of definitions.terms) {
    if (!termDef.type) continue;
    const eqArgs = extractEqualityArgs(termDef.type);
    if (!eqArgs) continue;

    const proofTerm: TTKTerm = { tag: 'Const', name };

    if (headFilter) {
      const lhsHead = getKernelHeadName(eqArgs.lhs);
      if (lhsHead === headFilter) candidates.push({ proofTerm, name, reverse: false });
      const rhsHead = getKernelHeadName(eqArgs.rhs);
      if (rhsHead === headFilter) candidates.push({ proofTerm, name, reverse: true });
    } else {
      candidates.push({ proofTerm, name, reverse: false });
      candidates.push({ proofTerm, name, reverse: true });
    }
  }

  return candidates;
}

/**
 * Compute rewrite suggestions incrementally.
 *
 * Calls `onProgress` after each candidate is checked, reporting how many
 * have been checked, the total, and any suggestions found so far.
 * Returns a cancel function.
 *
 * Uses setTimeout(0) batching so the UI can re-render between checks.
 */
export function computeRewriteSuggestionsIncremental(
  selectedPath: GoalPath | null,
  goal: InteractiveGoal,
  kernelGoal: KernelGoalInfo,
  onProgress: (progress: RewriteProgress) => void,
): () => void {
  let cancelled = false;
  const cancel = () => { cancelled = true; };

  if (!selectedPath) {
    onProgress({ checked: 0, total: 0, suggestions: [], done: true });
    return cancel;
  }

  const subtermInfo = goal.subtermMap.get(selectedPath);
  if (!subtermInfo) {
    onProgress({ checked: 0, total: 0, suggestions: [], done: true });
    return cancel;
  }

  // Need either a head constant name or a variable name to search for rewrites
  const hasHead = subtermInfo.headName && subtermInfo.occurrenceIndex;
  const hasVar = subtermInfo.varName;
  if (!hasHead && !hasVar) {
    onProgress({ checked: 0, total: 0, suggestions: [], done: true });
    return cancel;
  }

  const { engine, goal: metaGoal } = kernelGoal;
  const maybeGoalId = engine.getFocusedGoalId();
  if (!maybeGoalId) {
    onProgress({ checked: 0, total: 0, suggestions: [], done: true });
    return cancel;
  }
  const goalId = maybeGoalId;

  // For Const-headed subterms: filter by head name, use targeted occurrence
  // For Vars: broad search (try all equalities), no occurrence targeting
  const selectedOcc = hasHead ? subtermInfo.occurrenceIndex! : undefined;
  const filter = hasHead
    ? { selectedHead: subtermInfo.headName! } as const
    : { broadSearch: true } as const;
  const candidates = collectRewriteCandidates(metaGoal, kernelGoal.definitions, filter);
  const total = candidates.length;

  if (total === 0) {
    onProgress({ checked: 0, total: 0, suggestions: [], done: true });
    return cancel;
  }

  const suggestions: RewriteSuggestion[] = [];
  let checked = 0;

  // Report initial state
  onProgress({ checked: 0, total, suggestions: [], done: false });

  // Process candidates in batches via setTimeout for UI responsiveness
  function processBatch(startIdx: number) {
    if (cancelled) return;

    // Process a batch of candidates (up to BATCH_SIZE per tick)
    const BATCH_SIZE = 3;
    const endIdx = Math.min(startIdx + BATCH_SIZE, total);

    for (let i = startIdx; i < endIdx; i++) {
      if (cancelled) return;
      const c = candidates[i];
      const occs = selectedOcc !== undefined ? [selectedOcc] : [];
      const s = tryRewrite(engine, metaGoal, goalId, c.proofTerm, c.name, c.reverse, occs);
      if (s) suggestions.push(s);
      checked++;
    }

    if (cancelled) return;

    const done = endIdx >= total;
    onProgress({ checked, total, suggestions: [...suggestions], done });

    if (!done) {
      setTimeout(() => processBatch(endIdx), 0);
    }
  }

  // Start processing after a microtask to allow the caller to set up state
  setTimeout(() => processBatch(0), 0);

  return cancel;
}
