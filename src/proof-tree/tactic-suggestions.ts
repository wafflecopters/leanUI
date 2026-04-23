/**
 * Tactic Suggestion System
 *
 * Computes suggested tactics based on what the user has selected
 * in the interactive goal view. Pure functions — no React dependency.
 */

import { GoalPath, GoalBinderInfo, InteractiveGoal } from './interactive-goal';
import { renderGoalLatex, renderSubtermLatex } from './goal-computation';
import { TTKTerm } from '../compiler/kernel';
import { DefinitionsMap, MetaVar, createDefinitionsMap } from '../compiler/term';
import { fullNormalize, whnf } from '../compiler/whnf';
import { TacticEngine } from '../tactics/tacticsEngine';
import { ExactTactic, ApplyTactic } from '../tactics/tactic';
import { RewriteTactic } from '../tactics/rewrite-tactic';
import { UnfoldTactic } from '../tactics/unfold-tactic';
import { FoldTactic } from '../tactics/fold-tactic';
import { ttkTermsEqual } from '../tactics/fold-tactic';
import { ReverseRegistry } from '../math-editor/tt-to-math';
import { proposeVarName, freshenName } from './propose-var-name';

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
  /** For unfold tactics: which occurrence (1-based) of the head to unfold. */
  readonly unfoldOccurrence?: number;
  /** For fold tactics: which occurrence (1-based) of the definition body to fold. */
  readonly foldOccurrence?: number;
  /** For fold tactics: the definition name to fold. */
  readonly foldName?: string;
  /** LaTeX preview of the goal after this tactic is applied. */
  readonly resultGoalLatex?: string;
  /** For apply tactics: number of subgoals created. */
  readonly numSubgoals?: number;
  /** For construct suggestions: the constructor name to apply. */
  readonly applyCtorName?: string;
}

/** Escape a name for use in LaTeX (wrap multi-char names in \text{}, escape underscores). */
function texEscape(name: string): string {
  if (name.length === 1) return name;
  name = name.replace(/_/g, '\\_');
  return `\\text{${name}}`;
}

/** Render the result goal LaTeX after applying a tactic. Returns undefined if not possible. */
function renderResultGoal(
  newEngine: TacticEngine,
  definitions: DefinitionsMap,
  rev?: ReverseRegistry,
): string | undefined {
  if (!rev) return undefined;
  try {
    const newGoalId = newEngine.getFocusedGoalId();
    if (!newGoalId) return undefined;
    const newGoal = newEngine.metaVars.get(newGoalId);
    if (!newGoal) return undefined;
    return renderGoalLatex(newEngine, newGoal, definitions, rev);
  } catch {
    return undefined;
  }
}

/**
 * Find the first subterm that differs between two terms.
 * Returns the differing subterm from `newTerm`, or the whole `newTerm` if
 * the terms have different structure at the root.
 */
function findChangedSubterm(oldTerm: TTKTerm, newTerm: TTKTerm): TTKTerm {
  if (ttkTermsEqual(oldTerm, newTerm)) return newTerm;
  // If same tag and structure, recurse to find the specific changed subtree
  if (oldTerm.tag === 'App' && newTerm.tag === 'App') {
    if (!ttkTermsEqual(oldTerm.fn, newTerm.fn))
      return findChangedSubterm(oldTerm.fn, newTerm.fn);
    if (!ttkTermsEqual(oldTerm.arg, newTerm.arg))
      return findChangedSubterm(oldTerm.arg, newTerm.arg);
  }
  if (oldTerm.tag === 'Binder' && newTerm.tag === 'Binder'
    && oldTerm.binderKind.tag === newTerm.binderKind.tag) {
    if (!ttkTermsEqual(oldTerm.domain, newTerm.domain))
      return findChangedSubterm(oldTerm.domain, newTerm.domain);
    if (!ttkTermsEqual(oldTerm.body, newTerm.body))
      return findChangedSubterm(oldTerm.body, newTerm.body);
  }
  // Root-level difference — return the new term
  return newTerm;
}

/**
 * Render just the changed subterm after a tactic application.
 * Compares old goal with new goal, finds the divergent subtree, renders it.
 */
function renderChangedSubterm(
  oldGoal: MetaVar,
  newEngine: TacticEngine,
  definitions: DefinitionsMap,
  rev?: ReverseRegistry,
): string | undefined {
  if (!rev) return undefined;
  try {
    const newGoalId = newEngine.getFocusedGoalId();
    if (!newGoalId) return undefined;
    const newGoal = newEngine.metaVars.get(newGoalId);
    if (!newGoal) return undefined;
    // Normalize using actual definitions so constants like `two`
    // get delta-reduced and iota can fire on pattern-match results.
    const defs = newEngine.definitions;
    const oldNorm = fullNormalize(oldGoal.type, defs);
    const newNorm = fullNormalize(newGoal.type, defs);
    const changed = findChangedSubterm(oldNorm, newNorm);
    return renderSubtermLatex(changed, newGoal.ctx, definitions, rev);
  } catch {
    return undefined;
  }
}

/**
 * Check if unfolding produces a Match at the top of the changed subterm.
 * We suppress unfold suggestions for pattern-matching definitions when the
 * scrutinee is a variable (iota can't fire), since the result is an opaque
 * match expression that makes the goal harder to read.
 *
 * Uses the engine's definitions for normalization so that constants like
 * `two` (= Succ(Succ(Zero))) get delta-reduced, exposing constructors
 * for iota. Without this, `unfold mul` on `mul(two, n)` would produce
 * a Match with scrutinee `Const(two)` — iota can't fire because
 * `two` is opaque — and the suggestion would be wrongly suppressed.
 */
function unfoldResultIsMatch(oldGoal: MetaVar, newEngine: TacticEngine): boolean {
  try {
    const newGoalId = newEngine.getFocusedGoalId();
    if (!newGoalId) return false;
    const newGoal = newEngine.metaVars.get(newGoalId);
    if (!newGoal) return false;
    const defs = newEngine.definitions;
    const oldNorm = fullNormalize(oldGoal.type, defs);
    const newNorm = fullNormalize(newGoal.type, defs);
    const changed = findChangedSubterm(oldNorm, newNorm);
    return changed.tag === 'Match';
  } catch {
    return false;
  }
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

  // Constructor suggestions: when the selected subterm's head is an inductive
  // type, offer "Construct CtorName" for each constructor that unifies with
  // the goal. Single-constructor types just show "Construct".
  // This triggers on the goal-root subterm (the outermost expression) or any
  // subterm whose head matches an inductive type definition.
  if (kernelGoal && definitions) {
    const selectedInfo = goal.subtermMap.get(selectedPath);
    const headName = selectedInfo?.headName;
    if (headName && definitions.inductiveTypes.has(headName)) {
      const { engine, goal: metaGoal } = kernelGoal;
      const gId = engine.getFocusedGoalId();
      if (gId) {
        const inductiveDef = definitions.inductiveTypes.get(headName)!;
        const isSingle = inductiveDef.constructors.length === 1;
        for (const ctor of inductiveDef.constructors) {
          try {
            const tactic = new ApplyTactic({ tag: 'Const', name: ctor.name });
            const res = tactic.apply(engine, metaGoal, gId);
            if (res.success) {
              const label = isSingle ? 'Construct' : `Construct ${ctor.name}`;
              const numSubgoals = res.newEngine?.goals.length ?? 1;
              suggestions.push({
                id: `construct-${ctor.name}`,
                label,
                labelLatex: isSingle
                  ? '\\text{Construct}'
                  : `\\text{Construct } \\textbf{${texEscape(ctor.name)}}`,
                description: `Apply constructor ${ctor.name}`,
                applyCtorName: ctor.name,
                numSubgoals,
              });
            }
          } catch { /* constructor doesn't unify */ }
        }
      }
    }
  }

  // Check if a Pi binder is selected (path = "goal-N" where N is a valid binder index)
  const binderMatch = selectedPath.match(/^goal-(\d+)$/);
  if (binderMatch && goal.binders.length > 0) {
    const binderIndex = parseInt(binderMatch[1], 10);
    if (binderIndex >= 0 && binderIndex < goal.binders.length) {
      suggestions.push(...computeBinderSuggestions(binderIndex, goal, kernelGoal?.rev));
    }
  }

  // If a subterm within a binder's domain is clicked, also offer intro suggestions
  const subtermInfo = goal.subtermMap.get(selectedPath);
  if (subtermInfo?.binderIndex !== undefined && !binderMatch) {
    suggestions.push(...computeBinderSuggestions(subtermInfo.binderIndex, goal, kernelGoal?.rev));
  }

  // Check subterm-level suggestions
  if (definitions) {
    if (subtermInfo) {
      // Unfold: selected subterm is an App of a term definition (not inductive type or constructor)
      if (subtermInfo.isAppOfConst && subtermInfo.headName) {
        const name = subtermInfo.headName;
        if (definitions.terms.has(name)
          && !definitions.inductiveTypes.has(name)
          && !definitions.inductiveNameOfConstructor.has(name)
          && name !== kernelGoal?.currentDeclName) {
          let resultGoalLatex: string | undefined;
          let unfoldProducesMatch = false;
          if (kernelGoal) {
            try {
              const { engine, goal: metaGoal } = kernelGoal;
              const gId = engine.getFocusedGoalId();
              if (gId) {
                const tactic = new UnfoldTactic([name], subtermInfo.occurrenceIndex);
                const res = tactic.apply(engine, metaGoal, gId);
                if (res.success) {
                  unfoldProducesMatch = unfoldResultIsMatch(metaGoal, res.newEngine!);
                  if (!unfoldProducesMatch) {
                    resultGoalLatex = renderChangedSubterm(metaGoal, res.newEngine, definitions, kernelGoal.rev);
                  }
                }
              }
            } catch { /* ignore */ }
          }
          if (!unfoldProducesMatch) {
            suggestions.push({
              id: `unfold-${name}`,
              label: `Unfold ${name}`,
              labelLatex: `\\text{Unfold } \\textbf{${texEscape(name)}}`,
              description: `Unfold the definition of ${name}`,
              unfoldOccurrence: subtermInfo.occurrenceIndex,
              resultGoalLatex,
            });
          }
        }
      }

      // Fold: check if any term definition's normalized body matches the selected subterm
      // Only try for constructor-headed subterms (e.g., Succ(Succ(Zero)))
      if (kernelGoal && subtermInfo.headName) {
        const selectedHead = subtermInfo.headName;
        // Only suggest fold for constructor applications (not function definitions)
        if (definitions.inductiveNameOfConstructor.has(selectedHead) || selectedHead === 'Zero') {
          const emptyDefs = createDefinitionsMap();
          for (const [defName, termDef] of definitions.terms) {
            if (!termDef.value) continue;
            // Skip self-references (folding yourself is circular)
            if (defName === kernelGoal.currentDeclName) continue;
            // Skip function definitions (lambdas) — only fold closed terms
            if (termDef.value.tag === 'Binder' && termDef.value.binderKind.tag === 'BLam') continue;
            // Normalize the definition body
            const normalizedBody = fullNormalize(termDef.value, emptyDefs);
            // Check if the head matches (fast filter)
            const bodyHead = getKernelHeadName(normalizedBody);
            if (bodyHead !== selectedHead) continue;
            // TODO: could check structural equality against the kernel subterm here
            // For now, suggest fold and let the tactic validate
            let foldResultLatex: string | undefined;
            if (kernelGoal) {
              try {
                const { engine, goal: metaGoal } = kernelGoal;
                const gId = engine.getFocusedGoalId();
                if (gId) {
                  const tactic = new FoldTactic([defName], subtermInfo.occurrenceIndex);
                  const res = tactic.apply(engine, metaGoal, gId);
                  if (res.success) {
                    foldResultLatex = renderChangedSubterm(metaGoal, res.newEngine, definitions, kernelGoal.rev);
                  }
                }
              } catch { /* ignore */ }
            }
            suggestions.push({
              id: `fold-${defName}`,
              label: `Fold ${defName}`,
              labelLatex: `\\text{Fold } \\textbf{${texEscape(defName)}}`,
              description: `Replace with ${defName}`,
              foldName: defName,
              foldOccurrence: subtermInfo.occurrenceIndex,
              resultGoalLatex: foldResultLatex,
            });
          }
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

  // Try exact/apply on each hypothesis — for any non-binder selection
  if (!binderMatch && kernelGoal) {
    suggestions.push(...computeHypothesisSuggestions(kernelGoal));
  }

  return suggestions;
}

// ============================================================================
// Binder suggestions (intro)
// ============================================================================

function computeBinderSuggestions(
  selectedIndex: number,
  goal: InteractiveGoal,
  rev?: ReverseRegistry,
): TacticSuggestion[] {
  const { binders } = goal;
  const suggestions: TacticSuggestion[] = [];

  // Collect explicit binders up to and including the selected one
  const upToSelected = collectExplicitBinders(binders, 0, selectedIndex);

  if (upToSelected.length > 0) {
    const names = proposeBinderNames(upToSelected, rev);
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
    const allNames = proposeBinderNames(allExplicit, rev);
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

/** Propose names for a list of binders, using smart naming and freshening. */
function proposeBinderNames(binders: GoalBinderInfo[], rev?: ReverseRegistry): string[] {
  const usedNames = new Set<string>();
  return binders.map(b => {
    let name: string;
    if (b.name && b.name !== '_') {
      name = freshenName(b.name, usedNames);
    } else {
      name = proposeVarName(b.domain, usedNames, rev);
    }
    usedNames.add(name);
    return name;
  });
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

// ============================================================================
// Hypothesis suggestions (exact / apply on context entries)
// ============================================================================

/**
 * When the whole goal body is selected, try `exact` and `apply` on each
 * hypothesis in the context. Returns suggestions for any that succeed.
 */
function computeHypothesisSuggestions(kernelGoal: KernelGoalInfo): TacticSuggestion[] {
  const suggestions: TacticSuggestion[] = [];
  const { engine, goal: metaGoal } = kernelGoal;
  const goalId = engine.getFocusedGoalId();
  if (!goalId) return suggestions;

  const ctx = metaGoal.ctx;

  for (let i = 0; i < ctx.length; i++) {
    const entry = ctx[i];
    const name = entry.name;
    // Skip unnamed/wildcard entries
    if (!name || name === '_' || name.startsWith('?')) continue;

    const debruijnIdx = ctx.length - 1 - i;
    const varTerm: TTKTerm = { tag: 'Var', index: debruijnIdx };

    // Try exact
    try {
      const exactTactic = new ExactTactic(varTerm);
      const result = exactTactic.apply(engine, metaGoal, goalId);
      if (result.success) {
        suggestions.push({
          id: `exact-hyp-${name}`,
          label: `exact ${name}`,
          labelLatex: `\\text{exact}\\; \\textbf{${texEscape(name)}}`,
          description: `Close goal with hypothesis ${name}`,
        });
        continue; // If exact works, no need to try apply
      }
    } catch { /* doesn't apply */ }

    // Try apply
    try {
      const applyTactic = new ApplyTactic(varTerm);
      const result = applyTactic.apply(engine, metaGoal, goalId);
      if (result.success) {
        // Count the new subgoals (unsolved explicit args)
        const numSubgoals = result.newEngine
          ? result.newEngine.goals.length - engine.goals.length + 1
          : 1;
        suggestions.push({
          id: `apply-hyp-${name}`,
          label: `apply ${name}`,
          labelLatex: `\\text{apply}\\; \\textbf{${texEscape(name)}}`,
          description: numSubgoals > 0
            ? `Apply ${name}, creating ${numSubgoals} subgoal${numSubgoals > 1 ? 's' : ''}`
            : `Apply ${name}`,
          numSubgoals,
        });
      }
    } catch { /* doesn't apply */ }
  }

  return suggestions;
}

// ============================================================================
// Binder suggestions (clickable token → tactic suggestions in goal area)
// ============================================================================

/**
 * Compute tactic suggestions for a clicked binder in the proof prose view.
 * Returns standard TacticSuggestion[] so they render in GoalInteraction
 * and dispatch through the existing handleApplySuggestion.
 *
 * Checks:
 * - 'exact' if the hypothesis exactly solves the current goal
 * - 'apply' if the hypothesis's return type matches the goal
 * - 'induction' if the hypothesis type is inductive
 */
export function computeSelectedBinderSuggestions(
  name: string,
  kernelGoal: KernelGoalInfo | undefined,
  isInductive: boolean,
): TacticSuggestion[] {
  const suggestions: TacticSuggestion[] = [];

  // Check exact/apply if we have a kernel goal
  if (kernelGoal) {
    const { engine, goal: metaGoal } = kernelGoal;
    const goalId = engine.getFocusedGoalId();
    if (goalId) {
      const ctx = metaGoal.ctx;
      // Find this hypothesis by name in the context
      for (let i = 0; i < ctx.length; i++) {
        if (ctx[i].name === name) {
          const debruijnIdx = ctx.length - 1 - i;
          const varTerm: TTKTerm = { tag: 'Var', index: debruijnIdx };

          // Try exact
          try {
            const exactTactic = new ExactTactic(varTerm);
            const result = exactTactic.apply(engine, metaGoal, goalId);
            if (result.success) {
              suggestions.push({
                id: `exact-hyp-${name}`,
                label: `exact ${name}`,
                labelLatex: `\\text{exact}\\; \\textbf{${texEscape(name)}}`,
                description: `Close goal with hypothesis ${name}`,
              });
              break; // exact subsumes apply
            }
          } catch { /* doesn't apply */ }

          // Try apply
          try {
            const applyTactic = new ApplyTactic(varTerm);
            const result = applyTactic.apply(engine, metaGoal, goalId);
            if (result.success) {
              const numSubgoals = result.newEngine
                ? result.newEngine.goals.length - engine.goals.length + 1
                : 1;
              suggestions.push({
                id: `apply-hyp-${name}`,
                label: `apply ${name}`,
                labelLatex: `\\text{apply}\\; \\textbf{${texEscape(name)}}`,
                description: numSubgoals > 0
                  ? `Apply ${name}, creating ${numSubgoals} subgoal${numSubgoals > 1 ? 's' : ''}`
                  : `Apply ${name}`,
                numSubgoals,
              });
            }
          } catch { /* doesn't apply */ }

          break; // found the hypothesis
        }
      }
    }
  }

  // Induction — available if the type is inductive
  if (isInductive) {
    suggestions.push({
      id: `induction-${name}`,
      label: `Induction on ${name}`,
      description: `Proceed by induction on ${name}`,
    });
  }

  return suggestions;
}

// ============================================================================
// Rewrite suggestions (async — scans hypotheses and tries rewrites)
// ============================================================================

export interface RewriteSuggestion extends TacticSuggestion {
  readonly rewriteName: string;
  readonly reverse: boolean;
  readonly occurrences: readonly number[];
  /** Head constant name of the clicked subterm (for occurrence-targeted rewrites). */
  readonly targetHead?: string;
}

/** Kernel-level goal info needed for rewrite suggestions. */
export interface KernelGoalInfo {
  readonly engine: TacticEngine;
  readonly goal: MetaVar;
  readonly definitions: DefinitionsMap;
  readonly rev?: ReverseRegistry;
  /** Name of the declaration currently being proved (to filter self-references). */
  readonly currentDeclName?: string;
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
  targetHead?: string,
  definitions?: DefinitionsMap,
  rev?: ReverseRegistry,
): RewriteSuggestion | null {
  try {
    const opts: any = occurrences.length > 0 ? { reverse, occurrences } : { reverse };
    if (targetHead) opts.targetHead = targetHead;
    const tactic = new RewriteTactic(proofTerm, opts);
    const result = tactic.apply(engine, goal, goalId);
    if (!result.success) return null;
    const arrow = reverse ? '\\leftarrow' : '';
    // Normalize: empty occurrences means "all" — store as empty array (same as no restriction)
    const effectiveOcc = occurrences.length > 0 ? occurrences : [];
    const occDesc = effectiveOcc.length > 0 ? ` at occurrence ${effectiveOcc.join(', ')}` : '';
    // Render just the replacement subterm (what the selected subterm becomes),
    // not the full goal after rewrite. The unifiedEquation.rhs IS the replacement.
    let resultGoalLatex: string | undefined;
    if (definitions && rev && result.unifiedEquation) {
      try {
        resultGoalLatex = renderSubtermLatex(
          result.unifiedEquation.rhs, goal.ctx, definitions, rev
        );
      } catch { /* ignore */ }
    }
    return {
      id: `rewrite-${reverse ? 'rev-' : ''}${hypName}-occ${effectiveOcc.join(',')}`,
      label: `rw${reverse ? '\u2190' : ''} ${hypName}`,
      labelLatex: `\\text{rw}${arrow}\\; \\textbf{${texEscape(hypName)}}`,
      description: `Rewrite${reverse ? ' (reverse)' : ''} using ${hypName}${occDesc}`,
      rewriteName: hypName,
      reverse,
      occurrences: effectiveOcc,
      targetHead,
      resultGoalLatex,
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
export function collectRewriteCandidates(
  metaGoal: MetaVar,
  definitions: DefinitionsMap,
  filter: { selectedHead: string } | { broadSearch: true },
  currentDeclName?: string,
): Array<{ proofTerm: TTKTerm; name: string; reverse: boolean; isSelfReference?: boolean }> {
  const candidates: Array<{ proofTerm: TTKTerm; name: string; reverse: boolean; isSelfReference?: boolean }> = [];
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

    // Self-referential candidates: skip outside induction, tag inside induction
    if (name === currentDeclName) {
      if (!metaGoal.caseTag) continue; // Outside induction case — circular, skip
      // Inside induction case — include but tag for structural check
      const proofTerm: TTKTerm = { tag: 'Const', name };
      if (headFilter) {
        const lhsHead = getKernelHeadName(eqArgs.lhs);
        if (lhsHead === headFilter) candidates.push({ proofTerm, name, reverse: false, isSelfReference: true });
        const rhsHead = getKernelHeadName(eqArgs.rhs);
        if (rhsHead === headFilter) candidates.push({ proofTerm, name, reverse: true, isSelfReference: true });
      } else {
        candidates.push({ proofTerm, name, reverse: false, isSelfReference: true });
        candidates.push({ proofTerm, name, reverse: true, isSelfReference: true });
      }
      continue;
    }

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
  const hasHead = subtermInfo.headName && subtermInfo.occurrenceIndex !== undefined;
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
  const candidates = collectRewriteCandidates(metaGoal, kernelGoal.definitions, filter, kernelGoal.currentDeclName);
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
      if (selectedOcc !== undefined) {
        // Only try targeted rewrite at the clicked occurrence — don't fall back
        // to untargeted, which would rewrite a DIFFERENT subterm than selected
        const targeted = tryRewrite(engine, metaGoal, goalId, c.proofTerm, c.name, c.reverse, [selectedOcc], subtermInfo?.headName, kernelGoal.definitions, kernelGoal.rev);
        if (targeted) {
          suggestions.push(targeted);
        }
      } else {
        const s = tryRewrite(engine, metaGoal, goalId, c.proofTerm, c.name, c.reverse, [], undefined, kernelGoal.definitions, kernelGoal.rev);
        if (s) suggestions.push(s);
      }
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

// ============================================================================
// Hypothesis-level suggestions
// ============================================================================

/**
 * Compute tactic suggestions for a selected hypothesis.
 *
 * When the user clicks a hypothesis `h : T` in the context panel, this
 * returns actions like [Exact h], [Apply h], [Destructure h], and
 * [Use Projection] for each accessible projection of T's type.
 */
export function computeSelectedHypSuggestions(
  hypName: string,
  hypIndex: number,
  kernelGoal: KernelGoalInfo,
  definitions: DefinitionsMap,
): readonly TacticSuggestion[] {
  const { engine, goal, rev } = kernelGoal;
  const goalId = engine.getFocusedGoalId();
  if (!goalId) return [];

  const suggestions: TacticSuggestion[] = [];
  const hypVar: TTKTerm = { tag: 'Var', index: goal.ctx.length - 1 - hypIndex };

  // 1. Exact h — does the hypothesis directly solve the goal?
  try {
    const exactTactic = new ExactTactic(hypVar);
    const res = exactTactic.apply(engine, goal, goalId);
    if (res.success) {
      suggestions.push({
        id: `hyp-exact-${hypName}`,
        label: `Exact ${hypName}`,
        labelLatex: `\\text{exact } \\textbf{${texEscape(hypName)}}`,
        description: `Use ${hypName} to close the goal`,
      });
    }
  } catch { /* doesn't apply */ }

  // 2. Apply h — does the hypothesis produce the goal type when applied?
  try {
    const applyTactic = new ApplyTactic(hypVar);
    const res = applyTactic.apply(engine, goal, goalId);
    if (res.success) {
      const numSubgoals = res.newEngine?.goals.length ?? 1;
      suggestions.push({
        id: `hyp-apply-${hypName}`,
        label: `Apply ${hypName}`,
        labelLatex: `\\text{apply } \\textbf{${texEscape(hypName)}}`,
        description: `Apply ${hypName} to the goal`,
        numSubgoals,
      });
    }
  } catch { /* doesn't apply */ }

  // 3. Destructure h — if hypothesis type is an inductive type
  // 4. Use projection — if hypothesis type is a record with projections
  const hypEntry = goal.ctx[hypIndex];
  if (hypEntry) {
    try {
      const hypTypeWhnf = whnf(engine.zonkTerm(hypEntry.type, goal.ctx.length), {
        definitions, typingContext: goal.ctx,
      });
      let head = hypTypeWhnf;
      while (head.tag === 'App') head = head.fn;
      if (head.tag === 'Const' && definitions.inductiveTypes.has(head.name)) {
        const typeName = head.name;
        const inductiveDef = definitions.inductiveTypes.get(typeName)!;

        // Check if the type has constructors with explicit fields
        const hasFields = inductiveDef.constructors.some(c => {
          let t = c.type;
          const numImplicit = c.namedArgMap?.size ?? 0;
          let total = 0;
          while (t.tag === 'Binder' && t.binderKind.tag === 'BPi') { total++; t = t.body; }
          return total > numImplicit;
        });
        if (hasFields) {
          suggestions.push({
            id: `hyp-destruct-${hypName}`,
            label: `Destructure ${hypName}`,
            labelLatex: `\\text{cases } \\textbf{${texEscape(hypName)}}`,
            description: `Pattern-match on ${hypName}`,
          });
        }

        // Offer "Use <projection>" for each projection of this type.
        // Projections are terms named "TypeName.fieldName" in the definitions.
        for (const [projName] of definitions.terms) {
          if (projName.startsWith(typeName + '.')) {
            const fieldName = projName.slice(typeName.length + 1);
            suggestions.push({
              id: `hyp-proj-${hypName}-${fieldName}`,
              label: `Use ${fieldName}`,
              labelLatex: `\\text{Use } \\textbf{${texEscape(fieldName)}}`,
              description: `have h := ${projName} ${hypName} ...`,
              // Store the projection info for the click handler
              applyCtorName: projName,
            });
          }
        }
      }
    } catch { /* ignore */ }
  }

  return suggestions;
}
