/**
 * Tactic Suggestion System
 *
 * Computes suggested tactics based on what the user has selected
 * in the interactive goal view. Pure functions — no React dependency.
 */

import { GoalPath, GoalBinderInfo, InteractiveGoal } from './interactive-goal';

// ============================================================================
// Types
// ============================================================================

export interface TacticSuggestion {
  readonly id: string;
  readonly label: string;
  readonly description: string;
  /** For intro tactics: proposed variable names (editable by user). */
  readonly proposedNames?: readonly string[];
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
): readonly TacticSuggestion[] {
  if (!selectedPath || selectedPath.length === 0) return [];
  if (goal.binders.length === 0) return [];

  // Check if a Pi binder is selected (path = [N] where N is a valid binder index)
  if (selectedPath.length === 1 && selectedPath[0] >= 0 && selectedPath[0] < goal.binders.length) {
    return computeBinderSuggestions(selectedPath[0], goal);
  }

  return [];
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
    suggestions.push({
      id: 'intro-up-to',
      label: upToSelected.length === 1 ? 'Intro' : 'Intro up to here',
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
