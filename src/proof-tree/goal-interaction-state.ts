import type { GoalPath } from './interactive-goal-types';
import type { IntroToken } from './proof-prose';
import type { ProofNodeId } from './proof-tree';
import type { TacticSuggestion } from './suggestion-types';

/** A binder selected by clicking a variable name in the proof prose view. */
export interface SelectedBinder {
  readonly token: IntroToken;
  readonly introNodeId: ProofNodeId;
}

export interface GoalInteractionState {
  readonly selectedPath: GoalPath | null;
  readonly selectedBinder: SelectedBinder | null;
  readonly selectedHyp: number | null;
  readonly editingNames: string[] | null;
  readonly editingSuggestionId: string | null;
}

export const EMPTY_GOAL_INTERACTION_STATE: GoalInteractionState = {
  selectedPath: null,
  selectedBinder: null,
  selectedHyp: null,
  editingNames: null,
  editingSuggestionId: null,
};

function clearEditing(state: GoalInteractionState): GoalInteractionState {
  return {
    ...state,
    editingNames: null,
    editingSuggestionId: null,
  };
}

export function selectGoalInteractionPath(
  state: GoalInteractionState,
  path: GoalPath | null,
): GoalInteractionState {
  return clearEditing({
    ...state,
    selectedPath: path,
    selectedBinder: path ? null : state.selectedBinder,
    selectedHyp: path ? null : state.selectedHyp,
  });
}

export function selectGoalInteractionBinder(
  state: GoalInteractionState,
  binder: SelectedBinder | null,
): GoalInteractionState {
  return clearEditing({
    ...state,
    selectedBinder: binder,
    selectedPath: binder ? null : state.selectedPath,
    selectedHyp: binder ? null : state.selectedHyp,
  });
}

export function toggleGoalInteractionHypothesis(
  state: GoalInteractionState,
  hypIndex: number,
): GoalInteractionState {
  const nextHyp = state.selectedHyp === hypIndex ? null : hypIndex;
  return clearEditing({
    ...state,
    selectedHyp: nextHyp,
    selectedPath: nextHyp !== null ? null : state.selectedPath,
    selectedBinder: nextHyp !== null ? null : state.selectedBinder,
  });
}

export function clearGoalInteractionForCursorChange(): GoalInteractionState {
  return EMPTY_GOAL_INTERACTION_STATE;
}

export function clearGoalInteractionAfterApply(): GoalInteractionState {
  return EMPTY_GOAL_INTERACTION_STATE;
}

export function startGoalInteractionEditing(
  state: GoalInteractionState,
  suggestion: TacticSuggestion,
): GoalInteractionState {
  if (state.editingSuggestionId === suggestion.id) {
    return {
      ...state,
      editingSuggestionId: null,
      editingNames: null,
    };
  }
  return {
    ...state,
    editingSuggestionId: suggestion.id,
    editingNames: [...(suggestion.proposedNames ?? [])],
  };
}

export function updateGoalInteractionEditingNames(
  state: GoalInteractionState,
  names: string[] | null,
  suggestionId?: string,
): GoalInteractionState {
  return {
    ...state,
    editingNames: names,
    editingSuggestionId: suggestionId ?? state.editingSuggestionId,
  };
}

/**
 * Suggestions at the selected subterm / hypothesis used to be computed HERE, by
 * ranking and trialling candidates against the in-process TT kernel. The Lean
 * backend does it properly instead — `src/controller/candidates.ts` proposes and
 * `validate.ts` trials each one at the real cursor, so only tactics Lean
 * actually accepts are offered — and hands the results to the view. This module
 * is now purely the SELECTION state: what the user clicked, and what they are
 * editing.
 */
