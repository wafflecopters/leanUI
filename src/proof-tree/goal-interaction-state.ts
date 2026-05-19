import type { DefinitionsMap } from '../compiler/term';
import type { GoalPath, InteractiveGoal } from './interactive-goal';
import type { TypedProofContext, InductiveMap } from './goal-computation';
import type { IntroToken } from './proof-prose';
import type { ProofNodeId } from './proof-tree';
import {
  computeSelectedBinderSuggestionsForToken,
  computeSelectedHypSuggestions,
  computeTacticSuggestions,
  mergeGoalSuggestions,
  type KernelGoalInfo,
  type RewriteProgress,
  type TacticSuggestion,
} from './tactic-suggestions';

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

export function computeGoalInteractionSuggestions(
  state: GoalInteractionState,
  interactiveGoal: InteractiveGoal | null,
  definitions: DefinitionsMap | undefined,
  kernelGoal: KernelGoalInfo | undefined,
  inductiveMap?: InductiveMap,
  rewriteProgress?: RewriteProgress | null,
): readonly TacticSuggestion[] {
  if (state.selectedBinder) {
    return computeSelectedBinderSuggestionsForToken(
      state.selectedBinder.token.name,
      state.selectedBinder.token.rawType,
      kernelGoal,
      inductiveMap,
    );
  }

  if (!state.selectedPath || !interactiveGoal) return [];
  const syncSuggestions = computeTacticSuggestions(
    state.selectedPath,
    interactiveGoal,
    definitions,
    kernelGoal,
  );
  return mergeGoalSuggestions([], syncSuggestions, rewriteProgress?.suggestions ?? []);
}

export function computeGoalInteractionHypothesisSuggestions(
  state: GoalInteractionState,
  context: TypedProofContext | null,
  definitions: DefinitionsMap | undefined,
): readonly TacticSuggestion[] {
  if (state.selectedHyp === null || !context?.kernelGoal || !definitions) return [];
  const hyp = context.hypotheses[state.selectedHyp];
  if (!hyp) return [];
  return computeSelectedHypSuggestions(
    hyp.name,
    state.selectedHyp,
    context.kernelGoal,
    definitions,
  );
}
