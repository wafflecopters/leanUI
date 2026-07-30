import { describe, expect, test } from 'vitest';
import {
  EMPTY_GOAL_INTERACTION_STATE,
  clearGoalInteractionAfterApply,
  clearGoalInteractionForCursorChange,
  selectGoalInteractionBinder,
  selectGoalInteractionPath,
  startGoalInteractionEditing,
  toggleGoalInteractionHypothesis,
  updateGoalInteractionEditingNames,
  type GoalInteractionState,
  type SelectedBinder,
} from './goal-interaction-state';

function mkSelectedBinder(name = 'n'): SelectedBinder {
  return {
    introNodeId: 7,
    token: {
      name,
      nameLatex: name,
      nameIndex: 0,
      typeLatex: '\\mathbb{N}',
    },
  };
}

describe('goal interaction state', () => {
  test('selecting a binder clears goal path, hypothesis selection, and editing state', () => {
    const state: GoalInteractionState = {
      selectedPath: 'goal',
      selectedBinder: null,
      selectedHyp: 2,
      editingNames: ['x'],
      editingSuggestionId: 'intro-x',
    };

    expect(selectGoalInteractionBinder(state, mkSelectedBinder())).toEqual({
      selectedPath: null,
      selectedBinder: mkSelectedBinder(),
      selectedHyp: null,
      editingNames: null,
      editingSuggestionId: null,
    });
  });

  test('selecting a goal path clears binder, hypothesis selection, and editing state', () => {
    const state: GoalInteractionState = {
      selectedPath: null,
      selectedBinder: mkSelectedBinder(),
      selectedHyp: 1,
      editingNames: ['ih'],
      editingSuggestionId: 'induction-n',
    };

    expect(selectGoalInteractionPath(state, 'goal.rhs')).toEqual({
      selectedPath: 'goal.rhs',
      selectedBinder: null,
      selectedHyp: null,
      editingNames: null,
      editingSuggestionId: null,
    });
  });

  test('toggling a hypothesis is mutually exclusive with other selections', () => {
    const state: GoalInteractionState = {
      selectedPath: 'goal',
      selectedBinder: mkSelectedBinder(),
      selectedHyp: null,
      editingNames: ['h'],
      editingSuggestionId: 'exact-h',
    };

    expect(toggleGoalInteractionHypothesis(state, 3)).toEqual({
      selectedPath: null,
      selectedBinder: null,
      selectedHyp: 3,
      editingNames: null,
      editingSuggestionId: null,
    });

    expect(toggleGoalInteractionHypothesis({
      ...EMPTY_GOAL_INTERACTION_STATE,
      selectedHyp: 3,
    }, 3)).toEqual(EMPTY_GOAL_INTERACTION_STATE);
  });

  test('editing helpers track active suggestion names', () => {
    const editingStarted = startGoalInteractionEditing(EMPTY_GOAL_INTERACTION_STATE, {
      id: 'intro-ab',
      label: 'intro',
      description: 'Introduce names',
      proposedNames: ['a', 'b'],
    });
    expect(editingStarted.editingSuggestionId).toBe('intro-ab');
    expect(editingStarted.editingNames).toEqual(['a', 'b']);

    expect(updateGoalInteractionEditingNames(editingStarted, ['x', 'y'])).toEqual({
      ...editingStarted,
      editingNames: ['x', 'y'],
    });
  });

  test('clear helpers fully reset the shared interaction state', () => {
    const state: GoalInteractionState = {
      selectedPath: 'goal',
      selectedBinder: mkSelectedBinder(),
      selectedHyp: 0,
      editingNames: ['z'],
      editingSuggestionId: 'intro-z',
    };

    expect(clearGoalInteractionAfterApply()).toEqual(EMPTY_GOAL_INTERACTION_STATE);
    expect(clearGoalInteractionForCursorChange()).toEqual(EMPTY_GOAL_INTERACTION_STATE);
    expect(selectGoalInteractionPath(state, null).editingNames).toBeNull();
  });

});
