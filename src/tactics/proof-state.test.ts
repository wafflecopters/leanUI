/**
 * Tests for ProofState type and operations (Phase 2)
 */

import { describe, test, expect, beforeEach } from 'vitest';
import {
  ProofState,
  createProofState,
  getFocusedGoal,
  getFocusedGoalId,
  getUnsolvedGoals,
  isProofComplete,
  extractGoalStates,
  updateProofState,
  engineToProofState,
  proofStateToEngine
} from './proof-state';
import { createInitialEngine } from './tacticsEngine';
import { applyTacticToState, applyTacticsToState, extractProofTermFromState } from './apply-tactic';
import { resetMetaCounter } from './tactic';
import { TTKTerm } from '../compiler/kernel';
import { DefinitionsMap } from '../compiler/term';

// Test helper: Create Nat definitions
function createNatDefinitions(): DefinitionsMap {
  const terms = new Map();
  const inductiveTypes = new Map();
  const inductiveNameOfConstructor = new Map();

  inductiveTypes.set('Nat', {
    parameters: [],
    type: { tag: 'Type', level: { tag: 'LevelConst', value: 0 } },
    constructors: [
      {
        name: 'Zero',
        type: { tag: 'Const', name: 'Nat' }
      },
      {
        name: 'Succ',
        type: {
          tag: 'Binder',
          name: '_',
          binderKind: { tag: 'BPi' },
          domain: { tag: 'Const', name: 'Nat' },
          body: { tag: 'Const', name: 'Nat' }
        }
      }
    ]
  });

  terms.set('Zero', {
    name: 'Zero',
    type: { tag: 'Const', name: 'Nat' },
    value: { tag: 'Const', name: 'Zero' }
  });
  inductiveNameOfConstructor.set('Zero', 'Nat');

  terms.set('Succ', {
    name: 'Succ',
    type: {
      tag: 'Binder',
      name: '_',
      binderKind: { tag: 'BPi' },
      domain: { tag: 'Const', name: 'Nat' },
      body: { tag: 'Const', name: 'Nat' }
    },
    value: { tag: 'Const', name: 'Succ' }
  });
  inductiveNameOfConstructor.set('Succ', 'Nat');

  return { terms, inductiveTypes, inductiveNameOfConstructor };
}

describe('ProofState creation and queries', () => {
  beforeEach(() => {
    resetMetaCounter();
  });

  test('createProofState creates initial state', () => {
    const definitions = createNatDefinitions();
    const goalType: TTKTerm = { tag: 'Const', name: 'Nat' };

    const state = createProofState(goalType, [], definitions);

    expect(state.goals.length).toBe(1);
    expect(state.focusIndex).toBe(0);
    expect(state.term.tag).toBe('Meta');
    expect(state.metaVars.size).toBe(1);
  });

  test('getFocusedGoal returns current goal', () => {
    const definitions = createNatDefinitions();
    const goalType: TTKTerm = { tag: 'Const', name: 'Nat' };

    const state = createProofState(goalType, [], definitions);
    const goal = getFocusedGoal(state);

    expect(goal).not.toBeNull();
    expect(goal!.type).toEqual({ tag: 'Const', name: 'Nat' });
    expect(goal!.ctx.length).toBe(0);
  });

  test('getFocusedGoalId returns goal ID', () => {
    const definitions = createNatDefinitions();
    const goalType: TTKTerm = { tag: 'Const', name: 'Nat' };

    const state = createProofState(goalType, [], definitions, '?test_goal');
    const goalId = getFocusedGoalId(state);

    expect(goalId).toBe('?test_goal');
  });

  test('getUnsolvedGoals returns all unsolved goals', () => {
    const definitions = createNatDefinitions();
    const goalType: TTKTerm = { tag: 'Const', name: 'Nat' };

    const state = createProofState(goalType, [], definitions);
    const unsolved = getUnsolvedGoals(state);

    expect(unsolved.length).toBe(1);
    expect(unsolved[0].solution).toBeUndefined();
  });

  test('isProofComplete returns false for unsolved goals', () => {
    const definitions = createNatDefinitions();
    const goalType: TTKTerm = { tag: 'Const', name: 'Nat' };

    const state = createProofState(goalType, [], definitions);

    expect(isProofComplete(state)).toBe(false);
  });

  test('extractGoalStates formats goals for display', () => {
    const definitions = createNatDefinitions();
    const context = [
      { name: 'n', type: { tag: 'Const', name: 'Nat' } as TTKTerm },
      { name: 'm', type: { tag: 'Const', name: 'Nat' } as TTKTerm }
    ];
    const goalType: TTKTerm = { tag: 'Const', name: 'Nat' };

    const state = createProofState(goalType, context, definitions);
    const goalStates = extractGoalStates(state);

    expect(goalStates.length).toBe(1);
    expect(goalStates[0].hypotheses.length).toBe(2);
    expect(goalStates[0].hypotheses[0].name).toBe('n');
    expect(goalStates[0].hypotheses[1].name).toBe('m');
    expect(goalStates[0].target).toEqual({ tag: 'Const', name: 'Nat' });
  });

  test('updateProofState creates new state immutably', () => {
    const definitions = createNatDefinitions();
    const goalType: TTKTerm = { tag: 'Const', name: 'Nat' };

    const state1 = createProofState(goalType, [], definitions);
    const state2 = updateProofState(state1, { focusIndex: 1 });

    expect(state1.focusIndex).toBe(0); // Original unchanged
    expect(state2.focusIndex).toBe(1); // New state updated
    expect(state2.goals).toBe(state1.goals); // Other fields shared
  });
});

describe('ProofState <-> TacticEngine conversion', () => {
  beforeEach(() => {
    resetMetaCounter();
  });

  test('engineToProofState converts TacticEngine', () => {
    const definitions = createNatDefinitions();
    const goalType: TTKTerm = { tag: 'Const', name: 'Nat' };

    const engine = createInitialEngine(goalType, [], definitions, '?eng_goal');
    const state = engineToProofState(engine);

    expect(state.term).toBe(engine.term);
    expect(state.metaVars).toBe(engine.metaVars);
    expect(state.goals).toBe(engine.goals);
    expect(state.focusIndex).toBe(engine.focusIndex);
    expect(state.constraints).toBe(engine.constraints);
    expect(state.definitions).toBe(engine.definitions);
  });

  test('proofStateToEngine converts ProofState', () => {
    const definitions = createNatDefinitions();
    const goalType: TTKTerm = { tag: 'Const', name: 'Nat' };

    const state = createProofState(goalType, [], definitions);
    const engine = proofStateToEngine(state);

    expect(engine.term).toBe(state.term);
    expect(engine.metaVars).toBe(state.metaVars);
    expect(engine.goals).toBe(state.goals);
    expect(engine.focusIndex).toBe(state.focusIndex);
  });

  test('round-trip conversion preserves state', () => {
    const definitions = createNatDefinitions();
    const goalType: TTKTerm = { tag: 'Const', name: 'Nat' };

    const engine1 = createInitialEngine(goalType, [], definitions);
    const state = engineToProofState(engine1);
    const engine2 = proofStateToEngine(state);

    expect(engine2.term).toEqual(engine1.term);
    expect(engine2.goals).toEqual(engine1.goals);
    expect(engine2.focusIndex).toBe(engine1.focusIndex);
  });
});

describe('applyTacticToState (ProofState API)', () => {
  beforeEach(() => {
    resetMetaCounter();
  });

  test('applies Intro tactic to ProofState', () => {
    const definitions = createNatDefinitions();
    const goalType: TTKTerm = {
      tag: 'Binder',
      name: 'n',
      binderKind: { tag: 'BPi' },
      domain: { tag: 'Const', name: 'Nat' },
      body: { tag: 'Const', name: 'Nat' }
    };

    const state = createProofState(goalType, [], definitions);
    const result = applyTacticToState(state, { tag: 'Intro', name: 'n' });

    expect(result.success).toBe(true);
    if (!result.success) return;

    const newGoal = getFocusedGoal(result.newState)!;
    expect(newGoal.ctx.length).toBe(1);
    expect(newGoal.ctx[0].name).toBe('n');
  });

  test('applies Exact tactic to ProofState', () => {
    const definitions = createNatDefinitions();
    const goalType: TTKTerm = { tag: 'Const', name: 'Nat' };

    const state = createProofState(goalType, [], definitions);
    const result = applyTacticToState(state, {
      tag: 'Exact',
      term: { tag: 'Const', name: 'Zero' }
    });

    expect(result.success).toBe(true);
    if (!result.success) return;

    expect(isProofComplete(result.newState)).toBe(true);
  });

  test('fails with error when appropriate', () => {
    const definitions = createNatDefinitions();
    const goalType: TTKTerm = { tag: 'Const', name: 'Nat' };

    const state = createProofState(goalType, [], definitions);

    // Try intro on non-Pi type (should fail)
    const result = applyTacticToState(state, { tag: 'Intro' });

    expect(result.success).toBe(false);
    if (result.success) return;
    expect(result.error).toContain('not a function type');
  });
});

describe('applyTacticsToState (multi-step proofs)', () => {
  beforeEach(() => {
    resetMetaCounter();
  });

  test('proves identity function: Nat -> Nat', () => {
    const definitions = createNatDefinitions();
    const goalType: TTKTerm = {
      tag: 'Binder',
      name: 'n',
      binderKind: { tag: 'BPi' },
      domain: { tag: 'Const', name: 'Nat' },
      body: { tag: 'Const', name: 'Nat' }
    };

    const state = createProofState(goalType, [], definitions);

    const result = applyTacticsToState(state, [
      { tag: 'Intro', name: 'n' },
      { tag: 'Exact', term: { tag: 'Var', index: 0 } }
    ]);

    expect(result.success).toBe(true);
    if (!result.success) return;

    expect(isProofComplete(result.newState)).toBe(true);

    // Extract and verify final term
    const finalTerm = extractProofTermFromState(result.newState);
    expect(finalTerm.tag).toBe('Binder');
    if (finalTerm.tag !== 'Binder') return;
    expect(finalTerm.binderKind.tag).toBe('BLam');
    expect(finalTerm.body.tag).toBe('Var');
  });

  test('builds Succ Zero', () => {
    const definitions = createNatDefinitions();
    const goalType: TTKTerm = { tag: 'Const', name: 'Nat' };

    const state = createProofState(goalType, [], definitions);

    const result = applyTacticsToState(state, [
      { tag: 'Apply', fn: { tag: 'Const', name: 'Succ' } },
      { tag: 'Exact', term: { tag: 'Const', name: 'Zero' } }
    ]);

    expect(result.success).toBe(true);
    if (!result.success) return;

    expect(isProofComplete(result.newState)).toBe(true);

    const finalTerm = extractProofTermFromState(result.newState);
    expect(finalTerm.tag).toBe('App');
  });

  test('stops at first error', () => {
    const definitions = createNatDefinitions();
    const goalType: TTKTerm = {
      tag: 'Binder',
      name: 'n',
      binderKind: { tag: 'BPi' },
      domain: { tag: 'Const', name: 'Nat' },
      body: {
        tag: 'Binder',
        name: 'f',
        binderKind: { tag: 'BPi' },
        domain: { tag: 'Const', name: 'Nat' },
        body: { tag: 'Const', name: 'Nat' }
      }
    };

    const state = createProofState(goalType, [], definitions);

    // intro n, then assumption (should fail - no matching hypothesis)
    const result = applyTacticsToState(state, [
      { tag: 'Intro', name: 'n' },
      { tag: 'Assumption' }
    ]);

    expect(result.success).toBe(false);
    if (result.success) return;
    expect(result.error).toContain('no matching hypothesis');
  });
});
