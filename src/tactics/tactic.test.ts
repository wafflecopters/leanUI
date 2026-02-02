/**
 * Unit tests for individual tactics
 *
 * These tests verify that each tactic correctly transforms proof state
 * without relying on the full compilation pipeline.
 */

import { describe, test, expect, beforeEach } from 'vitest';
import {
  IntroTactic,
  IntrosTactic,
  ExactTactic,
  AssumptionTactic,
  ApplyTactic,
  resetMetaCounter
} from './tactic';
import { TacticEngine, createInitialEngine } from './tacticsEngine';
import { TTKTerm } from '../compiler/kernel';
import { DefinitionsMap } from '../compiler/term';

// =============================================================================
// Test Utilities
// =============================================================================

/**
 * Create a simple definitions map with Nat type and constructors
 */
function createNatDefinitions(): DefinitionsMap {
  const terms = new Map();
  const inductiveTypes = new Map();
  const inductiveNameOfConstructor = new Map();

  // Nat inductive type
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

  // Zero : Nat
  terms.set('Zero', {
    name: 'Zero',
    type: { tag: 'Const', name: 'Nat' },
    value: { tag: 'Const', name: 'Zero' }
  });
  inductiveNameOfConstructor.set('Zero', 'Nat');

  // Succ : Nat -> Nat
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

/**
 * Helper to extract term structure for assertions
 */
function extractTermStructure(term: TTKTerm): any {
  switch (term.tag) {
    case 'Var':
      return { tag: 'Var', index: term.index };
    case 'Const':
      return { tag: 'Const', name: term.name };
    case 'App':
      return {
        tag: 'App',
        fn: extractTermStructure(term.fn),
        arg: extractTermStructure(term.arg)
      };
    case 'Binder':
      return {
        tag: 'Binder',
        name: term.name,
        binderKind: term.binderKind.tag,
        domain: extractTermStructure(term.domain),
        body: extractTermStructure(term.body)
      };
    case 'Meta':
      return { tag: 'Meta', id: term.id };
    default:
      return { tag: term.tag };
  }
}

// =============================================================================
// IntroTactic Tests
// =============================================================================

describe('IntroTactic', () => {
  beforeEach(() => {
    resetMetaCounter();
  });

  test('introduces single Pi binder', () => {
    const definitions = createNatDefinitions();

    // Goal: Nat -> Nat
    const goalType: TTKTerm = {
      tag: 'Binder',
      name: 'n',
      binderKind: { tag: 'BPi' },
      domain: { tag: 'Const', name: 'Nat' },
      body: { tag: 'Const', name: 'Nat' }
    };

    const engine = createInitialEngine(goalType, [], definitions);

    // Apply intro
    const goal = engine.getFocusedGoal()!;
    const goalId = engine.getFocusedGoalId()!;
    const result = new IntroTactic().apply(engine, goal, goalId);

    // Should succeed
    expect(result.success).toBe(true);
    if (!result.success) return;

    const newEngine = result.newEngine;

    // Original goal should be solved with lambda
    const originalGoal = newEngine.metaVars.get(goalId)!;
    expect(originalGoal.solution?.tag).toBe('Binder');
    if (originalGoal.solution?.tag !== 'Binder') return;
    expect(originalGoal.solution.binderKind.tag).toBe('BLam');

    // New goal should be created in extended context
    const newGoalId = newEngine.getFocusedGoalId()!;
    const newGoal = newEngine.getFocusedGoal()!;
    expect(newGoal.ctx.length).toBe(1);
    expect(newGoal.ctx[0].name).toBe('n');
    expect(newGoal.ctx[0].type).toEqual({ tag: 'Const', name: 'Nat' });
    expect(newGoal.type).toEqual({ tag: 'Const', name: 'Nat' });
  });

  test('uses user-provided name', () => {
    const definitions = createNatDefinitions();

    const goalType: TTKTerm = {
      tag: 'Binder',
      name: 'x',
      binderKind: { tag: 'BPi' },
      domain: { tag: 'Const', name: 'Nat' },
      body: { tag: 'Const', name: 'Nat' }
    };

    const engine = createInitialEngine(goalType, [], definitions);
    const goal = engine.getFocusedGoal()!;
    const goalId = engine.getFocusedGoalId()!;

    // Apply intro with custom name
    const result = new IntroTactic('myVar').apply(engine, goal, goalId);

    expect(result.success).toBe(true);
    if (!result.success) return;

    const newGoal = result.newEngine.getFocusedGoal()!;
    expect(newGoal.ctx[0].name).toBe('myVar');
  });

  test('fails on non-Pi goal type', () => {
    const definitions = createNatDefinitions();

    // Goal: Nat (not a function type)
    const goalType: TTKTerm = { tag: 'Const', name: 'Nat' };
    const engine = createInitialEngine(goalType, [], definitions);

    const goal = engine.getFocusedGoal()!;
    const goalId = engine.getFocusedGoalId()!;
    const result = new IntroTactic().apply(engine, goal, goalId);

    expect(result.success).toBe(false);
    if (result.success) return;
    expect(result.error).toContain('not a function type');
  });
});

// =============================================================================
// IntrosTactic Tests
// =============================================================================

describe('IntrosTactic', () => {
  beforeEach(() => {
    resetMetaCounter();
  });

  test('introduces multiple Pi binders', () => {
    const definitions = createNatDefinitions();

    // Goal: Nat -> Nat -> Nat
    const goalType: TTKTerm = {
      tag: 'Binder',
      name: 'a',
      binderKind: { tag: 'BPi' },
      domain: { tag: 'Const', name: 'Nat' },
      body: {
        tag: 'Binder',
        name: 'b',
        binderKind: { tag: 'BPi' },
        domain: { tag: 'Const', name: 'Nat' },
        body: { tag: 'Const', name: 'Nat' }
      }
    };

    const engine = createInitialEngine(goalType, [], definitions);
    const goal = engine.getFocusedGoal()!;
    const goalId = engine.getFocusedGoalId()!;

    // Apply intros
    const result = new IntrosTactic().apply(engine, goal, goalId);

    expect(result.success).toBe(true);
    if (!result.success) return;

    // Should have introduced both parameters
    const newGoal = result.newEngine.getFocusedGoal()!;
    expect(newGoal.ctx.length).toBe(2);
    expect(newGoal.ctx[0].name).toBe('a');
    expect(newGoal.ctx[1].name).toBe('b');
    expect(newGoal.type).toEqual({ tag: 'Const', name: 'Nat' });
  });

  test('uses provided names in order', () => {
    const definitions = createNatDefinitions();

    const goalType: TTKTerm = {
      tag: 'Binder',
      name: 'x',
      binderKind: { tag: 'BPi' },
      domain: { tag: 'Const', name: 'Nat' },
      body: {
        tag: 'Binder',
        name: 'y',
        binderKind: { tag: 'BPi' },
        domain: { tag: 'Const', name: 'Nat' },
        body: { tag: 'Const', name: 'Nat' }
      }
    };

    const engine = createInitialEngine(goalType, [], definitions);
    const goal = engine.getFocusedGoal()!;
    const goalId = engine.getFocusedGoalId()!;

    const result = new IntrosTactic(['first', 'second']).apply(engine, goal, goalId);

    expect(result.success).toBe(true);
    if (!result.success) return;

    const newGoal = result.newEngine.getFocusedGoal()!;
    expect(newGoal.ctx[0].name).toBe('first');
    expect(newGoal.ctx[1].name).toBe('second');
  });

  test('stops when non-Pi type is reached', () => {
    const definitions = createNatDefinitions();

    // Goal: Nat -> Nat (will introduce one, then stop)
    const goalType: TTKTerm = {
      tag: 'Binder',
      name: 'n',
      binderKind: { tag: 'BPi' },
      domain: { tag: 'Const', name: 'Nat' },
      body: { tag: 'Const', name: 'Nat' }
    };

    const engine = createInitialEngine(goalType, [], definitions);
    const goal = engine.getFocusedGoal()!;
    const goalId = engine.getFocusedGoalId()!;

    const result = new IntrosTactic().apply(engine, goal, goalId);

    expect(result.success).toBe(true);
    if (!result.success) return;

    // Should have introduced one parameter, then stopped
    const newGoal = result.newEngine.getFocusedGoal()!;
    expect(newGoal.ctx.length).toBe(1);
    expect(newGoal.type.tag).toBe('Const');
  });

  test('succeeds immediately on non-Pi type', () => {
    const definitions = createNatDefinitions();

    // Goal: Nat (not a function, intros should do nothing)
    const goalType: TTKTerm = { tag: 'Const', name: 'Nat' };
    const engine = createInitialEngine(goalType, [], definitions);

    const goal = engine.getFocusedGoal()!;
    const goalId = engine.getFocusedGoalId()!;
    const result = new IntrosTactic().apply(engine, goal, goalId);

    // Should succeed but not change anything
    expect(result.success).toBe(true);
    if (!result.success) return;
    expect(result.newEngine.getFocusedGoal()!.ctx.length).toBe(0);
  });
});

// =============================================================================
// ExactTactic Tests
// =============================================================================

describe('ExactTactic', () => {
  beforeEach(() => {
    resetMetaCounter();
  });

  test('solves goal with correct term', () => {
    const definitions = createNatDefinitions();

    // Goal: Nat
    const goalType: TTKTerm = { tag: 'Const', name: 'Nat' };
    const engine = createInitialEngine(goalType, [], definitions);

    const goal = engine.getFocusedGoal()!;
    const goalId = engine.getFocusedGoalId()!;

    // Provide Zero : Nat
    const solution: TTKTerm = { tag: 'Const', name: 'Zero' };
    const result = new ExactTactic(solution).apply(engine, goal, goalId);

    expect(result.success).toBe(true);
    if (!result.success) return;

    // Goal should be solved
    const solvedGoal = result.newEngine.metaVars.get(goalId)!;
    expect(solvedGoal.solution).toBeDefined();
    expect(solvedGoal.solution?.tag).toBe('Const');

    // Goal should be removed from goals list
    expect(result.newEngine.goals).not.toContain(goalId);
  });

  test('solves goal with variable from context', () => {
    const definitions = createNatDefinitions();

    // Context: n : Nat
    const context = [{ name: 'n', type: { tag: 'Const', name: 'Nat' } as TTKTerm }];

    // Goal: Nat
    const goalType: TTKTerm = { tag: 'Const', name: 'Nat' };
    const engine = createInitialEngine(goalType, context, definitions);

    const goal = engine.getFocusedGoal()!;
    const goalId = engine.getFocusedGoalId()!;

    // Use variable 0 (n)
    const solution: TTKTerm = { tag: 'Var', index: 0 };
    const result = new ExactTactic(solution).apply(engine, goal, goalId);

    expect(result.success).toBe(true);
    if (!result.success) return;

    expect(result.newEngine.metaVars.get(goalId)!.solution).toBeDefined();
  });

  test('fails when term has wrong type', () => {
    const definitions = createNatDefinitions();

    // Goal: Nat -> Nat
    const goalType: TTKTerm = {
      tag: 'Binder',
      name: '_',
      binderKind: { tag: 'BPi' },
      domain: { tag: 'Const', name: 'Nat' },
      body: { tag: 'Const', name: 'Nat' }
    };
    const engine = createInitialEngine(goalType, [], definitions);

    const goal = engine.getFocusedGoal()!;
    const goalId = engine.getFocusedGoalId()!;

    // Try to provide Zero : Nat (wrong type - need function)
    const solution: TTKTerm = { tag: 'Const', name: 'Zero' };
    const result = new ExactTactic(solution).apply(engine, goal, goalId);

    expect(result.success).toBe(false);
  });
});

// =============================================================================
// AssumptionTactic Tests
// =============================================================================

describe('AssumptionTactic', () => {
  beforeEach(() => {
    resetMetaCounter();
  });

  test('finds matching hypothesis in context', () => {
    const definitions = createNatDefinitions();

    // Context: n : Nat, m : Nat
    const context = [
      { name: 'n', type: { tag: 'Const', name: 'Nat' } as TTKTerm },
      { name: 'm', type: { tag: 'Const', name: 'Nat' } as TTKTerm }
    ];

    // Goal: Nat
    const goalType: TTKTerm = { tag: 'Const', name: 'Nat' };
    const engine = createInitialEngine(goalType, context, definitions);

    const goal = engine.getFocusedGoal()!;
    const goalId = engine.getFocusedGoalId()!;

    const result = new AssumptionTactic().apply(engine, goal, goalId);

    expect(result.success).toBe(true);
    if (!result.success) return;

    // Should use most recent matching hypothesis (m, which is Var 0)
    const solution = result.newEngine.metaVars.get(goalId)!.solution!;
    expect(solution.tag).toBe('Var');
    if (solution.tag !== 'Var') return;
    expect(solution.index).toBe(0); // Most recent binding
  });

  test('uses most recent matching hypothesis', () => {
    const definitions = createNatDefinitions();

    // Context: a : Nat, b : Nat -> Nat, c : Nat
    const context = [
      { name: 'a', type: { tag: 'Const', name: 'Nat' } as TTKTerm },
      {
        name: 'b',
        type: {
          tag: 'Binder',
          name: '_',
          binderKind: { tag: 'BPi' },
          domain: { tag: 'Const', name: 'Nat' },
          body: { tag: 'Const', name: 'Nat' }
        } as TTKTerm
      },
      { name: 'c', type: { tag: 'Const', name: 'Nat' } as TTKTerm }
    ];

    // Goal: Nat (should match 'c', not 'a')
    const goalType: TTKTerm = { tag: 'Const', name: 'Nat' };
    const engine = createInitialEngine(goalType, context, definitions);

    const goal = engine.getFocusedGoal()!;
    const goalId = engine.getFocusedGoalId()!;

    const result = new AssumptionTactic().apply(engine, goal, goalId);

    expect(result.success).toBe(true);
    if (!result.success) return;

    const solution = result.newEngine.metaVars.get(goalId)!.solution!;
    expect(solution.tag).toBe('Var');
    if (solution.tag !== 'Var') return;
    expect(solution.index).toBe(0); // 'c' is most recent
  });

  test('fails when no matching hypothesis exists', () => {
    const definitions = createNatDefinitions();

    // Context: f : Nat -> Nat (no bare Nat)
    const context = [
      {
        name: 'f',
        type: {
          tag: 'Binder',
          name: '_',
          binderKind: { tag: 'BPi' },
          domain: { tag: 'Const', name: 'Nat' },
          body: { tag: 'Const', name: 'Nat' }
        } as TTKTerm
      }
    ];

    // Goal: Nat (no matching hypothesis)
    const goalType: TTKTerm = { tag: 'Const', name: 'Nat' };
    const engine = createInitialEngine(goalType, context, definitions);

    const goal = engine.getFocusedGoal()!;
    const goalId = engine.getFocusedGoalId()!;

    const result = new AssumptionTactic().apply(engine, goal, goalId);

    expect(result.success).toBe(false);
    if (result.success) return;
    expect(result.error).toContain('no matching hypothesis');
  });
});

// =============================================================================
// ApplyTactic Tests
// =============================================================================

describe('ApplyTactic', () => {
  beforeEach(() => {
    resetMetaCounter();
  });

  test('applies function with one argument', () => {
    const definitions = createNatDefinitions();

    // Goal: Nat
    const goalType: TTKTerm = { tag: 'Const', name: 'Nat' };
    const engine = createInitialEngine(goalType, [], definitions);

    const goal = engine.getFocusedGoal()!;
    const goalId = engine.getFocusedGoalId()!;

    // Apply Succ : Nat -> Nat
    const fn: TTKTerm = { tag: 'Const', name: 'Succ' };
    const result = new ApplyTactic(fn).apply(engine, goal, goalId);

    expect(result.success).toBe(true);
    if (!result.success) return;

    // Should create one subgoal of type Nat
    const newGoals = result.newEngine.getUnsolvedGoals();
    expect(newGoals.length).toBe(1);
    expect(newGoals[0].type).toEqual({ tag: 'Const', name: 'Nat' });

    // Original goal should be solved with (Succ ?arg)
    const solvedGoal = result.newEngine.metaVars.get(goalId)!;
    expect(solvedGoal.solution?.tag).toBe('App');
  });

  test('applies function with multiple arguments', () => {
    const definitions = createNatDefinitions();

    // Add: Nat -> Nat -> Nat
    definitions.terms.set('Add', {
      name: 'Add',
      type: {
        tag: 'Binder',
        name: '_',
        binderKind: { tag: 'BPi' },
        domain: { tag: 'Const', name: 'Nat' },
        body: {
          tag: 'Binder',
          name: '_',
          binderKind: { tag: 'BPi' },
          domain: { tag: 'Const', name: 'Nat' },
          body: { tag: 'Const', name: 'Nat' }
        }
      },
      value: { tag: 'Const', name: 'Zero' } // dummy
    });

    // Goal: Nat
    const goalType: TTKTerm = { tag: 'Const', name: 'Nat' };
    const engine = createInitialEngine(goalType, [], definitions);

    const goal = engine.getFocusedGoal()!;
    const goalId = engine.getFocusedGoalId()!;

    // Apply Add
    const fn: TTKTerm = { tag: 'Const', name: 'Add' };
    const result = new ApplyTactic(fn).apply(engine, goal, goalId);

    expect(result.success).toBe(true);
    if (!result.success) return;

    // Should create two subgoals, both of type Nat
    const newGoals = result.newEngine.getUnsolvedGoals();
    expect(newGoals.length).toBe(2);
    expect(newGoals[0].type).toEqual({ tag: 'Const', name: 'Nat' });
    expect(newGoals[1].type).toEqual({ tag: 'Const', name: 'Nat' });
  });

  test('applies variable from context', () => {
    const definitions = createNatDefinitions();

    // Context: f : Nat -> Nat
    const context = [
      {
        name: 'f',
        type: {
          tag: 'Binder',
          name: '_',
          binderKind: { tag: 'BPi' },
          domain: { tag: 'Const', name: 'Nat' },
          body: { tag: 'Const', name: 'Nat' }
        } as TTKTerm
      }
    ];

    // Goal: Nat
    const goalType: TTKTerm = { tag: 'Const', name: 'Nat' };
    const engine = createInitialEngine(goalType, context, definitions);

    const goal = engine.getFocusedGoal()!;
    const goalId = engine.getFocusedGoalId()!;

    // Apply f (Var 0)
    const fn: TTKTerm = { tag: 'Var', index: 0 };
    const result = new ApplyTactic(fn).apply(engine, goal, goalId);

    expect(result.success).toBe(true);
    if (!result.success) return;

    // Should create one subgoal of type Nat
    expect(result.newEngine.getUnsolvedGoals().length).toBe(1);
  });

  test('fails when return type does not match goal', () => {
    const definitions = createNatDefinitions();

    // Goal: Nat -> Nat (expecting a function)
    const goalType: TTKTerm = {
      tag: 'Binder',
      name: '_',
      binderKind: { tag: 'BPi' },
      domain: { tag: 'Const', name: 'Nat' },
      body: { tag: 'Const', name: 'Nat' }
    };
    const engine = createInitialEngine(goalType, [], definitions);

    const goal = engine.getFocusedGoal()!;
    const goalId = engine.getFocusedGoalId()!;

    // Try to apply Succ : Nat -> Nat (returns Nat, not Nat -> Nat)
    const fn: TTKTerm = { tag: 'Const', name: 'Succ' };
    const result = new ApplyTactic(fn).apply(engine, goal, goalId);

    expect(result.success).toBe(false);
    if (result.success) return;
    expect(result.error).toContain('type mismatch');
  });
});

// =============================================================================
// Integration: Multi-step proofs
// =============================================================================

describe('Multi-step tactic proofs', () => {
  beforeEach(() => {
    resetMetaCounter();
  });

  test('id function: intro then exact', () => {
    const definitions = createNatDefinitions();

    // Goal: Nat -> Nat
    const goalType: TTKTerm = {
      tag: 'Binder',
      name: 'n',
      binderKind: { tag: 'BPi' },
      domain: { tag: 'Const', name: 'Nat' },
      body: { tag: 'Const', name: 'Nat' }
    };

    let engine = createInitialEngine(goalType, [], definitions);

    // Step 1: intro n
    {
      const goal = engine.getFocusedGoal()!;
      const goalId = engine.getFocusedGoalId()!;
      const result = new IntroTactic('n').apply(engine, goal, goalId);
      expect(result.success).toBe(true);
      if (!result.success) return;
      engine = result.newEngine;
    }

    // Step 2: exact n (Var 0)
    {
      const goal = engine.getFocusedGoal()!;
      const goalId = engine.getFocusedGoalId()!;
      const result = new ExactTactic({ tag: 'Var', index: 0 }).apply(engine, goal, goalId);
      expect(result.success).toBe(true);
      if (!result.success) return;
      engine = result.newEngine;
    }

    // Proof should be complete
    expect(engine.isComplete()).toBe(true);

    // Zonk to get final term
    const finalTerm = engine.zonk();
    expect(finalTerm.tag).toBe('Binder');
    if (finalTerm.tag !== 'Binder') return;
    expect(finalTerm.binderKind.tag).toBe('BLam');
    expect(finalTerm.body.tag).toBe('Var');
  });

  test('apply Succ then exact Zero', () => {
    const definitions = createNatDefinitions();

    // Goal: Nat
    const goalType: TTKTerm = { tag: 'Const', name: 'Nat' };
    let engine = createInitialEngine(goalType, [], definitions);

    // Step 1: apply Succ
    {
      const goal = engine.getFocusedGoal()!;
      const goalId = engine.getFocusedGoalId()!;
      const result = new ApplyTactic({ tag: 'Const', name: 'Succ' }).apply(engine, goal, goalId);
      expect(result.success).toBe(true);
      if (!result.success) return;
      engine = result.newEngine;
    }

    // Should have one subgoal of type Nat
    expect(engine.getUnsolvedGoals().length).toBe(1);

    // Step 2: exact Zero
    {
      const goal = engine.getFocusedGoal()!;
      const goalId = engine.getFocusedGoalId()!;
      const result = new ExactTactic({ tag: 'Const', name: 'Zero' }).apply(engine, goal, goalId);
      expect(result.success).toBe(true);
      if (!result.success) return;
      engine = result.newEngine;
    }

    // Proof should be complete
    expect(engine.isComplete()).toBe(true);

    // Final term should be (Succ Zero)
    const finalTerm = engine.zonk();
    expect(finalTerm.tag).toBe('App');
    if (finalTerm.tag !== 'App') return;
    expect(finalTerm.fn).toEqual({ tag: 'Const', name: 'Succ' });
    expect(finalTerm.arg).toEqual({ tag: 'Const', name: 'Zero' });
  });

  test('intros then assumption', () => {
    const definitions = createNatDefinitions();

    // Goal: Nat -> Nat
    const goalType: TTKTerm = {
      tag: 'Binder',
      name: 'x',
      binderKind: { tag: 'BPi' },
      domain: { tag: 'Const', name: 'Nat' },
      body: { tag: 'Const', name: 'Nat' }
    };

    let engine = createInitialEngine(goalType, [], definitions);

    // Step 1: intros
    {
      const goal = engine.getFocusedGoal()!;
      const goalId = engine.getFocusedGoalId()!;
      const result = new IntrosTactic().apply(engine, goal, goalId);
      expect(result.success).toBe(true);
      if (!result.success) return;
      engine = result.newEngine;
    }

    // Step 2: assumption (should find x : Nat in context)
    {
      const goal = engine.getFocusedGoal()!;
      const goalId = engine.getFocusedGoalId()!;
      const result = new AssumptionTactic().apply(engine, goal, goalId);
      expect(result.success).toBe(true);
      if (!result.success) return;
      engine = result.newEngine;
    }

    // Proof should be complete
    expect(engine.isComplete()).toBe(true);
  });
});
