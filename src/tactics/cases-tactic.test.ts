/**
 * Tests for Cases tactic (Phase 4)
 */

import { describe, test, expect, beforeEach } from 'vitest';
import { CasesTactic } from './cases-tactic';
import { createInitialEngine } from './tacticsEngine';
import { resetMetaCounter } from './tactic';
import { applyTactic } from './apply-tactic';
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
          name: 'n',
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
      name: 'n',
      binderKind: { tag: 'BPi' },
      domain: { tag: 'Const', name: 'Nat' },
      body: { tag: 'Const', name: 'Nat' }
    },
    value: { tag: 'Const', name: 'Succ' }
  });
  inductiveNameOfConstructor.set('Succ', 'Nat');

  return { terms, inductiveTypes, inductiveNameOfConstructor };
}

describe('CasesTactic', () => {
  beforeEach(() => {
    resetMetaCounter();
  });

  test('creates multiple subgoals for inductive type', () => {
    const definitions = createNatDefinitions();

    // Context: n : Nat
    const context = [{ name: 'n', type: { tag: 'Const', name: 'Nat' } as TTKTerm }];

    // Goal: Nat (we'll do cases on n)
    const goalType: TTKTerm = { tag: 'Const', name: 'Nat' };
    const engine = createInitialEngine(goalType, context, definitions);

    const goal = engine.getFocusedGoal()!;
    const goalId = engine.getFocusedGoalId()!;

    // Apply cases on n (Var 0)
    const tactic = new CasesTactic({ tag: 'Var', index: 0 });
    const result = tactic.apply(engine, goal, goalId);

    expect(result.success).toBe(true);
    if (!result.success) return;

    // Should create 2 subgoals (Zero and Succ cases)
    expect(result.newEngine.goals.length).toBe(2);

    // Original goal should be solved
    const originalGoal = result.newEngine.metaVars.get(goalId);
    expect(originalGoal?.solution).toBeDefined();
  });

  test('creates goals with extended context for constructor params', () => {
    const definitions = createNatDefinitions();

    // Context: n : Nat
    const context = [{ name: 'n', type: { tag: 'Const', name: 'Nat' } as TTKTerm }];

    // Goal: Nat
    const goalType: TTKTerm = { tag: 'Const', name: 'Nat' };
    const engine = createInitialEngine(goalType, context, definitions);

    const goal = engine.getFocusedGoal()!;
    const goalId = engine.getFocusedGoalId()!;

    // Apply cases on n
    const tactic = new CasesTactic({ tag: 'Var', index: 0 });
    const result = tactic.apply(engine, goal, goalId);

    expect(result.success).toBe(true);
    if (!result.success) return;

    // Get the two branch goals
    const goal1 = result.newEngine.metaVars.get(result.newEngine.goals[0])!;
    const goal2 = result.newEngine.metaVars.get(result.newEngine.goals[1])!;

    // First goal (Zero case) - context unchanged
    expect(goal1.ctx.length).toBe(1); // Just 'n'

    // Second goal (Succ case) - context extended with Succ's parameter
    expect(goal2.ctx.length).toBe(2); // 'n' + Succ's parameter
  });

  test('fails on non-inductive type', () => {
    const definitions = createNatDefinitions();

    // Goal: Nat -> Nat (function type, not inductive)
    const goalType: TTKTerm = {
      tag: 'Binder',
      name: 'x',
      binderKind: { tag: 'BPi' },
      domain: { tag: 'Const', name: 'Nat' },
      body: { tag: 'Const', name: 'Nat' }
    };

    // Context: f : Nat -> Nat
    const context = [{ name: 'f', type: goalType }];

    const engine = createInitialEngine(goalType, context, definitions);

    const goal = engine.getFocusedGoal()!;
    const goalId = engine.getFocusedGoalId()!;

    // Try to do cases on f (which has function type)
    const tactic = new CasesTactic({ tag: 'Var', index: 0 });
    const result = tactic.apply(engine, goal, goalId);

    expect(result.success).toBe(false);
    if (result.success) return;
    expect(result.error).toContain('non-inductive type');
  });

  test('fails on undefined inductive type', () => {
    const definitions = createNatDefinitions();

    // Context: x : Foo (where Foo is not defined)
    const context = [{ name: 'x', type: { tag: 'Const', name: 'Foo' } as TTKTerm }];

    // Goal: Nat
    const goalType: TTKTerm = { tag: 'Const', name: 'Nat' };
    const engine = createInitialEngine(goalType, context, definitions);

    const goal = engine.getFocusedGoal()!;
    const goalId = engine.getFocusedGoalId()!;

    // Try to do cases on x (which has type Foo, not defined)
    const tactic = new CasesTactic({ tag: 'Var', index: 0 });
    const result = tactic.apply(engine, goal, goalId);

    expect(result.success).toBe(false);
    if (result.success) return;
    expect(result.error).toContain('not found');
  });

  test('works via applyTactic API', () => {
    const definitions = createNatDefinitions();

    // Context: n : Nat
    const context = [{ name: 'n', type: { tag: 'Const', name: 'Nat' } as TTKTerm }];

    // Goal: Nat
    const goalType: TTKTerm = { tag: 'Const', name: 'Nat' };
    const engine = createInitialEngine(goalType, context, definitions);

    // Apply via unified API
    const result = applyTactic(engine, {
      tag: 'Cases',
      scrutinee: { tag: 'Var', index: 0 }
    });

    expect(result.success).toBe(true);
    if (!result.success) return;

    // Should create 2 subgoals
    expect(result.newEngine.goals.length).toBe(2);
  });
});

describe('CasesTactic with Bool', () => {
  beforeEach(() => {
    resetMetaCounter();
  });

  // Create Bool definitions for additional testing
  function createBoolDefinitions(): DefinitionsMap {
    const terms = new Map();
    const inductiveTypes = new Map();
    const inductiveNameOfConstructor = new Map();

    inductiveTypes.set('Bool', {
      parameters: [],
      type: { tag: 'Type', level: { tag: 'LevelConst', value: 0 } },
      constructors: [
        {
          name: 'True',
          type: { tag: 'Const', name: 'Bool' }
        },
        {
          name: 'False',
          type: { tag: 'Const', name: 'Bool' }
        }
      ]
    });

    terms.set('True', {
      name: 'True',
      type: { tag: 'Const', name: 'Bool' },
      value: { tag: 'Const', name: 'True' }
    });
    inductiveNameOfConstructor.set('True', 'Bool');

    terms.set('False', {
      name: 'False',
      type: { tag: 'Const', name: 'Bool' },
      value: { tag: 'Const', name: 'False' }
    });
    inductiveNameOfConstructor.set('False', 'Bool');

    return { terms, inductiveTypes, inductiveNameOfConstructor };
  }

  test('creates two subgoals for Bool type', () => {
    const definitions = createBoolDefinitions();

    // Context: b : Bool
    const context = [{ name: 'b', type: { tag: 'Const', name: 'Bool' } as TTKTerm }];

    // Goal: Bool
    const goalType: TTKTerm = { tag: 'Const', name: 'Bool' };
    const engine = createInitialEngine(goalType, context, definitions);

    const goal = engine.getFocusedGoal()!;
    const goalId = engine.getFocusedGoalId()!;

    // Apply cases on b
    const tactic = new CasesTactic({ tag: 'Var', index: 0 });
    const result = tactic.apply(engine, goal, goalId);

    expect(result.success).toBe(true);
    if (!result.success) return;

    // Should create 2 subgoals (True and False cases)
    expect(result.newEngine.goals.length).toBe(2);
  });
});
