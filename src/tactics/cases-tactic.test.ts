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

  test('tags branch goals with constructor names', () => {
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

    // Get the two branch goals
    const goal1 = result.newEngine.metaVars.get(result.newEngine.goals[0])!;
    const goal2 = result.newEngine.metaVars.get(result.newEngine.goals[1])!;

    // Check that case tags are set correctly
    expect(goal1.caseTag).toBe('True');
    expect(goal2.caseTag).toBe('False');
  });
});

// =============================================================================
// Tests for indexed inductive types (dependent cases)
// =============================================================================

/**
 * Create Nat + Leq definitions for testing dependent cases.
 *
 * Leq : Nat -> Nat -> Type
 *   LeqZero : {n : Nat} -> Leq Zero n
 *   LeqSucc : {n m : Nat} -> Leq n m -> Leq (Succ n) (Succ m)
 *
 * indexPositions: [0, 1] (both Nat args are indices)
 */
function createLeqDefinitions(): DefinitionsMap {
  const terms = new Map();
  const inductiveTypes = new Map();
  const inductiveNameOfConstructor = new Map();

  // Nat
  inductiveTypes.set('Nat', {
    name: 'Nat',
    type: { tag: 'Sort', level: { tag: 'ULit', n: 1 } },
    constructors: [
      { name: 'Zero', type: { tag: 'Const', name: 'Nat' } },
      {
        name: 'Succ',
        type: {
          tag: 'Binder', name: 'n', binderKind: { tag: 'BPi' },
          domain: { tag: 'Const', name: 'Nat' },
          body: { tag: 'Const', name: 'Nat' }
        }
      }
    ],
    indexPositions: [],
  });
  terms.set('Zero', { name: 'Zero', type: { tag: 'Const', name: 'Nat' }, value: { tag: 'Const', name: 'Zero' } });
  terms.set('Succ', {
    name: 'Succ',
    type: { tag: 'Binder', name: 'n', binderKind: { tag: 'BPi' }, domain: { tag: 'Const', name: 'Nat' }, body: { tag: 'Const', name: 'Nat' } },
    value: { tag: 'Const', name: 'Succ' }
  });
  inductiveNameOfConstructor.set('Zero', 'Nat');
  inductiveNameOfConstructor.set('Succ', 'Nat');

  // Leq : Nat -> Nat -> Type
  // LeqZero : {n : Nat} -> Leq Zero n
  // LeqSucc : {n m : Nat} -> Leq n m -> Leq (Succ n) (Succ m)
  const leqType: TTKTerm = {
    tag: 'Binder', name: 'a', binderKind: { tag: 'BPi' },
    domain: { tag: 'Const', name: 'Nat' },
    body: {
      tag: 'Binder', name: 'b', binderKind: { tag: 'BPi' },
      domain: { tag: 'Const', name: 'Nat' },
      body: { tag: 'Sort', level: { tag: 'ULit', n: 1 } }
    }
  };

  // LeqZero : {n : Nat} -> Leq Zero n
  // Constructor type: (n : Nat) -> App(App(Const "Leq", Const "Zero"), Var(0))
  const leqZeroType: TTKTerm = {
    tag: 'Binder', name: 'n', binderKind: { tag: 'BPi' },
    domain: { tag: 'Const', name: 'Nat' },
    body: {
      tag: 'App',
      fn: { tag: 'App', fn: { tag: 'Const', name: 'Leq' }, arg: { tag: 'Const', name: 'Zero' } },
      arg: { tag: 'Var', index: 0 }  // n
    }
  };

  // LeqSucc : {n m : Nat} -> Leq n m -> Leq (Succ n) (Succ m)
  // Constructor type: (n : Nat) -> (m : Nat) -> Leq n m -> Leq (Succ n) (Succ m)
  // With de Bruijn: (n : Nat) -> (m : Nat) -> App(App(Leq, Var 1), Var 0) -> App(App(Leq, App(Succ, Var 2)), App(Succ, Var 1))
  const leqSuccType: TTKTerm = {
    tag: 'Binder', name: 'n', binderKind: { tag: 'BPi' },
    domain: { tag: 'Const', name: 'Nat' },
    body: {
      tag: 'Binder', name: 'm', binderKind: { tag: 'BPi' },
      domain: { tag: 'Const', name: 'Nat' },
      body: {
        tag: 'Binder', name: 'h', binderKind: { tag: 'BPi' },
        domain: {
          tag: 'App',
          fn: { tag: 'App', fn: { tag: 'Const', name: 'Leq' }, arg: { tag: 'Var', index: 1 } },
          arg: { tag: 'Var', index: 0 }
        },
        body: {
          tag: 'App',
          fn: {
            tag: 'App',
            fn: { tag: 'Const', name: 'Leq' },
            arg: { tag: 'App', fn: { tag: 'Const', name: 'Succ' }, arg: { tag: 'Var', index: 2 } }
          },
          arg: { tag: 'App', fn: { tag: 'Const', name: 'Succ' }, arg: { tag: 'Var', index: 1 } }
        }
      }
    }
  };

  inductiveTypes.set('Leq', {
    name: 'Leq',
    type: leqType,
    constructors: [
      { name: 'LeqZero', type: leqZeroType, namedArgMap: new Map([[0, 'n']]) },
      { name: 'LeqSucc', type: leqSuccType, namedArgMap: new Map([[0, 'n'], [1, 'm']]) },
    ],
    indexPositions: [0, 1],
  });

  terms.set('LeqZero', { name: 'LeqZero', type: leqZeroType, value: { tag: 'Const', name: 'LeqZero' } });
  terms.set('LeqSucc', { name: 'LeqSucc', type: leqSuccType, value: { tag: 'Const', name: 'LeqSucc' } });
  inductiveNameOfConstructor.set('LeqZero', 'Leq');
  inductiveNameOfConstructor.set('LeqSucc', 'Leq');

  return { terms, inductiveTypes, inductiveNameOfConstructor };
}

describe('CasesTactic with indexed types (dependent cases)', () => {
  beforeEach(() => {
    resetMetaCounter();
  });

  test('creates branch goals with refined types for Leq', () => {
    const definitions = createLeqDefinitions();

    // Context: [a : Nat, b : Nat, c : Nat, h : Leq a b]
    // Goal sees: a=Var(3), b=Var(2), c=Var(1), h=Var(0)
    const context = [
      { name: 'a', type: { tag: 'Const', name: 'Nat' } as TTKTerm },
      { name: 'b', type: { tag: 'Const', name: 'Nat' } as TTKTerm },
      { name: 'c', type: { tag: 'Const', name: 'Nat' } as TTKTerm },
      {
        name: 'h', type: {
          tag: 'App',
          fn: { tag: 'App', fn: { tag: 'Const', name: 'Leq' }, arg: { tag: 'Var', index: 2 } },
          arg: { tag: 'Var', index: 1 }
        } as TTKTerm
      }
    ];

    // Goal: Leq a c = App(App(Leq, Var(3)), Var(1))
    const goalType: TTKTerm = {
      tag: 'App',
      fn: { tag: 'App', fn: { tag: 'Const', name: 'Leq' }, arg: { tag: 'Var', index: 3 } },
      arg: { tag: 'Var', index: 1 }
    };

    const engine = createInitialEngine(goalType, context, definitions);
    const goal = engine.getFocusedGoal()!;
    const goalId = engine.getFocusedGoalId()!;

    // cases h (Var 0)
    const tactic = new CasesTactic({ tag: 'Var', index: 0 });
    const result = tactic.apply(engine, goal, goalId);

    expect(result.success).toBe(true);
    if (!result.success) return;

    // Should create 2 subgoals (LeqZero and LeqSucc)
    expect(result.newEngine.goals.length).toBe(2);

    const leqZeroGoal = result.newEngine.metaVars.get(result.newEngine.goals[0])!;
    const leqSuccGoal = result.newEngine.metaVars.get(result.newEngine.goals[1])!;

    // LeqZero branch: goal should be Leq Zero c (not Leq a c)
    // The first index 'a' should be refined to Zero
    expect(leqZeroGoal.caseTag).toBe('LeqZero');

    // LeqSucc branch: goal should be Leq (Succ n') c
    expect(leqSuccGoal.caseTag).toBe('LeqSucc');
  });

  test('detects impossible branches (Leq (Succ n) Zero)', () => {
    const definitions = createLeqDefinitions();

    // Context: [n : Nat, h : Leq (Succ n) Zero]
    const context = [
      { name: 'n', type: { tag: 'Const', name: 'Nat' } as TTKTerm },
      {
        name: 'h', type: {
          tag: 'App',
          fn: {
            tag: 'App',
            fn: { tag: 'Const', name: 'Leq' },
            arg: { tag: 'App', fn: { tag: 'Const', name: 'Succ' }, arg: { tag: 'Var', index: 0 } }
          },
          arg: { tag: 'Const', name: 'Zero' }
        } as TTKTerm
      }
    ];

    // Goal: Nat
    const goalType: TTKTerm = { tag: 'Const', name: 'Nat' };
    const engine = createInitialEngine(goalType, context, definitions);
    const goal = engine.getFocusedGoal()!;
    const goalId = engine.getFocusedGoalId()!;

    // cases h — both constructors should be impossible
    // LeqZero requires first index = Zero, but we have Succ n
    // LeqSucc requires second index = Succ m, but we have Zero
    const tactic = new CasesTactic({ tag: 'Var', index: 0 });
    const result = tactic.apply(engine, goal, goalId);

    expect(result.success).toBe(true);
    if (!result.success) return;

    // No goals should be generated — all branches are impossible
    expect(result.newEngine.goals.length).toBe(0);
  });

  test('preserves non-index context variables', () => {
    const definitions = createLeqDefinitions();

    // Context: [a : Nat, b : Nat, c : Nat, h : Leq a b]
    const context = [
      { name: 'a', type: { tag: 'Const', name: 'Nat' } as TTKTerm },
      { name: 'b', type: { tag: 'Const', name: 'Nat' } as TTKTerm },
      { name: 'c', type: { tag: 'Const', name: 'Nat' } as TTKTerm },
      {
        name: 'h', type: {
          tag: 'App',
          fn: { tag: 'App', fn: { tag: 'Const', name: 'Leq' }, arg: { tag: 'Var', index: 2 } },
          arg: { tag: 'Var', index: 1 }
        } as TTKTerm
      }
    ];

    // Goal: Nat
    const goalType: TTKTerm = { tag: 'Const', name: 'Nat' };
    const engine = createInitialEngine(goalType, context, definitions);
    const goal = engine.getFocusedGoal()!;
    const goalId = engine.getFocusedGoalId()!;

    const tactic = new CasesTactic({ tag: 'Var', index: 0 });
    const result = tactic.apply(engine, goal, goalId);

    expect(result.success).toBe(true);
    if (!result.success) return;

    // The LeqZero branch context should still contain 'c'
    const leqZeroGoal = result.newEngine.metaVars.get(result.newEngine.goals[0])!;
    const contextNames = leqZeroGoal.ctx.map(e => e.name);
    expect(contextNames).toContain('c');
  });
});
