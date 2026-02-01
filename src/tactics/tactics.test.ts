/**
 * Unit tests for tactics engine and core tactics
 */

import { describe, test, expect, beforeEach } from 'vitest';
import { TacticEngine, createInitialEngine } from './tacticsEngine';
import {
  ExactTactic,
  AssumptionTactic,
  IntroTactic,
  IntrosTactic,
  ApplyTactic,
  TacticSequence,
  resetMetaCounter
} from './tactic';
import { TTKTerm, TTKContext } from '../compiler/kernel';
import { DefinitionsMap } from '../compiler/term';

// =============================================================================
// Test Helpers
// =============================================================================

/**
 * Create a minimal DefinitionsMap for testing
 */
function createTestDefinitions(): DefinitionsMap {
  return {
    inductiveTypes: new Map([
      ['Nat', {
        name: 'Nat',
        type: { tag: 'Sort', level: { tag: 'ULit', n: 1 } },
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
        ],
        paramCount: 0,
        indexPositions: [],
        levelParamCount: 0
      }],
      ['Bool', {
        name: 'Bool',
        type: { tag: 'Sort', level: { tag: 'ULit', n: 1 } },
        constructors: [
          {
            name: 'True',
            type: { tag: 'Const', name: 'Bool' }
          },
          {
            name: 'False',
            type: { tag: 'Const', name: 'Bool' }
          }
        ],
        paramCount: 0,
        indexPositions: [],
        levelParamCount: 0
      }]
    ]),
    inductiveNameOfConstructor: new Map([
      ['Zero', 'Nat'],
      ['Succ', 'Nat'],
      ['True', 'Bool'],
      ['False', 'Bool']
    ]),
    terms: new Map()
  };
}

/**
 * Helper to create an engine with a specific goal type and context
 */
function createEngineWithContext(
  goalType: TTKTerm,
  context: TTKContext,
  definitions?: DefinitionsMap
): TacticEngine {
  return createInitialEngine(
    goalType,
    context,
    definitions ?? createTestDefinitions(),
    '?goal0'
  );
}

// =============================================================================
// TacticEngine Tests
// =============================================================================

describe('TacticEngine', () => {
  beforeEach(() => {
    resetMetaCounter();
  });

  test('createInitialEngine: creates engine with one goal', () => {
    const goalType: TTKTerm = { tag: 'Const', name: 'Nat' };
    const engine = createInitialEngine(goalType, [], createTestDefinitions());

    expect(engine.goals).toHaveLength(1);
    expect(engine.getFocusedGoal()?.type).toEqual(goalType);
    expect(engine.isComplete()).toBe(false);
  });

  test('isComplete: true when no unsolved goals', () => {
    const goalType: TTKTerm = { tag: 'Const', name: 'Nat' };
    const engine = createInitialEngine(goalType, [], createTestDefinitions());

    // Solve the goal
    const goalId = engine.goals[0];
    const goal = engine.metaVars.get(goalId)!;
    const newMetaVars = new Map(engine.metaVars);
    newMetaVars.set(goalId, { ...goal, solution: { tag: 'Const', name: 'Zero' } });

    const solvedEngine = engine.withUpdates({
      metaVars: newMetaVars,
      goals: []
    });

    expect(solvedEngine.isComplete()).toBe(true);
  });

  test('focusNext: cycles through goals', () => {
    const goalType: TTKTerm = { tag: 'Const', name: 'Nat' };
    const engine = createInitialEngine(goalType, [], createTestDefinitions())
      .withUpdates({ goals: ['?g1', '?g2', '?g3'], focusIndex: 0 });

    expect(engine.focusIndex).toBe(0);
    expect(engine.focusNext().focusIndex).toBe(1);
    expect(engine.focusNext().focusNext().focusIndex).toBe(2);
    expect(engine.focusNext().focusNext().focusNext().focusIndex).toBe(0); // Wraps around
  });

  test('focusPrev: cycles backwards through goals', () => {
    const goalType: TTKTerm = { tag: 'Const', name: 'Nat' };
    const engine = createInitialEngine(goalType, [], createTestDefinitions())
      .withUpdates({ goals: ['?g1', '?g2', '?g3'], focusIndex: 2 });

    expect(engine.focusIndex).toBe(2);
    expect(engine.focusPrev().focusIndex).toBe(1);
    expect(engine.focusPrev().focusPrev().focusIndex).toBe(0);
    expect(engine.focusPrev().focusPrev().focusPrev().focusIndex).toBe(2); // Wraps around
  });

  test('focusGoal: sets focus by goal ID', () => {
    const goalType: TTKTerm = { tag: 'Const', name: 'Nat' };
    const engine = createInitialEngine(goalType, [], createTestDefinitions())
      .withUpdates({ goals: ['?g1', '?g2', '?g3'], focusIndex: 0 });

    expect(engine.focusGoal('?g3').focusIndex).toBe(2);
    expect(engine.focusGoal('?g1').focusIndex).toBe(0);
    expect(engine.focusGoal('?unknown').focusIndex).toBe(0); // No change if not found
  });
});

// =============================================================================
// ExactTactic Tests
// =============================================================================

describe('ExactTactic', () => {
  beforeEach(() => {
    resetMetaCounter();
  });

  test('exact: solves goal with matching term', () => {
    const goalType: TTKTerm = { tag: 'Const', name: 'Nat' };
    const context: TTKContext = [
      { name: 'n', type: { tag: 'Const', name: 'Nat' } }
    ];

    const engine = createEngineWithContext(goalType, context);
    const tactic = new ExactTactic({ tag: 'Var', index: 0 }); // Use 'n'

    const result = tactic.apply(
      engine,
      engine.getFocusedGoal()!,
      engine.getFocusedGoalId()!
    );

    expect(result.success).toBe(true);
    if (!result.success) return;

    expect(result.newEngine.isComplete()).toBe(true);
    expect(result.newEngine.goals).toHaveLength(0);
  });

  test('exact: fails when term has wrong type', () => {
    const goalType: TTKTerm = { tag: 'Const', name: 'Nat' };
    const context: TTKContext = [
      { name: 'b', type: { tag: 'Const', name: 'Bool' } }
    ];

    const engine = createEngineWithContext(goalType, context);
    const tactic = new ExactTactic({ tag: 'Var', index: 0 }); // Use 'b' (Bool, not Nat)

    const result = tactic.apply(
      engine,
      engine.getFocusedGoal()!,
      engine.getFocusedGoalId()!
    );

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

  test('assumption: finds matching hypothesis', () => {
    const goalType: TTKTerm = { tag: 'Const', name: 'Nat' };
    const context: TTKContext = [
      { name: 'b', type: { tag: 'Const', name: 'Bool' } },
      { name: 'n', type: { tag: 'Const', name: 'Nat' } }
    ];

    const engine = createEngineWithContext(goalType, context);
    const tactic = new AssumptionTactic();

    const result = tactic.apply(
      engine,
      engine.getFocusedGoal()!,
      engine.getFocusedGoalId()!
    );

    expect(result.success).toBe(true);
    if (!result.success) return;

    expect(result.newEngine.isComplete()).toBe(true);
  });

  test('assumption: fails when no matching hypothesis', () => {
    const goalType: TTKTerm = { tag: 'Const', name: 'Nat' };
    const context: TTKContext = [
      { name: 'b', type: { tag: 'Const', name: 'Bool' } }
    ];

    const engine = createEngineWithContext(goalType, context);
    const tactic = new AssumptionTactic();

    const result = tactic.apply(
      engine,
      engine.getFocusedGoal()!,
      engine.getFocusedGoalId()!
    );

    expect(result.success).toBe(false);
    if (result.success) return; // Type guard
    expect(result.error).toContain('no matching hypothesis');
  });

  test('assumption: uses most recent matching hypothesis', () => {
    const goalType: TTKTerm = { tag: 'Const', name: 'Nat' };
    const context: TTKContext = [
      { name: 'n1', type: { tag: 'Const', name: 'Nat' } },
      { name: 'n2', type: { tag: 'Const', name: 'Nat' } }
    ];

    const engine = createEngineWithContext(goalType, context);
    const tactic = new AssumptionTactic();

    const result = tactic.apply(
      engine,
      engine.getFocusedGoal()!,
      engine.getFocusedGoalId()!
    );

    expect(result.success).toBe(true);
    if (!result.success) return;

    // Should use n2 (most recent), which is at index 0 in de Bruijn
    const zonked = result.newEngine.zonk();
    expect(zonked).toEqual({ tag: 'Var', index: 0 });
  });
});

// =============================================================================
// IntroTactic Tests
// =============================================================================

describe('IntroTactic', () => {
  beforeEach(() => {
    resetMetaCounter();
  });

  test('intro: introduces Pi binder', () => {
    const goalType: TTKTerm = {
      tag: 'Binder',
      name: 'x',
      binderKind: { tag: 'BPi' },
      domain: { tag: 'Const', name: 'Nat' },
      body: { tag: 'Const', name: 'Bool' }
    };

    const engine = createEngineWithContext(goalType, []);
    const tactic = new IntroTactic('n');

    const result = tactic.apply(
      engine,
      engine.getFocusedGoal()!,
      engine.getFocusedGoalId()!
    );

    expect(result.success).toBe(true);
    if (!result.success) return;

    const newGoal = result.newEngine.getFocusedGoal();
    expect(newGoal?.type).toEqual({ tag: 'Const', name: 'Bool' });
    expect(newGoal?.ctx).toHaveLength(1);
    expect(newGoal?.ctx[0].name).toBe('n');
    expect(newGoal?.ctx[0].type).toEqual({ tag: 'Const', name: 'Nat' });
  });

  test('intro: uses binder name when user name not provided', () => {
    const goalType: TTKTerm = {
      tag: 'Binder',
      name: 'myParam',
      binderKind: { tag: 'BPi' },
      domain: { tag: 'Const', name: 'Nat' },
      body: { tag: 'Const', name: 'Bool' }
    };

    const engine = createEngineWithContext(goalType, []);
    const tactic = new IntroTactic(); // No name provided

    const result = tactic.apply(
      engine,
      engine.getFocusedGoal()!,
      engine.getFocusedGoalId()!
    );

    expect(result.success).toBe(true);
    if (!result.success) return;

    const newGoal = result.newEngine.getFocusedGoal();
    expect(newGoal?.ctx[0].name).toBe('myParam');
  });

  test('intro: fails when goal is not a Pi type', () => {
    const goalType: TTKTerm = { tag: 'Const', name: 'Nat' };

    const engine = createEngineWithContext(goalType, []);
    const tactic = new IntroTactic('x');

    const result = tactic.apply(
      engine,
      engine.getFocusedGoal()!,
      engine.getFocusedGoalId()!
    );

    expect(result.success).toBe(false);
    if (result.success) return; // Type guard
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

  test('intros: introduces all Pi binders', () => {
    const goalType: TTKTerm = {
      tag: 'Binder',
      name: 'a',
      binderKind: { tag: 'BPi' },
      domain: { tag: 'Const', name: 'Nat' },
      body: {
        tag: 'Binder',
        name: 'b',
        binderKind: { tag: 'BPi' },
        domain: { tag: 'Const', name: 'Bool' },
        body: { tag: 'Const', name: 'Nat' }
      }
    };

    const engine = createEngineWithContext(goalType, []);
    const tactic = new IntrosTactic();

    const result = tactic.apply(
      engine,
      engine.getFocusedGoal()!,
      engine.getFocusedGoalId()!
    );

    expect(result.success).toBe(true);
    if (!result.success) return;

    const newGoal = result.newEngine.getFocusedGoal();
    expect(newGoal?.type).toEqual({ tag: 'Const', name: 'Nat' });
    expect(newGoal?.ctx).toHaveLength(2);
    expect(newGoal?.ctx[0].name).toBe('a');
    expect(newGoal?.ctx[1].name).toBe('b');
  });

  test('intros: uses provided names', () => {
    const goalType: TTKTerm = {
      tag: 'Binder',
      name: '_',
      binderKind: { tag: 'BPi' },
      domain: { tag: 'Const', name: 'Nat' },
      body: {
        tag: 'Binder',
        name: '_',
        binderKind: { tag: 'BPi' },
        domain: { tag: 'Const', name: 'Bool' },
        body: { tag: 'Const', name: 'Nat' }
      }
    };

    const engine = createEngineWithContext(goalType, []);
    const tactic = new IntrosTactic(['x', 'y']);

    const result = tactic.apply(
      engine,
      engine.getFocusedGoal()!,
      engine.getFocusedGoalId()!
    );

    expect(result.success).toBe(true);
    if (!result.success) return;

    const newGoal = result.newEngine.getFocusedGoal();
    expect(newGoal?.ctx[0].name).toBe('x');
    expect(newGoal?.ctx[1].name).toBe('y');
  });

  test('intros: stops at non-Pi type', () => {
    const goalType: TTKTerm = {
      tag: 'Binder',
      name: 'a',
      binderKind: { tag: 'BPi' },
      domain: { tag: 'Const', name: 'Nat' },
      body: { tag: 'Const', name: 'Bool' } // Not a Pi
    };

    const engine = createEngineWithContext(goalType, []);
    const tactic = new IntrosTactic();

    const result = tactic.apply(
      engine,
      engine.getFocusedGoal()!,
      engine.getFocusedGoalId()!
    );

    expect(result.success).toBe(true);
    if (!result.success) return;

    const newGoal = result.newEngine.getFocusedGoal();
    expect(newGoal?.ctx).toHaveLength(1); // Only introduced one binder
  });
});

// =============================================================================
// ApplyTactic Tests
// =============================================================================

describe('ApplyTactic', () => {
  beforeEach(() => {
    resetMetaCounter();
  });

  test('apply: creates subgoal for function argument', () => {
    const goalType: TTKTerm = { tag: 'Const', name: 'Bool' };
    const context: TTKContext = [
      {
        name: 'f',
        type: {
          tag: 'Binder',
      name: 'x',
      binderKind: { tag: 'BPi' },
          domain: { tag: 'Const', name: 'Nat' },
          body: { tag: 'Const', name: 'Bool' }
        }
      }
    ];

    const engine = createEngineWithContext(goalType, context);
    const tactic = new ApplyTactic({ tag: 'Var', index: 0 }); // Apply 'f'

    const result = tactic.apply(
      engine,
      engine.getFocusedGoal()!,
      engine.getFocusedGoalId()!
    );

    expect(result.success).toBe(true);
    if (!result.success) return;

    const unsolved = result.newEngine.getUnsolvedGoals();
    expect(unsolved).toHaveLength(1);
    expect(unsolved[0].type).toEqual({ tag: 'Const', name: 'Nat' });
  });

  test('apply: creates multiple subgoals for multi-argument function', () => {
    const goalType: TTKTerm = { tag: 'Const', name: 'Nat' };
    const context: TTKContext = [
      {
        name: 'g',
        type: {
          tag: 'Binder',
      name: 'a',
      binderKind: { tag: 'BPi' },
          domain: { tag: 'Const', name: 'Bool' },
          body: {
            tag: 'Binder',
      name: 'b',
      binderKind: { tag: 'BPi' },
            domain: { tag: 'Const', name: 'Bool' },
            body: { tag: 'Const', name: 'Nat' }
          }
        }
      }
    ];

    const engine = createEngineWithContext(goalType, context);
    const tactic = new ApplyTactic({ tag: 'Var', index: 0 }); // Apply 'g'

    const result = tactic.apply(
      engine,
      engine.getFocusedGoal()!,
      engine.getFocusedGoalId()!
    );

    expect(result.success).toBe(true);
    if (!result.success) return;

    const unsolved = result.newEngine.getUnsolvedGoals();
    expect(unsolved).toHaveLength(2);
    expect(unsolved[0].type).toEqual({ tag: 'Const', name: 'Bool' });
    expect(unsolved[1].type).toEqual({ tag: 'Const', name: 'Bool' });
  });

  test('apply: fails when return type does not match goal', () => {
    const goalType: TTKTerm = { tag: 'Const', name: 'Bool' };
    const context: TTKContext = [
      {
        name: 'f',
        type: {
          tag: 'Binder',
      name: 'x',
      binderKind: { tag: 'BPi' },
          domain: { tag: 'Const', name: 'Nat' },
          body: { tag: 'Const', name: 'Nat' } // Returns Nat, not Bool
        }
      }
    ];

    const engine = createEngineWithContext(goalType, context);
    const tactic = new ApplyTactic({ tag: 'Var', index: 0 });

    const result = tactic.apply(
      engine,
      engine.getFocusedGoal()!,
      engine.getFocusedGoalId()!
    );

    expect(result.success).toBe(false);
    if (result.success) return; // Type guard
    expect(result.error).toContain('return type mismatch');
  });
});

// =============================================================================
// TacticSequence Tests
// =============================================================================

describe('TacticSequence', () => {
  beforeEach(() => {
    resetMetaCounter();
  });

  test('sequence: applies tactics in order', () => {
    // Goal: Nat -> Bool -> Nat
    const goalType: TTKTerm = {
      tag: 'Binder',
      name: 'n',
      binderKind: { tag: 'BPi' },
      domain: { tag: 'Const', name: 'Nat' },
      body: {
        tag: 'Binder',
      name: 'b',
      binderKind: { tag: 'BPi' },
        domain: { tag: 'Const', name: 'Bool' },
        body: { tag: 'Const', name: 'Nat' }
      }
    };

    const engine = createEngineWithContext(goalType, []);

    const sequence = new TacticSequence('intro-intro-assumption', [
      new IntroTactic('x'),
      new IntroTactic('y'),
      new AssumptionTactic()
    ]);

    const result = sequence.apply(
      engine,
      engine.getFocusedGoal()!,
      engine.getFocusedGoalId()!
    );

    expect(result.success).toBe(true);
    if (!result.success) return;

    expect(result.newEngine.isComplete()).toBe(true);
  });

  test('sequence: fails if any tactic fails', () => {
    const goalType: TTKTerm = { tag: 'Const', name: 'Nat' };

    const engine = createEngineWithContext(goalType, []);

    const sequence = new TacticSequence('intro-assumption', [
      new IntroTactic('x'), // This will fail (goal is not a Pi)
      new AssumptionTactic()
    ]);

    const result = sequence.apply(
      engine,
      engine.getFocusedGoal()!,
      engine.getFocusedGoalId()!
    );

    expect(result.success).toBe(false);
  });
});

// =============================================================================
// Integration Tests
// =============================================================================

describe('Integration: Complete Proofs', () => {
  beforeEach(() => {
    resetMetaCounter();
  });

  test('prove const: Nat -> Bool -> Nat', () => {
    // Simple version: const : Nat -> Bool -> Nat
    const goalType: TTKTerm = {
      tag: 'Binder',
      name: 'a',
      binderKind: { tag: 'BPi' },
      domain: { tag: 'Const', name: 'Nat' },
      body: {
        tag: 'Binder',
        name: 'b',
        binderKind: { tag: 'BPi' },
        domain: { tag: 'Const', name: 'Bool' },
        body: { tag: 'Const', name: 'Nat' }
      }
    };

    const engine = createEngineWithContext(goalType, []);

    // Proof: intros, then exact (using first variable)
    let current = engine;

    // intros
    const introTacs = new IntrosTactic(['x', 'y']);
    const result1 = introTacs.apply(
      current,
      current.getFocusedGoal()!,
      current.getFocusedGoalId()!
    );
    expect(result1.success).toBe(true);
    if (!result1.success) return;
    current = result1.newEngine;

    // Goal should be Nat, context should have x:Nat, y:Bool  
    // exact x (which is Var index 1 after we introduced both)
    const exact = new ExactTactic({ tag: 'Var', index: 1 });
    const result2 = exact.apply(
      current,
      current.getFocusedGoal()!,
      current.getFocusedGoalId()!
    );
    expect(result2.success).toBe(true);
    if (!result2.success) return;
    current = result2.newEngine;

    expect(current.isComplete()).toBe(true);
  });
});
