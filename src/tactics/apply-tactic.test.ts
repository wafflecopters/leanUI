/**
 * Tests for the unified applyTactic API
 *
 * These tests verify that the applyTactic function correctly dispatches
 * to the underlying tactic implementations.
 */

import { describe, test, expect, beforeEach } from 'vitest';
import { applyTactic, applyTactics, isProofComplete, extractProofTerm } from './apply-tactic';
import { createInitialEngine } from './tacticsEngine';
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

describe('applyTactic', () => {
  beforeEach(() => {
    resetMetaCounter();
  });

  test('applies Intro tactic', () => {
    const definitions = createNatDefinitions();
    const goalType: TTKTerm = {
      tag: 'Binder',
      name: 'n',
      binderKind: { tag: 'BPi' },
      domain: { tag: 'Const', name: 'Nat' },
      body: { tag: 'Const', name: 'Nat' }
    };

    const engine = createInitialEngine(goalType, [], definitions);

    const result = applyTactic(engine, { tag: 'Intro', name: 'n' });

    expect(result.success).toBe(true);
    if (!result.success) return;

    const newGoal = result.newEngine.getFocusedGoal()!;
    expect(newGoal.ctx.length).toBe(1);
    expect(newGoal.ctx[0].name).toBe('n');
  });

  test('applies Intros tactic', () => {
    const definitions = createNatDefinitions();
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

    const result = applyTactic(engine, { tag: 'Intros', names: ['x', 'y'] });

    expect(result.success).toBe(true);
    if (!result.success) return;

    const newGoal = result.newEngine.getFocusedGoal()!;
    expect(newGoal.ctx.length).toBe(2);
    expect(newGoal.ctx[0].name).toBe('x');
    expect(newGoal.ctx[1].name).toBe('y');
  });

  test('applies Exact tactic', () => {
    const definitions = createNatDefinitions();
    const goalType: TTKTerm = { tag: 'Const', name: 'Nat' };

    const engine = createInitialEngine(goalType, [], definitions);

    const result = applyTactic(engine, {
      tag: 'Exact',
      term: { tag: 'Const', name: 'Zero' }
    });

    expect(result.success).toBe(true);
    if (!result.success) return;

    expect(result.newEngine.isComplete()).toBe(true);
  });

  test('applies Assumption tactic', () => {
    const definitions = createNatDefinitions();
    const context = [{ name: 'n', type: { tag: 'Const', name: 'Nat' } as TTKTerm }];
    const goalType: TTKTerm = { tag: 'Const', name: 'Nat' };

    const engine = createInitialEngine(goalType, context, definitions);

    const result = applyTactic(engine, { tag: 'Assumption' });

    expect(result.success).toBe(true);
    if (!result.success) return;

    expect(result.newEngine.isComplete()).toBe(true);
  });

  test('applies Apply tactic', () => {
    const definitions = createNatDefinitions();
    const goalType: TTKTerm = { tag: 'Const', name: 'Nat' };

    const engine = createInitialEngine(goalType, [], definitions);

    const result = applyTactic(engine, {
      tag: 'Apply',
      fn: { tag: 'Const', name: 'Succ' }
    });

    expect(result.success).toBe(true);
    if (!result.success) return;

    // Should create one subgoal
    expect(result.newEngine.getUnsolvedGoals().length).toBe(1);
  });

  test('fails with error when no focused goal', () => {
    const definitions = createNatDefinitions();
    const goalType: TTKTerm = { tag: 'Const', name: 'Nat' };

    // Create engine and solve the goal
    let engine = createInitialEngine(goalType, [], definitions);
    const result1 = applyTactic(engine, {
      tag: 'Exact',
      term: { tag: 'Const', name: 'Zero' }
    });
    expect(result1.success).toBe(true);
    if (!result1.success) return;
    engine = result1.newEngine;

    // Try to apply another tactic (should fail - no goals left)
    const result2 = applyTactic(engine, { tag: 'Assumption' });
    expect(result2.success).toBe(false);
    if (result2.success) return;
    expect(result2.error).toContain('no focused goal');
  });
});

describe('applyTactics (sequence)', () => {
  beforeEach(() => {
    resetMetaCounter();
  });

  test('applies tactics in sequence', () => {
    const definitions = createNatDefinitions();
    const goalType: TTKTerm = {
      tag: 'Binder',
      name: 'n',
      binderKind: { tag: 'BPi' },
      domain: { tag: 'Const', name: 'Nat' },
      body: { tag: 'Const', name: 'Nat' }
    };

    const engine = createInitialEngine(goalType, [], definitions);

    // Apply: intro n, exact n
    const result = applyTactics(engine, [
      { tag: 'Intro', name: 'n' },
      { tag: 'Exact', term: { tag: 'Var', index: 0 } }
    ]);

    expect(result.success).toBe(true);
    if (!result.success) return;

    expect(isProofComplete(result.newEngine)).toBe(true);

    // Extract final term (should be λn. n)
    const finalTerm = extractProofTerm(result.newEngine);
    expect(finalTerm.tag).toBe('Binder');
    if (finalTerm.tag !== 'Binder') return;
    expect(finalTerm.binderKind.tag).toBe('BLam');
    expect(finalTerm.body.tag).toBe('Var');
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

    const engine = createInitialEngine(goalType, [], definitions);

    // Apply: intro n, assumption (should fail - goal is Nat -> Nat, no matching hypothesis)
    const result = applyTactics(engine, [
      { tag: 'Intro', name: 'n' },
      { tag: 'Assumption' }
    ]);

    expect(result.success).toBe(false);
    if (result.success) return;
    expect(result.error).toContain('no matching hypothesis');
  });
});

describe('Integration: Complex proofs via applyTactics', () => {
  beforeEach(() => {
    resetMetaCounter();
  });

  test('Identity function: Nat -> Nat', () => {
    const definitions = createNatDefinitions();
    const goalType: TTKTerm = {
      tag: 'Binder',
      name: 'n',
      binderKind: { tag: 'BPi' },
      domain: { tag: 'Const', name: 'Nat' },
      body: { tag: 'Const', name: 'Nat' }
    };

    const engine = createInitialEngine(goalType, [], definitions);

    const result = applyTactics(engine, [
      { tag: 'Intro', name: 'n' },
      { tag: 'Exact', term: { tag: 'Var', index: 0 } }
    ]);

    expect(result.success).toBe(true);
    if (!result.success) return;
    expect(isProofComplete(result.newEngine)).toBe(true);
  });

  test('Build Succ Zero', () => {
    const definitions = createNatDefinitions();
    const goalType: TTKTerm = { tag: 'Const', name: 'Nat' };

    const engine = createInitialEngine(goalType, [], definitions);

    const result = applyTactics(engine, [
      { tag: 'Apply', fn: { tag: 'Const', name: 'Succ' } },
      { tag: 'Exact', term: { tag: 'Const', name: 'Zero' } }
    ]);

    expect(result.success).toBe(true);
    if (!result.success) return;
    expect(isProofComplete(result.newEngine)).toBe(true);

    const finalTerm = extractProofTerm(result.newEngine);
    expect(finalTerm.tag).toBe('App');
  });

  test('Const function: Nat -> Nat -> Nat (returns first arg)', () => {
    const definitions = createNatDefinitions();
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

    const result = applyTactics(engine, [
      { tag: 'Intros', names: ['a', 'b'] },
      { tag: 'Exact', term: { tag: 'Var', index: 1 } } // a is at index 1 (b is 0)
    ]);

    expect(result.success).toBe(true);
    if (!result.success) return;
    expect(isProofComplete(result.newEngine)).toBe(true);
  });
});
