/**
 * Tests for the simp meta-tactic.
 */

import { describe, test, expect, beforeEach } from 'vitest';
import { TTKTerm } from '../compiler/kernel';
import { compileTTFromText } from '../compiler/compile';
import { createInitialEngine } from './tacticsEngine';
import { IntrosTactic, resetMetaCounter } from './tactic';
import { DefinitionsMap } from '../compiler/term';
import { runSimp } from './simp-tactic';

beforeEach(() => {
  resetMetaCounter();
});

const BASE_SOURCE = `inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat
inductive Equal : {A : Type} -> A -> A -> Type where
  refl : {A : Type} -> {a : A} -> Equal a a
sym : {A : Type} -> {x y : A} -> Equal x y -> Equal y x
sym refl = refl
replace : {A : Type} -> {x y : A} -> (P : A -> Type) -> Equal x y -> P x -> P y
replace P refl px = px
plus : Nat -> Nat -> Nat
plus Zero n = n
plus (Succ m) n = Succ (plus m n)
congSucc : {m n : Nat} -> Equal m n -> Equal (Succ m) (Succ n)
congSucc refl = refl
plusZeroRight : (n : Nat) -> Equal (plus n Zero) n
plusZeroRight Zero = refl
plusZeroRight (Succ n) = congSucc (plusZeroRight n)
plusSuccRight : (m n : Nat) -> Equal (plus m (Succ n)) (Succ (plus m n))
plusSuccRight Zero n = refl
plusSuccRight (Succ m) n = congSucc (plusSuccRight m n)
mul : Nat -> Nat -> Nat
mul Zero m = Zero
mul (Succ n) m = plus m (mul n m)
`;

let _compiled: ReturnType<typeof compileTTFromText> | null = null;
function getCompiled() {
  if (!_compiled) {
    _compiled = compileTTFromText(BASE_SOURCE);
    if (!_compiled.success) {
      throw new Error('Base source failed to compile: ' + JSON.stringify((_compiled as any).errors));
    }
  }
  return _compiled;
}

function getDefs(): DefinitionsMap {
  return getCompiled().definitions!;
}

function makeEngine(goalType: TTKTerm, ctx: Array<{ name: string; type: TTKTerm }> = []) {
  return createInitialEngine(goalType, ctx, getDefs());
}

describe('runSimp', () => {
  test('fails with no lemmas', () => {
    const goalType: TTKTerm = {
      tag: 'App', fn: { tag: 'App', fn: { tag: 'Const', name: 'Equal' },
        arg: { tag: 'App', fn: { tag: 'App', fn: { tag: 'Const', name: 'plus' },
          arg: { tag: 'Const', name: 'Zero' } }, arg: { tag: 'Const', name: 'Zero' } } },
      arg: { tag: 'Const', name: 'Zero' }
    };
    const engine = makeEngine(goalType);
    const result = runSimp(engine, []);
    expect(result.success).toBe(false);
    expect(result.steps).toHaveLength(0);
  });

  test('single rewrite step', () => {
    // Goal: Equal (plus n Zero) n
    // Lemma: plusZeroRight
    const goalType: TTKTerm = {
      tag: 'Binder', binderKind: { tag: 'BPi' }, name: 'n',
      domain: { tag: 'Const', name: 'Nat' },
      body: {
        tag: 'App', fn: { tag: 'App', fn: { tag: 'Const', name: 'Equal' },
          arg: { tag: 'App', fn: { tag: 'App', fn: { tag: 'Const', name: 'plus' },
            arg: { tag: 'Var', index: 0 } }, arg: { tag: 'Const', name: 'Zero' } } },
        arg: { tag: 'Var', index: 0 }
      }
    };
    const engine = makeEngine(goalType);

    // intro n
    const goal = engine.getFocusedGoal()!;
    const goalId = engine.getFocusedGoalId()!;
    const introsResult = new IntrosTactic(['n']).apply(engine, goal, goalId);
    if (!introsResult.success) { expect.unreachable('intros failed'); return; }

    const afterIntros = introsResult.newEngine;
    const result = runSimp(afterIntros, ['plusZeroRight']);
    expect(result.success).toBe(true);
    expect(result.steps).toHaveLength(1);
    expect(result.steps[0]).toEqual({ type: 'rewrite', name: 'plusZeroRight', reverse: false });
    expect(result.proofNodes).toHaveLength(1);
    expect(result.proofNodes[0].tag).toBe('rewrite');
  });

  test('fails when no lemma applies', () => {
    // Goal: Equal Zero (Succ Zero) — plusSuccRight needs `plus m (Succ n)` pattern
    const goalType: TTKTerm = {
      tag: 'App', fn: { tag: 'App', fn: { tag: 'Const', name: 'Equal' },
        arg: { tag: 'Const', name: 'Zero' } },
      arg: { tag: 'App', fn: { tag: 'Const', name: 'Succ' }, arg: { tag: 'Const', name: 'Zero' } }
    };
    const engine = makeEngine(goalType);
    // plusSuccRight has pattern `plus m (Succ n)` — no plus in goal, so won't match
    const result = runSimp(engine, ['plusSuccRight']);
    expect(result.success).toBe(false);
    expect(result.error).toContain('no applicable lemma');
  });

  test('unfold step', () => {
    // Goal: Equal (mul Zero n) Zero  -- should unfold mul
    const goalType: TTKTerm = {
      tag: 'Binder', binderKind: { tag: 'BPi' }, name: 'n',
      domain: { tag: 'Const', name: 'Nat' },
      body: {
        tag: 'App', fn: { tag: 'App', fn: { tag: 'Const', name: 'Equal' },
          arg: { tag: 'App', fn: { tag: 'App', fn: { tag: 'Const', name: 'mul' },
            arg: { tag: 'Const', name: 'Zero' } }, arg: { tag: 'Var', index: 0 } } },
        arg: { tag: 'Const', name: 'Zero' }
      }
    };
    const engine = makeEngine(goalType);
    const goal = engine.getFocusedGoal()!;
    const goalId = engine.getFocusedGoalId()!;
    const introsResult = new IntrosTactic(['n']).apply(engine, goal, goalId);
    if (!introsResult.success) { expect.unreachable('intros failed'); return; }

    const result = runSimp(introsResult.newEngine, ['mul']);
    expect(result.success).toBe(true);
    // Should have at least one unfold step
    expect(result.steps.some(s => s.type === 'unfold' && s.name === 'mul')).toBe(true);
  });

  test('multiple steps chain', () => {
    // Goal: Equal (plus (plus n Zero) Zero) n
    // Should apply plusZeroRight twice
    const goalType: TTKTerm = {
      tag: 'Binder', binderKind: { tag: 'BPi' }, name: 'n',
      domain: { tag: 'Const', name: 'Nat' },
      body: {
        tag: 'App', fn: { tag: 'App', fn: { tag: 'Const', name: 'Equal' },
          arg: {
            tag: 'App', fn: { tag: 'App', fn: { tag: 'Const', name: 'plus' },
              arg: { tag: 'App', fn: { tag: 'App', fn: { tag: 'Const', name: 'plus' },
                arg: { tag: 'Var', index: 0 } }, arg: { tag: 'Const', name: 'Zero' } } },
            arg: { tag: 'Const', name: 'Zero' }
          } },
        arg: { tag: 'Var', index: 0 }
      }
    };
    const engine = makeEngine(goalType);
    const goal = engine.getFocusedGoal()!;
    const goalId = engine.getFocusedGoalId()!;
    const introsResult = new IntrosTactic(['n']).apply(engine, goal, goalId);
    if (!introsResult.success) { expect.unreachable('intros failed'); return; }

    const result = runSimp(introsResult.newEngine, ['plusZeroRight']);
    expect(result.success).toBe(true);
    // Should apply plusZeroRight at least twice
    expect(result.steps.length).toBeGreaterThanOrEqual(2);
    expect(result.steps.every(s => s.name === 'plusZeroRight')).toBe(true);
  });

  test('commutativity does not loop', () => {
    // plusZeroRight rewrites `plus n Zero → n`, but applied to `Equal n n`
    // the rewrite won't match. Instead, test with a self-inverting pattern:
    // Goal: Equal (plus Zero (plus Zero n)) n
    // plusZeroRight rewrites the inner `plus Zero n → n` giving `Equal (plus Zero n) n`
    // then rewrites outer `plus Zero n → n` giving `Equal n n`, done by refl.
    // But if we also had a reverse-direction lemma, it would cycle.
    // Instead, test directly: apply plusZeroRight to `Equal (plus n Zero) n` twice
    // by wrapping it: the second application sees `Equal n n` which doesn't match, so it stops.
    // For a true cycle test: use the same lemma where LHS and RHS have the same head.
    // plusSuccRight: plus m (Succ n) = Succ (plus m n) — not self-inverting.
    // A true commutativity cycle needs a commutative lemma.
    // We'll use a postulate for plusComm.
    const source = BASE_SOURCE + `postulate plusComm : (m n : Nat) -> Equal (plus m n) (plus n m)\n`;
    const compiled = compileTTFromText(source);
    if (!compiled.success) { expect.unreachable('plusComm compilation failed'); return; }

    // Goal: (m n : Nat) -> Equal (plus m n) (plus n m)
    const goalType: TTKTerm = {
      tag: 'Binder', binderKind: { tag: 'BPi' }, name: 'm',
      domain: { tag: 'Const', name: 'Nat' },
      body: {
        tag: 'Binder', binderKind: { tag: 'BPi' }, name: 'n',
        domain: { tag: 'Const', name: 'Nat' },
        body: {
          tag: 'App', fn: { tag: 'App', fn: { tag: 'Const', name: 'Equal' },
            arg: { tag: 'App', fn: { tag: 'App', fn: { tag: 'Const', name: 'plus' },
              arg: { tag: 'Var', index: 1 } }, arg: { tag: 'Var', index: 0 } } },
          arg: { tag: 'App', fn: { tag: 'App', fn: { tag: 'Const', name: 'plus' },
            arg: { tag: 'Var', index: 0 } }, arg: { tag: 'Var', index: 1 } }
        }
      }
    };
    const engine = createInitialEngine(goalType, [], compiled.definitions!);
    const goal = engine.getFocusedGoal()!;
    const goalId = engine.getFocusedGoalId()!;
    const introsResult = new IntrosTactic(['m', 'n']).apply(engine, goal, goalId);
    if (!introsResult.success) { expect.unreachable('intros failed'); return; }

    const result = runSimp(introsResult.newEngine, ['plusComm']);
    // Should NOT run 50 steps — cycle detection should stop it
    expect(result.steps.length).toBeLessThan(5);
  });
});
