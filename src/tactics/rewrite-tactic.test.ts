/**
 * Unit tests for RewriteTactic — focused on context search for premises.
 *
 * Tests that when rewriting with a lemma that has Pi-type prerequisites
 * (e.g., minusSucc : Leq i n -> Equal ...), the tactic automatically
 * searches the goal context for matching hypotheses.
 */

import { describe, test, expect, beforeEach } from 'vitest';
import { TTKTerm } from '../compiler/kernel';
import { compileTTFromText } from '../compiler/compile';
import { createInitialEngine, TacticEngine } from './tacticsEngine';
import { IntroTactic, IntrosTactic, resetMetaCounter } from './tactic';
import { RewriteTactic } from './rewrite-tactic';
import { UnfoldTactic } from './unfold-tactic';
import { DefinitionsMap } from '../compiler/term';
import { betaNormalize } from '../compiler/subst';

beforeEach(() => {
  resetMetaCounter();
});

// =============================================================================
// Test source code with Nat, Equal, Leq, and relevant lemmas
// =============================================================================

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
inductive Leq : Nat -> Nat -> Type where
  LeqZero : {n : Nat} -> Leq Zero n
  LeqSucc : {m n : Nat} -> Leq m n -> Leq (Succ m) (Succ n)
minus : Nat -> Nat -> Nat
minus n Zero = n
minus Zero (Succ m) = Zero
minus (Succ n) (Succ m) = minus n m
congSucc : {m n : Nat} -> Equal m n -> Equal (Succ m) (Succ n)
congSucc refl = refl
minusSucc : {i n : Nat} -> Leq i n -> Equal (minus (Succ n) i) (Succ (minus n i))
minusSucc LeqZero = refl
minusSucc (LeqSucc l) = minusSucc l
plusZeroRight : (n : Nat) -> Equal (plus n Zero) n
plusZeroRight Zero = refl
plusZeroRight (Succ n) = congSucc (plusZeroRight n)
mul : Nat -> Nat -> Nat
mul Zero m = Zero
mul (Succ n) m = plus m (mul n m)
cong : {A B : Type} -> {x y : A} -> (f : A -> B) -> Equal x y -> Equal (f x) (f y)
cong f refl = refl
sumStartCount : (start count : Nat) -> (Nat -> Nat) -> Nat
sumStartCount start Zero f = Zero
sumStartCount start (Succ k) f = plus (sumStartCount start k f) (f (plus start k))
mulZeroRight : (n : Nat) -> Equal (mul n Zero) Zero
mulZeroRight Zero = refl
mulZeroRight (Succ n) = mulZeroRight n
sumStartCountOne : (s : Nat) -> (f : Nat -> Nat) -> Equal (sumStartCount s (Succ Zero) f) (f s)
sumStartCountOne s f = cong f (plusZeroRight s)
minusSelf : {n : Nat} -> Equal (minus n n) Zero
minusSelf {n:=Zero} = refl
minusSelf {n:=Succ n} = minusSelf
sum : (start end : Nat) -> (Nat -> Nat) -> Nat
sum start end f = sumStartCount start (minus (Succ end) start) f
congPlusRight : {n m : Nat} -> (p : Nat) -> Equal n m -> Equal (plus p n) (plus p m)
congPlusRight Zero eq = eq
congPlusRight (Succ p) eq = congSucc (congPlusRight p eq)
congPlusLeft : {n m : Nat} -> (p : Nat) -> Equal n m -> Equal (plus n p) (plus m p)
congPlusLeft p refl = refl
trans : {A : Type} -> {x y z : A} -> Equal x y -> Equal y z -> Equal x z
trans refl refl = refl
plusAssoc : (n m p : Nat) -> Equal (plus (plus n m) p) (plus n (plus m p))
plusAssoc Zero m p = refl
plusAssoc (Succ n) m p = congSucc (plusAssoc n m p)
mulDistribRight : (n m p : Nat) -> Equal (mul (plus n m) p) (plus (mul n p) (mul m p))
mulDistribRight Zero m p = refl
mulDistribRight (Succ n) m p = trans (congPlusRight p (mulDistribRight n m p)) (sym (plusAssoc p (mul n p) (mul m p)))
postulate mulComm : (n m : Nat) -> Equal (mul n m) (mul m n)
succInj : {n m : Nat} -> Equal (Succ n) (Succ m) -> Equal n m
succInj refl = refl
plusCancelLeft : {a b c : Nat} -> Equal (plus a b) (plus a c) -> Equal b c
plusCancelLeft {a:=Zero} {b} {c} eq = eq
plusCancelLeft {a:=Succ a} {b} {c} eq = let k = succInj eq in plusCancelLeft k
`;

// Compile once and reuse
let _compiled: ReturnType<typeof compileTTFromText> | null = null;
function getCompiled() {
  if (!_compiled) {
    _compiled = compileTTFromText(BASE_SOURCE);
    if (!_compiled.success) {
      const errors: string[] = [];
      for (const b of _compiled.blocks) {
        if (b.parseErrors && b.parseErrors.length > 0) {
          errors.push(`Parse errors: ${JSON.stringify(b.parseErrors)}`);
        }
        if ((b as any).nameErrors && (b as any).nameErrors.length > 0) {
          errors.push(`Name errors: ${JSON.stringify((b as any).nameErrors)}`);
        }
        for (const d of b.declarations) {
          if (d.checkErrors && d.checkErrors.length > 0) {
            errors.push(`${d.name}: ${d.checkErrors.map(e => typeof e === 'string' ? e : (e as any).message || JSON.stringify(e)).join(', ')}`);
          }
        }
      }
      throw new Error(`Base compilation failed:\n${errors.join('\n')}`);
    }
  }
  return _compiled;
}

/**
 * Helper: get the kernel type of a declaration by name.
 */
function getDeclType(name: string): TTKTerm {
  const result = getCompiled();
  const decl = result.blocks.flatMap(b => b.declarations).find(d => d.name === name);
  if (!decl) throw new Error(`Declaration '${name}' not found`);
  if (!decl.kernelType) throw new Error(`Declaration '${name}' has no kernel type`);
  return decl.kernelType;
}

function getDefinitions(): DefinitionsMap {
  return getCompiled().definitions;
}

/**
 * Helper: create an engine with intros applied, returning the engine after intros.
 */
function setupEngineWithIntros(
  goalType: TTKTerm,
  definitions: DefinitionsMap,
  introNames: string[],
): TacticEngine {
  const engine = createInitialEngine(goalType, [], definitions);
  const goal = engine.getFocusedGoal()!;
  const goalId = engine.getFocusedGoalId()!;
  const result = new IntrosTactic(introNames).apply(engine, goal, goalId);
  if (!result.success) throw new Error(`intros failed: ${result.error}`);
  return result.newEngine;
}

// =============================================================================
// Tests
// =============================================================================

describe('RewriteTactic: basic rewrite (no premises)', () => {
  test('rewrite plusZeroRight transforms goal', () => {
    const defs = getDefinitions();

    // Goal: (n : Nat) -> Equal (plus n Zero) n
    // We use plusZeroRight's own type as the goal
    const goalType = getDeclType('plusZeroRight');
    const engine = setupEngineWithIntros(goalType, defs, ['n']);
    const goal = engine.getFocusedGoal()!;
    const goalId = engine.getFocusedGoalId()!;

    const tactic = new RewriteTactic({ tag: 'Const', name: 'plusZeroRight' });
    const result = tactic.apply(engine, goal, goalId);

    expect(result.success).toBe(true);
    if (!result.success) return;

    // After rewrite, goal should have changed (no more 'plus n Zero')
    const newGoal = result.newEngine.getFocusedGoal()!;
    expect(newGoal).not.toBeNull();
    const goalStr = termToString(newGoal.type);
    expect(goalStr).not.toContain('plus');
  });
});

describe('RewriteTactic: context search for premises', () => {
  test('rewrite minusSucc finds Leq premise in context', () => {
    const defs = getDefinitions();

    // Goal type is minusSucc's type: {i n : Nat} -> Leq i n -> Equal (minus (Succ n) i) (Succ (minus n i))
    // After intros [i, n, l], context is [i:Nat, n:Nat, l:Leq i n]
    // Goal is: Equal (minus (Succ n) i) (Succ (minus n i))
    const goalType = getDeclType('minusSucc');
    const engine = setupEngineWithIntros(goalType, defs, ['i', 'n', 'l']);
    const goal = engine.getFocusedGoal()!;
    const goalId = engine.getFocusedGoalId()!;

    // Verify context has the expected entries
    expect(goal.ctx).toHaveLength(3);
    expect(goal.ctx[0].name).toBe('i');
    expect(goal.ctx[1].name).toBe('n');
    expect(goal.ctx[2].name).toBe('l');

    // Apply rewrite minusSucc — should auto-find l : Leq i n in context
    const tactic = new RewriteTactic({ tag: 'Const', name: 'minusSucc' });
    const result = tactic.apply(engine, goal, goalId);

    expect(result.success).toBe(true);
    if (!result.success) {
      console.error('Rewrite failed:', result.error);
      return;
    }

    // After rewrite, the goal should have changed
    const newGoal = result.newEngine.getFocusedGoal()!;
    expect(newGoal).not.toBeNull();

    // The rewritten goal: 'minus (Succ n) i' replaced by 'Succ (minus n i)'
    // Result should be Equal (Succ (minus n i)) (Succ (minus n i))
    const goalStr = termToString(newGoal.type);
    // The LHS should now be Succ(minus n i) — not minus(Succ n, i)
    // Both sides should be identical (Equal X X pattern)
    expect(goalStr).toContain('Succ');
    expect(goalStr).toContain('Equal');
  });

  test('applied proof term includes context variable for Leq premise', () => {
    const defs = getDefinitions();
    const goalType = getDeclType('minusSucc');
    const engine = setupEngineWithIntros(goalType, defs, ['i', 'n', 'l']);
    const goal = engine.getFocusedGoal()!;
    const goalId = engine.getFocusedGoalId()!;

    const tactic = new RewriteTactic({ tag: 'Const', name: 'minusSucc' });
    const result = tactic.apply(engine, goal, goalId);

    expect(result.success).toBe(true);
    if (!result.success) return;

    // Check the proof term assigned to the original goal
    const solvedGoal = result.newEngine.metaVars.get(goalId);
    expect(solvedGoal?.solution).toBeDefined();

    // The proof should contain an application of minusSucc with all args
    const proofStr = termToString(solvedGoal!.solution!);
    expect(proofStr).toContain('minusSucc');
    // Should contain Var reference (the context variable for Leq premise)
    expect(proofStr).toContain('#');
  });

  test('rewrite fails gracefully when premise not in context', () => {
    const defs = getDefinitions();

    // Create a goal with minus (Succ n) i in it, but WITHOUT Leq in context
    // minusSucc type: {i n : Nat} -> Leq i n -> Equal (minus (Succ n) i) (Succ (minus n i))
    // Use individual IntroTactic calls to only introduce {i} and {n}, stopping before Leq
    const goalType = getDeclType('minusSucc');
    let engine = createInitialEngine(goalType, [], defs);

    // Intro {i}
    let goal = engine.getFocusedGoal()!;
    let goalId = engine.getFocusedGoalId()!;
    let introResult = new IntroTactic('i').apply(engine, goal, goalId);
    expect(introResult.success).toBe(true);
    if (!introResult.success) return;
    engine = introResult.newEngine;

    // Intro {n}
    goal = engine.getFocusedGoal()!;
    goalId = engine.getFocusedGoalId()!;
    introResult = new IntroTactic('n').apply(engine, goal, goalId);
    expect(introResult.success).toBe(true);
    if (!introResult.success) return;
    engine = introResult.newEngine;

    goal = engine.getFocusedGoal()!;
    goalId = engine.getFocusedGoalId()!;

    // Context has [i:Nat, n:Nat] — no Leq (the Leq binder is still in the goal type)
    expect(goal.ctx).toHaveLength(2);

    // Rewrite should not crash. The goal still has Leq as a Pi binder before Equal,
    // so the equality is nested inside. Rewrite may or may not find it.
    const tactic = new RewriteTactic({ tag: 'Const', name: 'minusSucc' });
    const result = tactic.apply(engine, goal, goalId);

    // Should not throw — either succeeds or returns error gracefully
    expect(typeof result.success).toBe('boolean');
  });

  test('premise search picks most recent matching hypothesis', () => {
    const defs = getDefinitions();

    // Compile a goal with TWO Leq hypotheses
    const source = BASE_SOURCE + `
testDoubleLeq : {i n : Nat} -> Leq i n -> Leq i n -> Equal (minus (Succ n) i) (Succ (minus n i))
testDoubleLeq l1 l2 = minusSucc l2
`;
    const compiled = compileTTFromText(source);
    const decl = compiled.blocks.flatMap(b => b.declarations).find(d => d.name === 'testDoubleLeq');
    expect(decl).toBeDefined();
    const goalType = decl!.kernelType!;

    const engine = setupEngineWithIntros(goalType, compiled.definitions, ['i', 'n', 'l1', 'l2']);
    const goal = engine.getFocusedGoal()!;
    const goalId = engine.getFocusedGoalId()!;

    expect(goal.ctx).toHaveLength(4);
    expect(goal.ctx[2].name).toBe('l1');
    expect(goal.ctx[3].name).toBe('l2');

    // Apply rewrite minusSucc — should pick l2 (most recent, at index 0 de Bruijn)
    const tactic = new RewriteTactic({ tag: 'Const', name: 'minusSucc' });
    const result = tactic.apply(engine, goal, goalId);

    expect(result.success).toBe(true);
    if (!result.success) return;

    // Verify the proof term uses Var(0) for l2 (most recent)
    const solvedGoal = result.newEngine.metaVars.get(goalId);
    const proofStr = termToString(solvedGoal!.solution!);
    // l2 is at de Bruijn index 0 (most recent in context of length 4)
    expect(proofStr).toContain('#0');
  });
});

describe('RewriteTactic: substitution precision (no over-matching)', () => {
  test('rewrite sumStartCountOne only replaces sumStartCount, not the surrounding mul', () => {
    const defs = getDefinitions();

    // Goal: Equal (mul (Succ (Succ Zero)) (sumStartCount Zero (Succ Zero) (\i => i)))
    //             (plus Zero (mul (Succ Zero) Zero))
    // After rewrite sumStartCountOne, sumStartCount(0, 1, \i=>i) -> (\i=>i)(0)
    // Expected new goal: Equal (mul (Succ (Succ Zero)) ((\i=>i)(Zero))) (plus Zero (mul (Succ Zero) Zero))
    // The mul wrapper and the RHS should NOT be replaced, even though they're
    // definitionally equal to the LHS after WHNF reduction.
    const source = BASE_SOURCE + `
testRwPrecision : Equal (mul (Succ (Succ Zero)) (sumStartCount Zero (Succ Zero) (\\i => i))) (plus Zero (mul (Succ Zero) Zero))
testRwPrecision = refl
`;
    const compiled = compileTTFromText(source);
    const decl = compiled.blocks.flatMap(b => b.declarations).find(d => d.name === 'testRwPrecision');
    expect(decl).toBeDefined();
    const goalType = decl!.kernelType!;

    // No intros needed — goal is already the equation
    const engine = createInitialEngine(goalType, [], defs);
    const goal = engine.getFocusedGoal()!;
    const goalId = engine.getFocusedGoalId()!;

    // Verify the goal has the expected structure
    const goalStr = termToString(goal.type);
    expect(goalStr).toContain('mul');
    expect(goalStr).toContain('sumStartCount');

    // Apply rewrite sumStartCountOne
    const tactic = new RewriteTactic({ tag: 'Const', name: 'sumStartCountOne' });
    const result = tactic.apply(engine, goal, goalId);

    expect(result.success).toBe(true);
    if (!result.success) return;

    const newGoal = result.newEngine.getFocusedGoal()!;
    const newGoalStr = termToString(newGoal.type);

    // The rewritten goal should still contain 'mul' — the rewrite should only
    // replace the sumStartCount subterm, not the entire mul expression.
    // BUG: termEqualModDefs uses WHNF comparison, so mul(2, sumStartCount(0,1,id))
    // and sumStartCount(0,1,id) both WHNF to Zero, causing the entire mul expr
    // to be replaced too.
    expect(newGoalStr).toContain('mul');
    // RHS should still contain 'plus' — it should NOT have been replaced
    expect(newGoalStr).toContain('plus');
  });
});

describe('RewriteTactic: mulZeroRight on concrete goal', () => {
  test('rewrite mulZeroRight makes progress on mul(2,0) = 0 + mul(1,0)', () => {
    const defs = getDefinitions();

    // Goal: Equal (mul (Succ (Succ Zero)) Zero) (plus Zero (mul (Succ Zero) Zero))
    // mulZeroRight : (n : Nat) -> Equal (mul n Zero) Zero
    // Should match mul(Succ(Succ Zero), Zero) and replace with Zero
    const source = BASE_SOURCE + `
testMulZero : Equal (mul (Succ (Succ Zero)) Zero) (plus Zero (mul (Succ Zero) Zero))
testMulZero = refl
`;
    const compiled = compileTTFromText(source);
    const decl = compiled.blocks.flatMap(b => b.declarations).find(d => d.name === 'testMulZero');
    expect(decl).toBeDefined();

    const engine = createInitialEngine(decl!.kernelType!, [], defs);
    const goal = engine.getFocusedGoal()!;
    const goalId = engine.getFocusedGoalId()!;

    const tactic = new RewriteTactic({ tag: 'Const', name: 'mulZeroRight' });
    const result = tactic.apply(engine, goal, goalId);

    expect(result.success).toBe(true);
    if (!result.success) return;

    const newGoal = result.newEngine.getFocusedGoal()!;
    const newGoalStr = termToString(newGoal.type);
    // After rewriting mul(Succ(Succ Zero), Zero) -> Zero,
    // goal should become Equal Zero (plus Zero (mul (Succ Zero) Zero))
    // or if it replaces both occurrences: Equal Zero (plus Zero Zero)
    expect(newGoalStr).toContain('Equal');
    expect(newGoalStr).toContain('Zero');
  });

  test('rewrite mulZeroRight works after rewrite sumStartCountOne (beta-redex in goal)', () => {
    const defs = getDefinitions();

    // After rewriting sumStartCountOne, the goal contains (\i => i)(Zero)
    // which is a beta-redex. mulZeroRight's pattern `mul ?n Zero` must still
    // match `mul (Succ (Succ Zero)) ((\i => i) Zero)` where the second arg
    // is a beta-redex, not a bare `Zero`.
    const source = BASE_SOURCE + `
testChainedRw : Equal (mul (Succ (Succ Zero)) (sumStartCount Zero (Succ Zero) (\\i => i))) (plus Zero (mul (Succ Zero) Zero))
testChainedRw = refl
`;
    const compiled = compileTTFromText(source);
    const decl = compiled.blocks.flatMap(b => b.declarations).find(d => d.name === 'testChainedRw');
    expect(decl).toBeDefined();

    let engine = createInitialEngine(decl!.kernelType!, [], defs);
    let goal = engine.getFocusedGoal()!;
    let goalId = engine.getFocusedGoalId()!;

    // Step 1: rewrite sumStartCountOne
    const rw1 = new RewriteTactic({ tag: 'Const', name: 'sumStartCountOne' });
    const res1 = rw1.apply(engine, goal, goalId);
    expect(res1.success).toBe(true);
    if (!res1.success) return;

    engine = res1.newEngine;
    goal = engine.getFocusedGoal()!;
    goalId = engine.getFocusedGoalId()!;

    // The goal now has (\i => i)(Zero) in place of sumStartCount(...)
    const midGoalStr = termToString(goal.type);
    expect(midGoalStr).toContain('mul');
    // Verify the beta-redex exists
    expect(midGoalStr).toContain('\\');  // lambda still present

    // Step 2: rewrite mulZeroRight — this should succeed despite the beta-redex
    const rw2 = new RewriteTactic({ tag: 'Const', name: 'mulZeroRight' });
    const res2 = rw2.apply(engine, goal, goalId);

    expect(res2.success).toBe(true);
    if (!res2.success) {
      console.error('mulZeroRight failed:', res2.error);
      return;
    }

    const finalGoal = res2.newEngine.getFocusedGoal()!;
    const finalGoalStr = termToString(finalGoal.type);
    // After mulZeroRight, mul(..., Zero) → Zero
    expect(finalGoalStr).toContain('Equal');
    expect(finalGoalStr).toContain('Zero');
  });
});

describe('betaNormalize: clean up lambda applications in goals', () => {
  test('betaNormalize reduces (\\i => i)(Zero) to Zero', () => {

    // (\i => i)(Zero) = App(Binder(BLam, "i", Nat, Var(0)), Const("Zero"))
    const term: TTKTerm = {
      tag: 'App',
      fn: {
        tag: 'Binder',
        binderKind: { tag: 'BLam' },
        name: 'i',
        domain: { tag: 'Const', name: 'Nat' },
        body: { tag: 'Var', index: 0 }
      },
      arg: { tag: 'Const', name: 'Zero' }
    };
    const result = betaNormalize(term);
    expect(result).toEqual({ tag: 'Const', name: 'Zero' });
  });

  test('betaNormalize reduces nested: mul(2, (\\i => i)(Zero)) keeps mul', () => {

    // mul (Succ (Succ Zero)) ((\i => i) Zero)
    const lambdaApp: TTKTerm = {
      tag: 'App',
      fn: {
        tag: 'Binder',
        binderKind: { tag: 'BLam' },
        name: 'i',
        domain: { tag: 'Const', name: 'Nat' },
        body: { tag: 'Var', index: 0 }
      },
      arg: { tag: 'Const', name: 'Zero' }
    };
    const term: TTKTerm = {
      tag: 'App',
      fn: {
        tag: 'App',
        fn: { tag: 'Const', name: 'mul' },
        arg: { tag: 'App', fn: { tag: 'Const', name: 'Succ' }, arg: { tag: 'App', fn: { tag: 'Const', name: 'Succ' }, arg: { tag: 'Const', name: 'Zero' } } }
      },
      arg: lambdaApp
    };
    const result = betaNormalize(term);
    const resultStr = termToString(result);
    // Should still have mul — only the lambda app was reduced
    expect(resultStr).toContain('mul');
    // The (\i => i)(Zero) part should be reduced to just Zero
    expect(resultStr).not.toContain('\\');
    expect(resultStr).toBe('((mul (Succ (Succ Zero))) Zero)');
  });

  test('betaNormalize leaves non-redex terms unchanged', () => {

    const term: TTKTerm = {
      tag: 'App',
      fn: { tag: 'Const', name: 'Succ' },
      arg: { tag: 'Const', name: 'Zero' }
    };
    const result = betaNormalize(term);
    // Should be reference-identical (no change)
    expect(result).toBe(term);
  });

  test('rewrite sumStartCountOne produces beta-normalized goal', () => {
    const defs = getDefinitions();
    const source = BASE_SOURCE + `
testRwBeta : Equal (mul (Succ (Succ Zero)) (sumStartCount Zero (Succ Zero) (\\i => i))) (plus Zero (mul (Succ Zero) Zero))
testRwBeta = refl
`;
    const compiled = compileTTFromText(source);
    const decl = compiled.blocks.flatMap(b => b.declarations).find(d => d.name === 'testRwBeta');
    expect(decl).toBeDefined();

    const engine = createInitialEngine(decl!.kernelType!, [], defs);
    const goal = engine.getFocusedGoal()!;
    const goalId = engine.getFocusedGoalId()!;

    const tactic = new RewriteTactic({ tag: 'Const', name: 'sumStartCountOne' });
    const result = tactic.apply(engine, goal, goalId);
    expect(result.success).toBe(true);
    if (!result.success) return;

    // Beta-normalize the rewritten goal

    const newGoal = result.newEngine.getFocusedGoal()!;
    const normalized = betaNormalize(newGoal.type);
    const normalizedStr = termToString(normalized);

    // After beta-normalization, (\i => i)(Zero) should be just Zero
    // So the goal should be: Equal (mul (Succ (Succ Zero)) Zero) (plus Zero (mul (Succ Zero) Zero))
    expect(normalizedStr).toContain('mul');
    expect(normalizedStr).toContain('plus');
    expect(normalizedStr).not.toContain('\\'); // no lambdas should remain
  });
});

// =============================================================================
// Helpers
// =============================================================================

function termToString(term: TTKTerm): string {
  switch (term.tag) {
    case 'Const': return term.name;
    case 'Var': return `#${term.index}`;
    case 'App': return `(${termToString(term.fn)} ${termToString(term.arg)})`;
    case 'Binder':
      if (term.binderKind.tag === 'BLam') return `(\\${term.name} => ${termToString(term.body)})`;
      return `(${term.name} : ${termToString(term.domain)}) -> ${termToString(term.body)}`;
    case 'Meta': return `?${term.id}`;
    case 'Hole': return `_${term.id}`;
    case 'Sort': return 'Type';
    case 'Match': return `match ${termToString(term.scrutinee)}`;
    default: return `<${term.tag}>`;
  }
}

describe('RewriteTactic: rewrite with context hypothesis (IH)', () => {
  test('rewrite Var(IH) works when IH is an equality in context', () => {
    const defs = getDefinitions();

    // Simulate: after induction on n for a theorem like
    // (n : Nat) -> Equal (plus n Zero) n
    // In the Succ case, context has [x0 : Nat, IH : Equal (plus x0 Zero) x0]
    // Goal: Equal (plus (Succ x0) Zero) (Succ x0)
    // which reduces to: Equal (Succ (plus x0 Zero)) (Succ x0)
    // Rewriting IH should replace (plus x0 Zero) with x0

    // Build the scenario: goal type = Equal (Succ (plus x0 Zero)) (Succ x0)
    // Context: [x0 : Nat, IH : Equal (plus x0 Zero) x0]
    const source = BASE_SOURCE + `
testIH : (n : Nat) -> Equal (plus n Zero) n
testIH n = testIH n
`;
    const compiled = compileTTFromText(source);
    const testIHType = compiled.blocks.flatMap(b => b.declarations).find(d => d.name === 'testIH')?.kernelType;
    if (!testIHType) throw new Error('testIH not found');

    // Use the InductionTactic approach: create context manually
    // x0 : Nat (index 0 in array)
    // IH : Equal (plus (Var 0) Zero) (Var 0)  -- Var(0) = x0 from IH's perspective
    const x0Entry = { name: 'x0', type: { tag: 'Const' as const, name: 'Nat' } };
    // IH type: Equal (plus x0 Zero) x0
    // In context position 1, x0 is at Var(0)
    const ihType: TTKTerm = {
      tag: 'App', fn: {
        tag: 'App', fn: {
          tag: 'App', fn: { tag: 'Const', name: 'Equal' },
          arg: { tag: 'Const', name: 'Nat' } // type arg
        },
        arg: { tag: 'App', fn: { tag: 'App', fn: { tag: 'Const', name: 'plus' }, arg: { tag: 'Var', index: 0 } }, arg: { tag: 'Const', name: 'Zero' } } // lhs: plus x0 Zero
      },
      arg: { tag: 'Var', index: 0 } // rhs: x0
    };
    const ihEntry = { name: 'IH', type: ihType };

    // Goal type: Equal (Succ (plus x0 Zero)) (Succ x0)
    // From goal's perspective: x0 is Var(1), IH is Var(0)
    const goalType: TTKTerm = {
      tag: 'App', fn: {
        tag: 'App', fn: {
          tag: 'App', fn: { tag: 'Const', name: 'Equal' },
          arg: { tag: 'Const', name: 'Nat' }
        },
        arg: { tag: 'App', fn: { tag: 'Const', name: 'Succ' }, arg: { tag: 'App', fn: { tag: 'App', fn: { tag: 'Const', name: 'plus' }, arg: { tag: 'Var', index: 1 } }, arg: { tag: 'Const', name: 'Zero' } } }
      },
      arg: { tag: 'App', fn: { tag: 'Const', name: 'Succ' }, arg: { tag: 'Var', index: 1 } }
    };

    const ctx = [x0Entry, ihEntry];
    const goalId = 'test_goal';
    const goal = { ctx, type: goalType, solution: undefined };
    const engine = createInitialEngine(goalType, [], compiled.definitions)
      .withUpdates({
        metaVars: new Map([['test_goal', goal]]),
        goals: ['test_goal'],
      });

    // Rewrite with IH (Var(0) in goal's context)
    const tactic = new RewriteTactic({ tag: 'Var', index: 0 });
    const result = tactic.apply(engine, goal as any, goalId);

    expect(result.success).toBe(true);
    if (!result.success) {
      console.error('Rewrite IH failed:', result.error);
      return;
    }

    const newGoal = result.newEngine.getFocusedGoal()!;
    const newGoalStr = termToString(newGoal.type);
    // After rewrite: plus x0 Zero -> x0, so goal becomes Equal (Succ x0) (Succ x0)
    expect(newGoalStr).not.toContain('plus');
    expect(newGoalStr).toContain('Succ');
  });
});

describe('RewriteTactic: rewrite IH after induction', () => {
  test('induction → unfold → rewrite IH in Succ case', async () => {
    const defs = getDefinitions();
    const goalType = getDeclType('plusZeroRight');

    // intros n → induction n → focus Succ case → unfold plus → rewrite IH
    let engine = setupEngineWithIntros(goalType, defs, ['n']);
    let goal = engine.getFocusedGoal()!;
    let goalId = engine.getFocusedGoalId()!;

    // Induction on n
    const { InductionTactic } = await import('./induction-tactic');
    const inductionResult = new InductionTactic({ tag: 'Var', index: 0 }).apply(engine, goal, goalId);
    expect(inductionResult.success).toBe(true);
    if (!inductionResult.success) return;
    engine = inductionResult.newEngine;

    // Focus Succ case (goal index 1)
    const succGoalId = engine.goals[1];
    const succGoal = engine.metaVars.get(succGoalId)!;
    expect(succGoal.ctx.some(e => e.name === 'IH')).toBe(true);
    engine = engine.withUpdates({ focusIndex: 1 });

    // Unfold plus — exposes Succ(plus(x0, Zero)) from plus(Succ(x0), Zero)
    const unfoldResult = new UnfoldTactic(['plus']).apply(engine, succGoal as any, succGoalId);
    expect(unfoldResult.success).toBe(true);
    if (!unfoldResult.success) return;
    engine = unfoldResult.newEngine;
    const postUnfoldGoal = engine.getFocusedGoal()!;
    const postUnfoldGoalId = engine.getFocusedGoalId()!;

    // Verify unfolded goal contains Succ(plus(x0, Zero))
    const unfoldedStr = termToString(postUnfoldGoal.type);
    expect(unfoldedStr).toContain('Succ');
    expect(unfoldedStr).toContain('plus');

    // Rewrite IH — replaces plus(x0, Zero) with x0
    const ihVarIndex = postUnfoldGoal.ctx.length - 1 - postUnfoldGoal.ctx.findIndex(e => e.name === 'IH');
    const rwResult = new RewriteTactic({ tag: 'Var', index: ihVarIndex }).apply(engine, postUnfoldGoal, postUnfoldGoalId);
    expect(rwResult.success).toBe(true);
    if (!rwResult.success) return;

    // After rewrite IH: goal should be Equal(Succ(x0), Succ(x0))
    const finalGoal = rwResult.newEngine.getFocusedGoal()!;
    const finalStr = termToString(finalGoal.type);
    expect(finalStr).not.toContain('plus');
    expect(finalStr).toContain('Succ');
  });
});

const SUMMATION_BASE_SOURCE = BASE_SOURCE + `
summationBase : (i : Nat) -> (f : Nat -> Nat) -> Equal (sum i i f) (f i)
summationBase i f = summationBase i f
`;

describe('summationBase chain: unfold sum, rewrite minusSucc, rewrite minusSelf, rewrite sumStartCountOne', () => {
  test('full chain succeeds on sum i i f = f i', () => {
    const compiled = compileTTFromText(SUMMATION_BASE_SOURCE);
    const defs = compiled.definitions;
    const summationBaseType = compiled.blocks.flatMap(b => b.declarations).find(d => d.name === 'summationBase')?.kernelType;
    if (!summationBaseType) throw new Error('summationBase not found');

    // Step 1: intros i f
    let engine = setupEngineWithIntros(summationBaseType, defs, ['i', 'f']);
    let goal = engine.getFocusedGoal()!;
    let goalId = engine.getFocusedGoalId()!;
    // Step 2: unfold sum
    const unfoldResult = new UnfoldTactic(['sum']).apply(engine, goal, goalId);
    if (!unfoldResult.success) throw new Error(`unfold failed: ${unfoldResult.error}`);
    engine = unfoldResult.newEngine;
    goal = engine.getFocusedGoal()!;
    goalId = engine.getFocusedGoalId()!;

    // Step 3: rewrite minusSucc
    const rwMinusSucc = new RewriteTactic(
      { tag: 'Const', name: 'minusSucc' },
    ).apply(engine, goal, goalId);
    if (!rwMinusSucc.success) throw new Error(`rewrite minusSucc failed: ${rwMinusSucc.error}`);
    engine = rwMinusSucc.newEngine;
    goal = engine.getFocusedGoal()!;
    goalId = engine.getFocusedGoalId()!;

    // Step 4: rewrite minusSelf
    const rwMinusSelf = new RewriteTactic(
      { tag: 'Const', name: 'minusSelf' },
    ).apply(engine, goal, goalId);
    if (!rwMinusSelf.success) throw new Error(`rewrite minusSelf failed: ${rwMinusSelf.error}`);
    engine = rwMinusSelf.newEngine;
    goal = engine.getFocusedGoal()!;
    goalId = engine.getFocusedGoalId()!;

    // Step 5: rewrite sumStartCountOne
    const rwSCO = new RewriteTactic(
      { tag: 'Const', name: 'sumStartCountOne' },
    ).apply(engine, goal, goalId);
    expect(rwSCO.success).toBe(true);
  });
});

describe('RewriteTactic: mulDistribRight on goal with mul(plus(...), ...)', () => {
  test('untargeted rewrite mulDistribRight rewrites RHS of equality', () => {
    const defs = getDefinitions();

    // Goal: Equal (mul (Succ (Succ Zero)) (plus X Y)) (mul (plus X (Succ Zero)) Y)
    // where X and Y are bound variables.
    // The RHS mul(plus(X, Succ Zero), Y) matches mulDistribRight's LHS mul(plus(n,m), p).
    const X: TTKTerm = { tag: 'Var', index: 1 };
    const Y: TTKTerm = { tag: 'Var', index: 0 };
    const SSZ: TTKTerm = { tag: 'App', fn: { tag: 'Const', name: 'Succ' }, arg: { tag: 'App', fn: { tag: 'Const', name: 'Succ' }, arg: { tag: 'Const', name: 'Zero' } } };
    const SZ: TTKTerm = { tag: 'App', fn: { tag: 'Const', name: 'Succ' }, arg: { tag: 'Const', name: 'Zero' } };

    const goalType: TTKTerm = {
      tag: 'App', fn: {
        tag: 'App', fn: {
          tag: 'App', fn: { tag: 'Const', name: 'Equal' },
          arg: { tag: 'Const', name: 'Nat' }
        },
        // LHS: mul(2, plus(X, Y))
        arg: { tag: 'App', fn: { tag: 'App', fn: { tag: 'Const', name: 'mul' }, arg: SSZ }, arg: { tag: 'App', fn: { tag: 'App', fn: { tag: 'Const', name: 'plus' }, arg: X }, arg: Y } }
      },
      // RHS: mul(plus(X, 1), Y)
      arg: { tag: 'App', fn: { tag: 'App', fn: { tag: 'Const', name: 'mul' }, arg: { tag: 'App', fn: { tag: 'App', fn: { tag: 'Const', name: 'plus' }, arg: X }, arg: SZ } }, arg: Y }
    };

    const ctx = [
      { name: 'x', type: { tag: 'Const' as const, name: 'Nat' } },
      { name: 'y', type: { tag: 'Const' as const, name: 'Nat' } },
    ];
    const goalId = 'test_distrib_goal';
    const goal = { ctx, type: goalType, solution: undefined };
    const engine = createInitialEngine(goalType, [], defs)
      .withUpdates({
        metaVars: new Map([[goalId, goal]]),
        goals: [goalId],
      });

    // Untargeted rewrite mulDistribRight (no occurrences specified)
    const tactic = new RewriteTactic({ tag: 'Const', name: 'mulDistribRight' });
    const result = tactic.apply(engine, goal as any, goalId);

    expect(result.success).toBe(true);
    if (!result.success) {
      console.error('mulDistribRight rewrite failed:', result.error);
      return;
    }

    // The RHS mul(plus(X, 1), Y) should be replaced with plus(mul(X, Y), mul(1, Y))
    const newGoal = result.newEngine.getFocusedGoal()!;
    const newGoalStr = termToString(newGoal.type);
    // The rewritten part should now contain 'plus' wrapping two 'mul' terms
    expect(newGoalStr).toContain('plus');
  });

  test('targeted rewrite mulDistribRight at occurrence 2 rewrites correct subterm', () => {
    const defs = getDefinitions();

    const X: TTKTerm = { tag: 'Var', index: 1 };
    const Y: TTKTerm = { tag: 'Var', index: 0 };
    const SSZ: TTKTerm = { tag: 'App', fn: { tag: 'Const', name: 'Succ' }, arg: { tag: 'App', fn: { tag: 'Const', name: 'Succ' }, arg: { tag: 'Const', name: 'Zero' } } };
    const SZ: TTKTerm = { tag: 'App', fn: { tag: 'Const', name: 'Succ' }, arg: { tag: 'Const', name: 'Zero' } };

    // Goal: Equal(Nat, mul(2, plus(x, y)), mul(plus(x, 1), y))
    const goalType: TTKTerm = {
      tag: 'App', fn: {
        tag: 'App', fn: {
          tag: 'App', fn: { tag: 'Const', name: 'Equal' },
          arg: { tag: 'Const', name: 'Nat' }
        },
        arg: { tag: 'App', fn: { tag: 'App', fn: { tag: 'Const', name: 'mul' }, arg: SSZ }, arg: { tag: 'App', fn: { tag: 'App', fn: { tag: 'Const', name: 'plus' }, arg: X }, arg: Y } }
      },
      arg: { tag: 'App', fn: { tag: 'App', fn: { tag: 'Const', name: 'mul' }, arg: { tag: 'App', fn: { tag: 'App', fn: { tag: 'Const', name: 'plus' }, arg: X }, arg: SZ } }, arg: Y }
    };

    const ctx = [
      { name: 'x', type: { tag: 'Const' as const, name: 'Nat' } },
      { name: 'y', type: { tag: 'Const' as const, name: 'Nat' } },
    ];
    const goalId = 'test_distrib_goal2';
    const goal = { ctx, type: goalType, solution: undefined };
    const engine = createInitialEngine(goalType, [], defs)
      .withUpdates({
        metaVars: new Map([[goalId, goal]]),
        goals: [goalId],
      });

    // With head-based occurrence counting, occurrence 2 targets the second mul-headed App:
    // mul(2, plus(x,y)) is occurrence 1, mul(plus(x,1), y) is occurrence 2.
    // mulDistribRight's LHS = mul(plus(?n, ?m), ?p) matches occurrence 2.
    // Result: mul(plus(x, 1), y) → plus(mul(x, y), mul(1, y))
    const tactic = new RewriteTactic(
      { tag: 'Const', name: 'mulDistribRight' },
      { occurrences: [2] }
    );
    const result = tactic.apply(engine, goal as any, goalId);
    expect(result.success).toBe(true);
    if (!result.success) return;

    // LHS of Equal should be untouched: mul(2, plus(x, y))
    const newGoal = result.newEngine.getFocusedGoal()!;
    const newGoalStr = termToString(newGoal.type);
    // RHS should now contain plus wrapping two mul terms
    expect(newGoalStr).toContain('plus');
  });
});

describe('RewriteTactic: mulComm on goal with mul(2, x)', () => {
  test('untargeted rewrite mulComm swaps mul arguments', () => {
    const compiled = getCompiled();
    const defs = compiled.definitions;

    // Goal: Equal (mul (Succ (Succ Zero)) X) (something)
    // mulComm : (n m : Nat) -> Equal (mul n m) (mul m n)
    // Should rewrite mul(2, X) to mul(X, 2)
    const X: TTKTerm = { tag: 'Var', index: 0 };
    const two: TTKTerm = { tag: 'App', fn: { tag: 'Const', name: 'Succ' }, arg: { tag: 'App', fn: { tag: 'Const', name: 'Succ' }, arg: { tag: 'Const', name: 'Zero' } } };
    const mulTwoX: TTKTerm = { tag: 'App', fn: { tag: 'App', fn: { tag: 'Const', name: 'mul' }, arg: two }, arg: X };
    const mulXTwo: TTKTerm = { tag: 'App', fn: { tag: 'App', fn: { tag: 'Const', name: 'mul' }, arg: X }, arg: two };
    const goalType: TTKTerm = {
      tag: 'App', fn: { tag: 'App', fn: { tag: 'App', fn: { tag: 'Const', name: 'Equal' },
        arg: { tag: 'Const', name: 'Nat' } }, arg: mulTwoX }, arg: mulXTwo
    };

    const engine = createInitialEngine(goalType, [{ name: 'X', type: { tag: 'Const', name: 'Nat' } }], defs);
    const goal = engine.getFocusedGoal()!;
    const goalId = engine.getFocusedGoalId()!;

    const tactic = new RewriteTactic({ tag: 'Const', name: 'mulComm' });
    const result = tactic.apply(engine, goal, goalId);
    expect(result.success).toBe(true);
  });

  test('mulComm skips no-op first match (mul(x,x)) and rewrites mul(2,x)', () => {
    const compiled = getCompiled();
    const defs = compiled.definitions;

    // Goal: Equal (plus (mul X X) (mul 2 X)) something
    // First mul match is mul(X,X) — mulComm produces mul(X,X), a no-op.
    // Second mul match is mul(2,X) — mulComm produces mul(X,2), non-trivial.
    const X: TTKTerm = { tag: 'Var', index: 0 };
    const two: TTKTerm = { tag: 'App', fn: { tag: 'Const', name: 'Succ' }, arg: { tag: 'App', fn: { tag: 'Const', name: 'Succ' }, arg: { tag: 'Const', name: 'Zero' } } };
    const mulXX: TTKTerm = { tag: 'App', fn: { tag: 'App', fn: { tag: 'Const', name: 'mul' }, arg: X }, arg: X };
    const mulTwoX: TTKTerm = { tag: 'App', fn: { tag: 'App', fn: { tag: 'Const', name: 'mul' }, arg: two }, arg: X };
    const lhs: TTKTerm = { tag: 'App', fn: { tag: 'App', fn: { tag: 'Const', name: 'plus' }, arg: mulXX }, arg: mulTwoX };
    const goalType: TTKTerm = {
      tag: 'App', fn: { tag: 'App', fn: { tag: 'App', fn: { tag: 'Const', name: 'Equal' },
        arg: { tag: 'Const', name: 'Nat' } }, arg: lhs }, arg: { tag: 'Const', name: 'Zero' }
    };

    const engine = createInitialEngine(goalType, [{ name: 'X', type: { tag: 'Const', name: 'Nat' } }], defs);
    const goal = engine.getFocusedGoal()!;
    const goalId = engine.getFocusedGoalId()!;

    const tactic = new RewriteTactic({ tag: 'Const', name: 'mulComm' });
    const result = tactic.apply(engine, goal, goalId);
    // Should succeed by skipping the no-op mul(X,X) match and rewriting mul(2,X) → mul(X,2)
    expect(result.success).toBe(true);
  });
});

describe('UnfoldTactic: targeted occurrence', () => {
  test('unfold mul at occurrence 2 only unfolds that site', () => {
    const compiled = getCompiled();
    const defs = compiled.definitions;

    // Goal: Equal (mul X X) (mul (Succ (Succ Zero)) X)
    // Occurrence 1 = mul X X, Occurrence 2 = mul 2 X
    const X: TTKTerm = { tag: 'Var', index: 0 };
    const two: TTKTerm = { tag: 'App', fn: { tag: 'Const', name: 'Succ' }, arg: { tag: 'App', fn: { tag: 'Const', name: 'Succ' }, arg: { tag: 'Const', name: 'Zero' } } };
    const mulXX: TTKTerm = { tag: 'App', fn: { tag: 'App', fn: { tag: 'Const', name: 'mul' }, arg: X }, arg: X };
    const mulTwoX: TTKTerm = { tag: 'App', fn: { tag: 'App', fn: { tag: 'Const', name: 'mul' }, arg: two }, arg: X };
    const goalType: TTKTerm = {
      tag: 'App', fn: { tag: 'App', fn: { tag: 'App', fn: { tag: 'Const', name: 'Equal' },
        arg: { tag: 'Const', name: 'Nat' } }, arg: mulXX }, arg: mulTwoX
    };

    const engine = createInitialEngine(goalType, [{ name: 'X', type: { tag: 'Const', name: 'Nat' } }], defs);
    const goal = engine.getFocusedGoal()!;
    const goalId = engine.getFocusedGoalId()!;

    // Unfold mul at occurrence 2 (1-based) — should only unfold mul(2, X)
    const tactic = new UnfoldTactic(['mul'], 2);
    const result = tactic.apply(engine, goal, goalId);
    expect(result.success).toBe(true);
    if (!result.success) return;

    // The result should still contain Const("mul") for the first occurrence (mul X X)
    const newGoal = result.newEngine.getFocusedGoal()!;
    const newType = newGoal.type;
    // LHS of Equal should still be mul(X, X) — check that Const("mul") is still there
    // The newType is Equal(Nat, lhs, rhs) — lhs is the third arg from the end
    function getEqualLhs(t: TTKTerm): TTKTerm {
      // Equal A lhs rhs → App(App(App(Const("Equal"), A), lhs), rhs)
      if (t.tag === 'App' && t.fn.tag === 'App') return t.fn.arg;
      throw new Error('not Equal app');
    }
    const lhs = getEqualLhs(newType);
    // lhs should still contain Const("mul") — it was NOT unfolded
    function containsConst(t: TTKTerm, name: string): boolean {
      if (t.tag === 'Const') return t.name === name;
      if (t.tag === 'App') return containsConst(t.fn, name) || containsConst(t.arg, name);
      if (t.tag === 'Binder') return containsConst(t.domain, name) || containsConst(t.body, name);
      return false;
    }
    expect(containsConst(lhs, 'mul')).toBe(true);

    // RHS should NOT contain Const("mul") at the top level — it was unfolded and reduced
    function getEqualRhs(t: TTKTerm): TTKTerm {
      if (t.tag === 'App') return t.arg;
      throw new Error('not Equal app');
    }
    const rhs = getEqualRhs(newType);
    console.log('RHS after targeted unfold:', JSON.stringify(rhs).substring(0, 300));
    // The RHS should be: plus(X, mul(Succ Zero, X)) — beta+iota reduced
    // It should contain 'plus' as head
    function getAppHead(t: TTKTerm): string | null {
      let cur = t;
      while (cur.tag === 'App') cur = cur.fn;
      return cur.tag === 'Const' ? cur.name : null;
    }
    expect(getAppHead(rhs)).toBe('plus');
  });
});

const TRIANGLE_SUM_SOURCE = BASE_SOURCE + `
postulate triangleSum : (n : Nat) -> Equal (mul (Succ (Succ Zero)) (sum Zero n (\\i => i))) (mul (plus n (Succ n)) n)
`;

describe('triangleSum: induction + rewrite IH', () => {
  test('Succ case after induction: IH LHS differs from goal (sum bound is Succ(x0) vs x0)', async () => {
    const compiled = compileTTFromText(TRIANGLE_SUM_SOURCE);
    expect(compiled.success).toBe(true);
    const defs = compiled.definitions;
    const tsType = compiled.blocks.flatMap(b => b.declarations).find(d => d.name === 'triangleSum')?.kernelType;
    if (!tsType) throw new Error('triangleSum not found');

    let engine = setupEngineWithIntros(tsType, defs, ['n']);
    let goal = engine.getFocusedGoal()!;
    let goalId = engine.getFocusedGoalId()!;

    const { InductionTactic } = await import('./induction-tactic');
    const inductionResult = new InductionTactic({ tag: 'Var', index: 0 }).apply(engine, goal, goalId);
    expect(inductionResult.success).toBe(true);
    if (!inductionResult.success) return;
    engine = inductionResult.newEngine;

    // Focus Succ case
    const succGoalId = engine.goals[1];
    const succGoal = engine.metaVars.get(succGoalId)!;
    expect(succGoal.ctx.some(e => e.name === 'IH')).toBe(true);
    engine = engine.withUpdates({ focusIndex: 1 });

    // Goal has sum(Zero, Succ(x0), ...) but IH has sum(Zero, x0, ...)
    // So rewrite IH correctly fails — summationSplit is needed first.
    const ihIdx = succGoal.ctx.length - 1 - succGoal.ctx.findIndex(e => e.name === 'IH');
    const rwResult = new RewriteTactic({ tag: 'Var', index: ihIdx }).apply(
      engine, succGoal as any, succGoalId
    );
    expect(rwResult.success).toBe(false);
    if (!rwResult.success) {
      expect(rwResult.error).toContain('no occurrences');
    }
  });
});

describe('RewriteTactic: post-order (bottom-up) occurrence counting', () => {
  // The surface annotator assigns occurrence indices BOTTOM-UP (inside-out):
  // children are rendered/annotated before parents in ttermToMathNodes.
  // So for plus(plus(a,b), c): innermost plus(a,b) = occ 1, outermost = occ 2.
  // The substitute function must count in the same order.

  test('left-associative chain: occurrence 2 targets outermost plus', () => {
    // Goal: Equal(Nat, plus(plus(a, b), c), d)
    // Surface rendering: (a + b) + c = d
    // Surface occurrences: plus(a,b) = occ 1, plus(plus(a,b), c) = occ 2
    // plusComm at occ 2 should swap outermost: plus(plus(a,b), c) → plus(c, plus(a,b))
    const compiled = getCompiled();
    const defs = compiled.definitions;

    const a: TTKTerm = { tag: 'Var', index: 3 };
    const b: TTKTerm = { tag: 'Var', index: 2 };
    const c: TTKTerm = { tag: 'Var', index: 1 };
    const d: TTKTerm = { tag: 'Var', index: 0 };
    const plusAB: TTKTerm = { tag: 'App', fn: { tag: 'App', fn: { tag: 'Const', name: 'plus' }, arg: a }, arg: b };
    const plusABC: TTKTerm = { tag: 'App', fn: { tag: 'App', fn: { tag: 'Const', name: 'plus' }, arg: plusAB }, arg: c };
    const goalType: TTKTerm = {
      tag: 'App', fn: { tag: 'App', fn: { tag: 'App', fn: { tag: 'Const', name: 'Equal' },
        arg: { tag: 'Const', name: 'Nat' } }, arg: plusABC }, arg: d
    };

    const ctx = [
      { name: 'a', type: { tag: 'Const' as const, name: 'Nat' } },
      { name: 'b', type: { tag: 'Const' as const, name: 'Nat' } },
      { name: 'c', type: { tag: 'Const' as const, name: 'Nat' } },
      { name: 'd', type: { tag: 'Const' as const, name: 'Nat' } },
    ];
    const engine = createInitialEngine(goalType, ctx, defs);
    const goal = engine.getFocusedGoal()!;
    const goalId = engine.getFocusedGoalId()!;

    // plusComm at occurrence 2 = the outermost plus (bottom-up counting)
    const tactic = new RewriteTactic(
      { tag: 'Const', name: 'mulComm' },  // mulComm matches any mul, but we want plusComm...
      { reverse: false, occurrences: [2] }
    );
    // Actually we don't have plusComm in our test source. Let's use a direct substitute test instead.
    // We can test the substitute method indirectly by checking that plusAssoc at occ 2
    // targets the outermost plus.

    // Better approach: use mulComm on a goal with nested mul applications.
    // Goal: Equal(Nat, mul(mul(a, b), c), d)
    const mulAB: TTKTerm = { tag: 'App', fn: { tag: 'App', fn: { tag: 'Const', name: 'mul' }, arg: a }, arg: b };
    const mulABC: TTKTerm = { tag: 'App', fn: { tag: 'App', fn: { tag: 'Const', name: 'mul' }, arg: mulAB }, arg: c };
    const goalType2: TTKTerm = {
      tag: 'App', fn: { tag: 'App', fn: { tag: 'App', fn: { tag: 'Const', name: 'Equal' },
        arg: { tag: 'Const', name: 'Nat' } }, arg: mulABC }, arg: d
    };

    const engine2 = createInitialEngine(goalType2, ctx, defs);
    const goal2 = engine2.getFocusedGoal()!;
    const goalId2 = engine2.getFocusedGoalId()!;

    // mulComm at occurrence 1 should target innermost mul(a, b) → mul(b, a)
    const tactic1 = new RewriteTactic(
      { tag: 'Const', name: 'mulComm' },
      { reverse: false, occurrences: [1] }
    );
    const result1 = tactic1.apply(engine2, goal2, goalId2);
    expect(result1.success).toBe(true);
    if (result1.success) {
      const newGoal1 = result1.newEngine.getFocusedGoal()!;
      // LHS of Equal should now be mul(mul(b, a), c) — inner mul swapped
      const lhs1 = newGoal1.type.tag === 'App' && newGoal1.type.fn.tag === 'App'
        ? newGoal1.type.fn.arg : null;
      expect(lhs1).not.toBeNull();
      // The inner mul's first arg should now be b (Var 2), not a (Var 3)
      if (lhs1 && lhs1.tag === 'App' && lhs1.fn.tag === 'App') {
        const innerMul = lhs1.fn.arg; // first arg of outer mul = inner mul
        if (innerMul.tag === 'App' && innerMul.fn.tag === 'App') {
          expect(innerMul.fn.arg).toEqual(b); // first arg of inner mul = b (was a)
          expect(innerMul.arg).toEqual(a);    // second arg of inner mul = a (was b)
        }
      }
    }

    // mulComm at occurrence 2 should target outermost mul(mul(a,b), c) → mul(c, mul(a,b))
    const tactic2 = new RewriteTactic(
      { tag: 'Const', name: 'mulComm' },
      { reverse: false, occurrences: [2] }
    );
    const result2 = tactic2.apply(engine2, goal2, goalId2);
    expect(result2.success).toBe(true);
    if (result2.success) {
      const newGoal2 = result2.newEngine.getFocusedGoal()!;
      // LHS of Equal should now be mul(c, mul(a, b)) — outer mul swapped
      const lhs2 = newGoal2.type.tag === 'App' && newGoal2.type.fn.tag === 'App'
        ? newGoal2.type.fn.arg : null;
      expect(lhs2).not.toBeNull();
      if (lhs2 && lhs2.tag === 'App' && lhs2.fn.tag === 'App') {
        // First arg of outer mul should now be c (Var 1)
        expect(lhs2.fn.arg).toEqual(c);
        // Second arg should be mul(a, b)
        expect(lhs2.arg).toEqual(mulAB);
      }
    }
  });

  test('occurrence targets correct subterm when some mul apps dont match LHS', () => {
    // Goal: Equal(Nat, mul(2, a), mul(1, a))
    // Surface sees: mul occ 1 = mul(2, a), mul occ 2 = mul(1, a)
    // mulOneLeft LHS = mul(Succ Zero, ?x), only matches mul(1, a)
    // With head-based counting, occurrence 2 should correctly target mul(1, a)
    const compiled = getCompiled();
    const defs = compiled.definitions;

    const one: TTKTerm = { tag: 'App', fn: { tag: 'Const', name: 'Succ' }, arg: { tag: 'Const', name: 'Zero' } };
    const two: TTKTerm = { tag: 'App', fn: { tag: 'Const', name: 'Succ' }, arg: one };
    const a: TTKTerm = { tag: 'Var', index: 0 };
    const mulTwoA: TTKTerm = { tag: 'App', fn: { tag: 'App', fn: { tag: 'Const', name: 'mul' }, arg: two }, arg: a };
    const mulOneA: TTKTerm = { tag: 'App', fn: { tag: 'App', fn: { tag: 'Const', name: 'mul' }, arg: one }, arg: a };
    // Equal(Nat, mul(2, a), mul(1, a))
    const goalType: TTKTerm = {
      tag: 'App', fn: { tag: 'App', fn: { tag: 'App', fn: { tag: 'Const', name: 'Equal' },
        arg: { tag: 'Const', name: 'Nat' } }, arg: mulTwoA }, arg: mulOneA
    };

    const engine = createInitialEngine(goalType, [{ name: 'a', type: { tag: 'Const', name: 'Nat' } }], defs);
    const goal = engine.getFocusedGoal()!;
    const goalId = engine.getFocusedGoalId()!;

    // plusZeroRight : (n : Nat) -> Equal (plus n Zero) n
    // Use this at occurrence 2 — should target mul(1, a) = the second 'mul' on the surface.
    // mul(1, a) computes to plus(a, mul(Zero, a)) = plus(a, Zero) ... but
    // plusZeroRight's LHS is plus(?n, Zero), which only matches plus-headed subterms, not mul.
    // Instead, let's test with mulComm which matches any mul(?,?).

    // mulComm : (n m) -> Equal (mul n m) (mul m n)
    // Surface occ 1 = mul(2, a), Surface occ 2 = mul(1, a)
    // Both match mulComm's LHS = mul(?n, ?m)
    // Occurrence [2] should rewrite mul(1, a) → mul(a, 1), leaving mul(2, a) untouched.
    const tactic = new RewriteTactic(
      { tag: 'Const', name: 'mulComm' },
      { reverse: false, occurrences: [2] }
    );
    const result = tactic.apply(engine, goal, goalId);
    expect(result.success).toBe(true);
    if (!result.success) return;

    const newGoal = result.newEngine.getFocusedGoal()!;
    // New goal RHS should be mul(a, Succ Zero) — the args swapped
    // Equal(Nat, mul(2, a), mul(a, 1))
    // RHS = last arg of Equal app
    const rhs = newGoal.type.tag === 'App' ? newGoal.type.arg : null;
    expect(rhs).not.toBeNull();
    // RHS head should still be 'mul'
    let rhsHead = rhs;
    while (rhsHead && rhsHead.tag === 'App') rhsHead = rhsHead.fn;
    expect(rhsHead?.tag).toBe('Const');
    expect((rhsHead as any)?.name).toBe('mul');
    // RHS first arg should be the variable 'a' (Var 0), not Succ(Zero)
    // mul(a, 1) = App(App(Const("mul"), Var(0)), Succ(Zero))
    if (rhs && rhs.tag === 'App' && rhs.fn.tag === 'App') {
      expect(rhs.fn.arg).toEqual(a); // first arg = a (was Succ Zero before swap)
    }

    // LHS should still be mul(2, a) — untouched
    const lhsOfEq = newGoal.type.tag === 'App' && newGoal.type.fn.tag === 'App'
      ? newGoal.type.fn.arg : null;
    expect(lhsOfEq).toEqual(mulTwoA);
  });
});

// =============================================================================
// Tests for rewriting with premise-carrying lemmas (like plusCancelLeft)
// =============================================================================

describe('RewriteTactic with premise-carrying lemmas', () => {
  test('rewrite plusCancelLeft cancels common plus prefix', () => {
    // Goal: Equal (plus a b) (plus a c) → should become Equal b c
    // plusCancelLeft : {a b c : Nat} -> Equal (plus a b) (plus a c) -> Equal b c
    const definitions = getDefinitions();
    const Nat: TTKTerm = { tag: 'Const', name: 'Nat' };
    const a: TTKTerm = { tag: 'Var', index: 2 };
    const b: TTKTerm = { tag: 'Var', index: 1 };
    const c: TTKTerm = { tag: 'Var', index: 0 };
    const plusAB: TTKTerm = { tag: 'App', fn: { tag: 'App', fn: { tag: 'Const', name: 'plus' }, arg: a }, arg: b };
    const plusAC: TTKTerm = { tag: 'App', fn: { tag: 'App', fn: { tag: 'Const', name: 'plus' }, arg: a }, arg: c };

    // Equal (plus a b) (plus a c)
    const goalType: TTKTerm = {
      tag: 'App',
      fn: { tag: 'App', fn: { tag: 'App', fn: { tag: 'Const', name: 'Equal' }, arg: Nat }, arg: plusAB },
      arg: plusAC
    };

    const ctx = [
      { name: 'a', type: Nat },
      { name: 'b', type: Nat },
      { name: 'c', type: Nat },
    ];

    const engine = createInitialEngine(goalType, ctx, definitions);
    const goal = engine.getFocusedGoal()!;
    const goalId = engine.getFocusedGoalId()!;

    const result = new RewriteTactic(
      { tag: 'Const', name: 'plusCancelLeft' },
      { enhanced: true }
    ).apply(engine, goal, goalId);

    // Should succeed and produce a goal without 'plus'
    if (!result.success) {
      throw new Error(`rewrite plusCancelLeft failed: ${result.error}`);
    }

    // Get the new goal from the new engine
    const newEngine = result.newEngine;
    const newGoalId = newEngine.goals[newEngine.focusIndex];
    const newGoal = newEngine.metaVars.get(newGoalId);
    expect(newGoal).toBeDefined();
    if (!newGoal) return;

    // Verify the new goal is Equal Nat b c — the 'plus a' prefix should be cancelled.
    // Expected structure: App(App(App(Const("Equal"), Const("Nat")), Var(1)), Var(0))
    const newType = newGoal.type;
    expect(newType.tag).toBe('App'); // Equal _ _ c
    const equalBC = newType as any;
    expect(equalBC.arg).toEqual(c); // c = Var(0)
    expect(equalBC.fn.tag).toBe('App'); // Equal _ b
    expect(equalBC.fn.arg).toEqual(b); // b = Var(1)
    expect(equalBC.fn.fn.tag).toBe('App'); // Equal Nat
    expect(equalBC.fn.fn.fn).toEqual({ tag: 'Const', name: 'Equal' });
    expect(equalBC.fn.fn.arg).toEqual(Nat);
  });
});
