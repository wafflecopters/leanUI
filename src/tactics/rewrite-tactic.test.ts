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
