/**
 * Unit tests for FoldTactic — the inverse of unfold.
 */

import { describe, test, expect, beforeEach } from 'vitest';
import { TTKTerm } from '../compiler/kernel';
import { compileTTFromText } from '../compiler/compile';
import { createInitialEngine, TacticEngine } from './tacticsEngine';
import { resetMetaCounter } from './tactic';
import { FoldTactic, ttkTermsEqual } from './fold-tactic';
import { UnfoldTactic } from './unfold-tactic';
import { DefinitionsMap } from '../compiler/term';

beforeEach(() => {
  resetMetaCounter();
});

const BASE_SOURCE = `inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat
inductive Equal : {A : Type} -> A -> A -> Type where
  refl : {A : Type} -> {a : A} -> Equal a a
two : Nat
two = Succ (Succ Zero)
three : Nat
three = Succ (Succ (Succ Zero))
myZero : Nat
myZero = Zero
plus : Nat -> Nat -> Nat
plus Zero n = n
plus (Succ m) n = Succ (plus m n)
`;

let _compiled: ReturnType<typeof compileTTFromText> | null = null;
function getCompiled() {
  if (!_compiled) {
    _compiled = compileTTFromText(BASE_SOURCE);
    if (!_compiled.success) {
      throw new Error(`Base compilation failed`);
    }
  }
  return _compiled;
}

function getDefinitions(): DefinitionsMap {
  return getCompiled().definitions;
}

function createEngine(goalType: TTKTerm, defs?: DefinitionsMap): TacticEngine {
  return createInitialEngine(goalType, [], defs ?? getDefinitions());
}

/** Build Equal(A, lhs, rhs) as a kernel term */
function mkEqual(lhs: TTKTerm, rhs: TTKTerm): TTKTerm {
  const nat: TTKTerm = { tag: 'Const', name: 'Nat' };
  let term: TTKTerm = { tag: 'Const', name: 'Equal' };
  term = { tag: 'App', fn: term, arg: nat };
  term = { tag: 'App', fn: term, arg: lhs };
  term = { tag: 'App', fn: term, arg: rhs };
  return term;
}

const ZERO: TTKTerm = { tag: 'Const', name: 'Zero' };
const SUCC = (x: TTKTerm): TTKTerm => ({ tag: 'App', fn: { tag: 'Const', name: 'Succ' }, arg: x });
const TWO_BODY = SUCC(SUCC(ZERO));

describe('ttkTermsEqual', () => {
  test('structurally equal terms', () => {
    expect(ttkTermsEqual(TWO_BODY, SUCC(SUCC(ZERO)))).toBe(true);
  });

  test('different terms', () => {
    expect(ttkTermsEqual(ZERO, SUCC(ZERO))).toBe(false);
  });

  test('same reference', () => {
    expect(ttkTermsEqual(ZERO, ZERO)).toBe(true);
  });
});

describe('FoldTactic', () => {
  test('fold two: replaces Succ(Succ(Zero)) with Const("two")', () => {
    const defs = getDefinitions();
    const goalType = mkEqual(TWO_BODY, TWO_BODY);
    const engine = createEngine(goalType, defs);
    const goal = engine.getFocusedGoal()!;
    const goalId = engine.getFocusedGoalId()!;

    const tactic = new FoldTactic(['two']);
    const result = tactic.apply(engine, goal, goalId);
    if (!result.success) throw new Error(result.error);

    const newGoal = result.newEngine.getFocusedGoal()!;
    expect(containsConst(newGoal.type, 'two')).toBe(true);
    expect(containsPattern(newGoal.type, TWO_BODY)).toBe(false);
  });

  test('fold fails when body not found in goal', () => {
    const defs = getDefinitions();
    const goalType = mkEqual(ZERO, ZERO);
    const engine = createEngine(goalType, defs);
    const goal = engine.getFocusedGoal()!;
    const goalId = engine.getFocusedGoalId()!;

    const tactic = new FoldTactic(['two']);
    const result = tactic.apply(engine, goal, goalId);
    expect(result.success).toBe(false);
    if (!result.success) {
      expect(result.error).toContain('no occurrences');
    }
  });

  test('fold with nonexistent definition', () => {
    const defs = getDefinitions();
    const goalType = mkEqual(ZERO, ZERO);
    const engine = createEngine(goalType, defs);
    const goal = engine.getFocusedGoal()!;
    const goalId = engine.getFocusedGoalId()!;

    const tactic = new FoldTactic(['nonexistent']);
    const result = tactic.apply(engine, goal, goalId);
    expect(result.success).toBe(false);
    if (!result.success) {
      expect(result.error).toContain('no definition');
    }
  });

  test('targeted fold at occurrence 1 only replaces first match', () => {
    const defs = getDefinitions();
    const goalType = mkEqual(TWO_BODY, TWO_BODY);
    const engine = createEngine(goalType, defs);
    const goal = engine.getFocusedGoal()!;
    const goalId = engine.getFocusedGoalId()!;

    const tactic = new FoldTactic(['two'], 1);
    const result = tactic.apply(engine, goal, goalId);
    if (!result.success) throw new Error(result.error);

    const newGoal = result.newEngine.getFocusedGoal()!;
    expect(containsConst(newGoal.type, 'two')).toBe(true);
    expect(containsPattern(newGoal.type, TWO_BODY)).toBe(true);
  });

  test('unfold then fold round-trips', () => {
    const defs = getDefinitions();
    const two: TTKTerm = { tag: 'Const', name: 'two' };
    const goalType = mkEqual(two, two);
    const engine = createEngine(goalType, defs);
    const goal = engine.getFocusedGoal()!;
    const goalId = engine.getFocusedGoalId()!;

    // Unfold
    const unfoldResult = new UnfoldTactic(['two']).apply(engine, goal, goalId);
    if (!unfoldResult.success) throw new Error('unfold failed');
    const unfoldedGoal = unfoldResult.newEngine.getFocusedGoal()!;
    const unfoldedGoalId = unfoldResult.newEngine.getFocusedGoalId()!;
    expect(containsConst(unfoldedGoal.type, 'two')).toBe(false);

    // Fold back
    const foldResult = new FoldTactic(['two']).apply(unfoldResult.newEngine, unfoldedGoal, unfoldedGoalId);
    if (!foldResult.success) throw new Error('fold failed');
    const foldedGoal = foldResult.newEngine.getFocusedGoal()!;
    expect(containsConst(foldedGoal.type, 'two')).toBe(true);
  });

  test('fold myZero: replaces Zero with Const("myZero")', () => {
    const defs = getDefinitions();
    const goalType = mkEqual(ZERO, ZERO);
    const engine = createEngine(goalType, defs);
    const goal = engine.getFocusedGoal()!;
    const goalId = engine.getFocusedGoalId()!;

    const tactic = new FoldTactic(['myZero']);
    const result = tactic.apply(engine, goal, goalId);
    if (!result.success) throw new Error(result.error);

    const newGoal = result.newEngine.getFocusedGoal()!;
    expect(containsConst(newGoal.type, 'myZero')).toBe(true);
  });
});

// Helpers

function containsConst(term: TTKTerm, name: string): boolean {
  if (term.tag === 'Const' && term.name === name) return true;
  switch (term.tag) {
    case 'App': return containsConst(term.fn, name) || containsConst(term.arg, name);
    case 'Binder': return containsConst(term.domain, name) || containsConst(term.body, name);
    case 'Match':
      return containsConst(term.scrutinee, name) || term.clauses.some(c => containsConst(c.rhs, name));
    default: return false;
  }
}

function containsPattern(term: TTKTerm, pattern: TTKTerm): boolean {
  if (ttkTermsEqual(term, pattern)) return true;
  switch (term.tag) {
    case 'App': return containsPattern(term.fn, pattern) || containsPattern(term.arg, pattern);
    case 'Binder': return containsPattern(term.domain, pattern) || containsPattern(term.body, pattern);
    case 'Match':
      return containsPattern(term.scrutinee, pattern) || term.clauses.some(c => containsPattern(c.rhs, pattern));
    default: return false;
  }
}
