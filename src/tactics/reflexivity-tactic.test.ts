import { describe, expect, test } from 'vitest';

import { compileTTFromText } from '../compiler/compile';
import { IntrosTactic } from './tactic';
import { ReflexivityTactic } from './reflexivity-tactic';
import { createInitialEngine } from './tacticsEngine';

function introAll(source: string, goalName: string, introNames: string[]) {
  const result = compileTTFromText(source);
  const goalDecl = result.blocks
    .flatMap(block => block.declarations)
    .find(decl => decl.name === goalName);

  expect(goalDecl?.kernelType).toBeDefined();

  let engine = createInitialEngine(goalDecl!.kernelType!, [], result.definitions);
  const goal = engine.getFocusedGoal()!;
  const goalId = engine.getFocusedGoalId()!;
  const introResult = new IntrosTactic(introNames).apply(engine, goal, goalId);
  expect(introResult.success).toBe(true);
  if (!introResult.success) {
    throw new Error(introResult.error);
  }
  engine = introResult.newEngine;

  return engine;
}

describe('ReflexivityTactic', () => {
  test('solves a direct equality goal through the kernel checker path', () => {
    const engine = introAll(`
inductive Equal : {A : Type} -> A -> A -> Type where
  refl : {A : Type} -> {a : A} -> Equal a a

postulate A : Type

goal : (x : A) -> Equal x x
goal x = ?hole
`, 'goal', ['x']);

    const goal = engine.getFocusedGoal()!;
    const goalId = engine.getFocusedGoalId()!;
    const result = new ReflexivityTactic().apply(engine, goal, goalId);

    expect(result.success).toBe(true);
    if (!result.success) return;
    expect(result.newEngine.isComplete()).toBe(true);
  });

  test('solves definitional equalities without hand-constructing proof terms', () => {
    const engine = introAll(`
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Equal : {A : Type} -> A -> A -> Type where
  refl : {A : Type} -> {a : A} -> Equal a a

plus : Nat -> Nat -> Nat
plus Zero n = n
plus (Succ n) m = Succ (plus n m)

goal : (n : Nat) -> Equal (plus Zero n) n
goal n = ?hole
`, 'goal', ['n']);

    const goal = engine.getFocusedGoal()!;
    const goalId = engine.getFocusedGoalId()!;
    const result = new ReflexivityTactic().apply(engine, goal, goalId);

    expect(result.success).toBe(true);
    if (!result.success) return;
    expect(result.newEngine.isComplete()).toBe(true);
  });

  test('rejects goals whose equality sides are not definitionally equal', () => {
    const engine = introAll(`
inductive Equal : {A : Type} -> A -> A -> Type where
  refl : {A : Type} -> {a : A} -> Equal a a

postulate A : Type
postulate B : Type
postulate f : A -> B

goal : (x : A) -> (y : A) -> Equal x y -> Equal (f x) (f y)
goal x y eq = ?hole
`, 'goal', ['x', 'y', 'eq']);

    const goal = engine.getFocusedGoal()!;
    const goalId = engine.getFocusedGoalId()!;
    const result = new ReflexivityTactic().apply(engine, goal, goalId);

    expect(result.success).toBe(false);
  });
});
