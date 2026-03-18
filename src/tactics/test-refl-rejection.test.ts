import { describe, test, expect } from 'vitest';
import { compileTTFromText } from '../compiler/compile';
import { createInitialEngine } from '../tactics/tacticsEngine';
import { ExactTactic, IntrosTactic } from '../tactics/tactic';

describe('ExactTactic refl rejection', () => {
  test('refl should NOT succeed on f(x) = f(y) where x ≠ y (postulate types)', () => {
    const source = `
inductive Equal : {A : Type} -> A -> A -> Type where
  refl : {A : Type} -> {a : A} -> Equal a a

postulate A : Type
postulate B : Type
postulate f : A -> B

goal : (x : A) -> (y : A) -> Equal x y -> Equal (f x) (f y)
goal x y eq = ?hole
`;
    const result = compileTTFromText(source);
    const goalBlock = result.blocks.find(b =>
      b.declarations.some(d => d.name === 'goal')
    );
    const goalDecl = goalBlock!.declarations.find(d => d.name === 'goal')!;
    const kernelType = goalDecl.kernelType!;
    const defs = result.definitions;

    let engine = createInitialEngine(kernelType, [], defs);
    const goalId = engine.goals[0];
    const goal = engine.metaVars.get(goalId)!;

    const intros = new IntrosTactic(['x', 'y', 'eq']);
    const introsResult = intros.apply(engine, goal, goalId);
    expect(introsResult.success).toBe(true);
    if (!introsResult.success) return;
    engine = introsResult.newEngine;

    const newGoalId = engine.goals[0];
    const newGoal = engine.metaVars.get(newGoalId)!;

    const reflTactic = new ExactTactic({ tag: 'Const', name: 'refl' });
    const reflResult = reflTactic.apply(engine, newGoal, newGoalId);
    expect(reflResult.success).toBe(false);
  });

  test('refl should NOT succeed on f(x) = f(y) where x ≠ y (implicit type params)', () => {
    // This matches the user's actual cong definition:
    // Types A, B and elements x, y are implicit parameters in context
    // (not postulates), so their types use de Bruijn indices at different depths.
    const source = `
inductive Equal : {A : Type} -> A -> A -> Type where
  refl : {A : Type} -> {a : A} -> Equal a a

goal : {A : Type} -> {B : Type} -> {x : A} -> {y : A} -> (f : A -> B) -> Equal x y -> Equal (f x) (f y)
goal f eq = ?hole
`;
    const result = compileTTFromText(source);
    const goalBlock = result.blocks.find(b =>
      b.declarations.some(d => d.name === 'goal')
    );
    const goalDecl = goalBlock!.declarations.find(d => d.name === 'goal')!;
    const kernelType = goalDecl.kernelType!;
    const defs = result.definitions;

    let engine = createInitialEngine(kernelType, [], defs);
    const goalId = engine.goals[0];
    const goal = engine.metaVars.get(goalId)!;

    // Intro all params including implicits
    const intros = new IntrosTactic(['A', 'B', 'x', 'y', 'f', 'eq']);
    const introsResult = intros.apply(engine, goal, goalId);
    expect(introsResult.success).toBe(true);
    if (!introsResult.success) return;
    engine = introsResult.newEngine;

    const newGoalId = engine.goals[0];
    const newGoal = engine.metaVars.get(newGoalId)!;

    // refl should FAIL: f(x) ≠ f(y) since x ≠ y
    const reflTactic = new ExactTactic({ tag: 'Const', name: 'refl' });
    const reflResult = reflTactic.apply(engine, newGoal, newGoalId);
    expect(reflResult.success).toBe(false);
  });

  test('refl should succeed on Equal a a (both sides identical)', () => {
    const source = `
inductive Equal : {A : Type} -> A -> A -> Type where
  refl : {A : Type} -> {a : A} -> Equal a a

postulate A : Type

goal : (x : A) -> Equal x x
goal x = ?hole
`;
    const result = compileTTFromText(source);
    const goalBlock = result.blocks.find(b =>
      b.declarations.some(d => d.name === 'goal')
    );
    const goalDecl = goalBlock!.declarations.find(d => d.name === 'goal')!;
    const kernelType = goalDecl.kernelType!;
    const defs = result.definitions;

    let engine = createInitialEngine(kernelType, [], defs);
    const goalId = engine.goals[0];
    const goal = engine.metaVars.get(goalId)!;

    const intros = new IntrosTactic(['x']);
    const introsResult = intros.apply(engine, goal, goalId);
    expect(introsResult.success).toBe(true);
    if (!introsResult.success) return;
    engine = introsResult.newEngine;

    const newGoalId = engine.goals[0];
    const newGoal = engine.metaVars.get(newGoalId)!;

    const reflTactic = new ExactTactic({ tag: 'Const', name: 'refl' });
    const reflResult = reflTactic.apply(engine, newGoal, newGoalId);
    expect(reflResult.success).toBe(true);
  });
});
