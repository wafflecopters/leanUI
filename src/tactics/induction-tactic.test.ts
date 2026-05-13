import { describe, expect, test } from 'vitest';
import { TTKTerm } from '../compiler/kernel';
import { DefinitionsMap } from '../compiler/term';
import { whnf } from '../compiler/whnf';
import { compileTTFromText } from '../compiler/compile';
import { createInitialEngine } from './tacticsEngine';
import { IntrosTactic } from './tactic';
import { InductionTactic } from './induction-tactic';

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
  inductiveNameOfConstructor.set('Zero', 'Nat');
  inductiveNameOfConstructor.set('Succ', 'Nat');

  return { terms, inductiveTypes, inductiveNameOfConstructor };
}

function mkNatToNat(): TTKTerm {
  return {
    tag: 'Binder',
    name: '_',
    binderKind: { tag: 'BPi' },
    domain: { tag: 'Const', name: 'Nat' },
    body: { tag: 'Const', name: 'Nat' }
  };
}

function mkEqualNat(lhs: TTKTerm, rhs: TTKTerm): TTKTerm {
  return {
    tag: 'App',
    fn: {
      tag: 'App',
      fn: {
        tag: 'App',
        fn: { tag: 'Const', name: 'Equal' },
        arg: { tag: 'Const', name: 'Nat' }
      },
      arg: lhs
    },
    arg: rhs
  };
}

function normalizeGoalType(goalType: TTKTerm, definitions: DefinitionsMap, ctx: readonly { name: string; type: TTKTerm }[]): TTKTerm {
  return whnf(goalType, { definitions, typingContext: [...ctx] });
}

describe('InductionTactic', () => {
  test('abstracts scrutinee variables that are not at de Bruijn index 0', () => {
    const definitions = createNatDefinitions();
    const goalType: TTKTerm = {
      tag: 'Binder',
      name: 'i',
      binderKind: { tag: 'BPi' },
      domain: { tag: 'Const', name: 'Nat' },
      body: {
        tag: 'Binder',
        name: 'n',
        binderKind: { tag: 'BPi' },
        domain: { tag: 'Const', name: 'Nat' },
        body: {
          tag: 'Binder',
          name: 'f',
          binderKind: { tag: 'BPi' },
          domain: mkNatToNat(),
          body: mkEqualNat(
            {
              tag: 'App',
              fn: { tag: 'Var', index: 0 },
              arg: { tag: 'Var', index: 1 }
            },
            {
              tag: 'App',
              fn: { tag: 'Var', index: 0 },
              arg: { tag: 'Var', index: 2 }
            }
          )
        }
      }
    };

    let engine = createInitialEngine(goalType, [], definitions);
    const initialGoal = engine.getFocusedGoal()!;
    const initialGoalId = engine.getFocusedGoalId()!;
    const intros = new IntrosTactic(['i', 'n', 'f']).apply(engine, initialGoal, initialGoalId);
    expect(intros.success).toBe(true);
    if (!intros.success) return;
    engine = intros.newEngine;

    const goal = engine.getFocusedGoal()!;
    const goalId = engine.getFocusedGoalId()!;
    const induction = new InductionTactic({ tag: 'Var', index: 1 }).apply(engine, goal, goalId);
    expect(induction.success).toBe(true);
    if (!induction.success) return;

    const zeroGoalId = induction.newEngine.goals[0];
    const zeroGoal = induction.newEngine.metaVars.get(zeroGoalId)!;
    const normalizedZeroGoal = normalizeGoalType(zeroGoal.type, definitions, zeroGoal.ctx);

    expect(normalizedZeroGoal.tag).toBe('App');
    if (normalizedZeroGoal.tag !== 'App') return;
    const lhs = normalizedZeroGoal.fn;
    expect(lhs.tag).toBe('App');
    if (lhs.tag !== 'App') return;
    const lhsTerm = lhs.arg;
    expect(lhsTerm.tag).toBe('App');
    if (lhsTerm.tag !== 'App') return;

    expect(lhsTerm.arg).toEqual({ tag: 'Const', name: 'Zero' });
  });

  test('removes the scrutinee binding and adds a correctly typed induction hypothesis', () => {
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Equal : {A : Type} -> A -> A -> Type where
  refl : {A : Type} -> {a : A} -> Equal a a

plus : Nat -> Nat -> Nat
plus Zero m = m
plus (Succ n) m = Succ (plus n m)

plusZeroRight : (n : Nat) -> Equal (plus n Zero) n := by
  intro n
  induction n with
  | Zero => exact refl
  | Succ n' IH => exact IH
`;

    const compiled = compileTTFromText(source);
    const decl = compiled.blocks.flatMap((b: any) => b.declarations).find((d: any) => d.name === 'plusZeroRight');
    const engine = createInitialEngine(decl.kernelType, [], compiled.definitions);
    const introResult = new IntrosTactic(['n']).apply(engine, engine.getFocusedGoal()!, engine.getFocusedGoalId()!);
    expect(introResult.success).toBe(true);
    if (!introResult.success) return;

    const inductionResult = new InductionTactic({ tag: 'Var', index: 0 }).apply(
      introResult.newEngine,
      introResult.newEngine.getFocusedGoal()!,
      introResult.newEngine.getFocusedGoalId()!,
    );
    expect(inductionResult.success).toBe(true);
    if (!inductionResult.success) return;

    const succGoalId = inductionResult.newEngine.goals[1];
    const succGoal = inductionResult.newEngine.metaVars.get(succGoalId)!;

    expect(succGoal.ctx).toHaveLength(2);
    expect(succGoal.ctx[1].name).toBe('IH');
    expect(whnf(succGoal.type, { definitions: compiled.definitions, typingContext: succGoal.ctx }).tag).toBe('App');

    const ihEntry = succGoal.ctx[1];
    expect(ihEntry.name).toBe('IH');
    expect(whnf(ihEntry.type, { definitions: compiled.definitions, typingContext: succGoal.ctx.slice(0, 1) }).tag).toBe('App');
  });

  test('preserves remaining Pi binders after substituting the scrutinee in each branch', () => {
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Equal : {A : Type} -> A -> A -> Type where
  refl : {A : Type} -> {a : A} -> Equal a a

plus : Nat -> Nat -> Nat
plus Zero m = m
plus (Succ n) m = Succ (plus n m)

goal : (n : Nat) -> (m : Nat) -> (p : Nat) -> Equal (plus (plus n m) p) (plus n (plus m p))
goal n m p = ?hole
`;

    const compiled = compileTTFromText(source);
    const decl = compiled.blocks.flatMap((b: any) => b.declarations).find((d: any) => d.name === 'goal');
    let engine = createInitialEngine(decl.kernelType, [], compiled.definitions);

    const introResult = new IntrosTactic(['n']).apply(engine, engine.getFocusedGoal()!, engine.getFocusedGoalId()!);
    expect(introResult.success).toBe(true);
    if (!introResult.success) return;
    engine = introResult.newEngine;

    const inductionResult = new InductionTactic({ tag: 'Var', index: 0 }).apply(
      engine,
      engine.getFocusedGoal()!,
      engine.getFocusedGoalId()!,
    );
    expect(inductionResult.success).toBe(true);
    if (!inductionResult.success) return;

    const zeroGoal = inductionResult.newEngine.metaVars.get(inductionResult.newEngine.goals[0])!;
    expect(zeroGoal.ctx).toHaveLength(0);

    const zeroGoalWhnf = whnf(zeroGoal.type, {
      definitions: compiled.definitions,
      typingContext: zeroGoal.ctx,
    });
    expect(zeroGoalWhnf.tag).toBe('Binder');
    if (zeroGoalWhnf.tag !== 'Binder') return;
    expect(zeroGoalWhnf.name).toBe('m');
    expect(zeroGoalWhnf.body.tag).toBe('Binder');
    if (zeroGoalWhnf.body.tag !== 'Binder') return;
    expect(zeroGoalWhnf.body.name).toBe('p');
  });
});
