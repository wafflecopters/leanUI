import { describe, expect, test } from 'vitest';
import { TTKTerm } from '../compiler/kernel';
import { DefinitionsMap } from '../compiler/term';
import { whnf } from '../compiler/whnf';
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
});
