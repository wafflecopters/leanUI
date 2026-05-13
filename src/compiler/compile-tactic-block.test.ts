import { describe, expect, test } from 'vitest';

import { prettyPrintFormatted } from './kernel';
import { prettyPrint } from './kernel';
import { compileTTFromText } from './compile';
import { elaborateTacticBlock } from './compile-tactic-block';
import { checkType } from './checker';
import { createInitialEngine } from '../tactics/tacticsEngine';
import { IntrosTactic, ExactTactic, resetMetaCounter } from '../tactics/tactic';
import { CasesTactic } from '../tactics/cases-tactic';
import { elaborateTacticArg } from '../tactics/elaborate-tactic-arg';
import { createTCEnv } from './term';

const NAT_BOOL_PRELUDE = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Bool : Type where
  True : Bool
  False : Bool
`;

describe('compile tactic block', () => {
  test('compiler-produced kernel theorem type also works through raw tactic engine flow', () => {
    resetMetaCounter();
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Leq : Nat -> Nat -> Type where
  LeqZero : {n : Nat} -> Leq Zero n
  LeqSucc : {n m : Nat} -> Leq n m -> Leq (Succ n) (Succ m)

keepZeroLeft : {b c : Nat} -> Leq Zero b -> Leq Zero c := by
  intros b c h0
  cases h0 with
  | LeqZero => exact LeqZero
`;
    const result = compileTTFromText(source);
    const decl = result.blocks.flatMap(block => block.declarations).find(d => d.name === 'keepZeroLeft');
    expect(decl?.kernelType).toBeDefined();

    const engine = createInitialEngine(decl!.kernelType!, [], result.definitions);
    const introResult = new IntrosTactic(['b', 'c', 'h0']).apply(
      engine,
      engine.getFocusedGoal()!,
      engine.getFocusedGoalId()!,
    );
    expect(introResult.success).toBe(true);
    if (!introResult.success) return;

    const afterIntros = introResult.newEngine;
    const introGoal = afterIntros.getFocusedGoal()!;
    expect(introGoal.ctx.map(entry => entry.name)).toEqual(['b', 'c', 'h0']);
    expect(prettyPrint(introGoal.ctx[2].type, introGoal.ctx.slice(0, 2).map(entry => entry.name).reverse())).toBe('(Leq Zero b)');
    expect(prettyPrint(introGoal.type, introGoal.ctx.map(entry => entry.name).reverse())).toBe('(Leq Zero c)');
    const casesResult = new CasesTactic({ tag: 'Var', index: 0 }).apply(
      afterIntros,
      afterIntros.getFocusedGoal()!,
      afterIntros.getFocusedGoalId()!,
    );
    expect(casesResult.success).toBe(true);
    if (!casesResult.success) return;

    const zeroGoalId = casesResult.newEngine.goals.find(id => casesResult.newEngine.metaVars.get(id)?.caseTag === 'LeqZero');
    expect(zeroGoalId).toBeDefined();
    const zeroGoalIndex = casesResult.newEngine.goals.findIndex(id => id === zeroGoalId);
    const zeroEngine = casesResult.newEngine.focusGoalAt(zeroGoalIndex);
    const zeroGoal = zeroEngine.getFocusedGoal()!;
    expect(prettyPrint(zeroGoal.type, zeroGoal.ctx.map(entry => entry.name).reverse())).toBe('(Leq Zero c)');

    const elaboratedLeqZero = elaborateTacticArg({ tag: 'Const', name: 'LeqZero' } as any, zeroGoal.ctx, result.definitions);
    const exactResult = new ExactTactic(elaboratedLeqZero).apply(
      zeroEngine,
      zeroGoal,
      zeroEngine.getFocusedGoalId()!,
    );
    expect(exactResult.success).toBe(true);
    if (!exactResult.success) return;

    const finalTerm = exactResult.newEngine.zonk();
    expect(() => checkType(
      createTCEnv({ definitions: result.definitions, options: { mode: 'check' } }).withValue(finalTerm),
      decl!.kernelType!,
    )).not.toThrow();
  });

  test('elaborates a simple exact proof block to a kernel term', () => {
    const definitions = compileTTFromText(NAT_BOOL_PRELUDE).definitions;
    const result = elaborateTacticBlock(
      {
        tag: 'TacticBlock',
        tactics: [{ name: 'exact', args: [{ tag: 'Const', name: 'Zero' }] }],
      },
      { tag: 'Const', name: 'Nat' },
      definitions,
      new Map(),
      new Map(),
      [],
    );

    expect(prettyPrintFormatted(result.term)).toBe('Zero');
    expect(result.infoTree.getStatistics().successfulTactics).toBe(1);
  });

  test('rejects tactic blocks whose proof term does not solve the expected goal', () => {
    const definitions = compileTTFromText(NAT_BOOL_PRELUDE).definitions;
    expect(() =>
      elaborateTacticBlock(
        {
          tag: 'TacticBlock',
          tactics: [{ name: 'exact', args: [{ tag: 'Const', name: 'True' }] }],
        },
        { tag: 'Const', name: 'Nat' },
        definitions,
        new Map(),
        new Map(),
        [],
      ),
    ).toThrow(/failed|Nat|Bool/);
  });

  test('rejects empty tactic blocks before any kernel term is trusted', () => {
    const definitions = compileTTFromText(NAT_BOOL_PRELUDE).definitions;
    expect(() =>
      elaborateTacticBlock(
        { tag: 'TacticBlock', tactics: [] },
        { tag: 'Const', name: 'Nat' },
        definitions,
        new Map(),
        new Map(),
        [],
      ),
    ).toThrow('no tactics');
  });

  test('structured case branches use user pattern names after nested destructuring', () => {
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

record Pair (A B : Type) where
  constructor MkPair
  fst : A
  snd : B

inductive Wrap : Type where
  MkWrap : Pair Nat Nat -> Wrap

leftOf : Wrap -> Nat := by
  intro w
  cases w with
  | MkWrap (MkPair left right) =>
    exact left
`;
    const result = compileTTFromText(source);
    const decl = result.blocks.flatMap(block => block.declarations).find(d => d.name === 'leftOf');

    expect(result.success).toBe(true);
    expect(decl?.checkSuccess).toBe(true);
    expect(decl?.checkErrors ?? []).toHaveLength(0);
  });

  test('cases on a non-variable scrutinee still checks through the kernel', () => {
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Wrap : Type where
  MkWrap : Nat -> Wrap

mkWrap : Nat -> Wrap
mkWrap n = MkWrap n

unwrapViaCases : Nat -> Nat := by
  intro n
  cases (mkWrap n) with
  | MkWrap m =>
    exact m
`;
    const result = compileTTFromText(source);
    const decl = result.blocks.flatMap(block => block.declarations).find(d => d.name === 'unwrapViaCases');

    expect(result.success).toBe(true);
    expect(decl?.checkSuccess).toBe(true);
    expect(decl?.checkErrors ?? []).toHaveLength(0);
  });

  test('dependent cases branch can exact an implicit constructor through compileTTFromText', () => {
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Leq : Nat -> Nat -> Type where
  LeqZero : {n : Nat} -> Leq Zero n
  LeqSucc : {n m : Nat} -> Leq n m -> Leq (Succ n) (Succ m)

keepZeroLeft : {b c : Nat} -> Leq Zero b -> Leq Zero c := by
  intros b c h0
  cases h0 with
  | LeqZero => exact LeqZero
`;
    const result = compileTTFromText(source);
    const decl = result.blocks.flatMap(block => block.declarations).find(d => d.name === 'keepZeroLeft');

    if (!result.success || !decl?.checkSuccess) {
      throw new Error([
        `type=${decl?.kernelType ? prettyPrintFormatted(decl.kernelType) : '<missing>'}`,
        ...((decl?.checkErrors ?? []).map(error => error.message)),
      ].join('\n'));
    }
    expect(result.success).toBe(true);
    expect(decl?.checkSuccess).toBe(true);
    expect(decl?.checkErrors ?? []).toHaveLength(0);
  });

  test('nested indexed cases can re-check a transitivity proof term through compileTTFromText', () => {
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Leq : Nat -> Nat -> Type where
  LeqZero : {n : Nat} -> Leq Zero n
  LeqSucc : {n m : Nat} -> Leq n m -> Leq (Succ n) (Succ m)

leqTrans : {a b c : Nat} -> Leq a b -> Leq b c -> Leq a c := by
  intros a b c hab hbc
  cases hab with
  | LeqZero => exact LeqZero
  | LeqSucc p =>
    cases hbc with
    | LeqSucc q => exact (LeqSucc (leqTrans p q))
`;
    const result = compileTTFromText(source);
    const decl = result.blocks.flatMap(block => block.declarations).find(d => d.name === 'leqTrans');

    if (!result.success || !decl?.checkSuccess) {
      throw new Error([
        `type=${decl?.kernelType ? prettyPrintFormatted(decl.kernelType) : '<missing>'}`,
        ...((decl?.checkErrors ?? []).map(error => error.message)),
      ].join('\n'));
    }
    expect(result.success).toBe(true);
    expect(decl?.checkSuccess).toBe(true);
    expect(decl?.checkErrors ?? []).toHaveLength(0);
  });

  test('adjacent nested indexed cases can re-check an antisymmetry proof term through compileTTFromText', () => {
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Equal : {A : Type} -> A -> A -> Type where
  refl : {A : Type} -> {a : A} -> Equal a a

inductive Leq : Nat -> Nat -> Type where
  LeqZero : {n : Nat} -> Leq Zero n
  LeqSucc : {n m : Nat} -> Leq n m -> Leq (Succ n) (Succ m)

congSucc : {n m : Nat} -> Equal n m -> Equal (Succ n) (Succ m)
congSucc refl = refl

leqAntisym : {a b : Nat} -> Leq a b -> Leq b a -> Equal a b := by
  intros a b hab hba
  cases hab with
  | LeqZero =>
    cases hba with
  | LeqSucc p =>
    cases hba with
    | LeqSucc q => exact (congSucc (leqAntisym p q))
`;
    const result = compileTTFromText(source);
    const decl = result.blocks.flatMap(block => block.declarations).find(d => d.name === 'leqAntisym');

    if (!result.success || !decl?.checkSuccess) {
      throw new Error([
        `type=${decl?.kernelType ? prettyPrintFormatted(decl.kernelType) : '<missing>'}`,
        ...((decl?.checkErrors ?? []).map(error => error.message)),
      ].join('\n'));
    }
    expect(result.success).toBe(true);
    expect(decl?.checkSuccess).toBe(true);
    expect(decl?.checkErrors ?? []).toHaveLength(0);
  });
});
