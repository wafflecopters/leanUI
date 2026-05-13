import { describe, expect, test } from 'vitest';
import { compileTTFromText } from './compile';
import { parseTTSource } from './compile-parse';
import { prepareTermSignature } from './compile-term-signature';
import { checkSimpleTermValue, type ElaborateTacticBlockFn } from './compile-term-simple-value';
import { createNamedArgInfoLookup } from './term';
import { elabToKernelWithMap } from './elab';
import { prettyPrintFormatted } from './kernel';
import { elaborateTacticBlock } from './compile-tactic-block';
import { TacticInfoTree } from '../tactics/info-tree';

function buildTermDeclaration(source: string, prelude: string) {
  const definitions = compileTTFromText(prelude).definitions;
  const parseResult = parseTTSource(source);
  const declBlock = parseResult.blocks.find(block => block.kind === 'declarations');
  expect(declBlock?.kind).toBe('declarations');
  if (!declBlock || declBlock.kind !== 'declarations') {
    throw new Error('expected declaration block');
  }
  const parsedDecl = declBlock.declarations[0];
  const elabMap = new Map();
  const typePath = [{ kind: 'field', name: 'type' }] as const;
  const kernelType = elabToKernelWithMap(
    parsedDecl.type!,
    elabMap,
    [...typePath],
    [...typePath],
    undefined,
    createNamedArgInfoLookup(definitions),
  );
  return {
    definitions,
    decl: {
      name: parsedDecl.name,
      kind: 'term' as const,
      surfaceType: parsedDecl.type,
      surfaceValue: parsedDecl.value,
      kernelType,
      elabMap,
      sourceMap: new Map(),
    },
  };
}

const NAT_PRELUDE = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat
`;

const NAT_PAIR_PRELUDE = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

add : Nat -> Nat -> Nat
add Zero m = m
add (Succ n) m = Succ (add n m)

record Pair (A B : Type) where
  constructor MkPair
  fst : A
  snd : B
`;

const SEMIGROUP_REWRITE_PRELUDE = `
inductive Equal : {A : Type} -> A -> A -> Type where
  refl : {A : Type} -> {a : A} -> Equal a a

sym : {A : Type} -> {x y : A} -> Equal x y -> Equal y x
sym refl = refl

replace : {A : Type} -> {x y : A} -> (P : A -> Type) -> Equal x y -> P x -> P y
replace P refl px = px

record Semi where
  constructor MkSemi
  Carrier : Type
  op : Carrier -> Carrier -> Carrier
  assoc : (x y z : Carrier) -> Equal (op (op x y) z) (op x (op y z))
`;

const NAT_ALIAS_REWRITE_PRELUDE = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Equal : {A : Type} -> A -> A -> Type where
  refl : {A : Type} -> {a : A} -> Equal a a

sym : {A : Type} -> {x y : A} -> Equal x y -> Equal y x
sym refl = refl

replace : {A : Type} -> {x y : A} -> (P : A -> Type) -> Equal x y -> P x -> P y
replace P refl px = px

add : Nat -> Nat -> Nat
add a Zero = a
add a (Succ b) = Succ (add a b)

neg : Nat -> Nat
neg Zero = Zero
neg (Succ a) = Succ a

sub : Nat -> Nat -> Nat
sub a b = add a (neg b)

negZero : Equal (neg Zero) Zero
negZero = refl

addZeroRight : (a : Nat) -> Equal (add a Zero) a
addZeroRight a = refl
`;

const neverElaborateTacticBlock: ElaborateTacticBlockFn = () => {
  throw new Error('unexpected tactic block elaboration');
};

describe('compile-term-simple-value', () => {
  test('checks a simple non-recursive value and stores the zonked term', () => {
    const { definitions, decl } = buildTermDeclaration(`
zeroId : Nat
zeroId = Zero
`, NAT_PRELUDE);
    const signatureResult = prepareTermSignature(decl, definitions);
    expect(signatureResult.success).toBe(true);
    if (!signatureResult.success) {
      throw new Error('expected signature preparation to succeed');
    }

    const result = checkSimpleTermValue(
      decl,
      'zeroId',
      signatureResult.prepared.termEnv,
      signatureResult.prepared.zonkedKernelType,
      signatureResult.prepared.namedArgMap,
      neverElaborateTacticBlock,
    );

    expect(result.success).toBe(true);
    if (!result.success) {
      throw new Error('expected simple value check to succeed');
    }
    expect(prettyPrintFormatted(result.checkedValue)).toBe('Zero');
  });

  test('rejects self-recursive simple definitions', () => {
    const { definitions, decl } = buildTermDeclaration(`
loop : Nat
loop = loop
`, NAT_PRELUDE);
    const signatureResult = prepareTermSignature(decl, definitions);
    expect(signatureResult.success).toBe(true);
    if (!signatureResult.success) {
      throw new Error('expected signature preparation to succeed');
    }

    const result = checkSimpleTermValue(
      decl,
      'loop',
      signatureResult.prepared.termEnv,
      signatureResult.prepared.zonkedKernelType,
      signatureResult.prepared.namedArgMap,
      neverElaborateTacticBlock,
    );

    expect(result.success).toBe(false);
    if (result.success) {
      throw new Error('expected simple recursion rejection');
    }
    expect(result.errors[0].message).toContain('simple definitions cannot be recursive');
  });

  test('re-checks tactic block elaboration output through the kernel checker', () => {
    const { definitions, decl } = buildTermDeclaration(`
proved : Nat
proved := by
  exact Zero
`, NAT_PRELUDE);
    const signatureResult = prepareTermSignature(decl, definitions);
    expect(signatureResult.success).toBe(true);
    if (!signatureResult.success) {
      throw new Error('expected signature preparation to succeed');
    }

    const result = checkSimpleTermValue(
      decl,
      'proved',
      signatureResult.prepared.termEnv,
      signatureResult.prepared.zonkedKernelType,
      signatureResult.prepared.namedArgMap,
      () => ({
        term: { tag: 'Const', name: 'Zero' },
        infoTree: new TacticInfoTree({
          position: { line: 1, col: 1, endLine: 1, endCol: 1 },
          goalsBefore: [],
          goalsAfter: [],
          tactic: { tag: 'Exact', term: { tag: 'Const', name: 'Zero' } },
          children: [],
        }),
      }),
    );

    expect(result.success).toBe(true);
    if (!result.success) {
      throw new Error('expected tactic block result to succeed');
    }
    expect(prettyPrintFormatted(result.checkedValue)).toBe('Zero');
    expect(result.tacticInfoTree).toBeInstanceOf(TacticInfoTree);
  });

  test('rejects tactic block elaboration output when it does not match the declared type', () => {
    const { definitions, decl } = buildTermDeclaration(`
badProof : Nat
badProof := by
  exact Zero
`, NAT_PRELUDE);
    const signatureResult = prepareTermSignature(decl, definitions);
    expect(signatureResult.success).toBe(true);
    if (!signatureResult.success) {
      throw new Error('expected signature preparation to succeed');
    }

    const result = checkSimpleTermValue(
      decl,
      'badProof',
      signatureResult.prepared.termEnv,
      signatureResult.prepared.zonkedKernelType,
      signatureResult.prepared.namedArgMap,
      () => ({
        term: {
          tag: 'Binder',
          name: 'x',
          binderKind: { tag: 'BLam' },
          domain: { tag: 'Const', name: 'Nat' },
          body: { tag: 'Var', index: 0 },
        },
        infoTree: new TacticInfoTree({
          position: { line: 1, col: 1, endLine: 1, endCol: 1 },
          goalsBefore: [],
          goalsAfter: [],
          tactic: { tag: 'Exact', term: { tag: 'Const', name: 'Zero' } },
          children: [],
        }),
      }),
    );

    expect(result.success).toBe(false);
    if (result.success) {
      throw new Error('expected kernel re-check to reject invalid tactic output');
    }
    expect(result.errors[0].fullMessage).toContain('Nat');
  });

  test('rejects self-referential tactic output just like ordinary simple values', () => {
    const { definitions, decl } = buildTermDeclaration(`
loopBy : Nat
loopBy := by
  exact Zero
`, NAT_PRELUDE);
    const signatureResult = prepareTermSignature(decl, definitions);
    expect(signatureResult.success).toBe(true);
    if (!signatureResult.success) {
      throw new Error('expected signature preparation to succeed');
    }

    const result = checkSimpleTermValue(
      decl,
      'loopBy',
      signatureResult.prepared.termEnv,
      signatureResult.prepared.zonkedKernelType,
      signatureResult.prepared.namedArgMap,
      () => ({
        term: { tag: 'Const', name: 'loopBy' },
        infoTree: new TacticInfoTree({
          position: { line: 1, col: 1, endLine: 1, endCol: 1 },
          goalsBefore: [],
          goalsAfter: [],
          tactic: { tag: 'Exact', term: { tag: 'Const', name: 'loopBy' } },
          children: [],
        }),
      }),
    );

    expect(result.success).toBe(false);
    if (result.success) {
      throw new Error('expected self-reference rejection for tactic output');
    }
    expect(result.errors[0].message).toContain('simple definitions cannot be recursive');
  });

  test('accepts tactic-generated structural recursion guarded by match branches', () => {
    const { definitions, decl } = buildTermDeclaration(`
leqTrans : {a b c : Nat} -> Leq a b -> Leq b c -> Leq a c := by
  intros a b c hab hbc
  cases hab with
  | LeqZero => exact LeqZero
  | LeqSucc p =>
    cases hbc with
    | LeqSucc q => exact (LeqSucc (leqTrans p q))
`, `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Leq : Nat -> Nat -> Type where
  LeqZero : {n : Nat} -> Leq Zero n
  LeqSucc : {n m : Nat} -> Leq n m -> Leq (Succ n) (Succ m)
`);
    const signatureResult = prepareTermSignature(decl, definitions);
    expect(signatureResult.success).toBe(true);
    if (!signatureResult.success) {
      throw new Error('expected signature preparation to succeed');
    }

    const result = checkSimpleTermValue(
      decl,
      'leqTrans',
      signatureResult.prepared.termEnv,
      signatureResult.prepared.zonkedKernelType,
      signatureResult.prepared.namedArgMap,
      elaborateTacticBlock,
    );

    expect(result.success).toBe(true);
    if (!result.success) {
      throw new Error(result.errors.map(error => error.fullMessage).join('\n\n'));
    }
    expect(prettyPrintFormatted(result.checkedValue)).toContain('match');
    expect(prettyPrintFormatted(result.checkedValue)).toContain('leqTrans');
  });

  test('rejects tactic-generated recursion when the recursive argument does not get smaller', () => {
    const { definitions, decl } = buildTermDeclaration(`
badRec : Nat -> Nat := by
  intro n
  cases n with
  | Zero => exact Zero
  | Succ k => exact (badRec n)
`, NAT_PRELUDE);
    const signatureResult = prepareTermSignature(decl, definitions);
    expect(signatureResult.success).toBe(true);
    if (!signatureResult.success) {
      throw new Error('expected signature preparation to succeed');
    }

    const result = checkSimpleTermValue(
      decl,
      'badRec',
      signatureResult.prepared.termEnv,
      signatureResult.prepared.zonkedKernelType,
      signatureResult.prepared.namedArgMap,
      elaborateTacticBlock,
    );

    expect(result.success).toBe(false);
    if (result.success) {
      throw new Error('expected non-decreasing recursive tactic output to be rejected');
    }
    expect(result.errors[0].message).toContain('simple definitions cannot be recursive');
  });

  test('accepts checked tactic output even when unrelated universe metas remain in the environment', () => {
    const { definitions, decl } = buildTermDeclaration(`
pairSum : Pair Nat (Pair Nat Nat) -> Nat := by
  intro p
  cases p with
  | MkPair n (MkPair a b) =>
    exact (add n (add a b))
`, NAT_PAIR_PRELUDE);
    const signatureResult = prepareTermSignature(decl, definitions);
    expect(signatureResult.success).toBe(true);
    if (!signatureResult.success) {
      throw new Error('expected signature preparation to succeed');
    }

    const result = checkSimpleTermValue(
      decl,
      'pairSum',
      signatureResult.prepared.termEnv,
      signatureResult.prepared.zonkedKernelType,
      signatureResult.prepared.namedArgMap,
      elaborateTacticBlock,
    );

    expect(result.success).toBe(true);
    if (!result.success) {
      throw new Error(result.errors.map(err => err.fullMessage).join('\n\n'));
    }
    expect(prettyPrintFormatted(result.checkedValue)).toContain('match');
    expect(prettyPrintFormatted(result.checkedValue)).toContain('add fst');
  });

  test('normalizes theorem goal types before rewriting against record projection equalities', () => {
    const { definitions, decl } = buildTermDeclaration(`
assocHelper : (S : Semi) -> (x y z : Semi.Carrier S) -> Equal (Semi.op S (Semi.op S x y) z) (Semi.op S x (Semi.op S y z)) := by
  intros S x y z
  erw (Semi.assoc S x y z)
`, SEMIGROUP_REWRITE_PRELUDE);
    const signatureResult = prepareTermSignature(decl, definitions);
    expect(signatureResult.success).toBe(true);
    if (!signatureResult.success) {
      throw new Error('expected signature preparation to succeed');
    }

    const result = checkSimpleTermValue(
      decl,
      'assocHelper',
      signatureResult.prepared.termEnv,
      signatureResult.prepared.zonkedKernelType,
      signatureResult.prepared.namedArgMap,
      elaborateTacticBlock,
    );

    expect(result.success).toBe(true);
    if (!result.success) {
      throw new Error(result.errors.map(err => err.fullMessage).join('\n\n'));
    }
    expect(prettyPrintFormatted(result.checkedValue)).toContain('replace');
  });

  test('enhanced rewrite unfolds one alias layer without normalizing away the target occurrence', () => {
    const { definitions, decl } = buildTermDeclaration(`
subZeroRight : (a : Nat) -> Equal (sub a Zero) a := by
  intros a
  erw negZero, (addZeroRight a)
`, NAT_ALIAS_REWRITE_PRELUDE);
    const signatureResult = prepareTermSignature(decl, definitions);
    expect(signatureResult.success).toBe(true);
    if (!signatureResult.success) {
      throw new Error('expected signature preparation to succeed');
    }

    const result = checkSimpleTermValue(
      decl,
      'subZeroRight',
      signatureResult.prepared.termEnv,
      signatureResult.prepared.zonkedKernelType,
      signatureResult.prepared.namedArgMap,
      elaborateTacticBlock,
    );

    expect(result.success).toBe(true);
    if (!result.success) {
      throw new Error(result.errors.map(err => err.fullMessage).join('\n\n'));
    }
    const rendered = prettyPrintFormatted(result.checkedValue);
    expect(rendered).toContain('replace');
    expect(rendered).toContain('addZeroRight');
  });
});
