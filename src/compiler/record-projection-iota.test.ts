import { describe, test, expect } from 'vitest';
import { whnf } from './whnf';
import { compileTTFromText } from './compile';
import { mkApp, mkConst, mkVar, prettyPrintFormatted, TTKTerm } from './kernel';

/**
 * Tests for record projection iota-reduction.
 *
 * Record projections are elaborated as lambda-wrapped Match terms whose RHS
 * must point at the target field's constructor position in the full argument
 * list. For a record with fields [f1, f2, ..., fn], the projection for fi
 * should return Var(n - 1 - i).
 *
 * Bug regression: buildProjectionValue previously returned Var(0) for every
 * projection, which makes large-record projections drift to the final field
 * (`CompleteOrderedField.add` projected `supLeast`).
 */

const mkULit = (n: number): TTKTerm => ({ tag: 'ULit', n });
const prettyProjection = (term: TTKTerm) => prettyPrintFormatted(term);

describe('record projection iota-reduction via WHNF', () => {

  test('DPair.fst (MkDPair a b) reduces to a, not b', () => {
    const source = `
record DPair {u v : ULevel} (A : Type u) (B : A -> Type v) : Type (UMax u v) where
  constructor MkDPair
  fst : A
  snd : B fst

test : Type
test = Type
`;
    const result = compileTTFromText(source);
    const defs = result.definitions;

    // Build: DPair.fst {0} {0} {A} {B} (MkDPair {0} {0} {A} {B} a b)
    const ulit0 = mkULit(0);
    const A = mkVar(3);
    const B = mkVar(2);
    const a = mkVar(1);
    const b = mkVar(0);

    const mkdpair = mkApp(mkApp(mkApp(mkApp(mkApp(mkApp(
      mkConst('MkDPair'), ulit0), ulit0), A), B), a), b);
    const dpairFst = mkApp(mkApp(mkApp(mkApp(mkApp(
      mkConst('DPair.fst'), ulit0), ulit0), A), B), mkdpair);

    const reduced = whnf(dpairFst, { definitions: defs });
    expect(reduced.tag).toBe('Var');
    expect((reduced as any).index).toBe(1); // a is at Var(1)
  });

  test('DPair.snd (MkDPair a b) reduces to b, not a', () => {
    const source = `
record DPair {u v : ULevel} (A : Type u) (B : A -> Type v) : Type (UMax u v) where
  constructor MkDPair
  fst : A
  snd : B fst

test : Type
test = Type
`;
    const result = compileTTFromText(source);
    const defs = result.definitions;

    const ulit0 = mkULit(0);
    const A = mkVar(3);
    const B = mkVar(2);
    const a = mkVar(1);
    const b = mkVar(0);

    const mkdpair = mkApp(mkApp(mkApp(mkApp(mkApp(mkApp(
      mkConst('MkDPair'), ulit0), ulit0), A), B), a), b);
    const dpairSnd = mkApp(mkApp(mkApp(mkApp(mkApp(
      mkConst('DPair.snd'), ulit0), ulit0), A), B), mkdpair);

    const reduced = whnf(dpairSnd, { definitions: defs });
    expect(reduced.tag).toBe('Var');
    expect((reduced as any).index).toBe(0); // b is at Var(0)
  });

  test('Pair.fst (MkPair a b) reduces to a', () => {
    const source = `
record Pair (A B : Type) where
  constructor MkPair
  fst : A
  snd : B

test : Type
test = Type
`;
    const result = compileTTFromText(source);
    const defs = result.definitions;

    const A = mkVar(3);
    const B = mkVar(2);
    const a = mkVar(1);
    const b = mkVar(0);

    const mkpair = mkApp(mkApp(mkApp(mkApp(
      mkConst('MkPair'), A), B), a), b);
    const pairFst = mkApp(mkApp(mkApp(
      mkConst('Pair.fst'), A), B), mkpair);

    const reduced = whnf(pairFst, { definitions: defs });
    expect(reduced.tag).toBe('Var');
    expect((reduced as any).index).toBe(1); // a
  });

  test('Pair.snd (MkPair a b) reduces to b', () => {
    const source = `
record Pair (A B : Type) where
  constructor MkPair
  fst : A
  snd : B

test : Type
test = Type
`;
    const result = compileTTFromText(source);
    const defs = result.definitions;

    const A = mkVar(3);
    const B = mkVar(2);
    const a = mkVar(1);
    const b = mkVar(0);

    const mkpair = mkApp(mkApp(mkApp(mkApp(
      mkConst('MkPair'), A), B), a), b);
    const pairSnd = mkApp(mkApp(mkApp(
      mkConst('Pair.snd'), A), B), mkpair);

    const reduced = whnf(pairSnd, { definitions: defs });
    expect(reduced.tag).toBe('Var');
    expect((reduced as any).index).toBe(0); // b
  });

  test('3-field record: projections return correct fields', () => {
    const source = `
record Triple (A B C : Type) where
  constructor MkTriple
  first : A
  second : B
  third : C

test : Type
test = Type
`;
    const result = compileTTFromText(source);
    const defs = result.definitions;

    const A = mkVar(5);
    const B = mkVar(4);
    const C = mkVar(3);
    const a = mkVar(2);
    const b = mkVar(1);
    const c = mkVar(0);

    const mktriple = mkApp(mkApp(mkApp(mkApp(mkApp(mkApp(
      mkConst('MkTriple'), A), B), C), a), b), c);

    // Triple.first should return a (Var(2))
    const tripleFirst = mkApp(mkApp(mkApp(mkApp(
      mkConst('Triple.first'), A), B), C), mktriple);
    const reduced1 = whnf(tripleFirst, { definitions: defs });
    expect(reduced1.tag).toBe('Var');
    expect((reduced1 as any).index).toBe(2); // a

    // Triple.second should return b (Var(1))
    const tripleSecond = mkApp(mkApp(mkApp(mkApp(
      mkConst('Triple.second'), A), B), C), mktriple);
    const reduced2 = whnf(tripleSecond, { definitions: defs });
    expect(reduced2.tag).toBe('Var');
    expect((reduced2 as any).index).toBe(1); // b

    // Triple.third should return c (Var(0))
    const tripleThird = mkApp(mkApp(mkApp(mkApp(
      mkConst('Triple.third'), A), B), C), mktriple);
    const reduced3 = whnf(tripleThird, { definitions: defs });
    expect(reduced3.tag).toBe('Var');
    expect((reduced3 as any).index).toBe(0); // c
  });

  test('DPair.fst reduces with concrete values', () => {
    const source = `
record DPair {u v : ULevel} (A : Type u) (B : A -> Type v) : Type (UMax u v) where
  constructor MkDPair
  fst : A
  snd : B fst

test : Type
test = Type
`;
    const result = compileTTFromText(source);
    const defs = result.definitions;

    const ulit0 = mkULit(0);
    const natType = mkConst('Nat');
    const bFn = mkConst('P'); // some predicate

    // MkDPair {0} {0} Nat P Zero someProof
    const mkdpair = mkApp(mkApp(mkApp(mkApp(mkApp(mkApp(
      mkConst('MkDPair'), ulit0), ulit0), natType), bFn), mkConst('Zero')), mkConst('someProof'));
    const dpairFst = mkApp(mkApp(mkApp(mkApp(mkApp(
      mkConst('DPair.fst'), ulit0), ulit0), natType), bFn), mkdpair);

    const reduced = whnf(dpairFst, { definitions: defs });
    console.log('concrete DPair.fst result:', JSON.stringify(reduced));
    // DPair.fst applied with ALL 5 explicit args reduces correctly
    expect(reduced).toEqual(mkConst('Zero'));
  });

  test('DPair.fst via type checker - inspect elaborated term', () => {
    const source = `
record DPair {u v : ULevel} (A : Type u) (B : A -> Type v) : Type (UMax u v) where
  constructor MkDPair
  fst : A
  snd : B fst

inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Equal : {A : Type} -> A -> A -> Type where
  refl : {A : Type} -> {a : A} -> Equal a a

P : Nat -> Type
P n = Nat

myPair : DPair Nat P
myPair = MkDPair Zero (Succ Zero)

testFst : Equal (DPair.fst myPair) Zero
testFst = refl
`;
    const result = compileTTFromText(source);
    const testFstDecl = result.blocks.flatMap(b => b.declarations).find(d => d.name === 'testFst');
    console.log('testFst checkSuccess:', testFstDecl?.checkSuccess);
    if (testFstDecl?.checkErrors) {
      for (const e of testFstDecl.checkErrors) {
        console.log('  Error:', String(e.message || e).slice(0, 300));
      }
    }
  });
});

function findDecl(result: ReturnType<typeof compileTTFromText>, name: string) {
  return result.blocks.flatMap(b => b.declarations).find(d => d.name === name);
}

describe('record projection end-to-end type checking', () => {

  test('Pair.fst and Pair.snd type-check correctly', () => {
    const source = `
record Pair (A B : Type) where
  constructor MkPair
  fst : A
  snd : B

inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Equal : {A : Type} -> A -> A -> Type where
  refl : {A : Type} -> {a : A} -> Equal a a

myPair : Pair Nat Nat
myPair = MkPair Zero (Succ Zero)

testFst : Equal (Pair.fst myPair) Zero
testFst = refl

testSnd : Equal (Pair.snd myPair) (Succ Zero)
testSnd = refl
`;
    const result = compileTTFromText(source);
    const fstDecl = findDecl(result, 'testFst');
    const sndDecl = findDecl(result, 'testSnd');
    expect(fstDecl?.checkSuccess).toBe(true);
    expect(sndDecl?.checkSuccess).toBe(true);
  });

  test('dpairElim with dependent motive C (DPair.fst d)', () => {
    const source = `
record DPair {u v : ULevel} (A : Type u) (B : A -> Type v) : Type (UMax u v) where
  constructor MkDPair
  fst : A
  snd : B fst

dpairElim : {A : Type} -> {B : A -> Type} -> (C : DPair A B -> Type) -> ((x : A) -> (y : B x) -> C (MkDPair x y)) -> (d : DPair A B) -> C d
dpairElim C f (MkDPair a b) = f a b
`;
    const result = compileTTFromText(source);
    const testDecl = findDecl(result, 'dpairElim');
    expect(testDecl?.checkSuccess).toBe(true);
  });

  test('Sigma.fst type-checks correctly', () => {
    const source = `
record Sigma (A : Type) (B : A -> Type) : Type where
  constructor MkSigma
  fst : A
  snd : B fst

inductive Nat : Type where
  Zero : Nat

P : Nat -> Type
P n = Nat

mySigma : Sigma Nat P
mySigma = MkSigma Zero Zero

getFst : Nat
getFst = Sigma.fst mySigma
`;
    const result = compileTTFromText(source);
    const fstDecl = findDecl(result, 'getFst');
    expect(fstDecl?.checkSuccess).toBe(true);
  });

  test('3-field record projections type-check correctly', () => {
    const source = `
record Triple (A B C : Type) where
  constructor MkTriple
  first : A
  second : B
  third : C

inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Equal : {A : Type} -> A -> A -> Type where
  refl : {A : Type} -> {a : A} -> Equal a a

myTriple : Triple Nat Nat Nat
myTriple = MkTriple Zero (Succ Zero) (Succ (Succ Zero))

testFirst : Equal (Triple.first myTriple) Zero
testFirst = refl

testSecond : Equal (Triple.second myTriple) (Succ Zero)
testSecond = refl

testThird : Equal (Triple.third myTriple) (Succ (Succ Zero))
testThird = refl
`;
    const result = compileTTFromText(source);
    const firstDecl = findDecl(result, 'testFirst');
    const secondDecl = findDecl(result, 'testSecond');
    const thirdDecl = findDecl(result, 'testThird');
    expect(firstDecl?.checkSuccess).toBe(true);
    expect(secondDecl?.checkSuccess).toBe(true);
    expect(thirdDecl?.checkSuccess).toBe(true);
  });
});

describe('pattern-matching function kernel value inspection', () => {

  test('DPair.fst projection kernel value uses Var(0)', () => {
    const source = `
record DPair {u v : ULevel} (A : Type u) (B : A -> Type v) : Type (UMax u v) where
  constructor MkDPair
  fst : A
  snd : B fst

test : Type
test = Type
`;
    const result = compileTTFromText(source);
    const defs = result.definitions;

    // Get the projection definition from the definitions map
    const fstDef = defs.terms.get('DPair.fst');
    expect(fstDef).toBeDefined();

    // DPair.fst value is: λu. λv. λA. λB. λr. match r with { MkDPair _ _ _ _ fst _ => Var(0) }
    // Unwrap lambdas to get to the Match
    let current: any = fstDef!.value;
    let lamCount = 0;
    while (current?.tag === 'Binder' && current.binderKind?.tag === 'BLam') {
      lamCount++;
      current = current.body;
    }
    expect(current.tag).toBe('Match');
    if (current.tag === 'Match') {
      const clause = current.clauses[0];
      // RHS should be Var(0) — the single PVar binding
      expect(clause.rhs).toEqual({ tag: 'Var', index: 0 });

      // The pattern should have MkDPair with 6 args (4 params + 2 fields)
      // Only the target field (fst) should be PVar, everything else PWild
      expect(clause.patterns[0].tag).toBe('PCtor');
      if (clause.patterns[0].tag === 'PCtor') {
        expect(clause.patterns[0].name).toBe('MkDPair');
        expect(clause.patterns[0].args).toHaveLength(6);
        // fst is at index 4 (0-based: u, v, A, B, fst, snd)
        expect(clause.patterns[0].args[4].tag).toBe('PVar');
        expect(clause.patterns[0].args[4].name).toBe('fst');
        // All others should be PWild
        expect(clause.patterns[0].args[0].tag).toBe('PWild');
        expect(clause.patterns[0].args[1].tag).toBe('PWild');
        expect(clause.patterns[0].args[2].tag).toBe('PWild');
        expect(clause.patterns[0].args[3].tag).toBe('PWild');
        expect(clause.patterns[0].args[5].tag).toBe('PWild');
      }
    }
  });

  test('record with 5+ fields: each projection returns correct field', () => {
    const source = `
record BigRecord (A : Type) where
  constructor MkBig
  f1 : A
  f2 : A
  f3 : A
  f4 : A
  f5 : A

test : Type
test = Type
`;
    const result = compileTTFromText(source);
    const defs = result.definitions;

    const A = mkVar(5);
    const a1 = mkVar(4);
    const a2 = mkVar(3);
    const a3 = mkVar(2);
    const a4 = mkVar(1);
    const a5 = mkVar(0);

    const big = mkApp(mkApp(mkApp(mkApp(mkApp(mkApp(
      mkConst('MkBig'), A), a1), a2), a3), a4), a5);

    for (let i = 0; i < 5; i++) {
      const projName = `BigRecord.f${i + 1}`;
      const proj = mkApp(mkApp(mkConst(projName), A), big);
      const reduced = whnf(proj, { definitions: defs });
      const expected = mkVar(4 - i); // f1=Var(4), f2=Var(3), ..., f5=Var(0)
      expect(reduced).toEqual(expected);
    }
  });

  test('real-analysis projections work correctly', { timeout: 140000 }, async () => {
    const { REAL_ANALYSIS_CODE } = await import('../presets/real-analysis');
    const result = compileTTFromText(REAL_ANALYSIS_CODE);

    const addProj = result.definitions.terms.get('CompleteOrderedField.add');
    const zeroProj = result.definitions.terms.get('CompleteOrderedField.zero');
    expect(addProj?.value ? prettyProjection(addProj.value) : '').toContain('=> add');
    expect(zeroProj?.value ? prettyProjection(zeroProj.value) : '').toContain('=> zero');
  });

  test('eitherElim kernel RHS keeps the expected branch variable references', () => {
    const source = `
inductive Either : Type -> Type -> Type where
  Left : {A B : Type} -> A -> Either A B
  Right : {A B : Type} -> B -> Either A B

eitherElim : {A B C : Type} -> (A -> C) -> (B -> C) -> Either A B -> C
eitherElim f g (Left a) = f a
eitherElim f g (Right b) = g b
`;
    const result = compileTTFromText(source);
    const eitherElimDecl = findDecl(result, 'eitherElim');
    expect(eitherElimDecl?.checkSuccess).toBe(true);

    const kernelValue = eitherElimDecl!.kernelValue!;
    expect(kernelValue.tag).toBe('Match');
    if (kernelValue.tag !== 'Match') return;

    // Clause 0: eitherElim f g (Left a) = f a
    const clause0 = kernelValue.clauses[0];
    expect(clause0.rhs.tag).toBe('App');
    if (clause0.rhs.tag === 'App') {
      expect(clause0.rhs.fn.tag).toBe('Var');
      expect(clause0.rhs.arg.tag).toBe('Var');
      expect(prettyPrintFormatted(clause0.rhs, clause0.contextNames)).toBe('(f a)');
    }

    // Clause 1: eitherElim f g (Right b) = g b
    const clause1 = kernelValue.clauses[1];
    expect(clause1.rhs.tag).toBe('App');
    if (clause1.rhs.tag === 'App') {
      expect(clause1.rhs.fn.tag).toBe('Var');
      expect(clause1.rhs.arg.tag).toBe('Var');
      expect(prettyPrintFormatted(clause1.rhs, clause1.contextNames)).toBe('(g b)');
    }
  });

  test('eitherElim with explicit named patterns keeps branch variable references in runtime order', () => {
    const source = `
inductive Either : Type -> Type -> Type where
  Left : {A B : Type} -> A -> Either A B
  Right : {A B : Type} -> B -> Either A B

eitherElim : {A B C : Type} -> (A -> C) -> (B -> C) -> Either A B -> C
eitherElim {A} {B} {C} f g (Left a) = f a
eitherElim {A} {B} {C} f g (Right b) = g b
`;
    const result = compileTTFromText(source);
    const eitherElimDecl = findDecl(result, 'eitherElim');
    expect(eitherElimDecl?.checkSuccess).toBe(true);

    const kernelValue = eitherElimDecl!.kernelValue!;
    expect(kernelValue.tag).toBe('Match');
    if (kernelValue.tag !== 'Match') return;

    expect(prettyPrintFormatted(kernelValue.clauses[0]!.rhs, kernelValue.clauses[0]!.contextNames)).toBe('(f a)');
    expect(prettyPrintFormatted(kernelValue.clauses[1]!.rhs, kernelValue.clauses[1]!.contextNames)).toBe('(g b)');
  });

  test('eitherElim with explicit named patterns still computes by refl', () => {
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Equal : {A : Type} -> A -> A -> Type where
  refl : {A : Type} -> {a : A} -> Equal {A} a a

inductive Either : Type -> Type -> Type where
  Left : {A B : Type} -> A -> Either A B
  Right : {A B : Type} -> B -> Either A B

eitherElim : {A B C : Type} -> (A -> C) -> (B -> C) -> Either A B -> C
eitherElim {A} {B} {C} f g (Left a) = f a
eitherElim {A} {B} {C} f g (Right b) = g b

leftBeta : (a b : Nat) -> Equal (eitherElim (\\_ => a) (\\_ => b) (Left a)) a
leftBeta a b = refl
`;
    const result = compileTTFromText(source);
    const leftBetaDecl = findDecl(result, 'leftBeta');
    expect(leftBetaDecl?.checkSuccess).toBe(true);
  });
});
