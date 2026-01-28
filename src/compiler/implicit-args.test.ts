/**
 * Tests for implicit argument handling issues.
 *
 * Investigating problems with plusZeroRight example:
 *
 * plusZeroRight : {n : Nat} -> Equal n (plus n Zero)
 * plusZeroRight {n:=Zero} = refl {A:=Nat} {a:=Zero}
 * plusZeroRight {n:=Succ n} =
 *   let rec = plusZeroRight {n} in
 *     cong rec
 *
 * Issues:
 * 1. Removing just {a:=Zero} causes error
 * 2. Removing both {A:=Nat} {a:=Zero} causes error, but just {A:=Nat} doesn't
 * 3. Elab UI shows unsolved metas - should be error or zonking issue
 * 4. Elab UI shows extra implicit in refl even when all args specified explicitly
 */

import { describe, test, expect } from 'vitest';
import { compileTTFromText } from './compile';
import { resetWildcardCounter } from './elab';

// Standard preamble for all tests
const preamble = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Equal : {A : Type} -> A -> A -> Type where
  refl : {A : Type} -> {a : A} -> Equal a a

plus : Nat -> Nat -> Nat
plus Zero n = n
plus (Succ m) n = Succ (plus m n)

cong : {A B : Type} -> {x y : A} -> (f : A -> B) -> Equal x y -> Equal (f x) (f y)
cong f refl = refl
`;

describe('Implicit argument inference', () => {
  test('refl with all named args explicit: {A:=Nat} {a:=Zero}', () => {
    const source = preamble + `
test : Equal Zero Zero
test = refl {A:=Nat} {a:=Zero}
`;
    const result = compileTTFromText(source);
    const allDecls = result.blocks.flatMap(b => (b as any).declarations ?? []);
    const testDecl = allDecls.find((d: any) => d?.name === 'test');

    console.log('test checkSuccess:', testDecl?.checkSuccess);
    console.log('test checkErrors:', testDecl?.checkErrors?.map((e: any) => e?.message));
    console.log('test prettyValue:', testDecl?.prettyValue);

    expect(testDecl?.checkSuccess).toBe(true);

    // Check for unsolved metas in the pretty-printed output (zonking issue)
    const prettyValue = testDecl?.prettyValue || '';
    const hasUnsolvedMeta = prettyValue.includes('?_implicit') || prettyValue.includes('?m');
    if (hasUnsolvedMeta) {
      console.log('ZONKING BUG: Unsolved metas in prettyValue:', prettyValue);
    }
    expect(hasUnsolvedMeta).toBe(false);
  });

  test('refl with just {A:=Nat} (a inferred)', () => {
    const source = preamble + `
test : Equal Zero Zero
test = refl {A:=Nat}
`;
    const result = compileTTFromText(source);
    const allDecls = result.blocks.flatMap(b => (b as any).declarations ?? []);
    const testDecl = allDecls.find((d: any) => d?.name === 'test');

    console.log('test (A only) checkSuccess:', testDecl?.checkSuccess);
    console.log('test (A only) checkErrors:', testDecl?.checkErrors?.map((e: any) => e?.message));
    console.log('test (A only) prettyValue:', testDecl?.prettyValue);

    expect(testDecl?.checkSuccess).toBe(true);
  });

  test('ISSUE 1: refl with just {a:=Zero} (A inferred) - should work but may fail', () => {
    const source = preamble + `
test : Equal Zero Zero
test = refl {a:=Zero}
`;
    const result = compileTTFromText(source);
    const allDecls = result.blocks.flatMap(b => (b as any).declarations ?? []);
    const testDecl = allDecls.find((d: any) => d?.name === 'test');

    console.log('test (a only) checkSuccess:', testDecl?.checkSuccess);
    console.log('test (a only) checkErrors:', testDecl?.checkErrors?.map((e: any) => e?.message));
    console.log('test (a only) prettyValue:', testDecl?.prettyValue);

    // This SHOULD work - A should be inferred from a's type
    expect(testDecl?.checkSuccess).toBe(true);
  });

  test('ISSUE 2: refl with no named args (both inferred) - should work but may fail', () => {
    resetWildcardCounter(); // Reset counter for clean test

    const source = preamble + `
test : Equal Zero Zero
test = refl
`;
    const result = compileTTFromText(source);
    const allDecls = result.blocks.flatMap(b => (b as any).declarations ?? []);
    const testDecl = allDecls.find((d: any) => d?.name === 'test');

    console.log('test (no args) checkSuccess:', testDecl?.checkSuccess);
    console.log('test (no args) checkErrors:', testDecl?.checkErrors?.map((e: any) => e?.message));
    console.log('test (no args) prettyValue:', testDecl?.prettyValue);
    console.log('test (no args) kernelValue tag:', testDecl?.kernelValue?.tag);
    console.log('test (no args) surfaceValue tag:', testDecl?.surfaceValue?.tag);

    // This SHOULD work - both A and a should be inferred from expected type
    expect(testDecl?.checkSuccess).toBe(true);
  });
});

describe('plusZeroRight variations', () => {
  test('plusZeroRight with all args explicit', () => {
    const source = preamble + `
plusZeroRight : {n : Nat} -> Equal n (plus n Zero)
plusZeroRight {n:=Zero} = refl {A:=Nat} {a:=Zero}
plusZeroRight {n:=Succ n} =
  let rec = plusZeroRight {n} in
    cong Succ rec
`;
    const result = compileTTFromText(source);
    const allDecls = result.blocks.flatMap(b => (b as any).declarations ?? []);
    const pzrDecl = allDecls.find((d: any) => d?.name === 'plusZeroRight');

    console.log('plusZeroRight (full) checkSuccess:', pzrDecl?.checkSuccess);
    console.log('plusZeroRight (full) checkErrors:', pzrDecl?.checkErrors?.map((e: any) => e?.message));
    console.log('plusZeroRight (full) prettyValue:', pzrDecl?.prettyValue);

    expect(pzrDecl?.checkSuccess).toBe(true);

    // ISSUE 3: Check for unsolved metas in elaborated form (zonking bug)
    const prettyValue = pzrDecl?.prettyValue || '';
    const hasUnsolvedMetas = prettyValue.includes('?_implicit') || prettyValue.includes('?m');
    if (hasUnsolvedMetas) {
      console.log('ZONKING BUG: Type check succeeded but unsolved metas remain in output:', prettyValue);
    }
    expect(hasUnsolvedMetas).toBe(false);
  });

  test('ISSUE 1: plusZeroRight removing just {a:=Zero}', () => {
    const source = preamble + `
plusZeroRight : {n : Nat} -> Equal n (plus n Zero)
plusZeroRight {n:=Zero} = refl {A:=Nat}
plusZeroRight {n:=Succ n} =
  let rec = plusZeroRight {n} in
    cong Succ rec
`;
    const result = compileTTFromText(source);
    const allDecls = result.blocks.flatMap(b => (b as any).declarations ?? []);
    const pzrDecl = allDecls.find((d: any) => d?.name === 'plusZeroRight');

    console.log('plusZeroRight (no a) checkSuccess:', pzrDecl?.checkSuccess);
    console.log('plusZeroRight (no a) checkErrors:', pzrDecl?.checkErrors?.map((e: any) => e?.message));

    // This SHOULD work - a should be inferred as Zero from expected type
    expect(pzrDecl?.checkSuccess).toBe(true);
  });

  test('ISSUE 2a: plusZeroRight removing both {A:=Nat} {a:=Zero}', () => {
    const source = preamble + `
plusZeroRight : {n : Nat} -> Equal n (plus n Zero)
plusZeroRight {n:=Zero} = refl
plusZeroRight {n:=Succ n} =
  let rec = plusZeroRight {n} in
    cong Succ rec
`;
    const result = compileTTFromText(source);
    const allDecls = result.blocks.flatMap(b => (b as any).declarations ?? []);
    const pzrDecl = allDecls.find((d: any) => d?.name === 'plusZeroRight');

    console.log('plusZeroRight (no A, no a) checkSuccess:', pzrDecl?.checkSuccess);
    console.log('plusZeroRight (no A, no a) checkErrors:', pzrDecl?.checkErrors?.map((e: any) => e?.message));

    // This SHOULD work - both should be inferred from expected type Equal Zero Zero
    expect(pzrDecl?.checkSuccess).toBe(true);
  });

  test('ISSUE 2b: plusZeroRight removing just {A:=Nat} (a stays)', () => {
    const source = preamble + `
plusZeroRight : {n : Nat} -> Equal n (plus n Zero)
plusZeroRight {n:=Zero} = refl {a:=Zero}
plusZeroRight {n:=Succ n} =
  let rec = plusZeroRight {n} in
    cong Succ rec
`;
    const result = compileTTFromText(source);
    const allDecls = result.blocks.flatMap(b => (b as any).declarations ?? []);
    const pzrDecl = allDecls.find((d: any) => d?.name === 'plusZeroRight');

    console.log('plusZeroRight (no A, yes a) checkSuccess:', pzrDecl?.checkSuccess);
    console.log('plusZeroRight (no A, yes a) checkErrors:', pzrDecl?.checkErrors?.map((e: any) => e?.message));

    // User says this works (no error)
    expect(pzrDecl?.checkSuccess).toBe(true);
  });
});

describe('ISSUE 4: Zonking and elaborated output investigation', () => {
  test('refl elaboration should not show unsolved metas when all args provided', () => {
    const source = preamble + `
test : Equal Zero Zero
test = refl {A:=Nat} {a:=Zero}
`;
    const result = compileTTFromText(source);
    const allDecls = result.blocks.flatMap(b => (b as any).declarations ?? []);
    const testDecl = allDecls.find((d: any) => d?.name === 'test');

    console.log('Elaborated form:', testDecl?.prettyValue);

    // Check type checking succeeded
    expect(testDecl?.checkSuccess).toBe(true);

    // After zonking, there should be no unsolved metas in the output
    const prettyValue = testDecl?.prettyValue || '';
    const hasUnsolvedMeta = prettyValue.includes('?_implicit') || prettyValue.includes('?m');
    console.log('Has unsolved meta in elaborated:', hasUnsolvedMeta);

    expect(hasUnsolvedMeta).toBe(false);
  });

  test('refl with inferred args should not show unsolved metas', () => {
    const source = preamble + `
test : Equal Zero Zero
test = refl
`;
    const result = compileTTFromText(source);
    const allDecls = result.blocks.flatMap(b => (b as any).declarations ?? []);
    const testDecl = allDecls.find((d: any) => d?.name === 'test');

    console.log('Elaborated form (inferred):', testDecl?.prettyValue);

    expect(testDecl?.checkSuccess).toBe(true);

    // After zonking, inferred metas should be replaced with their solutions
    const prettyValue = testDecl?.prettyValue || '';
    const hasUnsolvedMeta = prettyValue.includes('?_implicit') || prettyValue.includes('?m');
    console.log('Has unsolved meta in elaborated (inferred):', hasUnsolvedMeta);

    expect(hasUnsolvedMeta).toBe(false);
  });
});

describe('Named implicit arg matching', () => {
  test('named args should match by name, not position', () => {
    // When we write refl {a:=Zero}, it should match the 'a' parameter
    // regardless of whether A was specified
    const source = preamble + `
-- refl has: {A : Type} -> {a : A} -> Equal a a
-- If we provide {a:=Zero}, A should be inferred as Nat

test1 : Equal Zero Zero
test1 = refl {a:=Zero}

test2 : Equal (Succ Zero) (Succ Zero)
test2 = refl {a:=Succ Zero}
`;
    const result = compileTTFromText(source);
    const allDecls = result.blocks.flatMap(b => (b as any).declarations ?? []);

    const test1Decl = allDecls.find((d: any) => d?.name === 'test1');
    const test2Decl = allDecls.find((d: any) => d?.name === 'test2');

    console.log('test1 checkSuccess:', test1Decl?.checkSuccess);
    console.log('test1 checkErrors:', test1Decl?.checkErrors?.map((e: any) => e?.message));

    console.log('test2 checkSuccess:', test2Decl?.checkSuccess);
    console.log('test2 checkErrors:', test2Decl?.checkErrors?.map((e: any) => e?.message));

    expect(test1Decl?.checkSuccess).toBe(true);
    expect(test2Decl?.checkSuccess).toBe(true);
  });

  test('out-of-order named args should work', () => {
    // If we have f : {A : Type} -> {B : Type} -> {a : A} -> ...
    // Then f {a:=x} {A:=T} should work (B inferred, a and A in any order)
    const source = preamble + `
-- Test that named args can be provided in any order
idPair : {A : Type} -> {B : Type} -> A -> B -> A
idPair a b = a

test : Nat
test = idPair {B:=Nat} {A:=Nat} Zero (Succ Zero)
`;
    const result = compileTTFromText(source);
    const allDecls = result.blocks.flatMap(b => (b as any).declarations ?? []);
    const testDecl = allDecls.find((d: any) => d?.name === 'test');

    console.log('out-of-order named args checkSuccess:', testDecl?.checkSuccess);
    console.log('out-of-order named args checkErrors:', testDecl?.checkErrors?.map((e: any) => e?.message));

    expect(testDecl?.checkSuccess).toBe(true);
  });
});
