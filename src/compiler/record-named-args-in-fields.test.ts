import { describe, test, expect } from 'vitest';
import { compileTTFromText } from './compile';

describe('Named args in record/inductive field types', () => {
  test('record field type can use named args', () => {
    const source = `
inductive Equal : {A : Type} -> A -> A -> Type where
  refl : {A : Type} -> {a : A} -> Equal a a

record LeftMonoid (A : Type) where
  op : A -> A -> A
  e : A
  identLeft : (a : A) -> Equal {A} (op a e) a
`;
    const result = compileTTFromText(source);
    const allDecls = result.blocks.flatMap(b => (b as any).declarations ?? []);

    const leftMonoidDecl = allDecls.find((d: any) => d?.name === 'LeftMonoid');
    console.log('LeftMonoid checkErrors:', leftMonoidDecl?.checkErrors?.map((e: any) => e?.message));
    expect(leftMonoidDecl?.checkSuccess).toBe(true);
  });

  test('inductive constructor type can use named args', () => {
    const source = `
inductive Equal : {A : Type} -> A -> A -> Type where
  refl : {A : Type} -> {a : A} -> Equal a a

inductive LeftMonoid' : Type -> Type where
  MkLeftMonoid' : {A : Type} -> (op : A -> A -> A) -> (e : A) -> (identLeft : ((a : A) -> Equal {A} (op a e) a)) -> LeftMonoid' A
`;
    const result = compileTTFromText(source);
    const allDecls = result.blocks.flatMap(b => (b as any).declarations ?? []);

    const leftMonoidDecl = allDecls.find((d: any) => d?.name === "LeftMonoid'");
    console.log("LeftMonoid' checkErrors:", leftMonoidDecl?.checkErrors?.map((e: any) => e?.message));
    expect(leftMonoidDecl?.checkSuccess).toBe(true);
  });

  test('record field type with inferred type arg (no crash on Hole)', () => {
    // This tests that positivity checking handles Holes properly
    const source = `
inductive Equal : {A : Type} -> A -> A -> Type where
  refl : {A : Type} -> {a : A} -> Equal a a

record LeftMonoid (A : Type) where
  op : A -> A -> A
  e : A
  identLeft : (a : A) -> Equal (op a e) a
`;
    // This should compile without crashing - the {A} is inferred
    const result = compileTTFromText(source);
    const allDecls = result.blocks.flatMap(b => (b as any).declarations ?? []);

    const leftMonoidDecl = allDecls.find((d: any) => d?.name === 'LeftMonoid');
    console.log('LeftMonoid (inferred) checkErrors:', leftMonoidDecl?.checkErrors?.map((e: any) => e?.message));
    // We expect this to type-check successfully since A should be inferred
    expect(leftMonoidDecl?.checkSuccess).toBe(true);
  });

  test('simple record extends', () => {
    // Test a simple extends case without complex types
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

record Point where
  x : Nat
  y : Nat

record ColoredPoint extends Point where
  color : Nat
`;
    const result = compileTTFromText(source);
    const allDecls = result.blocks.flatMap(b => (b as any).declarations ?? []);

    const pointDecl = allDecls.find((d: any) => d?.name === 'Point');
    console.log('Point checkErrors:', pointDecl?.checkErrors?.map((e: any) => e?.message));
    expect(pointDecl?.checkSuccess).toBe(true);

    const coloredPointDecl = allDecls.find((d: any) => d?.name === 'ColoredPoint');
    console.log('ColoredPoint checkErrors:', coloredPointDecl?.checkErrors?.map((e: any) => e?.message));
    expect(coloredPointDecl?.checkSuccess).toBe(true);
  });

  test('record with extends and parameterized parent', () => {
    // Test that extends works with parameterized parent records.
    // Local fields CAN reference inherited fields by name.
    const source = `
inductive Equal : {A : Type} -> A -> A -> Type where
  refl : {A : Type} -> {a : A} -> Equal a a

record Semigroup (A : Type) where
  op : A -> A -> A
  assoc : (a b c : A) -> Equal (op (op a b) c) (op a (op b c))

record Monoid (A : Type) extends Semigroup A where
  e : A
  identLeft : (a : A) -> Equal (op e a) a
  identRight : (a : A) -> Equal (op a e) a
`;
    const result = compileTTFromText(source);
    const allDecls = result.blocks.flatMap(b => (b as any).declarations ?? []);

    const semigroupDecl = allDecls.find((d: any) => d?.name === 'Semigroup');
    console.log('Semigroup checkSuccess:', semigroupDecl?.checkSuccess);
    console.log('Semigroup checkErrors:', semigroupDecl?.checkErrors?.map((e: any) => e?.message));
    expect(semigroupDecl?.checkSuccess).toBe(true);

    const monoidDecl = allDecls.find((d: any) => d?.name === 'Monoid');
    console.log('Monoid extends checkSuccess:', monoidDecl?.checkSuccess);
    console.log('Monoid extends checkErrors:', monoidDecl?.checkErrors?.map((e: any) => e?.message));
    expect(monoidDecl?.checkSuccess).toBe(true);
  });
});
