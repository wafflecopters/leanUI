import { describe, test, expect } from 'vitest';
import { compileTTFromText } from './compile';

describe('Record extends with universe levels', () => {
  test('record with ULevel param and universe-polymorphic Equal', () => {
    const source = `
inductive Equal : {u : ULevel} -> {A : Type u} -> A -> A -> Type where
  refl : {u : ULevel} -> {A : Type u} -> {a : A} -> Equal a a

record Semigroup {u : ULevel} (A : Type u) : Type u where
  op : A -> A -> A
  assoc : (a b c : A) -> Equal (op (op a b) c) (op a (op b c))

record Monoid {u : ULevel} (A : Type u) : Type u extends Semigroup A where
  e : A
  identLeft : (a : A) -> Equal (op e a) a
  identRight : (a : A) -> Equal (op a e) a
`;
    const result = compileTTFromText(source);
    const allDecls = result.blocks.flatMap(b => (b as any).declarations ?? []);

    const equalDecl = allDecls.find((d: any) => d?.name === 'Equal');
    console.log('Equal checkSuccess:', equalDecl?.checkSuccess);
    console.log('Equal checkErrors:', equalDecl?.checkErrors?.map((e: any) => e?.message));
    expect(equalDecl?.checkSuccess).toBe(true);

    const semigroupDecl = allDecls.find((d: any) => d?.name === 'Semigroup');
    console.log('Semigroup checkSuccess:', semigroupDecl?.checkSuccess);
    console.log('Semigroup checkErrors:', semigroupDecl?.checkErrors?.map((e: any) => e?.message));
    expect(semigroupDecl?.checkSuccess).toBe(true);

    const monoidDecl = allDecls.find((d: any) => d?.name === 'Monoid');
    console.log('Monoid checkSuccess:', monoidDecl?.checkSuccess);
    console.log('Monoid checkErrors:', monoidDecl?.checkErrors?.map((e: any) => e?.message));
    expect(monoidDecl?.checkSuccess).toBe(true);
  });

  test('record with op field and Equal reference (no extends)', () => {
    // This tests whether the issue is with extends or with level inference generally
    const source = `
inductive Equal : {u : ULevel} -> {A : Type u} -> A -> A -> Type where
  refl : {u : ULevel} -> {A : Type u} -> {a : A} -> Equal a a

record MonoidNoExtends {u : ULevel} (A : Type u) : Type u where
  op : A -> A -> A
  e : A
  identLeft : (a : A) -> Equal (op e a) a
`;
    const result = compileTTFromText(source);
    const allDecls = result.blocks.flatMap(b => (b as any).declarations ?? []);

    const monoidDecl = allDecls.find((d: any) => d?.name === 'MonoidNoExtends');
    console.log('MonoidNoExtends checkSuccess:', monoidDecl?.checkSuccess);
    console.log('MonoidNoExtends checkErrors:', monoidDecl?.checkErrors?.map((e: any) => e?.message));
    expect(monoidDecl?.checkSuccess).toBe(true);
  });

  test('simple record with ULevel param needs explicit result sort', () => {
    // Records with ULevel params need explicit result sort annotation
    // Without it, the result defaults to Type 0 which causes universe violations
    const source = `
record Pair {u : ULevel} (A : Type u) : Type u where
  fst : A
  snd : A
`;
    const result = compileTTFromText(source);
    const allDecls = result.blocks.flatMap(b => (b as any).declarations ?? []);

    const pairDecl = allDecls.find((d: any) => d?.name === 'Pair');
    console.log('Pair checkSuccess:', pairDecl?.checkSuccess);
    console.log('Pair checkErrors:', pairDecl?.checkErrors?.map((e: any) => e?.message));
    console.log('Pair prettyType:', pairDecl?.prettyType);
    expect(pairDecl?.checkSuccess).toBe(true);
    // Verify the type is universe polymorphic (Type #0 or Type #1 means it references a level variable)
    expect(pairDecl?.prettyType).toMatch(/Type #\d/);
  });
});
