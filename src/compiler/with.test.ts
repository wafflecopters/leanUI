import { describe, test, expect, beforeEach } from 'vitest';
import { compileTTFromText } from './compile';
import { resetWithCounter } from './with-desugar';

describe('With clauses', () => {
  beforeEach(() => {
    resetWithCounter();
  });

  test('basic with clause - isZero', () => {
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Bool : Type where
  True : Bool
  False : Bool

isZero : Nat -> Bool
isZero n with n
  | Zero => True
  | Succ m => False
`;
    const result = compileTTFromText(source);
    const allDecls = result.blocks.flatMap(b => (b as any).declarations ?? []);

    // Should have: Nat, Bool, isZero, and the auxiliary function
    const natDecl = allDecls.find((d: any) => d?.name === 'Nat');
    expect(natDecl?.checkSuccess).toBe(true);

    const boolDecl = allDecls.find((d: any) => d?.name === 'Bool');
    expect(boolDecl?.checkSuccess).toBe(true);

    // Verify auxiliary function was generated and type-checks
    const auxDecl = allDecls.find((d: any) => d?.name?.startsWith('isZero-with-'));
    expect(auxDecl).toBeDefined();
    expect(auxDecl?.checkSuccess).toBe(true);

    // Verify main function type-checks
    const isZeroDecl = allDecls.find((d: any) => d?.name === 'isZero');
    expect(isZeroDecl?.checkSuccess).toBe(true);
    expect(isZeroDecl?.prettyType).toBe('(Nat -> Bool)');
  });

  test('with clause matching on function arg directly', () => {
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Bool : Type where
  True : Bool
  False : Bool

pred : Nat -> Nat
pred n with n
  | Zero => Zero
  | Succ m => m
`;
    const result = compileTTFromText(source);
    const allDecls = result.blocks.flatMap(b => (b as any).declarations ?? []);

    const predDecl = allDecls.find((d: any) => d?.name === 'pred');
    expect(predDecl?.checkSuccess).toBe(true);
  });

  test('with clause with two patterns', () => {
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

add : Nat -> Nat -> Nat
add m n with m
  | Zero => n
  | Succ k => Succ (add k n)
`;
    const result = compileTTFromText(source);
    const allDecls = result.blocks.flatMap(b => (b as any).declarations ?? []);

    const addDecl = allDecls.find((d: any) => d?.name === 'add');
    expect(addDecl?.checkSuccess).toBe(true);
  });

  test('multiple scrutinees in with', () => {
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Bool : Type where
  True : Bool
  False : Bool

bothZero : Nat -> Nat -> Bool
bothZero m n with m, n
  | Zero, Zero => True
  | _, _ => False
`;
    const result = compileTTFromText(source);
    const allDecls = result.blocks.flatMap(b => (b as any).declarations ?? []);

    const bothZeroDecl = allDecls.find((d: any) => d?.name === 'bothZero');
    expect(bothZeroDecl?.checkSuccess).toBe(true);
  });
});
