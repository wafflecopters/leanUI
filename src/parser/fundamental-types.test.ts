/**
 * Tests for fundamental inductive types (Nat, List, Vec, Fin, Equal, etc.)
 *
 * These are the core types that any proof assistant should be able to parse
 * and type check successfully.
 *
 * Note: This compiler requires explicit type parameters. Implicit parameter
 * syntax like `Nil : List A` is not supported - use `Nil : (A : Type) -> List A`.
 */

import { describe, test, expect } from 'vitest';
import { compileSource } from '../test-utils';

describe('Fundamental Inductive Types', () => {
  describe('Natural Numbers', () => {
    test('Nat: basic definition', () => {
      const source = `inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat`;

      const results = compileSource(source);

      expect(results.length).toBe(1);
      expect(results[0].parseSuccess).toBe(true);
      expect(results[0].checkSuccess).toBe(true);
      expect(results[0].checkErrors.length).toBe(0);
      expect(results[0].name).toBe('Nat');
    });
  });

  describe('Lists', () => {
    test('List: polymorphic list definition', () => {
      // Explicit type parameter required (no implicit parameter support)
      const source = `inductive List : Type -> Type where
  Nil : (A : Type) -> List A
  Cons : (A : Type) -> A -> List A -> List A`;

      const results = compileSource(source);

      expect(results.length).toBe(1);
      expect(results[0].parseSuccess).toBe(true);
      expect(results[0].checkSuccess).toBe(true);
      expect(results[0].checkErrors.length).toBe(0);
      expect(results[0].name).toBe('List');
    });
  });

  describe('Booleans', () => {
    test('Bool: boolean type', () => {
      const source = `inductive Bool : Type where
  True : Bool
  False : Bool`;

      const results = compileSource(source);

      expect(results.length).toBe(1);
      expect(results[0].parseSuccess).toBe(true);
      expect(results[0].checkSuccess).toBe(true);
      expect(results[0].checkErrors.length).toBe(0);
      expect(results[0].name).toBe('Bool');
    });
  });

  describe('Unit Type', () => {
    test('Unit: trivial type', () => {
      const source = `inductive Unit : Type where
  unit : Unit`;

      const results = compileSource(source);

      expect(results.length).toBe(1);
      expect(results[0].parseSuccess).toBe(true);
      expect(results[0].checkSuccess).toBe(true);
      expect(results[0].checkErrors.length).toBe(0);
      expect(results[0].name).toBe('Unit');
    });
  });

  describe('Empty Type', () => {
    test('Empty: empty type with no constructors', () => {
      const source = `inductive Empty : Type where`;

      const results = compileSource(source);

      expect(results.length).toBe(1);
      expect(results[0].parseSuccess).toBe(true);
      expect(results[0].checkSuccess).toBe(true);
      expect(results[0].checkErrors.length).toBe(0);
      expect(results[0].name).toBe('Empty');
    });
  });

  describe('Sum Type', () => {
    test('Sum: binary sum type', () => {
      // Explicit type parameters required
      const source = `inductive Sum : Type -> Type -> Type where
  Left : (A : Type) -> (B : Type) -> A -> Sum A B
  Right : (A : Type) -> (B : Type) -> B -> Sum A B`;

      const results = compileSource(source);

      expect(results.length).toBe(1);
      expect(results[0].parseSuccess).toBe(true);
      expect(results[0].checkSuccess).toBe(true);
      expect(results[0].checkErrors.length).toBe(0);
      expect(results[0].name).toBe('Sum');
    });
  });

  describe('Product Type', () => {
    test('Prod: binary product type', () => {
      // Explicit type parameters required
      const source = `inductive Prod : Type -> Type -> Type where
  Pair : (A : Type) -> (B : Type) -> A -> B -> Prod A B`;

      const results = compileSource(source);

      expect(results.length).toBe(1);
      expect(results[0].parseSuccess).toBe(true);
      expect(results[0].checkSuccess).toBe(true);
      expect(results[0].checkErrors.length).toBe(0);
      expect(results[0].name).toBe('Prod');
    });
  });

  describe('Option Type', () => {
    test('Option: optional value type', () => {
      // Explicit type parameter required
      const source = `inductive Option : Type -> Type where
  None : (A : Type) -> Option A
  Some : (A : Type) -> A -> Option A`;

      const results = compileSource(source);

      expect(results.length).toBe(1);
      expect(results[0].parseSuccess).toBe(true);
      expect(results[0].checkSuccess).toBe(true);
      expect(results[0].checkErrors.length).toBe(0);
      expect(results[0].name).toBe('Option');
    });
  });

  describe('Vectors', () => {
    test('Vec: length-indexed vectors', () => {
      // Need Nat defined first, explicit parameters required
      const source = `inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Vec : Type -> Nat -> Type where
  VNil : (A : Type) -> Vec A Zero
  VCons : (A : Type) -> (n : Nat) -> A -> Vec A n -> Vec A (Succ n)`;

      const results = compileSource(source);

      expect(results.length).toBe(2);
      expect(results[0].parseSuccess).toBe(true);
      expect(results[0].checkSuccess).toBe(true);
      expect(results[1].parseSuccess).toBe(true);
      expect(results[1].checkSuccess).toBe(true);
      expect(results[1].name).toBe('Vec');
    });
  });

  describe('Finite Numbers', () => {
    test('Fin: bounded natural numbers', () => {
      // Need Nat defined first, explicit parameters required
      const source = `inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Fin : Nat -> Type where
  FZero : (n : Nat) -> Fin (Succ n)
  FSucc : (n : Nat) -> Fin n -> Fin (Succ n)`;

      const results = compileSource(source);

      expect(results.length).toBe(2);
      expect(results[0].parseSuccess).toBe(true);
      expect(results[0].checkSuccess).toBe(true);
      expect(results[1].parseSuccess).toBe(true);
      expect(results[1].checkSuccess).toBe(true);
      expect(results[1].name).toBe('Fin');
    });
  });

  describe('Equality', () => {
    test('Eq: propositional equality', () => {
      // Explicit type and value parameters required
      const source = `inductive Eq : (A : Type) -> A -> A -> Type where
  Refl : (A : Type) -> (x : A) -> Eq A x x`;

      const results = compileSource(source);

      expect(results.length).toBe(1);
      expect(results[0].parseSuccess).toBe(true);
      expect(results[0].checkSuccess).toBe(true);
      expect(results[0].checkErrors.length).toBe(0);
      expect(results[0].name).toBe('Eq');
    });
  });

  describe('Existential', () => {
    test('Exists: sigma type (dependent pair)', () => {
      // Explicit parameters required
      const source = `inductive Exists : (A : Type) -> (A -> Type) -> Type where
  ExIntro : (A : Type) -> (P : A -> Type) -> (x : A) -> P x -> Exists A P`;

      const results = compileSource(source);

      expect(results.length).toBe(1);
      expect(results[0].parseSuccess).toBe(true);
      expect(results[0].checkSuccess).toBe(true);
      expect(results[0].checkErrors.length).toBe(0);
      expect(results[0].name).toBe('Exists');
    });
  });

  describe('Accessibility', () => {
    // NOTE: The traditional Acc type is NOT strictly positive because the constructor
    // takes a function argument `(y : A) -> R y x -> Acc A R y` where `Acc` appears
    // in a negative position (argument of a function). This compiler enforces strict
    // positivity, so this definition is correctly rejected.
    //
    // Supporting non-strict positivity would require sized types or similar mechanisms.
    test('Acc: rejected due to non-strict positivity', () => {
      const source = `inductive Acc : (A : Type) -> (A -> A -> Type) -> A -> Type where
  AccIntro : (A : Type) -> (R : A -> A -> Type) -> (x : A) -> ((y : A) -> R y x -> Acc A R y) -> Acc A R x`;

      const results = compileSource(source);

      expect(results.length).toBe(1);
      expect(results[0].parseSuccess).toBe(true);
      // Should fail type check due to non-strict positivity
      expect(results[0].checkSuccess).toBe(false);
      expect(results[0].checkErrors.some(e =>
        e.message.includes('positive')
      )).toBe(true);
      expect(results[0].name).toBe('Acc');
    });
  });

  describe('Multiple Types', () => {
    test('Multiple fundamental types together', () => {
      const source = `inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Bool : Type where
  True : Bool
  False : Bool

inductive List : Type -> Type where
  Nil : (A : Type) -> List A
  Cons : (A : Type) -> A -> List A -> List A`;

      const results = compileSource(source);

      expect(results.length).toBe(3);
      expect(results[0].name).toBe('Nat');
      expect(results[1].name).toBe('Bool');
      expect(results[2].name).toBe('List');
      expect(results.every(r => r.parseSuccess)).toBe(true);
      expect(results.every(r => r.checkSuccess)).toBe(true);
    });
  });

  describe('Multiline Signatures', () => {
    test('Multiline inductive type signature with where', () => {
      const source = `inductive Foo : Type
  -> Type where
  Bar : Foo`;

      const results = compileSource(source);

      expect(results.length).toBe(1);
      expect(results[0].parseSuccess).toBe(true);
      expect(results[0].checkSuccess).toBe(true);
      expect(results[0].name).toBe('Foo');
      expect(results[0].declarations?.[0].kernelConstructors?.length).toBe(1);
    });
  });
});
