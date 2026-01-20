/**
 * Tests for fundamental inductive types (Nat, List, Vec, Fin, Equal, etc.)
 *
 * These are the core types that any proof assistant should be able to parse
 * and type check successfully.
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
      const source = `inductive List : Type -> Type where
  Nil : List A
  Cons : A -> List A -> List A`;

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
      const source = `inductive Sum : Type -> Type -> Type where
  Left : A -> Sum A B
  Right : B -> Sum A B`;

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
      const source = `inductive Prod : Type -> Type -> Type where
  Pair : A -> B -> Prod A B`;

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
      const source = `inductive Option : Type -> Type where
  None : Option A
  Some : A -> Option A`;

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
      const source = `inductive Vec : Type -> Nat -> Type where
  VNil : Vec A Zero
  VCons : A -> Vec A n -> Vec A (Succ n)`;

      const results = compileSource(source);

      expect(results.length).toBe(1);
      expect(results[0].parseSuccess).toBe(true);
      expect(results[0].checkSuccess).toBe(true);
      expect(results[0].checkErrors.length).toBe(0);
      expect(results[0].name).toBe('Vec');
    });
  });

  describe('Finite Numbers', () => {
    test('Fin: bounded natural numbers', () => {
      const source = `inductive Fin : Nat -> Type where
  FZero : Fin (Succ n)
  FSucc : Fin n -> Fin (Succ n)`;

      const results = compileSource(source);

      expect(results.length).toBe(1);
      expect(results[0].parseSuccess).toBe(true);
      expect(results[0].checkSuccess).toBe(true);
      expect(results[0].checkErrors.length).toBe(0);
      expect(results[0].name).toBe('Fin');
    });
  });

  describe('Equality', () => {
    test('Eq: propositional equality', () => {
      const source = `inductive Eq : A -> A -> Type where
  Refl : Eq x x`;

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
      const source = `inductive Exists : (A -> Type) -> Type where
  ExIntro : (x : A) -> P x -> Exists P`;

      const results = compileSource(source);

      expect(results.length).toBe(1);
      expect(results[0].parseSuccess).toBe(true);
      expect(results[0].checkSuccess).toBe(true);
      expect(results[0].checkErrors.length).toBe(0);
      expect(results[0].name).toBe('Exists');
    });
  });

  describe('Accessibility', () => {
    test('Acc: accessibility predicate', () => {
      const source = `inductive Acc : (A -> A -> Type) -> A -> Type where
  AccIntro : ((y : A) -> R y x -> Acc R y) -> Acc R x`;

      const results = compileSource(source);

      expect(results.length).toBe(1);
      expect(results[0].parseSuccess).toBe(true);
      expect(results[0].checkSuccess).toBe(true);
      expect(results[0].checkErrors.length).toBe(0);
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
  Nil : List A
  Cons : A -> List A -> List A`;

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
