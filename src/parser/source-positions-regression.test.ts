/**
 * Regression tests for source position tracking
 *
 * These tests ensure that error detection works correctly.
 * Note: Detailed source position tracking for name resolution errors
 * was removed during the API migration. These tests now focus on
 * ensuring errors are detected correctly.
 */

import { describe, test, expect } from 'vitest';
import { compileSource } from '../test-utils';

describe('Source Position Regression', () => {
  describe('Arrow Type Error Detection', () => {
    test('Error on domain of arrow type is detected', () => {
      const source = `inductive Nat : Type where
  Zero : Nat
  Succ : Na -> Nat`;

      const results = compileSource(source);

      expect(results.length).toBe(1);
      expect(results[0].checkSuccess).toBe(false);
    });

    test('Error on body of arrow type is detected', () => {
      const source = `inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Na`;

      const results = compileSource(source);

      expect(results.length).toBe(1);
      expect(results[0].checkSuccess).toBe(false);
    });

    test('Error in nested arrow type is detected', () => {
      const source = `f : Na -> Nat -> Nat`;

      const results = compileSource(source);

      expect(results.length).toBe(1);
      expect(results[0].checkSuccess).toBe(false);
    });
  });

  describe('Type Signature vs Pattern Clause Error Detection', () => {
    test('Error in type signature is detected', () => {
      const source = `inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

plus : Nat -> Nat -> Na
plus Zero b = b
plus (Succ a) b = Succ (plus a b)`;

      const results = compileSource(source);

      expect(results.length).toBe(2);
      expect(results[0].checkSuccess).toBe(true);
      expect(results[1].checkSuccess).toBe(false);
    });

    test('Error in first argument of type signature is detected', () => {
      const source = `plus : Na -> Nat -> Nat`;

      const results = compileSource(source);

      expect(results.length).toBe(1);
      expect(results[0].checkSuccess).toBe(false);
    });

    test('Error in second argument of type signature is detected', () => {
      const source = `plus : Nat -> Na -> Nat`;

      const results = compileSource(source);

      expect(results.length).toBe(1);
      expect(results[0].checkSuccess).toBe(false);
    });

    test('Error in return type of type signature is detected', () => {
      const source = `plus : Nat -> Nat -> Na`;

      const results = compileSource(source);

      expect(results.length).toBe(1);
      expect(results[0].checkSuccess).toBe(false);
    });
  });

  describe('Inductive Type Signature Error Detection', () => {
    test('Error in inductive type signature is detected', () => {
      const source = `inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Vec : Na -> Type where
  VNil : Vec Zero`;

      const results = compileSource(source);

      expect(results.length).toBe(2);
      expect(results[0].checkSuccess).toBe(true);
      expect(results[1].checkSuccess).toBe(false);
    });

    test('Error in nested inductive type signature is detected', () => {
      const source = `inductive Vec : Nat -> Type -> Wrong where
  VNil : Vec Zero`;

      const results = compileSource(source);

      expect(results.length).toBe(1);
      expect(results[0].checkSuccess).toBe(false);
    });
  });

  describe('Pattern Clause Body Error Detection', () => {
    test('Error in pattern clause body is detected', () => {
      const source = `inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

plus : Nat -> Nat -> Nat
plus Zero b = b
plus (Succ a) b = Succ (plu a b)`;

      const results = compileSource(source);

      expect(results.length).toBe(2);
      expect(results[0].checkSuccess).toBe(true);
      expect(results[1].checkSuccess).toBe(false);
    });

    test('Error in nested application within pattern clause is detected', () => {
      const source = `inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

plus : Nat -> Nat -> Nat
plus Zero b = b
plus (Succ a) b = Succ (plus a wrong)`;

      const results = compileSource(source);

      expect(results.length).toBe(2);
      expect(results[1].checkSuccess).toBe(false);
    });
  });

  describe('Pi Type Error Detection', () => {
    test('Error in Pi type domain is detected', () => {
      const source = `f : (x : Wrong) -> Nat`;

      const results = compileSource(source);

      expect(results.length).toBe(1);
      expect(results[0].checkSuccess).toBe(false);
    });
  });

  describe('Application Error Detection', () => {
    test('Error in function position of application is detected', () => {
      const source = `x = wrongFn arg`;

      const results = compileSource(source);

      expect(results.length).toBe(1);
      expect(results[0].checkSuccess).toBe(false);
    });

    test('Error in argument position of application is detected', () => {
      const source = `inductive Nat : Type where
  Zero : Nat

x = Nat wrongArg`;

      const results = compileSource(source);

      expect(results.length).toBe(2);
      expect(results[1].checkSuccess).toBe(false);
    });

    test('Error in nested application - multiple levels is detected', () => {
      const source = `x = f (g (h wrong))`;

      const results = compileSource(source);

      expect(results.length).toBe(1);
      expect(results[0].checkSuccess).toBe(false);
    });

    test('Error in chained application is detected', () => {
      const source = `x = f g h wrong`;

      const results = compileSource(source);

      expect(results.length).toBe(1);
      expect(results[0].checkSuccess).toBe(false);
    });
  });

  describe('Constructor Type Error Detection', () => {
    test('Error in first constructor type is detected', () => {
      const source = `inductive List : Type where
  Nil : Wrong
  Cons : Nat -> List`;

      const results = compileSource(source);

      expect(results.length).toBe(1);
      expect(results[0].checkSuccess).toBe(false);
    });

    test('Error in second constructor type is detected', () => {
      const source = `inductive Nat : Type where
  Zero : Nat
  Succ : Wrong -> Nat`;

      const results = compileSource(source);

      expect(results.length).toBe(1);
      expect(results[0].checkSuccess).toBe(false);
    });

    test('Error in constructor with complex type is detected', () => {
      const source = `inductive Vec : Nat -> Type where
  VCons : (A : Type) -> (n : Nat) -> A -> Vec n -> Vec (Wrong n)`;

      const results = compileSource(source);

      expect(results.length).toBe(1);
      expect(results[0].checkSuccess).toBe(false);
    });
  });

  describe('Multiple Pattern Clauses Error Detection', () => {
    test('Error in first pattern clause is detected', () => {
      const source = `inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

plus : Nat -> Nat -> Nat
plus Zero b = wrong
plus (Succ a) b = Succ (plus a b)`;

      const results = compileSource(source);

      expect(results.length).toBe(2);
      expect(results[1].checkSuccess).toBe(false);
    });

    test('Error in second pattern clause is detected', () => {
      const source = `inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

plus : Nat -> Nat -> Nat
plus Zero b = b
plus (Succ a) b = wrong a b`;

      const results = compileSource(source);

      expect(results.length).toBe(2);
      expect(results[1].checkSuccess).toBe(false);
    });

    test('Error in third pattern clause is detected', () => {
      const source = `inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

f : Nat -> Nat
f Zero = Zero
f (Succ Zero) = Zero
f (Succ (Succ n)) = wrong n`;

      const results = compileSource(source);

      expect(results.length).toBe(2);
      expect(results[1].checkSuccess).toBe(false);
    });
  });

  describe('Parenthesized Expressions Error Detection', () => {
    test('Error inside parenthesized expression is detected', () => {
      const source = `x = (wrong)`;

      const results = compileSource(source);

      expect(results.length).toBe(1);
      expect(results[0].checkSuccess).toBe(false);
    });

    test('Error in nested parenthesized expressions is detected', () => {
      const source = `x = ((wrong))`;

      const results = compileSource(source);

      expect(results.length).toBe(1);
      expect(results[0].checkSuccess).toBe(false);
    });

    test('Error in parenthesized arrow type is detected', () => {
      const source = `f : (Wrong -> Nat) -> Nat`;

      const results = compileSource(source);

      expect(results.length).toBe(1);
      expect(results[0].checkSuccess).toBe(false);
    });
  });

  describe('Complex Nested Structures Error Detection', () => {
    test('Error in deeply nested lambda is detected', () => {
      const source = `f = fun x => fun y => fun z => wrong x y z`;

      const results = compileSource(source);

      expect(results.length).toBe(1);
      expect(results[0].checkSuccess).toBe(false);
    });

    test('Error in lambda inside application is detected', () => {
      const source = `inductive Nat : Type where
  Zero : Nat

x = Nat (fun y => wrong y)`;

      const results = compileSource(source);

      expect(results.length).toBe(2);
      expect(results[1].checkSuccess).toBe(false);
    });

    test('Error in application inside lambda is detected', () => {
      const source = `f = fun x => wrong x`;

      const results = compileSource(source);

      expect(results.length).toBe(1);
      expect(results[0].checkSuccess).toBe(false);
    });

    test('Multiple errors in same expression are detected', () => {
      const source = `x = wrong1 wrong2 wrong3`;

      const results = compileSource(source);

      expect(results.length).toBe(1);
      expect(results[0].checkSuccess).toBe(false);
    });
  });

  describe('Edge Cases Error Detection', () => {
    test('Error in constructor with no arrow type is detected', () => {
      const source = `inductive Unit : Type where
  MkUnit : Wrong`;

      const results = compileSource(source);

      expect(results.length).toBe(1);
      expect(results[0].checkSuccess).toBe(false);
    });

    test('Error in long chain of arrows is detected', () => {
      const source = `f : A -> B -> C -> D -> Wrong -> F`;

      const results = compileSource(source);

      expect(results.length).toBe(1);
      expect(results[0].checkSuccess).toBe(false);
    });
  });
});
