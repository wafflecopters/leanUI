/**
 * Tests for name resolution integration in block-checker
 */

import { describe, test, expect } from 'vitest';
import { compileSource } from '../test-utils';

describe('Block-Checker Name Resolution', () => {
  describe('Basic Name Resolution', () => {
    test('Undefined symbol in simple case', () => {
      const source = `plus : Nat -> Nat -> Nat`;

      const results = compileSource(source);

      expect(results.length).toBe(1);
      expect(results[0].parseSuccess).toBe(true);
      // Name resolution is checked during type checking, errors surface as check errors
      expect(results[0].checkSuccess).toBe(false);
    });

    test('Defined symbol works', () => {
      const source = `inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

plus : Nat -> Nat -> Nat
plus Zero b = b
plus (Succ a) b = Succ (plus a b)`;

      const results = compileSource(source);

      expect(results.length).toBe(2);
      expect(results[0].parseSuccess).toBe(true);
      expect(results[0].checkSuccess).toBe(true);
      expect(results[1].parseSuccess).toBe(true);
      expect(results[1].checkSuccess).toBe(true);
    });

    test('Typo case: Na instead of Nat', () => {
      const source = `inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

plus : Nat -> Nat -> Na`;

      const results = compileSource(source);

      expect(results.length).toBe(2);
      expect(results[0].checkSuccess).toBe(true);
      expect(results[1].checkSuccess).toBe(false);
    });
  });

  describe('Forward References', () => {
    test('Forward reference in same block fails', () => {
      const source = `f : A -> A`;

      const results = compileSource(source);

      expect(results.length).toBe(1);
      expect(results[0].checkSuccess).toBe(false);
    });

    test('Symbol from previous block works', () => {
      const source = `inductive Bool : Type where
  True : Bool
  False : Bool

not : Bool -> Bool
not True = False
not False = True`;

      const results = compileSource(source);

      expect(results.length).toBe(2);
      expect(results[0].checkSuccess).toBe(true);
      expect(results[1].checkSuccess).toBe(true);
    });
  });

  describe('Constructors in Scope', () => {
    test('Constructors are in scope', () => {
      const source = `inductive Bool : Type where
  True : Bool
  False : Bool

test : Bool
test = True`;

      const results = compileSource(source);

      expect(results.length).toBe(2);
      expect(results[0].checkSuccess).toBe(true);
      expect(results[1].checkSuccess).toBe(true);
    });

    test('Multiple undefined symbols', () => {
      const source = `f : A -> B -> C`;

      const results = compileSource(source);

      expect(results.length).toBe(1);
      expect(results[0].checkSuccess).toBe(false);
    });
  });

  describe('Self-Reference', () => {
    test('Self-reference in type works', () => {
      const source = `inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat`;

      const results = compileSource(source);

      expect(results.length).toBe(1);
      expect(results[0].checkSuccess).toBe(true);
    });
  });

  describe('Context Accumulation', () => {
    test('Context accumulates across blocks', () => {
      const source = `inductive A : Type where
  MkA : A

inductive B : Type where
  MkB : B

f : A -> B -> A
f a b = a`;

      const results = compileSource(source);

      expect(results.length).toBe(3);
      expect(results[0].checkSuccess).toBe(true);
      expect(results[1].checkSuccess).toBe(true);
      expect(results[2].checkSuccess).toBe(true);
    });
  });

  describe('Parse Errors and Name Resolution', () => {
    test('Parse error in one block does not affect later blocks', () => {
      const source = `inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

bad syntax here!!!

plus : Nat -> Nat -> Nat
plus Zero b = b
plus (Succ a) b = Succ (plus a b)`;

      const results = compileSource(source);

      expect(results.length).toBe(3);
      expect(results[0].checkSuccess).toBe(true);
      expect(results[1].parseSuccess).toBe(false);
      expect(results[2].checkSuccess).toBe(true);
    });
  });
});
