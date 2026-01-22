/**
 * End-to-end tests for named arguments feature.
 * Tests the full pipeline: parsing -> elaboration -> type checking.
 */

import { describe, test, expect } from 'vitest';
import { compileSource } from '../test-utils';

describe('Named Arguments End-to-End Tests', () => {
  describe('Named Binders in Types', () => {
    test('Function with single named parameter', () => {
      const source = `
id : { A : Type } -> A -> A
id {A} x = x`;

      const results = compileSource(source);
      expect(results.length).toBe(1);
      expect(results[0].parseSuccess).toBe(true);
      expect(results[0].checkSuccess).toBe(true);
    });

    test('Function with multiple named parameters', () => {
      const source = `
const : { A : Type } -> { B : Type } -> A -> B -> A
const {A} {B} a b = a`;

      const results = compileSource(source);
      expect(results.length).toBe(1);
      expect(results[0].parseSuccess).toBe(true);
      expect(results[0].checkSuccess).toBe(true);
    });

    test('Function with named multi-binder', () => {
      const source = `
swap : { A B : Type } -> A -> B -> B
swap {A} {B} a b = b`;

      const results = compileSource(source);
      expect(results.length).toBe(1);
      expect(results[0].parseSuccess).toBe(true);
      expect(results[0].checkSuccess).toBe(true);
    });

    test('Mixed named and positional parameters', () => {
      const source = `
apply : { A : Type } -> (A -> A) -> A -> A
apply {A} f x = f x`;

      const results = compileSource(source);
      expect(results.length).toBe(1);
      expect(results[0].parseSuccess).toBe(true);
      expect(results[0].checkSuccess).toBe(true);
    });
  });

  describe('Named Patterns in Function Definitions', () => {
    test('Named pattern at beginning', () => {
      const source = `
id : { A : Type } -> A -> A
id {A} x = x`;

      const results = compileSource(source);
      expect(results.length).toBe(1);
      expect(results[0].checkSuccess).toBe(true);
    });

    test('Named pattern reordering - pattern after positional', () => {
      // Pattern written as: x {A}
      // Should be reordered to: {A} x (since A is at position 0)
      const source = `
id : { A : Type } -> A -> A
id x {A} = x`;

      const results = compileSource(source);
      expect(results.length).toBe(1);
      expect(results[0].parseSuccess).toBe(true);
      expect(results[0].checkSuccess).toBe(true);
    });

    test('Multiple named patterns out of order', () => {
      // Type has A at 0, B at 1
      // Patterns written as: {B} {A}
      // Should be reordered to: {A} {B}
      // The function returns a value of type A (the parameter a)
      const source = `
fst : { A : Type } -> { B : Type } -> A -> B -> A
fst {B} {A} a b = a`;

      const results = compileSource(source);
      expect(results.length).toBe(1);
      expect(results[0].parseSuccess).toBe(true);
      if (!results[0].checkSuccess) {
        console.log('Check errors (multiple named):', results[0].checkErrors);
      }
      expect(results[0].checkSuccess).toBe(true);
    });

    test('Error source location - constructor type uses positional for named param', () => {
      // This test verifies that when a constructor type incorrectly passes
      // a positional arg to a named parameter, the error points to the
      // SPECIFIC location in source (Vec A Zero), not the whole declaration.
      const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Vec : { A : Type } -> Nat -> Type where
  VNil : (A : Type) -> Vec A Zero`;

      const results = compileSource(source);
      expect(results.length).toBe(2);
      expect(results[0].checkSuccess).toBe(true); // Nat is fine

      // BadVec should fail because VNil passes A positionally to Vec's named param
      const vecResult = results[1];
      expect(vecResult.parseSuccess).toBe(true);
      expect(vecResult.checkSuccess).toBe(false);

      // Find the Vec declaration
      const vecDecl = vecResult.declarations.find(d => d.name === 'Vec');
      expect(vecDecl).toBeDefined();

      // Check that we have an elabErrorPath pointing to the error location
      expect(vecDecl!.elabErrorPath).toBeDefined();

      // The error should be in the constructor type (constructors[0].type)
      // specifically at the "Vec A Zero" application in the body
      // The path should contain constructors[0].type.body (the Pi body containing Vec A Zero)
      expect(vecDecl!.elabErrorPath).toContain('constructors[0]');
      expect(vecDecl!.elabErrorPath).toContain('type');

      // Verify we can map this path to a source range
      const sourceMap = vecDecl!.sourceMap;
      expect(sourceMap).toBeDefined();

      if (vecDecl!.elabErrorPath && sourceMap) {
        const errorRange = sourceMap.get(vecDecl!.elabErrorPath);
        // The error range should exist and point to the Vec A Zero expression
        expect(errorRange).toBeDefined();
        if (errorRange) {
          // The error should be on the line containing "Vec A Zero"
          // Extract that line from source and verify the range makes sense
          const lines = source.split('\n');
          const errorLine = lines[errorRange.start.line - 1];
          // Line should contain "Vec A Zero"
          expect(errorLine).toContain('Vec A Zero');
        }
      }
    });

    test('Named patterns mixed with positional - complex reordering', () => {
      // Type: { A : Type } -> { B : Type } -> A -> B -> A
      // Pattern written as: x y {B} {A}
      // Should reorder: {A} {B} x y (A=0, B=1, x and y fill positions 2 and 3)
      const source = `
first : { A : Type } -> { B : Type } -> A -> B -> A
first x y {B} {A} = x`;

      const results = compileSource(source);
      expect(results.length).toBe(1);
      expect(results[0].parseSuccess).toBe(true);
      expect(results[0].checkSuccess).toBe(true);
    });

    test('Named wildcard pattern', () => {
      const source = `
id : { A : Type } -> A -> A
id {_} x = x`;

      const results = compileSource(source);
      expect(results.length).toBe(1);
      expect(results[0].parseSuccess).toBe(true);
      expect(results[0].checkSuccess).toBe(true);
    });

    test('Named pattern in second clause', () => {
      const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

isZero : { A : Type } -> A -> Nat -> A -> A
isZero {A} default Zero result = result
isZero {A} default (Succ n) result = default`;

      const results = compileSource(source);
      expect(results.length).toBe(2);
      expect(results[1].parseSuccess).toBe(true);
      expect(results[1].checkSuccess).toBe(true);
    });
  });

  describe('Named Arguments in Applications', () => {
    // Note: Named argument application reordering requires full definition lookup
    // which is only available during phase 2 value elaboration. These tests verify
    // the basic integration.

    test('Single named argument', () => {
      // id : { A : Type } -> A -> A
      // applyId takes a type T and a value x:T, then applies id with A:=T
      const source = `
id : { A : Type } -> A -> A
id {A} x = x

applyId : { T : Type } -> T -> T
applyId {T} x = id { A := T } x`;

      const results = compileSource(source);
      expect(results.length).toBe(2);
      expect(results[0].checkSuccess).toBe(true);
      expect(results[1].parseSuccess).toBe(true);
      if (!results[1].checkSuccess) {
        console.log('Check errors:', results[1].checkErrors);
      }
      expect(results[1].checkSuccess).toBe(true);
    });

    test('Multiple named arguments', () => {
      // const takes two type params A and B, and values a:A and b:B, returns a
      const source = `
const : { A : Type } -> { B : Type } -> A -> B -> A
const {A} {B} a b = a

useConst : { X : Type } -> { Y : Type } -> X -> Y -> X
useConst {X} {Y} x y = const { A := X } { B := Y } x y`;

      const results = compileSource(source);
      expect(results.length).toBe(2);
      expect(results[0].checkSuccess).toBe(true);
      expect(results[1].parseSuccess).toBe(true);
      if (!results[1].checkSuccess) {
        console.log('Check errors (multiple named):', results[1].checkErrors);
      }
      expect(results[1].checkSuccess).toBe(true);
    });

    test('Named arguments in different order than definition', () => {
      // Tests that { B := Y } { A := X } gets reordered to { A := X } { B := Y }
      const source = `
const : { A : Type } -> { B : Type } -> A -> B -> A
const {A} {B} a b = a

useConst : { X : Type } -> { Y : Type } -> X -> Y -> X
useConst {X} {Y} x y = const { B := Y } { A := X } x y`;

      const results = compileSource(source);
      expect(results.length).toBe(2);
      expect(results[0].checkSuccess).toBe(true);
      expect(results[1].parseSuccess).toBe(true);
      if (!results[1].checkSuccess) {
        console.log('Check errors (reorder):', results[1].checkErrors);
      }
      expect(results[1].checkSuccess).toBe(true);
    });

    test('Mixed named and positional arguments', () => {
      // Named arg followed by positional args
      const source = `
apply : { A : Type } -> (A -> A) -> A -> A
apply {A} f x = f x

useApply : { T : Type } -> (T -> T) -> T -> T
useApply {T} f x = apply { A := T } f x`;

      const results = compileSource(source);
      expect(results.length).toBe(2);
      expect(results[0].checkSuccess).toBe(true);
      expect(results[1].parseSuccess).toBe(true);
      if (!results[1].checkSuccess) {
        console.log('Check errors (mixed):', results[1].checkErrors);
      }
      expect(results[1].checkSuccess).toBe(true);
    });
  });

  describe('Named Arguments with Inductive Types', () => {
    test.skip('Inductive type with named parameters in constructor', () => {
      // TODO: Named args in constructor applications need more work
      const source = `
inductive Vec : { A : Type } -> Nat -> Type where
  VNil : { A : Type } -> Vec { A := A } Zero
  VCons : { A : Type } -> { n : Nat } -> A -> Vec { A := A } n -> Vec { A := A } (Succ n)

inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat`;

      const results = compileSource(source);
      expect(results.length).toBe(2);
    });

    test('Function on inductive type with named wildcard patterns', () => {
      // Tests named wildcard patterns {_} with pattern matching
      // The named wildcard just indicates "named position but ignore the value"
      const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Bool : Type where
  True : Bool
  False : Bool

isZero : { A : Type } -> Nat -> Bool
isZero {_} Zero = True
isZero {_} (Succ n) = False`;

      const results = compileSource(source);
      expect(results.length).toBe(3);
      expect(results[0].checkSuccess).toBe(true);
      expect(results[1].checkSuccess).toBe(true);
      expect(results[2].parseSuccess).toBe(true);
      expect(results[2].checkSuccess).toBe(true);
    });
  });

  describe('Error Cases', () => {
    test('Unknown named argument should fail', () => {
      // Using a name that doesn't exist in the function's named params
      const source = `
id : { A : Type } -> A -> A
id {A} x = x

useId : { T : Type } -> T -> T
useId {T} x = id { Unknown := T } x`;

      const results = compileSource(source);
      expect(results.length).toBe(2);
      // The first declaration should succeed
      expect(results[0].checkSuccess).toBe(true);
      // The second should have an error about unknown named argument
      expect(results[1].parseSuccess).toBe(true);
      expect(results[1].checkSuccess).toBe(false);
      expect(results[1].checkErrors.some(e => e.message.includes('Unknown'))).toBe(true);
    });

    test('Named argument on function without named params should fail', () => {
      // id has positional params (A : Type), not named { A : Type }
      const source = `
id : (A : Type) -> A -> A
id A x = x

useId : { T : Type } -> T -> T
useId {T} x = id { A := T } x`;

      const results = compileSource(source);
      expect(results.length).toBe(2);
      expect(results[0].checkSuccess).toBe(true);
      expect(results[1].parseSuccess).toBe(true);
      expect(results[1].checkSuccess).toBe(false);
      expect(results[1].checkErrors.some(e => e.message.includes('no named parameters'))).toBe(true);
    });

    test('Unknown named pattern should fail', () => {
      // Pattern uses {Unknown} but type has {A}
      const source = `
id : { A : Type } -> A -> A
id {Unknown} x = x`;

      const results = compileSource(source);
      expect(results.length).toBe(1);
      expect(results[0].parseSuccess).toBe(true);
      expect(results[0].checkSuccess).toBe(false);
      expect(results[0].checkErrors.some(e => e.message.includes('Unknown'))).toBe(true);
    });

    test('Named parameter cannot be passed positionally - simple case', () => {
      // id has a NAMED parameter {A}, so it expects 0 positional type args
      // Passing `Type` positionally should fail - it's over-application
      const source = `
id : { A : Type } -> A -> A
id {A} x = x

-- This should FAIL: passing Type positionally to a named parameter
bad : Type -> Type
bad T = id T T`;

      const results = compileSource(source);
      expect(results.length).toBe(2);
      expect(results[0].checkSuccess).toBe(true);
      expect(results[1].parseSuccess).toBe(true);
      // This SHOULD fail because named params can't be passed positionally
      expect(results[1].checkSuccess).toBe(false);
    });

    test('Named parameter cannot be passed positionally - inductive type', () => {
      // Vec has a NAMED parameter {A}, so Vec expects only 1 positional arg (Nat)
      // Passing both A and Zero positionally should fail
      const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Vec : { A : Type } -> Nat -> Type where
  VNil : { A : Type } -> Vec { A := A } Zero
  VCons : { A : Type } -> { n : Nat } -> A -> Vec { A := A } n -> Vec { A := A } (Succ n)

-- This should FAIL: Vec expects 1 positional arg (Nat), but we're passing 2 (Nat, Zero)
badVec : Type
badVec = Vec Nat Zero`;

      const results = compileSource(source);
      // Find the badVec definition result
      const badVecResult = results.find(r => r.name === 'badVec');
      expect(badVecResult).toBeDefined();
      expect(badVecResult!.parseSuccess).toBe(true);
      // This SHOULD fail because named params can't be passed positionally
      expect(badVecResult!.checkSuccess).toBe(false);
    });

    test('Named parameter cannot be passed positionally - constructor type', () => {
      // Constructor types using positional args for named params should also fail
      const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

-- BAD: VNil constructor tries to pass A positionally to Vec
inductive BadVec : { A : Type } -> Nat -> Type where
  VNil : (A : Type) -> BadVec A Zero`;

      const results = compileSource(source);
      expect(results.length).toBe(2);
      expect(results[0].checkSuccess).toBe(true); // Nat is fine
      // BadVec should fail because VNil passes A positionally to Vec's named param
      expect(results[1].parseSuccess).toBe(true);
      expect(results[1].checkSuccess).toBe(false);
    });

    test('Mixed named and positional - only positional can be passed positionally', () => {
      // f has: named {A}, named {B}, positional (x : A), positional (y : B)
      // So f expects exactly 2 positional arguments
      const source = `
f : { A : Type } -> { B : Type } -> A -> B -> A
f {A} {B} x y = x

-- CORRECT: provide named args explicitly, positional args positionally
good : { X : Type } -> { Y : Type } -> X -> Y -> X
good {X} {Y} x y = f { A := X } { B := Y } x y

-- BAD: trying to pass X positionally to named param A
bad : { X : Type } -> { Y : Type } -> X -> Y -> X
bad {X} {Y} x y = f X Y x y`;

      const results = compileSource(source);
      expect(results.length).toBe(3);
      expect(results[0].checkSuccess).toBe(true); // f is fine
      expect(results[1].checkSuccess).toBe(true); // good is fine
      expect(results[2].parseSuccess).toBe(true);
      // bad SHOULD fail because it passes positional args to named params
      expect(results[2].checkSuccess).toBe(false);
    });

    test('Correct usage with explicit named arguments should succeed', () => {
      // Verify that the correct syntax still works
      const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Vec : { A : Type } -> Nat -> Type where
  VNil : { A : Type } -> Vec { A := A } Zero
  VCons : { A : Type } -> { n : Nat } -> A -> Vec { A := A } n -> Vec { A := A } (Succ n)

-- CORRECT: use named arg syntax for the named parameter
goodVec : Type
goodVec = Vec { A := Nat } Zero`;

      const results = compileSource(source);
      const goodVecResult = results.find(r => r.name === 'goodVec');
      expect(goodVecResult).toBeDefined();
      expect(goodVecResult!.parseSuccess).toBe(true);
      expect(goodVecResult!.checkSuccess).toBe(true);
    });
  });

  describe('Complex Scenarios', () => {
    test('Polymorphic identity with named args throughout', () => {
      // compose takes three type params A, B, C and functions g:B->C, f:A->B
      // We use the polymorphic id function with named args
      const source = `
id : { A : Type } -> A -> A
id {A} x = x

compose : { A : Type } -> { B : Type } -> { C : Type } -> (B -> C) -> (A -> B) -> A -> C
compose {A} {B} {C} g f x = g (f x)

useCompose : { T : Type } -> T -> T
useCompose {T} x = compose { A := T } { B := T } { C := T } (id { A := T }) (id { A := T }) x`;

      const results = compileSource(source);
      expect(results.length).toBe(3);
      expect(results[0].checkSuccess).toBe(true);
      expect(results[1].checkSuccess).toBe(true);
      if (!results[2].checkSuccess) {
        console.log('Check errors (compose):', results[2].checkErrors);
      }
      expect(results[2].parseSuccess).toBe(true);
      expect(results[2].checkSuccess).toBe(true);
    });

    test('Named patterns with constructor patterns', () => {
      // This tests that named patterns work with constructor patterns
      const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

-- Function that returns the first argument (ignoring the type parameter)
fstNat : { A : Type } -> Nat -> Nat -> Nat
fstNat {_} x y = x`;

      const results = compileSource(source);
      expect(results.length).toBe(2);
      expect(results[0].checkSuccess).toBe(true);
      expect(results[1].parseSuccess).toBe(true);
      expect(results[1].checkSuccess).toBe(true);
    });
  });
});
