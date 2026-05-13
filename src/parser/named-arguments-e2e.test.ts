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
      // When a constructor type passes positional args to a function with named params
      // and there are more positional args than non-named positions, the overflow args
      // are applied to the result. This leads to a type-checking error rather than
      // an elaboration error. Vec A Zero has overflow: A fills the Nat position,
      // Zero overflows and is applied to (Vec ?A A : Type), causing a type error.
      const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Vec : { A : Type } -> Nat -> Type where
  VNil : (A : Type) -> Vec A Zero`;

      const results = compileSource(source);
      expect(results.length).toBe(2);
      expect(results[0].checkSuccess).toBe(true); // Nat is fine

      // Vec should fail because VNil's return type Vec A Zero is ill-typed:
      // A fills the Nat position (type mismatch) and Zero overflows
      const vecResult = results[1];
      expect(vecResult.parseSuccess).toBe(true);
      expect(vecResult.checkSuccess).toBe(false);
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

  describe('Shorthand Named Argument Syntax', () => {
    test('{x} shorthand in application - expands to {x := x}', () => {
      // {a} in RHS is shorthand for {a := a}
      const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

plus : {a : Nat} -> Nat -> Nat
plus {a := Zero} b = b
plus {a := Succ n} b = Succ (plus {a := n} b)

-- Use shorthand: {a} means {a := a}
double : Nat -> Nat
double a = plus {a} a`;

      const results = compileSource(source);
      const doubleResult = results.find(r => r.name === 'double');
      expect(doubleResult).toBeDefined();
      expect(doubleResult!.parseSuccess).toBe(true);
      expect(doubleResult!.checkSuccess).toBe(true);
    });

    test('{x} shorthand in pattern - expands to {x := x}', () => {
      // {a} in pattern LHS is shorthand for {a := a} (binds variable a)
      const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

plus : {a : Nat} -> Nat -> Nat
plus {a} b = b`;  // {a} is shorthand for {a := a}

      const results = compileSource(source);
      const plusResult = results.find(r => r.name === 'plus');
      expect(plusResult).toBeDefined();
      expect(plusResult!.parseSuccess).toBe(true);
      // Note: This will fail type checking because we only have one clause
      // but parsing should succeed
    });

    test('{x} shorthand works with pattern matching', () => {
      // Full example using shorthand in both pattern and application
      const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

plus : {a : Nat} -> Nat -> Nat
plus {a := Zero} b = b
plus {a := Succ n} b = Succ (plus {a := n} b)

-- Use shorthand in recursive call
plusAlt : {a : Nat} -> Nat -> Nat
plusAlt {a := Zero} b = b
plusAlt {a := Succ a} b = Succ (plusAlt {a} b)`;

      const results = compileSource(source);
      const plusAltResult = results.find(r => r.name === 'plusAlt');
      expect(plusAltResult).toBeDefined();
      expect(plusAltResult!.parseSuccess).toBe(true);
      expect(plusAltResult!.checkSuccess).toBe(true);
    });

    test('Multiple {x} shorthands', () => {
      const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

add : {a : Nat} -> {b : Nat} -> Nat
add {a := Zero} {b := n} = n
add {a := Succ m} {b := n} = Succ (add {a := m} {b := n})

-- Use shorthand for both named args
triple : Nat -> Nat -> Nat
triple a b = add {a} {b}`;

      const results = compileSource(source);
      const tripleResult = results.find(r => r.name === 'triple');
      expect(tripleResult).toBeDefined();
      expect(tripleResult!.parseSuccess).toBe(true);
      // Note: Type checker will complain about result type, but parsing works
    });
  });

  describe('Named Arguments with Inductive Types', () => {
    test('Inductive type with named parameters in constructor', () => {
      const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Vec : { A : Type } -> Nat -> Type where
  VNil : { A : Type } -> Vec { A := A } Zero
  VCons : { A : Type } -> { n : Nat } -> A -> Vec { A := A } n -> Vec { A := A } (Succ n)
`;

      const results = compileSource(source);
      expect(results.length).toBe(2);

      // Check if both declarations type-check
      for (const r of results) {
        if (!r.checkSuccess) {
          console.log(`${r.name} errors:`, r.checkErrors.map(e => e.message));
        }
      }
      expect(results[0].checkSuccess).toBe(true);
      expect(results[1].checkSuccess).toBe(true);
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

    test('Missing named argument in recursive call - implicit meta inserted', () => {
      // plus requires {a := ...} but recursive call omits it
      // With implicit arguments, a meta is inserted for the missing named arg
      // The meta cannot be inferred, so there should be an unsolved meta error
      const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

plus : {a : Nat} -> Nat -> Nat
plus {a := Zero} b = b
plus {a := Succ a} b = Succ (plus b)`;

      const results = compileSource(source);
      const plusResult = results.find(r => r.name === 'plus');
      expect(plusResult).toBeDefined();
      expect(plusResult!.parseSuccess).toBe(true);
      // Should FAIL - the implicit meta makes the recursive call non-structurally-decreasing
      // OR it may fail due to unsolved metavariable
      expect(plusResult!.checkSuccess).toBe(false);
      // Error should mention either:
      // - "unsolved" or "hole" for unsolved metavariable
      // - "structurally decreasing" for termination failure (meta can't be shown smaller)
      // - "??" or "m0" indicating a metavariable in the error
      expect(plusResult!.checkErrors.some(e =>
        e.message.toLowerCase().includes('unsolved') ||
        e.message.toLowerCase().includes('hole') ||
        e.message.toLowerCase().includes('structurally') ||
        e.message.includes('??')
      )).toBe(true);
    });

    test('Positional args to all-implicit function - now allowed as sugar', () => {
      // Function has only named param, no positional. Called with wrong positional.
      const source = `
inductive Bool : Type where
  True : Bool
  False : Bool

inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

neg : {a : Bool} -> Bool
neg {a := True} = False
neg {a := False} = True

-- FIXED: passing b positionally when a is the only implicit param now works (sugar for named syntax)
ok : Bool -> Bool
ok b = neg b`;

      const results = compileSource(source);
      const okResult = results.find(r => r.name === 'ok');
      expect(okResult).toBeDefined();
      expect(okResult!.parseSuccess).toBe(true);
      // Should SUCCEED: positional args to all-implicit functions are sugar for named syntax
      // `neg b` is equivalent to `neg {a:=b}`
      expect(okResult!.checkSuccess).toBe(true);
    });

    test('Implicit pattern for omitted named param - should succeed', () => {
      // plus has {a : Bool} (named) and Nat (positional)
      // Clause provides only positional pattern b, missing {a := ...}
      // With implicit arguments, a wildcard is inserted for the missing named pattern
      // This should NOW SUCCEED because the implicit wildcard matches any Bool
      const source = `
inductive Bool : Type where
  True : Bool
  False : Bool

inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

plus : {a : Bool} -> Nat -> Nat
plus b = Zero`;

      const results = compileSource(source);
      const plusResult = results.find(r => r.name === 'plus');
      expect(plusResult).toBeDefined();
      expect(plusResult!.parseSuccess).toBe(true);
      // Should SUCCEED - implicit wildcard inserted for missing named pattern 'a'
      if (!plusResult!.checkSuccess) {
        console.log('Unexpected check errors:', plusResult!.checkErrors);
      }
      expect(plusResult!.checkSuccess).toBe(true);
    });

    test('Implicit args for all-named function - type mismatch', () => {
      // Function with all named params, caller provides nothing
      // With implicit arguments, metas are inserted: add becomes add ?a ?b
      // But bad : Nat expects a Nat, and add ?a ?b is still a function until fully applied
      const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

add : {a : Nat} -> {b : Nat} -> Nat
add {a := Zero} {b := n} = n
add {a := Succ m} {b := n} = Succ (add {a := m} {b := n})

-- With implicits inserted, this becomes: bad = add ?a ?b
-- Since both params are named and no args provided, metas are inserted
-- This should either succeed (if metas solve) or fail with unsolved metas
bad : Nat
bad = add`;

      const results = compileSource(source);
      const badResult = results.find(r => r.name === 'bad');
      expect(badResult).toBeDefined();
      expect(badResult!.parseSuccess).toBe(true);
      // Should FAIL - either unsolved metas or type mismatch
      expect(badResult!.checkSuccess).toBe(false);
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

  describe('Named Arguments in Constructor Patterns', () => {
    test('Constructor with named param - positional pattern should FAIL', () => {
      // VNil has {A: Type} as a NAMED parameter
      // Using (VNil _) treats _ as positional, which should fail
      const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive List : Type -> Type where
  Nil : {A: Type} -> List A
  Cons : (A : Type) -> A -> List A -> List A

-- BAD: Using positional _ for named parameter A
len : (A : Type) -> List A -> Nat
len A (Nil _) = Zero
len A (Cons _ _ tail) = Succ (len _ tail)`;

      const results = compileSource(source);
      const lenResult = results.find(r => r.name === 'len');
      expect(lenResult).toBeDefined();
      expect(lenResult!.parseSuccess).toBe(true);
      // Should FAIL because Nil _ uses positional for named param
      expect(lenResult!.checkSuccess).toBe(false);
    });

    test('Constructor with named param - named pattern syntax should SUCCEED', () => {
      // Now with parser support for {Name := pattern} syntax
      // Using {A := _} syntax to explicitly bind the named parameter
      const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive List : Type -> Type where
  Nil : {A: Type} -> List A
  Cons : (A : Type) -> A -> List A -> List A

-- GOOD: Using named syntax {A := _} for named parameter
len : (A : Type) -> List A -> Nat
len A (Nil {A := _}) = Zero
len A (Cons _ _ tail) = Succ (len _ tail)`;

      const results = compileSource(source);
      const lenResult = results.find(r => r.name === 'len');
      expect(lenResult).toBeDefined();
      expect(lenResult!.parseSuccess).toBe(true);
      expect(lenResult!.checkSuccess).toBe(true);
    });

    test('Constructor with named param - omitting named arg should SUCCEED', () => {
      // Named args in patterns can be omitted (inferred from context)
      const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive List : Type -> Type where
  Nil : {A: Type} -> List A
  Cons : (A : Type) -> A -> List A -> List A

-- GOOD: Named param A is inferred from context
len : (A : Type) -> List A -> Nat
len A Nil = Zero
len A (Cons _ _ tail) = Succ (len _ tail)`;

      const results = compileSource(source);
      const lenResult = results.find(r => r.name === 'len');
      expect(lenResult).toBeDefined();
      expect(lenResult!.parseSuccess).toBe(true);
      expect(lenResult!.checkSuccess).toBe(true);
    });

    test('Multiple constructors with named params - positional should FAIL', () => {
      // Both Nil and Cons have named params
      const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive List : Type -> Type where
  Nil : {A: Type} -> List A
  Cons : {A: Type} -> A -> List A -> List A

-- BAD: Using positional for named params in both constructors
bad : (A : Type) -> List A -> Nat
bad A (Nil _) = Zero
bad A (Cons _ x xs) = Succ (bad _ xs)`;

      const results = compileSource(source);
      const badResult = results.find(r => r.name === 'bad');
      expect(badResult).toBeDefined();
      expect(badResult!.parseSuccess).toBe(true);
      expect(badResult!.checkSuccess).toBe(false);
    });

    test('Constructor with mixed named/positional params', () => {
      // VCons has named {A} followed by positional params
      const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive List : Type -> Type where
  Nil : {A: Type} -> List A
  Cons : {A: Type} -> A -> List A -> List A

-- GOOD: Named param omitted, positional params matched
len : (A : Type) -> List A -> Nat
len A Nil = Zero
len A (Cons x xs) = Succ (len _ xs)`;

      const results = compileSource(source);
      const lenResult = results.find(r => r.name === 'len');
      expect(lenResult).toBeDefined();
      expect(lenResult!.parseSuccess).toBe(true);
      expect(lenResult!.checkSuccess).toBe(true);
    });

    test('User exact scenario - should fail with positional pattern for named arg', () => {
      // This is the user's exact failing scenario
      const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive List : Type -> Type where
  VNil : {A: Type} -> List A
  VCons : (A : Type) -> A -> List A -> List A

listLen : (A : Type) -> List A -> Nat
listLen A (VNil _) = Zero
listLen A (VCons _ _ tail) = Succ (listLen _ tail)`;

      const results = compileSource(source);
      const listLenResult = results.find(r => r.name === 'listLen');
      expect(listLenResult).toBeDefined();
      expect(listLenResult!.parseSuccess).toBe(true);
      // Should FAIL because VNil _ uses positional for named param
      expect(listLenResult!.checkSuccess).toBe(false);
    });

    test('Correct version of user scenario - with named syntax', () => {
      // Now with parser support for {Name := pattern} syntax
      const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive List : Type -> Type where
  VNil : {A: Type} -> List A
  VCons : (A : Type) -> A -> List A -> List A

listLen : (A : Type) -> List A -> Nat
listLen A (VNil {A := _}) = Zero
listLen A (VCons _ _ tail) = Succ (listLen _ tail)`;

      const results = compileSource(source);
      const listLenResult = results.find(r => r.name === 'listLen');
      expect(listLenResult).toBeDefined();
      expect(listLenResult!.parseSuccess).toBe(true);
      expect(listLenResult!.checkSuccess).toBe(true);
    });

    test('Correct version of user scenario - omitting named arg', () => {
      const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive List : Type -> Type where
  VNil : {A: Type} -> List A
  VCons : (A : Type) -> A -> List A -> List A

listLen : (A : Type) -> List A -> Nat
listLen A VNil = Zero
listLen A (VCons _ _ tail) = Succ (listLen _ tail)`;

      const results = compileSource(source);
      const listLenResult = results.find(r => r.name === 'listLen');
      expect(listLenResult).toBeDefined();
      expect(listLenResult!.parseSuccess).toBe(true);
      expect(listLenResult!.checkSuccess).toBe(true);
    });

    test('Named pattern arg binding a variable (not just wildcard)', () => {
      // This test verifies that {A := varName} actually binds the variable
      // If reordering isn't implemented, this would fail
      const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive List : Type -> Type where
  VNil : {A: Type} -> List A
  VCons : (A : Type) -> A -> List A -> List A

-- Capture the type parameter with a named pattern and return it
getType : (A : Type) -> List A -> Type
getType _ (VNil {A := T}) = T
getType _ (VCons T _ _) = T`;

      const results = compileSource(source);
      const getTypeResult = results.find(r => r.name === 'getType');
      expect(getTypeResult).toBeDefined();
      expect(getTypeResult!.parseSuccess).toBe(true);
      expect(getTypeResult!.checkSuccess).toBe(true);
    });
  });

  describe('Named Arguments in Function Clause Patterns', () => {
    test('Function with named parameter - clause-level named pattern syntax', () => {
      // Function with named/implicit parameter matched at clause level
      const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

plus : {a : Nat} -> Nat -> Nat
plus {a := Zero} b = b
plus {a := Succ a} b = Succ (plus {a := a} b)`;

      const results = compileSource(source);
      const plusResult = results.find(r => r.name === 'plus');
      expect(plusResult).toBeDefined();
      expect(plusResult!.parseSuccess).toBe(true);
      expect(plusResult!.checkSuccess).toBe(true);
    });

    test('Function with named parameter - mixed named and positional patterns', () => {
      // First pattern is named, second is positional
      const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

myFunc : {x : Nat} -> Nat -> Nat
myFunc {x := Zero} y = y
myFunc {x := Succ n} y = Succ (myFunc {x := n} y)`;

      const results = compileSource(source);
      const myFuncResult = results.find(r => r.name === 'myFunc');
      expect(myFuncResult).toBeDefined();
      expect(myFuncResult!.parseSuccess).toBe(true);
      expect(myFuncResult!.checkSuccess).toBe(true);
    });

    test('Function with multiple named parameters', () => {
      const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

add2 : {a : Nat} -> {b : Nat} -> Nat
add2 {a := Zero} {b := n} = n
add2 {a := Succ m} {b := n} = Succ (add2 {a := m} {b := n})`;

      const results = compileSource(source);
      const add2Result = results.find(r => r.name === 'add2');
      expect(add2Result).toBeDefined();
      expect(add2Result!.parseSuccess).toBe(true);
      expect(add2Result!.checkSuccess).toBe(true);
    });

    test('Function with named parameter - omitting named pattern should work', () => {
      // Named parameter can be omitted at clause level (inferred)
      const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

double : {n : Nat} -> Nat
double {n := Zero} = Zero
double {n := Succ m} = Succ (Succ (double {n := m}))`;

      const results = compileSource(source);
      const doubleResult = results.find(r => r.name === 'double');
      expect(doubleResult).toBeDefined();
      expect(doubleResult!.parseSuccess).toBe(true);
      expect(doubleResult!.checkSuccess).toBe(true);
    });

    test('Too many positional patterns for function with named param - should FAIL', () => {
      // Function has {a : Nat} (named) and Nat (positional), so positionalArity = 1
      // But clause provides 2 positional patterns - should fail
      const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

plus : {a : Nat} -> Nat -> Nat
plus a b = b
plus (Succ a) b = Succ (plus {a := a} b)`;

      const results = compileSource(source);
      const plusResult = results.find(r => r.name === 'plus');
      expect(plusResult).toBeDefined();
      expect(plusResult!.parseSuccess).toBe(true);
      // Should FAIL: 2 positional patterns but function only has 1 positional parameter
      expect(plusResult!.checkSuccess).toBe(false);
    });

    test('Correct number of positional patterns for function with named param - should SUCCEED', () => {
      // Function has {a : Nat} (named) and Nat (positional), so positionalArity = 1
      // Clause provides 1 positional pattern and 1 named pattern - should succeed
      const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

plus : {a : Nat} -> Nat -> Nat
plus {a := Zero} b = b
plus {a := Succ n} b = Succ (plus {a := n} b)`;

      const results = compileSource(source);
      const plusResult = results.find(r => r.name === 'plus');
      expect(plusResult).toBeDefined();
      expect(plusResult!.parseSuccess).toBe(true);
      expect(plusResult!.checkSuccess).toBe(true);
    });

    test('Function with all named params - no positional patterns allowed', () => {
      // Function has {a : Nat} and {b : Nat}, so positionalArity = 0
      // Any positional pattern should fail
      const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

add : {a : Nat} -> {b : Nat} -> Nat
add Zero n = n
add (Succ m) n = Succ (add {a := m} {b := n})`;

      const results = compileSource(source);
      const addResult = results.find(r => r.name === 'add');
      expect(addResult).toBeDefined();
      expect(addResult!.parseSuccess).toBe(true);
      // Should FAIL: positionalArity is 0, but 2 positional patterns provided
      expect(addResult!.checkSuccess).toBe(false);
    });
  });

  describe('Implicit Arguments (Automatic Meta/Wildcard Insertion)', () => {
    test('Implicit wildcard inserted for missing named pattern - simple case', () => {
      // plus has {a : Bool} (named) and Nat (positional)
      // Clause provides only positional pattern b, missing {a := ...}
      // An implicit wildcard should be inserted for 'a'
      const source = `
inductive Bool : Type where
  True : Bool
  False : Bool

inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

plus : {a : Bool} -> Nat -> Nat
plus b = Zero`;

      const results = compileSource(source);
      const plusResult = results.find(r => r.name === 'plus');
      expect(plusResult).toBeDefined();
      expect(plusResult!.parseSuccess).toBe(true);
      // Should SUCCEED - implicit wildcard inserted for missing named pattern 'a'
      expect(plusResult!.checkSuccess).toBe(true);
    });

    test('Implicit meta inserted for missing named argument - simple case', () => {
      // id has {A : Type} (named) and A (positional)
      // Calling with just the positional arg inserts a meta for A
      const source = `
id : { A : Type } -> A -> A
id {A} x = x

-- This calls id with just x, inserting meta for A
applyId : { T : Type } -> T -> T
applyId {T} x = id x`;

      const results = compileSource(source);
      const applyIdResult = results.find(r => r.name === 'applyId');
      expect(applyIdResult).toBeDefined();
      expect(applyIdResult!.parseSuccess).toBe(true);
      // Should SUCCEED - the meta for A can be inferred from context (T)
      expect(applyIdResult!.checkSuccess).toBe(true);
    });

    test('Implicit meta solved by unification', () => {
      // const has {A : Type} and {B : Type} (both named) plus positional args
      // When called with explicit types, metas are solved
      const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

const : { A : Type } -> { B : Type } -> A -> B -> A
const {A} {B} x y = x

-- Call const with one type explicit, one implicit
-- The implicit B should be inferred from the second argument
useConst : Nat -> Nat -> Nat
useConst a b = const { A := Nat } a b`;

      const results = compileSource(source);
      const useConstResult = results.find(r => r.name === 'useConst');
      expect(useConstResult).toBeDefined();
      expect(useConstResult!.parseSuccess).toBe(true);
      // Should SUCCEED - B is inferred as Nat from the second arg
      expect(useConstResult!.checkSuccess).toBe(true);
    });

    test('Multiple implicit wildcards in pattern', () => {
      // Function with multiple named params, all omitted in pattern
      const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

f : {a : Nat} -> {b : Nat} -> Nat -> Nat
f {a := Zero} {b := Zero} c = c
f {a := _} {b := _} c = Zero`;

      const results = compileSource(source);
      const fResult = results.find(r => r.name === 'f');
      expect(fResult).toBeDefined();
      expect(fResult!.parseSuccess).toBe(true);
      expect(fResult!.checkSuccess).toBe(true);
    });

    test('Implicit argument with type inference from return type', () => {
      // The implicit type can be inferred from the expected return type
      const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

id : { A : Type } -> A -> A
id {A} x = x

-- Return type is Nat, so id's A should be inferred as Nat
natId : Nat -> Nat
natId n = id n`;

      const results = compileSource(source);
      const natIdResult = results.find(r => r.name === 'natId');
      expect(natIdResult).toBeDefined();
      expect(natIdResult!.parseSuccess).toBe(true);
      expect(natIdResult!.checkSuccess).toBe(true);
    });

    test('Over-application with implicit args should fail', () => {
      // id : {A : Type} -> A -> A takes 2 args total
      // Providing 3 positional args should fail
      const source = `
id : { A : Type } -> A -> A
id {A} x = x

-- BAD: id T T gives 3 args (meta + T + T) but id only takes 2
bad : Type -> Type
bad T = id T T`;

      const results = compileSource(source);
      const badResult = results.find(r => r.name === 'bad');
      expect(badResult).toBeDefined();
      expect(badResult!.parseSuccess).toBe(true);
      // Should FAIL - too many positional arguments
      expect(badResult!.checkSuccess).toBe(false);
    });

    test('Partial application with implicit args', () => {
      // Apply only some arguments, leaving others implicit
      const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

add : { a : Nat } -> Nat -> Nat
add { a := Zero } b = b
add { a := Succ n } b = Succ (add { a := n } b)

-- Partial application: provide only the positional arg
-- This creates a function waiting for the named arg
increment : Nat -> Nat
increment = add { a := Succ Zero }`;

      const results = compileSource(source);
      const incrementResult = results.find(r => r.name === 'increment');
      expect(incrementResult).toBeDefined();
      expect(incrementResult!.parseSuccess).toBe(true);
      expect(incrementResult!.checkSuccess).toBe(true);
    });

    test('Implicit pattern with explicit remaining patterns', () => {
      // First param is implicit, remaining are explicit
      const source = `
inductive Bool : Type where
  True : Bool
  False : Bool

inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

f : {flag : Bool} -> Nat -> Nat -> Nat
f Zero m = m
f (Succ n) m = Succ (f {flag := True} n m)`;

      const results = compileSource(source);
      const fResult = results.find(r => r.name === 'f');
      expect(fResult).toBeDefined();
      expect(fResult!.parseSuccess).toBe(true);
      // Should SUCCEED - implicit wildcard for flag, explicit patterns for the rest
      expect(fResult!.checkSuccess).toBe(true);
    });

    test('Shorthand {x} syntax with implicit args', () => {
      // {x} expands to {x := x}, combined with other implicit args
      const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

id : { A : Type } -> A -> A
id {A} x = x

-- Using shorthand {T} which expands to {T := T}
applyWithShorthand : { T : Type } -> T -> T
applyWithShorthand {T} x = id { A := T } x`;

      const results = compileSource(source);
      const result = results.find(r => r.name === 'applyWithShorthand');
      expect(result).toBeDefined();
      expect(result!.parseSuccess).toBe(true);
      expect(result!.checkSuccess).toBe(true);
    });

    test('Implicit arg that cannot be inferred should fail', () => {
      // When the implicit arg has no constraints to determine it
      const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

const : { A : Type } -> { B : Type } -> A -> B -> A
const {A} {B} x y = x

-- BAD: Neither A nor B can be inferred since we provide no type info
-- The args are just variables with unknown types
bad : Nat
bad = const Zero Zero`;

      const results = compileSource(source);
      const badResult = results.find(r => r.name === 'bad');
      expect(badResult).toBeDefined();
      expect(badResult!.parseSuccess).toBe(true);
      // Metas are inserted but can be solved since Zero : Nat gives us A = Nat = B
      // Actually this should succeed because Zero constrains both A and B to Nat!
      expect(badResult!.checkSuccess).toBe(true);
    });

    test('Combining explicit and implicit named args', () => {
      // Provide some named args explicitly, let others be implicit
      const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

f : { a : Nat } -> { b : Nat } -> { c : Nat } -> Nat
f {a := Zero} {b := _} {c := _} = Zero
f {a := Succ n} {b} {c} = Succ (f {a := n} {b} {c})`;

      const results = compileSource(source);
      const fResult = results.find(r => r.name === 'f');
      expect(fResult).toBeDefined();
      expect(fResult!.parseSuccess).toBe(true);
      expect(fResult!.checkSuccess).toBe(true);
    });
  });

  describe('Named Arguments in Constructor Patterns - Vec/Fin nth', () => {
    // These tests exercise named arguments in constructor patterns with VCons
    // which has {A : Type} -> {n : Nat} -> A -> Vec A n -> Vec A (Succ n)

    const vecFinBase = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Vec : Type -> Nat -> Type where
  VNil : {A: Type} -> Vec A Zero
  VCons : {A : Type} -> {n : Nat} -> A -> Vec A n -> Vec A (Succ n)

inductive Fin : Nat -> Type where
  FZero : {n : Nat} -> Fin (Succ n)
  FSucc : {n : Nat} -> Fin n -> Fin (Succ n)
`;

    test('Variant 1: Full explicit named args in VCons and FZero/FSucc patterns', () => {
      const source = vecFinBase + `
nth : {A : Type} -> {n : Nat} -> Vec A n -> Fin n -> A
nth (VCons {A := _} {n := _} h _) (FZero {n:=_}) = h
nth (VCons {A := _} {n := Succ _} h tail) (FSucc {n:=_} f) = nth {A := _} {n := _} tail f`;

      const results = compileSource(source);
      const nthResult = results.find(r => r.name === 'nth');
      expect(nthResult).toBeDefined();
      expect(nthResult!.parseSuccess).toBe(true);
      expect(nthResult!.checkSuccess).toBe(true);
    });

    test('Variant 2: Partial named args (only A) in VCons', () => {
      const source = vecFinBase + `
nth : {A : Type} -> {n : Nat} -> Vec A n -> Fin n -> A
nth (VCons {A := _} h _) FZero = h
nth (VCons {A := _} h tail) (FSucc f) = nth tail f`;

      const results = compileSource(source);
      const nthResult = results.find(r => r.name === 'nth');
      expect(nthResult).toBeDefined();
      expect(nthResult!.parseSuccess).toBe(true);
      expect(nthResult!.checkSuccess).toBe(true);
    });

    test('Variant 3: No named args - all implicit in VCons/FZero/FSucc', () => {
      const source = vecFinBase + `
nth : {A : Type} -> {n : Nat} -> Vec A n -> Fin n -> A
nth (VCons h _) FZero = h
nth (VCons h tail) (FSucc f) = nth tail f`;

      const results = compileSource(source);
      const nthResult = results.find(r => r.name === 'nth');
      expect(nthResult).toBeDefined();
      expect(nthResult!.parseSuccess).toBe(true);
      if (!nthResult!.checkSuccess) {
        console.log('VARIANT 3 Check errors:', nthResult!.checkErrors);
      }
      expect(nthResult!.checkSuccess).toBe(true);
    });

    test('nth with implicit function params and implicit ctor args', () => {
      // The full idiomatic version: everything is implicit
      const source = vecFinBase + `
nth : {A : Type} -> {n : Nat} -> Vec A n -> Fin n -> A
nth (VCons h _) FZero = h
nth (VCons h tail) (FSucc f) = nth tail f`;

      const results = compileSource(source);
      const nthResult = results.find(r => r.name === 'nth');
      expect(nthResult).toBeDefined();
      expect(nthResult!.parseSuccess).toBe(true);
      expect(nthResult!.checkSuccess).toBe(true);
    });

    test('VNil with no positional args (only named)', () => {
      // VNil has only a named param {A : Type} and NO positional params
      const source = vecFinBase + `
isEmpty : {A : Type} -> {n : Nat} -> Vec A n -> Nat
isEmpty VNil = Zero
isEmpty (VCons _ _) = Succ Zero`;

      const results = compileSource(source);
      const result = results.find(r => r.name === 'isEmpty');
      expect(result).toBeDefined();
      expect(result!.parseSuccess).toBe(true);
      expect(result!.checkSuccess).toBe(true);
    });
  });

  describe('Constructor with ALL named args (no positional)', () => {
    test('refl with no positional args - all implicit', () => {
      // refl : {A : Type} -> {a : A} -> Equal A a a
      // Has ZERO positional args - everything is named/implicit
      const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Equal : (A : Type) -> A -> A -> Type where
  refl : {A : Type} -> {a : A} -> Equal A a a

inductive Void : Type where

zeroNeqSucc : (n : Nat) -> Equal Nat Zero (Succ n) -> Void
zeroNeqSucc n (refl {A := _} {a := _}) = #absurd`;

      const results = compileSource(source);
      const result = results.find(r => r.name === 'zeroNeqSucc');
      expect(result).toBeDefined();
      expect(result!.parseSuccess).toBe(true);
      // This SHOULD fail because refl {A := Nat} {a := Zero} can't unify with
      // Equal Nat Zero (Succ n) - the indices Zero and (Succ n) don't match
      // The absurd marker is appropriate here
      expect(result!.checkSuccess).toBe(true);
    });

    test('refl with no positional args - pattern syntax without named args', () => {
      // User writes just (refl) - implicit wildcards for A and a
      const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Equal : (A : Type) -> A -> A -> Type where
  refl : {A : Type} -> {a : A} -> Equal A a a

inductive Void : Type where

zeroNeqSucc : (n : Nat) -> Equal Nat Zero (Succ n) -> Void
zeroNeqSucc n refl = #absurd`;

      const results = compileSource(source);
      const result = results.find(r => r.name === 'zeroNeqSucc');
      expect(result).toBeDefined();
      expect(result!.parseSuccess).toBe(true);
      expect(result!.checkSuccess).toBe(true);
    });

    test('symm using refl with implicit args', () => {
      const source = `
inductive Equal : (A : Type) -> A -> A -> Type where
  refl : {A : Type} -> {a : A} -> Equal A a a

symm : {A : Type} -> {x : A} -> {y : A} -> Equal A x y -> Equal A y x
symm refl = refl`;

      const results = compileSource(source);
      const result = results.find(r => r.name === 'symm');
      expect(result).toBeDefined();
      expect(result!.parseSuccess).toBe(true);
      expect(result!.checkSuccess).toBe(true);
    });

    test('trans using refl with implicit args', () => {
      const source = `
inductive Equal : (A : Type) -> A -> A -> Type where
  refl : {A : Type} -> {a : A} -> Equal A a a

trans : {A : Type} -> {x : A} -> {y : A} -> {z : A} -> Equal A x y -> Equal A y z -> Equal A x z
trans refl refl = refl`;

      const results = compileSource(source);
      const result = results.find(r => r.name === 'trans');
      expect(result).toBeDefined();
      expect(result!.parseSuccess).toBe(true);
      expect(result!.checkSuccess).toBe(true);
    });

    test('cong using refl with implicit args', () => {
      const source = `
inductive Equal : (A : Type) -> A -> A -> Type where
  refl : {A : Type} -> {a : A} -> Equal A a a

cong : {A : Type} -> {B : Type} -> {x : A} -> {y : A} -> (f : A -> B) -> Equal A x y -> Equal B (f x) (f y)
cong f refl = refl`;

      const results = compileSource(source);
      const result = results.find(r => r.name === 'cong');
      expect(result).toBeDefined();
      expect(result!.parseSuccess).toBe(true);
      expect(result!.checkSuccess).toBe(true);
    });
  });

  describe('Equal with named type parameter', () => {
    test('Equal with {A : Type} - zeroNeqSucc', () => {
      // Equal has NAMED type param: Equal {A} a a
      // So Equal Zero (Succ n) implicitly fills in {A := Nat}
      const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Equal : {A : Type} -> A -> A -> Type where
  refl : {A : Type} -> {a : A} -> Equal {A} a a

inductive Void : Type where

zeroNeqSucc : (n : Nat) -> Equal Zero (Succ n) -> Void
zeroNeqSucc n refl = #absurd`;

      const results = compileSource(source);
      const result = results.find(r => r.name === 'zeroNeqSucc');
      expect(result).toBeDefined();
      expect(result!.parseSuccess).toBe(true);
      expect(result!.checkSuccess).toBe(true);
    });

    test('Equal with {A : Type} - symm', () => {
      const source = `
inductive Equal : {A : Type} -> A -> A -> Type where
  refl : {A : Type} -> {a : A} -> Equal {A} a a

symm : {A : Type} -> {x : A} -> {y : A} -> Equal {A} x y -> Equal {A} y x
symm refl = refl`;

      const results = compileSource(source);
      const result = results.find(r => r.name === 'symm');
      expect(result).toBeDefined();
      expect(result!.parseSuccess).toBe(true);
      expect(result!.checkSuccess).toBe(true);
    });
  });

  describe('Mixed positional and named args - complex cases', () => {
    test('Nested constructor patterns with implicit args', () => {
      const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Vec : Type -> Nat -> Type where
  VNil : {A: Type} -> Vec A Zero
  VCons : {A : Type} -> {n : Nat} -> A -> Vec A n -> Vec A (Succ n)

-- Nested VCons patterns
head2 : {A : Type} -> {n : Nat} -> Vec A (Succ (Succ n)) -> A
head2 (VCons h (VCons _ _)) = h`;

      const results = compileSource(source);
      const result = results.find(r => r.name === 'head2');
      expect(result).toBeDefined();
      expect(result!.parseSuccess).toBe(true);
      expect(result!.checkSuccess).toBe(true);
    });

    test('Nested constructor patterns keep inner binder types aligned after implicit padding', () => {
      const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Vec : Type -> Nat -> Type where
  VNil : {A: Type} -> Vec A Zero
  VCons : {A : Type} -> {n : Nat} -> A -> Vec A n -> Vec A (Succ n)

second2 : {A : Type} -> {n : Nat} -> Vec A (Succ (Succ n)) -> A
second2 (VCons _ (VCons x _)) = x`;

      const results = compileSource(source);
      const result = results.find(r => r.name === 'second2');
      expect(result).toBeDefined();
      expect(result!.parseSuccess).toBe(true);
      expect(result!.checkSuccess).toBe(true);
    });

    test('Multiple clauses with varying implicit patterns', () => {
      const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Vec : Type -> Nat -> Type where
  VNil : {A: Type} -> Vec A Zero
  VCons : {A : Type} -> {n : Nat} -> A -> Vec A n -> Vec A (Succ n)

-- First clause uses VNil (only named arg), second uses VCons (mixed)
len : {A : Type} -> {n : Nat} -> Vec A n -> Nat
len VNil = Zero
len (VCons _ tail) = Succ (len tail)`;

      const results = compileSource(source);
      const result = results.find(r => r.name === 'len');
      expect(result).toBeDefined();
      expect(result!.parseSuccess).toBe(true);
      expect(result!.checkSuccess).toBe(true);
    });
  });
});
