/**
 * Regression test for vecConcat with plus function
 *
 * This tests that function definitions (like `plus`) can be used as constants
 * in later definitions (like `vecConcat`).
 *
 * The core issue: When a function like `plus` is defined and later used in a
 * TYPE ANNOTATION (not just a value), the type checker needs to resolve
 * `plus` to its type `Nat -> Nat -> Nat`. Otherwise we get:
 *   "Application requires Pi type, got: ?plus_type"
 */

import { describe, test, expect } from 'vitest';
import { compileSource } from '../test-utils';

describe('vecConcat Regression', () => {
  // ============================================================================
  // Test 1: The core issue - using a defined function in a TYPE position
  // ============================================================================

  test('Using defined function in type annotation triggers proper constant resolution', () => {
    // The core issue: when `plus` is a defined constant, and it's used inside
    // a type expression (like `F (plus a b)` where F : Nat -> Type),
    // the type checker must resolve `plus` to its declared type `Nat -> Nat -> Nat`.
    //
    // If constant resolution fails, we get: "Application requires Pi type, got: ?plus_type"
    //
    // Minimal reproduction:
    // 1. Define `plus : Nat -> Nat -> Nat` with implementation
    // 2. Define a type family `F : Nat -> Type` with implementation
    // 3. Use `F (plus Zero Zero)` in a type signature
    //
    // For (3) to work, `plus Zero Zero` must have type `Nat`.
    // That requires knowing `plus : Nat -> Nat -> Nat`.
    const source = `inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

plus : Nat -> Nat -> Nat
plus Zero b = b
plus (Succ a) b = Succ (plus a b)

-- A type family indexed by Nat (using inductive to have a proper definition)
inductive F : Nat -> Type where
  MkF : (n : Nat) -> F n

-- This uses 'plus' inside a type expression
-- Type checker must resolve plus, then infer (plus Zero Zero) : Nat,
-- then check F (plus Zero Zero) : Type
test : F (plus Zero Zero)
test = MkF Zero`;

    const results = compileSource(source);

    expect(results.length).toBeGreaterThanOrEqual(1);

    const testBlock = results.find(r => r.name === 'test');
    expect(testBlock).toBeDefined();
    expect(testBlock!.checkSuccess).toBe(true);
  });

  // ============================================================================
  // Test 2: The specific vecConcat scenario
  // ============================================================================

  test('vecConcat type signature uses plus in a dependent type', () => {
    // This is the actual user scenario that was failing:
    //   Vec A (plus a b)
    // Here `plus a b` appears inside a TYPE, not a value.
    // The type checker must:
    // 1. Know that `plus : Nat -> Nat -> Nat`
    // 2. Infer that `plus a b : Nat`
    // 3. Accept `Vec A (plus a b)` as well-typed

    const source = `inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

plus : Nat -> Nat -> Nat

inductive Vec : Type -> Nat -> Type where
  VNil : (A: Type) -> Vec A Zero
  VCons : (A : Type) -> (n : Nat) -> A -> Vec A n -> Vec A (Succ n)

-- The key test: using 'plus' in the RETURN TYPE of vecConcat
vecConcat : (A : Type) -> (a : Nat) -> (b : Nat) -> Vec A a -> Vec A b -> Vec A (plus a b)`;

    const results = compileSource(source);

    // Check that vecConcat type-checks
    const vecConcatBlock = results.find(r => r.name === 'vecConcat');
    expect(vecConcatBlock).toBeDefined();

    // This is the assertion that exposes the bug:
    // If constant resolution doesn't work, we'll get:
    //   "Application requires Pi type, got: ?plus_type"
    expect(vecConcatBlock!.checkSuccess).toBe(true);
  });

  // ============================================================================
  // Test 3: The exact user example that was reported as failing
  // ============================================================================

  test('Exact user example with full pattern matching definitions', () => {
    // The exact example from the user bug report:
    const source = `inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

plus : Nat -> Nat -> Nat
plus Zero b = b
plus (Succ a) b = Succ (plus a b)

inductive Vec : Type -> Nat -> Type where
  VNil : (A: Type) -> Vec A Zero
  VCons : (A : Type) -> (n : Nat) -> A -> Vec A n -> Vec A (Succ n)

vecConcat : (A : Type) -> (a : Nat) -> (b : Nat) -> Vec A a -> Vec A b -> Vec A (plus a b)
vecConcat _ _ _ (VNil _) v = v
vecConcat _ _ _ (VCons _ _ h tail) v = VCons _ _ h (vecConcat _ _ _ tail v)`;

    const results = compileSource(source);

    // Check vecConcat specifically
    const vecConcatBlock = results.find(r => r.name === 'vecConcat');
    expect(vecConcatBlock).toBeDefined();

    // The user reported this error:
    // "Type check failed for 'vecConcat': Application requires Pi type, got: ?plus_type"
    //
    // After the fix:
    // - The TYPE signature of plus is now added to global context even though
    //   the VALUE check failed (pattern matching not implemented)
    // - So vecConcat's type signature can properly reference `plus`
    // - The error we get now should be about pattern matching in vecConcat's
    //   OWN value, NOT about an unresolved `plus_type` hole
    if (!vecConcatBlock!.checkSuccess) {
      const errorMsg = vecConcatBlock!.checkErrors.map(e => e.message).join(', ');

      // The OLD bug: unresolved constant type
      // This is the key assertion - we should NOT see unresolved holes for plus's type
      expect(errorMsg).not.toContain('plus_type');

      // After the fix, we may get various errors (pattern matching, constructor types, etc.)
      // The important thing is that we're not failing due to unresolved plus_type
    }
  });
});
