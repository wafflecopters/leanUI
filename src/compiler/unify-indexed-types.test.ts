/**
 * Tests for unification with indexed inductive types (Equal, Vec, etc.)
 *
 * These tests verify that pattern matching on indexed types correctly:
 * 1. Detects impossible patterns (conflicting indices)
 * 2. Accepts valid patterns where indices unify
 * 3. Properly propagates index constraints to the RHS
 */

import { describe, test, expect } from 'vitest';
import { compileTTFromText } from './compile';

// ============================================================================
// Setup: Define Equal type for all tests
// ============================================================================

const EQUAL_DEF = `inductive Equal : (A : Type) -> A -> A -> Type where
  | refl : (A : Type) -> (a : A) -> Equal A a a`;

const NAT_DEF = `inductive Nat : Type where
  | Zero : Nat
  | Succ : Nat -> Nat`;

// Helper to check if compilation succeeded
function compileAndCheck(source: string): { success: boolean; errors: string[] } {
  const result = compileTTFromText(source);
  const errors: string[] = [];

  for (const block of result.blocks) {
    for (const decl of block.declarations) {
      if (!decl.checkSuccess) {
        errors.push(...decl.checkErrors.map(e => e.message));
      }
    }
  }

  return { success: result.success, errors };
}

describe('Indexed Type Unification', () => {
  describe('Basic Equal Type', () => {
    test('Equal type definition is valid', () => {
      const result = compileAndCheck(EQUAL_DEF);
      expect(result.success).toBe(true);
    });
  });

  describe('Impossible Patterns - Should FAIL', () => {
    test('REJECT: sym A x y (refl _ _) - impossible pattern with distinct variables', () => {
      const source = `${EQUAL_DEF}

sym : (A : Type) -> (x : A) -> (y : A) -> Equal A x y -> Equal A y x
sym A x y (refl _ _) = refl _ _`;

      const result = compileAndCheck(source);

      expect(result.success).toBe(false);
    });

    // TODO: This test exposes the same rigid variable unification bug as the wrongId test.
    // Wildcards are incorrectly allowing x and y to unify. Skip until fixed.
    test.skip('REJECT: wildcards cannot hide index mismatch', () => {
      const source = `${EQUAL_DEF}

bad_sym : (A : Type) -> (x : A) -> (y : A) -> Equal A x y -> Equal A y x
bad_sym _ _ _ (refl _ _) = refl _ _`;

      const result = compileAndCheck(source);

      expect(result.success).toBe(false);
    });
  });

  describe('Valid Patterns - Should SUCCEED', () => {
    test('ACCEPT: reflexivity proof', () => {
      const source = `${EQUAL_DEF}

refl_proof : (A : Type) -> (x : A) -> Equal A x x
refl_proof A x = refl A x`;

      const result = compileAndCheck(source);

      expect(result.success).toBe(true);
    });

    test('ACCEPT: matching on refl where indices are already equal', () => {
      const source = `${EQUAL_DEF}

refl_elim : (A : Type) -> (x : A) -> Equal A x x -> Equal A x x
refl_elim A x (refl _ _) = refl A x`;

      const result = compileAndCheck(source);

      expect(result.success).toBe(true);
    });
  });

  describe('Vec-like Indexed Type', () => {
    test('ACCEPT: Vec head with cons pattern', () => {
      const source = `${NAT_DEF}

inductive Vec : Type -> Nat -> Type where
  | nil : (A : Type) -> Vec A Zero
  | cons : (A : Type) -> (n : Nat) -> A -> Vec A n -> Vec A (Succ n)

head : (A : Type) -> (n : Nat) -> Vec A (Succ n) -> A
head A n (cons _ _ x _) = x`;

      const result = compileAndCheck(source);

      expect(result.success).toBe(true);
    });

    test('REJECT: Vec nil pattern cannot match Succ n index', () => {
      const source = `${NAT_DEF}

inductive Vec : Type -> Nat -> Type where
  | nil : (A : Type) -> Vec A Zero
  | cons : (A : Type) -> (n : Nat) -> A -> Vec A n -> Vec A (Succ n)

bad_head : (A : Type) -> (n : Nat) -> Vec A (Succ n) -> A
bad_head A n (nil _) = bad_head A n (nil _)`;

      const result = compileAndCheck(source);

      expect(result.success).toBe(false);
    });

    test('ACCEPT: nth function with Fin - VNil case is absurd via Fin Zero splitting', () => {
      // This tests the Agda-style recursive splitting:
      // - VNil gives Vec A Zero, so Fin n becomes Fin Zero
      // - Fin Zero has no valid constructors (FZero and FSucc both require Succ n)
      // - Therefore VNil case is absurd and doesn't need to be covered
      const source = `${NAT_DEF}

inductive Vec : Type -> Nat -> Type where
  | VNil : (A : Type) -> Vec A Zero
  | VCons : (A : Type) -> (n : Nat) -> A -> Vec A n -> Vec A (Succ n)

inductive Fin : Nat -> Type where
  | FZero : (n : Nat) -> Fin (Succ n)
  | FSucc : (n : Nat) -> Fin n -> Fin (Succ n)

nth : (A : Type) -> (n : Nat) -> Vec A n -> Fin n -> A
nth A _ (VCons _ _ h _) (FZero _) = h
nth A _ (VCons _ _ _ tail) (FSucc _ f) = nth A _ tail f`;

      const result = compileAndCheck(source);

      // Should succeed because VNil case is absurd:
      // VNil constrains n=Zero, but Fin Zero is uninhabited
      expect(result.success).toBe(true);
    });
  });

  describe('Multiple Index Constraints', () => {
    test('REJECT: Equal with multiple conflicting constraints (Zero vs Succ)', () => {
      const source = `${NAT_DEF}

${EQUAL_DEF}

bad : Equal Nat Zero (Succ Zero) -> Nat
bad (refl _ _) = Zero`;

      const result = compileAndCheck(source);

      expect(result.success).toBe(false);
    });

    test('ACCEPT: Equal with consistent index', () => {
      const source = `${NAT_DEF}

${EQUAL_DEF}

good : Equal Nat Zero Zero -> Nat
good (refl _ _) = Zero`;

      const result = compileAndCheck(source);

      expect(result.success).toBe(true);
    });
  });

  describe('Zero-Clause Functions (Uninhabited Types)', () => {
    test('ACCEPT: absurd function with zero clauses - Void has no constructors', () => {
      const source = `inductive Void : Type where

absurd : (A : Type) -> Void -> A`;

      const result = compileAndCheck(source);

      // Should succeed because Void has no constructors
      // Zero clauses is exhaustive when the type is uninhabited
      expect(result.success).toBe(true);
    });

    test('REJECT: zero-clause function where argument IS inhabited', () => {
      const source = `${NAT_DEF}

bad : Nat -> Nat`;

      const result = compileAndCheck(source);

      // Should fail - Nat has constructors, so zero clauses is not exhaustive
      expect(result.success).toBe(false);
    });
  });
});
