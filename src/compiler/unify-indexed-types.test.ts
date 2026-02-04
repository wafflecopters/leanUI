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
    test('ACCEPT: sym A x y (refl _ _) - refl unifies x and y (Agda-style)', () => {
      // In Agda-style dependent pattern matching, matching on `refl` forces x=y.
      // Both x and y become aliases for the same binding. This is valid.
      const source = `${EQUAL_DEF}

sym : (A : Type) -> (x : A) -> (y : A) -> Equal A x y -> Equal A y x
sym A x y (refl _ _) = refl _ _`;

      const result = compileAndCheck(source);

      expect(result.success).toBe(true);
    });

    // This test is about whether pattern matching should implicitly unify indices.
    // In Agda/Idris, matching on `refl` would force x=y, making this VALID.
    // Let's test if our type checker follows Agda semantics (accepts) or is stricter (rejects).
    test('Check wildcards dependent pattern matching behavior', () => {
      const source = `${EQUAL_DEF}

bad_sym : (A : Type) -> (x : A) -> (y : A) -> Equal A x y -> Equal A y x
bad_sym _ _ _ (refl _ _) = refl _ _`;

      const result = compileAndCheck(source);

      // In Agda-style dependent pattern matching, matching on `refl` forces x=y,
      // so this is VALID. If we want stricter semantics, we'd need to reject this.
      // For now, let's accept Agda-style semantics:
      if (!result.success) {
        console.log('bad_sym errors:', result.errors);
      }
      expect(result.success).toBe(true);
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

  describe('#absurd Syntax', () => {
    test('ACCEPT: #absurd on truly absurd case (nil in Vec (Succ n))', () => {
      const source = `${NAT_DEF}

inductive Vec : Type -> Nat -> Type where
  | nil : (A : Type) -> Vec A Zero
  | cons : (A : Type) -> (n : Nat) -> A -> Vec A n -> Vec A (Succ n)

head : (A : Type) -> (n : Nat) -> Vec A (Succ n) -> A
head A n (nil _) = #absurd
head A n (cons _ _ x _) = x`;

      const result = compileAndCheck(source);

      // Should succeed - nil case is genuinely absurd (Zero ≠ Succ n)
      expect(result.success).toBe(true);
    });

    test('REJECT: #absurd on reachable case (cons is NOT absurd)', () => {
      const source = `${NAT_DEF}

inductive Vec : Type -> Nat -> Type where
  | nil : (A : Type) -> Vec A Zero
  | cons : (A : Type) -> (n : Nat) -> A -> Vec A n -> Vec A (Succ n)

bad : (A : Type) -> (n : Nat) -> Vec A (Succ n) -> A
bad A n (cons _ _ x _) = #absurd`;

      const result = compileAndCheck(source);

      // Should fail - cons is NOT absurd, it's a valid case
      expect(result.success).toBe(false);
      expect(result.errors.some(e => e.includes('#absurd') || e.includes('not absurd'))).toBe(true);
    });

    test('ACCEPT: #absurd via recursive splitting (Fin Zero is uninhabited)', () => {
      // This tests that #absurd validation uses Agda-style recursive splitting
      const source = `${NAT_DEF}

inductive Fin : Nat -> Type where
  | FZero : (n : Nat) -> Fin (Succ n)
  | FSucc : (n : Nat) -> Fin n -> Fin (Succ n)

absurdFinZero : Fin Zero -> (A : Type) -> A
absurdFinZero f _ = #absurd`;

      const result = compileAndCheck(source);

      // Should succeed - Fin Zero is uninhabited (both constructors require Succ n)
      // This requires the Agda-style splitting to detect
      expect(result.success).toBe(true);
    });

    test('REJECT: #absurd on inhabited type (Fin (Succ n) has constructors)', () => {
      const source = `${NAT_DEF}

inductive Fin : Nat -> Type where
  | FZero : (n : Nat) -> Fin (Succ n)
  | FSucc : (n : Nat) -> Fin n -> Fin (Succ n)

bad : (n : Nat) -> Fin (Succ n) -> (A : Type) -> A
bad n f _ = #absurd`;

      const result = compileAndCheck(source);

      // Should fail - Fin (Succ n) IS inhabited (FZero n works)
      expect(result.success).toBe(false);
    });

    test('ACCEPT: #absurd with conflicting Equal indices', () => {
      const source = `${NAT_DEF}

${EQUAL_DEF}

zeroNotSucc : Equal Nat Zero (Succ Zero) -> (A : Type) -> A
zeroNotSucc eq _ = #absurd`;

      const result = compileAndCheck(source);

      // Should succeed - Equal Nat Zero (Succ Zero) is uninhabited
      // refl requires both indices to be equal, but Zero ≠ Succ Zero
      expect(result.success).toBe(true);
    });

    test('REJECT: #absurd with satisfiable Equal indices', () => {
      const source = `${NAT_DEF}

${EQUAL_DEF}

bad : Equal Nat Zero Zero -> (A : Type) -> A
bad eq _ = #absurd`;

      const result = compileAndCheck(source);

      // Should fail - Equal Nat Zero Zero IS inhabited (refl Nat Zero)
      expect(result.success).toBe(false);
    });

    test('ACCEPT: #absurd clause is erased during elaboration', () => {
      // Verify that #absurd clauses don't appear in the kernel output
      const source = `${NAT_DEF}

inductive Vec : Type -> Nat -> Type where
  | nil : (A : Type) -> Vec A Zero
  | cons : (A : Type) -> (n : Nat) -> A -> Vec A n -> Vec A (Succ n)

head : (A : Type) -> (n : Nat) -> Vec A (Succ n) -> A
head A n (nil _) = #absurd
head A n (cons _ _ x _) = x`;

      const result = compileTTFromText(source);

      // Find the head definition
      const headDecl = result.blocks
        .flatMap(b => b.declarations)
        .find(d => d.name === 'head');

      expect(headDecl).toBeDefined();
      expect(headDecl?.checkSuccess).toBe(true);

      // The kernel should only have 1 clause (cons), not 2
      // The #absurd clause should be erased during elaboration
      if (headDecl?.kernelValue?.tag === 'Match') {
        expect(headDecl.kernelValue.clauses.length).toBe(1);
      }
    });
  });
});
