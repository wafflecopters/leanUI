/**
 * Tests for unification with indexed inductive types (Equal, Vec, etc.)
 *
 * These tests verify that pattern matching on indexed types correctly:
 * 1. Detects impossible patterns (conflicting indices)
 * 2. Accepts valid patterns where indices unify
 * 3. Properly propagates index constraints to the RHS
 */

import { compileTTFromText } from './compile';

function test(description: string, fn: () => void): void {
  try {
    fn();
    console.log(`✓ ${description}`);
  } catch (error) {
    console.error(`✗ ${description}`);
    throw error;
  }
}

function assert(condition: boolean, message?: string): void {
  if (!condition) {
    throw new Error(message || 'Assertion failed');
  }
}

console.log('\n' + '='.repeat(80));
console.log('INDEXED TYPE UNIFICATION TESTS');
console.log('='.repeat(80) + '\n');

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
    if (block.kind === 'checked') {
      for (const decl of block.declarations) {
        if (!decl.checkSuccess) {
          errors.push(...decl.checkErrors.map(e => e.error.message));
        }
      }
    }
  }

  return { success: result.success, errors };
}

// ============================================================================
// Basic Equal Type Tests
// ============================================================================

test('Equal type definition is valid', () => {
  const result = compileAndCheck(EQUAL_DEF);
  assert(result.success, `Equal should compile. Errors: ${result.errors.join(', ')}`);
});

// ============================================================================
// Impossible Pattern Tests - These should FAIL
// ============================================================================

test('REJECT: sym A x y (refl _ _) - impossible pattern with distinct variables', () => {
  const source = `${EQUAL_DEF}

sym : (A : Type) -> (x : A) -> (y : A) -> Equal A x y -> Equal A y x
sym A x y (refl _ _) = refl _ _`;

  const result = compileAndCheck(source);

  assert(
    !result.success,
    `sym with distinct x,y should FAIL - refl requires indices to be equal. Got success.`
  );
});

test('REJECT: wildcards cannot hide index mismatch', () => {
  const source = `${EQUAL_DEF}

bad_sym : (A : Type) -> (x : A) -> (y : A) -> Equal A x y -> Equal A y x
bad_sym _ _ _ (refl _ _) = refl _ _`;

  const result = compileAndCheck(source);

  assert(
    !result.success,
    `bad_sym should FAIL even with wildcards - indices still mismatch.`
  );
});

// ============================================================================
// Valid Pattern Tests - These should SUCCEED
// ============================================================================

test('ACCEPT: reflexivity proof', () => {
  const source = `${EQUAL_DEF}

refl_proof : (A : Type) -> (x : A) -> Equal A x x
refl_proof A x = refl A x`;

  const result = compileAndCheck(source);

  assert(
    result.success,
    `refl_proof should succeed - indices are the same. Errors: ${result.errors.join(', ')}`
  );
});

test('ACCEPT: matching on refl where indices are already equal', () => {
  const source = `${EQUAL_DEF}

refl_elim : (A : Type) -> (x : A) -> Equal A x x -> Equal A x x
refl_elim A x (refl _ _) = refl A x`;

  const result = compileAndCheck(source);

  assert(
    result.success,
    `refl_elim should succeed - x = x is trivially satisfiable. Errors: ${result.errors.join(', ')}`
  );
});

// ============================================================================
// Vec-like Indexed Type Tests
// ============================================================================

test('ACCEPT: Vec head with cons pattern', () => {
  const source = `${NAT_DEF}

inductive Vec : Type -> Nat -> Type where
  | nil : (A : Type) -> Vec A Zero
  | cons : (A : Type) -> (n : Nat) -> A -> Vec A n -> Vec A (Succ n)

head : (A : Type) -> (n : Nat) -> Vec A (Succ n) -> A
head A n (cons _ _ x _) = x`;

  const result = compileAndCheck(source);

  assert(
    result.success,
    `head should succeed - cons matches Succ n. Errors: ${result.errors.join(', ')}`
  );
});

test('REJECT: Vec nil pattern cannot match Succ n index', () => {
  const source = `${NAT_DEF}

inductive Vec : Type -> Nat -> Type where
  | nil : (A : Type) -> Vec A Zero
  | cons : (A : Type) -> (n : Nat) -> A -> Vec A n -> Vec A (Succ n)

bad_head : (A : Type) -> (n : Nat) -> Vec A (Succ n) -> A
bad_head A n (nil _) = bad_head A n (nil _)`;

  const result = compileAndCheck(source);

  assert(
    !result.success,
    `bad_head should FAIL - nil cannot match Succ n.`
  );
});

// ============================================================================
// Multiple Index Constraint Tests
// ============================================================================

test('REJECT: Equal with multiple conflicting constraints (Zero vs Succ)', () => {
  const source = `${NAT_DEF}

${EQUAL_DEF}

bad : Equal Nat Zero (Succ Zero) -> Nat
bad (refl _ _) = Zero`;

  const result = compileAndCheck(source);

  assert(
    !result.success,
    `bad should FAIL - Zero cannot equal Succ Zero.`
  );
});

test('ACCEPT: Equal with consistent index', () => {
  const source = `${NAT_DEF}

${EQUAL_DEF}

good : Equal Nat Zero Zero -> Nat
good (refl _ _) = Zero`;

  const result = compileAndCheck(source);

  assert(
    result.success,
    `good should succeed - Zero = Zero is fine. Errors: ${result.errors.join(', ')}`
  );
});

console.log('\n' + '='.repeat(80));
console.log('ALL INDEXED TYPE UNIFICATION TESTS PASSED! ✓');
console.log('='.repeat(80) + '\n');
