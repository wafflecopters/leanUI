/**
 * Tests for Axiom K / UIP (Uniqueness of Identity Proofs) handling.
 *
 * This module tests the `assumeUIP` option in type checking, which controls
 * whether the deletion rule for rigid variables is allowed during pattern matching.
 *
 * The deletion rule in unification treats `x = x` as trivially true for rigid variables.
 * When assumeUIP is false, this rule is disabled, causing pattern matches that rely
 * on K to fail with a specific error.
 *
 * Key test cases:
 * 1. streichersK - the canonical K axiom
 * 2. matchOnReflexive - matching on Equal A a a with variable a
 * 3. uipRefl - proving all reflexivity proofs equal to refl
 */

import { compileTTFromText, CompileOptions } from './compile';

// ============================================================================
// Test Framework
// ============================================================================

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

// ============================================================================
// Test Setup
// ============================================================================

const EQUAL_DEF = `inductive Equal : (A : Type) -> A -> A -> Type where
  | refl : (A : Type) -> (a : A) -> Equal A a a`;

// Helper to compile with specific UIP setting
function compileWithUIP(source: string, assumeUIP: boolean): { success: boolean; errors: string[] } {
  const options: CompileOptions = {
    tcEnvOptions: { assumeUIP }
  };
  const result = compileTTFromText(source, options);
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

console.log('\n' + '='.repeat(80));
console.log('AXIOM K / UIP TESTS');
console.log('='.repeat(80) + '\n');

// ============================================================================
// K-Independent Functions (should pass with both settings)
// ============================================================================

console.log('--- K-Independent Functions ---\n');

test('reflexivity proof construction should pass without K', () => {
  const REFL_PROOF_SOURCE = `${EQUAL_DEF}

refl_proof : (A : Type) -> (x : A) -> Equal A x x
refl_proof A x = refl A x`;

  const result = compileWithUIP(REFL_PROOF_SOURCE, false);
  assert(result.success, `refl_proof should pass without K. Errors: ${result.errors.join(', ')}`);
});

test('reflexivity proof construction should pass with K', () => {
  const REFL_PROOF_SOURCE = `${EQUAL_DEF}

refl_proof : (A : Type) -> (x : A) -> Equal A x x
refl_proof A x = refl A x`;

  const result = compileWithUIP(REFL_PROOF_SOURCE, true);
  assert(result.success, `refl_proof should pass with K. Errors: ${result.errors.join(', ')}`);
});

// ============================================================================
// K-Dependent Functions (should pass only with assumeUIP: true)
// ============================================================================

console.log('\n--- K-Dependent Functions ---\n');

test("Streicher's K should FAIL without K (assumeUIP: false)", () => {
  const K_SOURCE = `${EQUAL_DEF}

streichersK : (A : Type) -> (a : A) -> (P : Equal A a a -> Type) -> P (refl A a) -> (e : Equal A a a) -> P e
streichersK A a P p (refl _ _) = p`;

  const result = compileWithUIP(K_SOURCE, false);
  assert(!result.success, `streichersK should FAIL without K`);

  // Check that error message mentions K or UIP
  const hasKError = result.errors.some(e =>
    e.toLowerCase().includes('k') || e.toLowerCase().includes('uip')
  );
  assert(hasKError, `Error should mention K or UIP. Got: ${result.errors.join(', ')}`);
});

test("Streicher's K should pass with K (assumeUIP: true)", () => {
  const K_SOURCE = `${EQUAL_DEF}

streichersK : (A : Type) -> (a : A) -> (P : Equal A a a -> Type) -> P (refl A a) -> (e : Equal A a a) -> P e
streichersK A a P p (refl _ _) = p`;

  const result = compileWithUIP(K_SOURCE, true);
  assert(result.success, `streichersK should pass with K. Errors: ${result.errors.join(', ')}`);
});

test('matching on Equal A a a (with variable a) should FAIL without K', () => {
  // This is the simplest K-dependent pattern: matching on reflexive equality with variable indices
  const VAR_INDEX_SOURCE = `${EQUAL_DEF}

matchOnReflexive : (A : Type) -> (a : A) -> Equal A a a -> Equal A a a
matchOnReflexive A a (refl _ _) = refl A a`;

  const result = compileWithUIP(VAR_INDEX_SOURCE, false);
  assert(!result.success, `matchOnReflexive should FAIL without K`);
});

test('matching on Equal A a a (with variable a) should pass with K', () => {
  const VAR_INDEX_SOURCE = `${EQUAL_DEF}

matchOnReflexive : (A : Type) -> (a : A) -> Equal A a a -> Equal A a a
matchOnReflexive A a (refl _ _) = refl A a`;

  const result = compileWithUIP(VAR_INDEX_SOURCE, true);
  assert(result.success, `matchOnReflexive should pass with K. Errors: ${result.errors.join(', ')}`);
});

test('uipRefl (proof that p = refl for p : a = a) should FAIL without K', () => {
  const UIP_REFL_SOURCE = `${EQUAL_DEF}

uipRefl : (A : Type) -> (x : A) -> (p : Equal A x x) -> Equal (Equal A x x) p (refl A x)
uipRefl _ _ (refl _ _) = refl (Equal _ _ _) (refl _ _)`;

  const result = compileWithUIP(UIP_REFL_SOURCE, false);
  assert(!result.success, `uipRefl should FAIL without K`);
});

test('uipRefl should pass with K (assumeUIP: true)', () => {
  const UIP_REFL_SOURCE = `${EQUAL_DEF}

uipRefl : (A : Type) -> (x : A) -> (p : Equal A x x) -> Equal (Equal A x x) p (refl A x)
uipRefl _ _ (refl _ _) = refl (Equal _ _ _) (refl _ _)`;

  const result = compileWithUIP(UIP_REFL_SOURCE, true);
  assert(result.success, `uipRefl should pass with K. Errors: ${result.errors.join(', ')}`);
});

test('weak K (K at equality of equalities) should FAIL without K', () => {
  const WEAK_K_SOURCE = `${EQUAL_DEF}

weakK : (A : Type) -> (a : A) -> (P : Equal (Equal A a a) (refl A a) (refl A a) -> Type) -> P (refl (Equal A a a) (refl A a)) -> (e : Equal (Equal A a a) (refl A a) (refl A a)) -> P e
weakK A a P p (refl _ _) = p`;

  const result = compileWithUIP(WEAK_K_SOURCE, false);
  assert(!result.success, `weakK should FAIL without K`);
});

test('weak K should pass with K (assumeUIP: true)', () => {
  const WEAK_K_SOURCE = `${EQUAL_DEF}

weakK : (A : Type) -> (a : A) -> (P : Equal (Equal A a a) (refl A a) (refl A a) -> Type) -> P (refl (Equal A a a) (refl A a)) -> (e : Equal (Equal A a a) (refl A a) (refl A a)) -> P e
weakK A a P p (refl _ _) = p`;

  const result = compileWithUIP(WEAK_K_SOURCE, true);
  assert(result.success, `weakK should pass with K. Errors: ${result.errors.join(', ')}`);
});

// ============================================================================
// Default Behavior Tests
// ============================================================================

console.log('\n--- Default Behavior ---\n');

test('default should be assumeUIP: false (K-free mode)', () => {
  const K_SOURCE = `${EQUAL_DEF}

streichersK : (A : Type) -> (a : A) -> (P : Equal A a a -> Type) -> P (refl A a) -> (e : Equal A a a) -> P e
streichersK A a P p (refl _ _) = p`;

  // Compile without options - should use default (assumeUIP: false)
  const result = compileTTFromText(K_SOURCE);

  assert(!result.success, `Default should be K-free mode (assumeUIP: false)`);
});

console.log('\n' + '='.repeat(80));
console.log('ALL AXIOM K / UIP TESTS PASSED! ✓');
console.log('='.repeat(80) + '\n');
