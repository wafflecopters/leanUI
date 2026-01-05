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

import { checkSourceBlocks } from './block-checker';

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
console.log('VECCONCAT REGRESSION TEST');
console.log('='.repeat(80) + '\n');

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
  // 1. Define `plus : Nat -> Nat -> Nat`
  // 2. Define a type family `F : Nat -> Type`
  // 3. Use `F (plus Zero Zero)` in a type signature
  //
  // For (3) to work, `plus Zero Zero` must have type `Nat`.
  // That requires knowing `plus : Nat -> Nat -> Nat`.
  const source = `inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

plus : Nat -> Nat -> Nat

-- A type family indexed by Nat
F : Nat -> Type

-- This uses 'plus' inside a type expression
-- Type checker must resolve plus, then infer (plus Zero Zero) : Nat,
-- then check F (plus Zero Zero) : Type
test : F (plus Zero Zero)`;

  const results = checkSourceBlocks(source);

  console.log(`  Found ${results.length} blocks`);

  for (const r of results) {
    console.log(`  Block ${r.name}: parse=${r.parseSuccess}, check=${r.checkSuccess}`);
    if (!r.checkSuccess && r.checkErrors.length > 0) {
      console.log(`    Errors: ${r.checkErrors.map(e => e.error.message).join('; ')}`);
    }
  }

  const testBlock = results.find(r => r.name === 'test');
  assert(testBlock !== undefined, 'Should find test block');
  assert(
    testBlock!.checkSuccess === true,
    `test should type-check when using 'plus' in type. Error: ${testBlock!.checkErrors.map(e => e.error.message).join(', ')}`
  );
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

  const results = checkSourceBlocks(source);

  console.log(`  Found ${results.length} blocks`);

  for (const r of results) {
    console.log(`  Block ${r.name}: parse=${r.parseSuccess}, check=${r.checkSuccess}`);
    if (!r.checkSuccess && r.checkErrors.length > 0) {
      console.log(`    Errors: ${r.checkErrors.map(e => e.error.message).join('; ')}`);
    }
  }

  // Check that vecConcat type-checks
  const vecConcatBlock = results.find(r => r.name === 'vecConcat');
  assert(vecConcatBlock !== undefined, 'Should find vecConcat block');

  // This is the assertion that exposes the bug:
  // If constant resolution doesn't work, we'll get:
  //   "Application requires Pi type, got: ?plus_type"
  assert(
    vecConcatBlock!.checkSuccess === true,
    `vecConcat should type-check. Error: ${vecConcatBlock!.checkErrors.map(e => e.error.message).join(', ')}`
  );
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

  const results = checkSourceBlocks(source);

  console.log(`  Found ${results.length} blocks`);

  for (const r of results) {
    console.log(`  Block ${r.name}: parse=${r.parseSuccess}, check=${r.checkSuccess}`);
    if (!r.checkSuccess && r.checkErrors.length > 0) {
      console.log(`    Errors: ${r.checkErrors.map(e => e.error.message).join('; ')}`);
    }
  }

  // Check vecConcat specifically
  const vecConcatBlock = results.find(r => r.name === 'vecConcat');
  assert(vecConcatBlock !== undefined, 'Should find vecConcat block');

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
    const errorMsg = vecConcatBlock!.checkErrors.map(e => e.error.message).join(', ');
    console.log(`  VECCONCAT ERROR: ${errorMsg}`);

    // The OLD bug: unresolved constant type
    if (errorMsg.includes('plus_type')) {
      throw new Error(`Bug not fixed! Got: ${errorMsg}`);
    }

    // The EXPECTED error after the fix: pattern matching not implemented
    // This is fine - it's a known limitation, not a constant resolution bug
    assert(
      errorMsg.includes('Pattern matching'),
      `Expected pattern matching error, got: ${errorMsg}`
    );
  }
});

console.log('\n' + '='.repeat(80));
console.log('VECCONCAT REGRESSION TEST COMPLETE');
console.log('='.repeat(80) + '\n');
