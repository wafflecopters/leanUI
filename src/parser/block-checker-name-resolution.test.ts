/**
 * Tests for name resolution integration in block-checker
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
console.log('BLOCK-CHECKER NAME RESOLUTION TESTS');
console.log('='.repeat(80) + '\n');

// ============================================================================
// Basic name resolution
// ============================================================================

test('Undefined symbol in simple case', () => {
  const source = `plus : Nat -> Nat -> Nat`;

  const results = checkSourceBlocks(source);

  assert(results.length === 1, 'Should have 1 block');
  assert(results[0].parseSuccess === true, 'Parse should succeed');
  assert(results[0].nameResolutionSuccess === false, 'Name resolution should fail');
  assert(results[0].nameResolutionErrors.length === 3, 'Should have 3 errors (3 uses of Nat)');
  assert(results[0].nameResolutionErrors[0].error.symbolName === 'Nat', 'Error for Nat');
});

test('Defined symbol works', () => {
  const source = `inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

plus : Nat -> Nat -> Nat`;

  const results = checkSourceBlocks(source);

  assert(results.length === 2, 'Should have 2 blocks');
  assert(results[0].parseSuccess === true, 'First block parse should succeed');
  assert(results[0].nameResolutionSuccess === true, 'First block name resolution should succeed');
  assert(results[1].parseSuccess === true, 'Second block parse should succeed');
  assert(results[1].nameResolutionSuccess === true, 'Second block name resolution should succeed');
});

test('Typo case: Na instead of Nat', () => {
  const source = `inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

plus : Nat -> Nat -> Na`;

  const results = checkSourceBlocks(source);

  assert(results.length === 2, 'Should have 2 blocks');
  assert(results[0].nameResolutionSuccess === true, 'First block should succeed');
  assert(results[1].nameResolutionSuccess === false, 'Second block should fail');
  assert(results[1].nameResolutionErrors.length === 1, 'Should have 1 error');
  assert(results[1].nameResolutionErrors[0].error.symbolName === 'Na', 'Error for Na typo');
  assert(results[1].nameResolutionErrors[0].error.message.includes('Undefined symbol'), 'Helpful message');
});

// ============================================================================
// Forward references
// ============================================================================

test('Forward reference in same block fails', () => {
  const source = `f : A -> A`;

  const results = checkSourceBlocks(source);

  assert(results.length === 1, 'Should have 1 block');
  assert(results[0].nameResolutionSuccess === false, 'Should fail');
  assert(results[0].nameResolutionErrors.length === 2, 'Two uses of A');
});

test('Symbol from previous block works', () => {
  const source = `inductive Bool : Type where
  True : Bool
  False : Bool

not : Bool -> Bool`;

  const results = checkSourceBlocks(source);

  assert(results.length === 2, 'Should have 2 blocks');
  assert(results[0].nameResolutionSuccess === true, 'First block succeeds');
  assert(results[1].nameResolutionSuccess === true, 'Second block succeeds (uses Bool from first)');
});

// ============================================================================
// Constructors in scope
// ============================================================================

test('Constructors are in scope', () => {
  const source = `inductive Bool : Type where
  True : Bool
  False : Bool

test : Bool
test = True`;

  const results = checkSourceBlocks(source);

  assert(results.length === 2, 'Should have 2 blocks');
  assert(results[0].nameResolutionSuccess === true, 'First block succeeds');
  assert(results[1].nameResolutionSuccess === true, 'Second block succeeds (uses True constructor)');
});

test('Multiple undefined symbols', () => {
  const source = `f : A -> B -> C`;

  const results = checkSourceBlocks(source);

  assert(results.length === 1, 'Should have 1 block');
  assert(results[0].nameResolutionSuccess === false, 'Should fail');
  assert(results[0].nameResolutionErrors.length === 3, 'Three undefined symbols');
});

// ============================================================================
// Self-reference
// ============================================================================

test('Self-reference in type works', () => {
  const source = `inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat`;

  const results = checkSourceBlocks(source);

  assert(results.length === 1, 'Should have 1 block');
  assert(results[0].nameResolutionSuccess === true, 'Self-reference works');
});

// ============================================================================
// Context accumulation
// ============================================================================

test('Context accumulates across blocks', () => {
  const source = `inductive A : Type where
  MkA : A

inductive B : Type where
  MkB : B

f : A -> B -> A`;

  const results = checkSourceBlocks(source);

  assert(results.length === 3, 'Should have 3 blocks');
  assert(results[0].nameResolutionSuccess === true, 'Block 1 succeeds');
  assert(results[1].nameResolutionSuccess === true, 'Block 2 succeeds');
  assert(results[2].nameResolutionSuccess === true, 'Block 3 succeeds (uses A and B)');
});

// ============================================================================
// Parse errors don't prevent name resolution tracking
// ============================================================================

test('Parse error in one block does not affect later blocks', () => {
  const source = `inductive Nat : Type where
  Zero : Nat

bad syntax here!!!

plus : Nat -> Nat -> Nat`;

  const results = checkSourceBlocks(source);

  assert(results.length === 3, 'Should have 3 blocks');
  assert(results[0].nameResolutionSuccess === true, 'Block 1 succeeds');
  assert(results[1].parseSuccess === false, 'Block 2 parse fails');
  assert(results[2].nameResolutionSuccess === true, 'Block 3 succeeds (Nat is still in scope)');
});

console.log('\n' + '='.repeat(80));
console.log('ALL BLOCK-CHECKER NAME RESOLUTION TESTS PASSED! ✓');
console.log('='.repeat(80) + '\n');
