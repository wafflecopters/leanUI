/**
 * Tests for name resolution integration in block-checker
 */

import { compileSource } from '../test-utils';

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

  const results = compileSource(source);

  assert(results.length === 1, 'Should have 1 block');
  assert(results[0].parseSuccess === true, 'Parse should succeed');
  // Name resolution is checked during type checking, errors surface as check errors
  assert(results[0].checkSuccess === false, 'Check should fail due to undefined Nat');
});

test('Defined symbol works', () => {
  const source = `inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

plus : Nat -> Nat -> Nat
plus Zero b = b
plus (Succ a) b = Succ (plus a b)`;

  const results = compileSource(source);

  assert(results.length === 2, 'Should have 2 blocks');
  assert(results[0].parseSuccess === true, 'First block parse should succeed');
  assert(results[0].checkSuccess === true, 'First block check should succeed');
  assert(results[1].parseSuccess === true, 'Second block parse should succeed');
  assert(results[1].checkSuccess === true, `Second block check should succeed. Errors: ${results[1].checkErrors.map(e => e.message).join(', ')}`);
});

test('Typo case: Na instead of Nat', () => {
  const source = `inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

plus : Nat -> Nat -> Na`;

  const results = compileSource(source);

  assert(results.length === 2, 'Should have 2 blocks');
  assert(results[0].checkSuccess === true, 'First block should succeed');
  assert(results[1].checkSuccess === false, 'Second block should fail due to typo');
});

// ============================================================================
// Forward references
// ============================================================================

test('Forward reference in same block fails', () => {
  const source = `f : A -> A`;

  const results = compileSource(source);

  assert(results.length === 1, 'Should have 1 block');
  assert(results[0].checkSuccess === false, 'Should fail due to undefined A');
});

test('Symbol from previous block works', () => {
  const source = `inductive Bool : Type where
  True : Bool
  False : Bool

not : Bool -> Bool
not True = False
not False = True`;

  const results = compileSource(source);

  assert(results.length === 2, 'Should have 2 blocks');
  assert(results[0].checkSuccess === true, 'First block succeeds');
  assert(results[1].checkSuccess === true, `Second block succeeds (uses Bool from first). Errors: ${results[1].checkErrors.map(e => e.message).join(', ')}`);
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

  const results = compileSource(source);

  assert(results.length === 2, 'Should have 2 blocks');
  assert(results[0].checkSuccess === true, 'First block succeeds');
  assert(results[1].checkSuccess === true, 'Second block succeeds (uses True constructor)');
});

test('Multiple undefined symbols', () => {
  const source = `f : A -> B -> C`;

  const results = compileSource(source);

  assert(results.length === 1, 'Should have 1 block');
  assert(results[0].checkSuccess === false, 'Should fail due to undefined symbols');
});

// ============================================================================
// Self-reference
// ============================================================================

test('Self-reference in type works', () => {
  const source = `inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat`;

  const results = compileSource(source);

  assert(results.length === 1, 'Should have 1 block');
  assert(results[0].checkSuccess === true, 'Self-reference works');
});

// ============================================================================
// Context accumulation
// ============================================================================

test('Context accumulates across blocks', () => {
  const source = `inductive A : Type where
  MkA : A

inductive B : Type where
  MkB : B

f : A -> B -> A
f a b = a`;

  const results = compileSource(source);

  assert(results.length === 3, 'Should have 3 blocks');
  assert(results[0].checkSuccess === true, 'Block 1 succeeds');
  assert(results[1].checkSuccess === true, 'Block 2 succeeds');
  assert(results[2].checkSuccess === true, `Block 3 succeeds (uses A and B). Errors: ${results[2].checkErrors.map(e => e.message).join(', ')}`);
});

// ============================================================================
// Parse errors don't prevent name resolution tracking
// ============================================================================

test('Parse error in one block does not affect later blocks', () => {
  const source = `inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

bad syntax here!!!

plus : Nat -> Nat -> Nat
plus Zero b = b
plus (Succ a) b = Succ (plus a b)`;

  const results = compileSource(source);

  assert(results.length === 3, 'Should have 3 blocks');
  assert(results[0].checkSuccess === true, 'Block 1 succeeds');
  assert(results[1].parseSuccess === false, 'Block 2 parse fails');
  assert(results[2].checkSuccess === true, `Block 3 succeeds (Nat is still in scope). Errors: ${results[2].checkErrors.map(e => e.message).join(', ')}`);
});

console.log('\n' + '='.repeat(80));
console.log('ALL BLOCK-CHECKER NAME RESOLUTION TESTS PASSED! ✓');
console.log('='.repeat(80) + '\n');
