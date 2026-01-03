/**
 * Tests for pattern matching syntax parsing
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
console.log('PATTERN MATCHING TESTS');
console.log('='.repeat(80) + '\n');

// ============================================================================
// Basic Pattern Matching
// ============================================================================

test('Pattern matching: simple function with type signature', () => {
  const source = `plus : Nat -> Nat -> Nat
plus Zero b = b
plus (Succ a) b = Succ (plus a b)`;

  const results = checkSourceBlocks(source);

  assert(results.length === 1, 'Should have 1 block');
  assert(results[0].parseSuccess === true, 'Parse should succeed');
  assert(results[0].name === 'plus', 'Should have correct name');
  assert(results[0].declarations?.length === 1, 'Should have 1 declaration (merged)');
});

test('Pattern matching: multiple clauses', () => {
  const source = `isZero : Nat -> Bool
isZero Zero = True
isZero (Succ n) = False`;

  const results = checkSourceBlocks(source);

  assert(results.length === 1, 'Should have 1 block');
  assert(results[0].parseSuccess === true, 'Parse should succeed');
  assert(results[0].name === 'isZero', 'Should have correct name');
});

test('Pattern matching: nested patterns', () => {
  const source = `add : Nat -> Nat -> Nat
add Zero n = n
add (Succ m) n = Succ (add m n)`;

  const results = checkSourceBlocks(source);

  assert(results.length === 1, 'Should have 1 block');
  assert(results[0].parseSuccess === true, 'Parse should succeed');
});

test('Pattern matching: underscore patterns', () => {
  const source = `const : A -> B -> A
const x _ = x`;

  const results = checkSourceBlocks(source);

  assert(results.length === 1, 'Should have 1 block');
  assert(results[0].parseSuccess === true, 'Parse should succeed');
});

test('Pattern matching: variable patterns', () => {
  const source = `id : A -> A
id x = x`;

  const results = checkSourceBlocks(source);

  assert(results.length === 1, 'Should have 1 block');
  assert(results[0].parseSuccess === true, 'Parse should succeed');
});

console.log('\n' + '='.repeat(80));
console.log('ALL PATTERN MATCHING TESTS PASSED! ✓');
console.log('='.repeat(80) + '\n');
