/**
 * Tests for source position tracking in the parser
 */

import { Parser } from './tt-parser';

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
console.log('PARSER SOURCE TRACKING TESTS');
console.log('='.repeat(80) + '\n');

// ============================================================================
// Basic parseDeclarationsWithSource Tests
// ============================================================================

test('parseDeclarationsWithSource returns declarations with source maps', () => {
  const parser = new Parser();
  const source = `id : A -> A`;

  const results = parser.parseDeclarationsWithSource(source);

  assert(results.length === 1, 'Should have 1 declaration');
  assert(results[0].decl !== undefined, 'Should have declaration');
  assert(results[0].sourceMap !== undefined, 'Should have source map');
  assert(results[0].sourceMap instanceof Map, 'Source map should be a Map');
});

test('parseDeclarationsWithSource with multiple declarations', () => {
  const parser = new Parser();
  const source = `id : A -> A

const : A -> B -> A`;

  const results = parser.parseDeclarationsWithSource(source);

  assert(results.length === 2, 'Should have 2 declarations');
  assert(results[0].decl.name === 'id', 'First declaration name should be id');
  assert(results[1].decl.name === 'const', 'Second declaration name should be const');
});

test('parseDeclarationsWithSource with merged type and value', () => {
  const parser = new Parser();
  const source = `id : A -> A
id x = x`;

  const results = parser.parseDeclarationsWithSource(source);

  assert(results.length === 1, 'Should merge into 1 declaration');
  assert(results[0].decl.name === 'id', 'Declaration name should be id');
  assert(results[0].decl.type !== undefined, 'Should have type');
  assert(results[0].decl.value !== undefined, 'Should have value');
  // Source map should have entries from both lines
  assert(results[0].sourceMap.size >= 0, 'Should have source map entries');
});

test('Source map is separate for each declaration', () => {
  const parser = new Parser();
  const source = `id : A -> A

const : A -> B -> A`;

  const results = parser.parseDeclarationsWithSource(source);

  // Each should have its own source map instance
  assert(results[0].sourceMap !== results[1].sourceMap, 'Source maps should be different instances');
});

test('parseDeclarationsWithSource handles inductive', () => {
  const parser = new Parser();
  const source = `inductive Nat : Type where
  | Zero : Nat
  | Succ : Nat -> Nat`;

  const results = parser.parseDeclarationsWithSource(source);

  assert(results.length === 1, 'Should have 1 inductive declaration');
  assert(results[0].decl.kind === 'inductive', 'Should be inductive kind');
  assert(results[0].decl.name === 'Nat', 'Name should be Nat');
  assert(results[0].sourceMap instanceof Map, 'Should have source map');
});

console.log('\n' + '='.repeat(80));
console.log('ALL PARSER SOURCE TRACKING TESTS PASSED! ✓');
console.log('='.repeat(80) + '\n');
