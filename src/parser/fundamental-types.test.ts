/**
 * Tests for fundamental inductive types (Nat, List, Vec, Fin, Equal, etc.)
 *
 * These are the core types that any proof assistant should be able to parse
 * and type check successfully.
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
console.log('FUNDAMENTAL INDUCTIVE TYPES TESTS');
console.log('='.repeat(80) + '\n');

// ============================================================================
// Natural Numbers (Nat)
// ============================================================================

test('Nat: basic definition', () => {
  const source = `inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat`;

  const results = checkSourceBlocks(source);

  assert(results.length === 1, 'Should have 1 block');
  assert(results[0].parseSuccess === true, 'Parse should succeed');
  assert(results[0].checkSuccess === true, 'Check should succeed');
  assert(results[0].checkErrors.length === 0, 'Should have no errors');
  assert(results[0].name === 'Nat', 'Should have correct name');
});

// ============================================================================
// Lists (polymorphic)
// ============================================================================

test('List: polymorphic list definition', () => {
  const source = `inductive List : Type -> Type where
  Nil : List A
  Cons : A -> List A -> List A`;

  const results = checkSourceBlocks(source);

  assert(results.length === 1, 'Should have 1 block');
  assert(results[0].parseSuccess === true, 'Parse should succeed');
  assert(results[0].checkSuccess === true, 'Check should succeed');
  assert(results[0].checkErrors.length === 0, 'Should have no errors');
  assert(results[0].name === 'List', 'Should have correct name');
});

// ============================================================================
// Booleans
// ============================================================================

test('Bool: boolean type', () => {
  const source = `inductive Bool : Type where
  True : Bool
  False : Bool`;

  const results = checkSourceBlocks(source);

  assert(results.length === 1, 'Should have 1 block');
  assert(results[0].parseSuccess === true, 'Parse should succeed');
  assert(results[0].checkSuccess === true, 'Check should succeed');
  assert(results[0].checkErrors.length === 0, 'Should have no errors');
  assert(results[0].name === 'Bool', 'Should have correct name');
});

// ============================================================================
// Unit type
// ============================================================================

test('Unit: trivial type', () => {
  const source = `inductive Unit : Type where
  unit : Unit`;

  const results = checkSourceBlocks(source);

  assert(results.length === 1, 'Should have 1 block');
  assert(results[0].parseSuccess === true, 'Parse should succeed');
  assert(results[0].checkSuccess === true, 'Check should succeed');
  assert(results[0].checkErrors.length === 0, 'Should have no errors');
  assert(results[0].name === 'Unit', 'Should have correct name');
});

// ============================================================================
// Empty type (False)
// ============================================================================

test('Empty: empty type with no constructors', () => {
  const source = `inductive Empty : Type where`;

  const results = checkSourceBlocks(source);

  assert(results.length === 1, 'Should have 1 block');
  assert(results[0].parseSuccess === true, 'Parse should succeed');
  assert(results[0].checkSuccess === true, 'Check should succeed');
  assert(results[0].checkErrors.length === 0, 'Should have no errors');
  assert(results[0].name === 'Empty', 'Should have correct name');
});

// ============================================================================
// Sum type (Either/Or)
// ============================================================================

test('Sum: binary sum type', () => {
  const source = `inductive Sum : Type -> Type -> Type where
  Left : A -> Sum A B
  Right : B -> Sum A B`;

  const results = checkSourceBlocks(source);

  assert(results.length === 1, 'Should have 1 block');
  assert(results[0].parseSuccess === true, 'Parse should succeed');
  assert(results[0].checkSuccess === true, 'Check should succeed');
  assert(results[0].checkErrors.length === 0, 'Should have no errors');
  assert(results[0].name === 'Sum', 'Should have correct name');
});

// ============================================================================
// Product type (Pair)
// ============================================================================

test('Prod: binary product type', () => {
  const source = `inductive Prod : Type -> Type -> Type where
  Pair : A -> B -> Prod A B`;

  const results = checkSourceBlocks(source);

  assert(results.length === 1, 'Should have 1 block');
  assert(results[0].parseSuccess === true, 'Parse should succeed');
  assert(results[0].checkSuccess === true, 'Check should succeed');
  assert(results[0].checkErrors.length === 0, 'Should have no errors');
  assert(results[0].name === 'Prod', 'Should have correct name');
});

// ============================================================================
// Option/Maybe type
// ============================================================================

test('Option: optional value type', () => {
  const source = `inductive Option : Type -> Type where
  None : Option A
  Some : A -> Option A`;

  const results = checkSourceBlocks(source);

  assert(results.length === 1, 'Should have 1 block');
  assert(results[0].parseSuccess === true, 'Parse should succeed');
  assert(results[0].checkSuccess === true, 'Check should succeed');
  assert(results[0].checkErrors.length === 0, 'Should have no errors');
  assert(results[0].name === 'Option', 'Should have correct name');
});

// ============================================================================
// Vectors (length-indexed lists)
// ============================================================================

test('Vec: length-indexed vectors', () => {
  const source = `inductive Vec : Type -> Nat -> Type where
  VNil : Vec A Zero
  VCons : A -> Vec A n -> Vec A (Succ n)`;

  const results = checkSourceBlocks(source);

  assert(results.length === 1, 'Should have 1 block');
  assert(results[0].parseSuccess === true, 'Parse should succeed');
  assert(results[0].checkSuccess === true, 'Check should succeed');
  assert(results[0].checkErrors.length === 0, 'Should have no errors');
  assert(results[0].name === 'Vec', 'Should have correct name');
});

// ============================================================================
// Fin (bounded natural numbers)
// ============================================================================

test('Fin: bounded natural numbers', () => {
  const source = `inductive Fin : Nat -> Type where
  FZero : Fin (Succ n)
  FSucc : Fin n -> Fin (Succ n)`;

  const results = checkSourceBlocks(source);

  assert(results.length === 1, 'Should have 1 block');
  assert(results[0].parseSuccess === true, 'Parse should succeed');
  assert(results[0].checkSuccess === true, 'Check should succeed');
  assert(results[0].checkErrors.length === 0, 'Should have no errors');
  assert(results[0].name === 'Fin', 'Should have correct name');
});

// ============================================================================
// Equality (propositional equality)
// ============================================================================

test('Eq: propositional equality', () => {
  const source = `inductive Eq : A -> A -> Type where
  Refl : Eq x x`;

  const results = checkSourceBlocks(source);

  assert(results.length === 1, 'Should have 1 block');
  assert(results[0].parseSuccess === true, 'Parse should succeed');
  assert(results[0].checkSuccess === true, 'Check should succeed');
  assert(results[0].checkErrors.length === 0, 'Should have no errors');
  assert(results[0].name === 'Eq', 'Should have correct name');
});

// ============================================================================
// Exists (Sigma type / dependent pair)
// ============================================================================

test('Exists: sigma type (dependent pair)', () => {
  const source = `inductive Exists : (A -> Type) -> Type where
  ExIntro : (x : A) -> P x -> Exists P`;

  const results = checkSourceBlocks(source);

  assert(results.length === 1, 'Should have 1 block');
  assert(results[0].parseSuccess === true, 'Parse should succeed');
  assert(results[0].checkSuccess === true, 'Check should succeed');
  assert(results[0].checkErrors.length === 0, 'Should have no errors');
  assert(results[0].name === 'Exists', 'Should have correct name');
});

// ============================================================================
// Accessibility (well-founded recursion)
// ============================================================================

test('Acc: accessibility predicate', () => {
  const source = `inductive Acc : (A -> A -> Type) -> A -> Type where
  AccIntro : ((y : A) -> R y x -> Acc R y) -> Acc R x`;

  const results = checkSourceBlocks(source);

  assert(results.length === 1, 'Should have 1 block');
  assert(results[0].parseSuccess === true, 'Parse should succeed');
  assert(results[0].checkSuccess === true, 'Check should succeed');
  assert(results[0].checkErrors.length === 0, 'Should have no errors');
  assert(results[0].name === 'Acc', 'Should have correct name');
});

// ============================================================================
// Multiple types in one file
// ============================================================================

test('Multiple fundamental types together', () => {
  const source = `inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Bool : Type where
  True : Bool
  False : Bool

inductive List : Type -> Type where
  Nil : List A
  Cons : A -> List A -> List A`;

  const results = checkSourceBlocks(source);

  assert(results.length === 3, 'Should have 3 blocks');
  assert(results[0].name === 'Nat', 'First should be Nat');
  assert(results[1].name === 'Bool', 'Second should be Bool');
  assert(results[2].name === 'List', 'Third should be List');
  assert(results.every(r => r.parseSuccess === true), 'All should parse');
  assert(results.every(r => r.checkSuccess === true), 'All should check');
});

// ============================================================================
// Multiline type signatures
// ============================================================================

test('Multiline inductive type signature with where', () => {
  const source = `inductive Foo : Type
  -> Type where
  Bar : Foo`;

  const results = checkSourceBlocks(source);

  assert(results.length === 1, 'Should have 1 block');
  assert(results[0].parseSuccess === true, 'Parse should succeed');
  assert(results[0].checkSuccess === true, 'Check should succeed');
  assert(results[0].name === 'Foo', 'Should have correct name');
  assert(results[0].declarations?.[0].constructors?.length === 1, 'Should have 1 constructor');
});

console.log('\n' + '='.repeat(80));
console.log('ALL FUNDAMENTAL TYPES TESTS PASSED! ✓');
console.log('='.repeat(80) + '\n');
