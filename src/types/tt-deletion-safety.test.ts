/**
 * Tests for Deletion Safety System
 * 
 * Verifies that variables cannot be deleted if they are still in use
 */

import {
  isNameUsed,
  mkConst,
  mkApp,
  mkProp,
  mkPi,
  mkLet,
  mkHole,
  mkType,
  TT_CONSTANTS
} from './tt-core';

/**
 * Simple assertion helper
 */
function assert(condition: boolean, message: string): void {
  if (!condition) {
    throw new Error(`Assertion failed: ${message}`);
  }
}

/**
 * Run a test with a description
 */
function test(description: string, fn: () => void): void {
  try {
    fn();
    console.log(`✓ ${description}`);
  } catch (error) {
    console.error(`✗ ${description}`);
    throw error;
  }
}

// ============================================================================
// Basic Usage Detection Tests
// ============================================================================

test('detects constant name usage', () => {
  const term = mkConst('a', TT_CONSTANTS.Real);

  assert(isNameUsed('a', term) === true, 'should detect "a"');
  assert(isNameUsed('b', term) === false, 'should not detect "b"');
});

test('detects name in function application', () => {
  // (+ a b)
  const term = mkApp(
    mkApp(mkConst('+', TT_CONSTANTS.Real), mkConst('a', TT_CONSTANTS.Real)),
    mkConst('b', TT_CONSTANTS.Real)
  );

  assert(isNameUsed('a', term) === true, 'should detect "a"');
  assert(isNameUsed('b', term) === true, 'should detect "b"');
  assert(isNameUsed('c', term) === false, 'should not detect "c"');
});

test('detects name in nested applications', () => {
  // ((+ a) ((* 2) a))
  const term = mkApp(
    mkApp(mkConst('+', TT_CONSTANTS.Real), mkConst('a', TT_CONSTANTS.Real)),
    mkApp(
      mkApp(mkConst('*', TT_CONSTANTS.Real), mkConst('2', TT_CONSTANTS.Real)),
      mkConst('a', TT_CONSTANTS.Real)
    )
  );

  assert(isNameUsed('a', term) === true, 'should detect "a"');
  assert(isNameUsed('2', term) === true, 'should detect "2"');
});

// ============================================================================
// Shadowing Behavior Tests
// ============================================================================

test('does not detect shadowed name in Pi binder', () => {
  // ∀ (a : Real), a + a
  // The 'a' in the body is bound by the Pi, not free
  const term = mkPi(
    TT_CONSTANTS.Real,
    mkApp(
      mkApp(mkConst('+', TT_CONSTANTS.Real), mkConst('a', TT_CONSTANTS.Real)),
      mkConst('a', TT_CONSTANTS.Real)
    ),
    'a'
  );

  // 'a' is bound in the body, so not a free occurrence
  assert(isNameUsed('a', term) === false, '"a" should be bound, not free');
});

test('detects name in domain but not in shadowed body', () => {
  // (b : Real) → b + b, where b is a constant in the domain
  const domainWithB = mkApp(
    mkConst('SomeType', mkProp()),
    mkConst('b', TT_CONSTANTS.Real)
  );

  const term = mkPi(
    domainWithB,
    mkApp(
      mkApp(mkConst('+', TT_CONSTANTS.Real), mkConst('b', TT_CONSTANTS.Real)),
      mkConst('b', TT_CONSTANTS.Real)
    ),
    'b'
  );

  // 'b' is used in the domain, even though it's shadowed in the body
  assert(isNameUsed('b', term) === true, '"b" should be detected in domain');
});

test('handles nested shadowing correctly', () => {
  // ∀ (a : Real), ∀ (a : Real), a
  // Both 'a' bindings, inner one shadows outer
  const inner = mkPi(
    TT_CONSTANTS.Real,
    mkConst('a', TT_CONSTANTS.Real),
    'a'
  );

  const outer = mkPi(
    TT_CONSTANTS.Real,
    inner,
    'a'
  );

  // Both 'a's are bound, no free occurrence
  assert(isNameUsed('a', outer) === false, 'nested "a" should be bound');
});

// ============================================================================
// Let-Binding Detection Tests
// ============================================================================

test('detects name in let-binding value', () => {
  // let x = a + 1 in x
  const letTerm = mkLet(
    'x',
    TT_CONSTANTS.Real,
    mkApp(
      mkApp(mkConst('+', TT_CONSTANTS.Real), mkConst('a', TT_CONSTANTS.Real)),
      mkConst('1', TT_CONSTANTS.Real)
    ),
    mkConst('x', TT_CONSTANTS.Real)
  );

  assert(isNameUsed('a', letTerm) === true, '"a" should be detected in let value');
  assert(isNameUsed('x', letTerm) === false, '"x" should be bound');
});

test('detects name in let-binding type', () => {
  // let x : (T a) = 1 in x
  const typeWithA = mkApp(
    mkConst('T', mkProp()),
    mkConst('a', TT_CONSTANTS.Real)
  );

  const letTerm = mkLet(
    'x',
    typeWithA,
    mkConst('1', TT_CONSTANTS.Real),
    mkConst('x', TT_CONSTANTS.Real)
  );

  assert(isNameUsed('a', letTerm) === true, '"a" should be detected in type');
});

// ============================================================================
// Type Holes Tests
// ============================================================================

test('detects name in hole type', () => {
  // ?hole : (T a)
  const holeType = mkApp(
    mkConst('T', mkProp()),
    mkConst('a', TT_CONSTANTS.Real)
  );

  const hole = mkHole('myhole', holeType, []);

  assert(isNameUsed('a', hole) === true, '"a" should be detected in hole type');
});

test('works with type holes themselves', () => {
  // ?type_a : Type
  const typeHole = mkHole('type_a', mkType(1), []);

  // The hole ID is 'type_a', but we're checking for constant usage
  assert(isNameUsed('type_a', typeHole) === false, 'hole ID is not a constant');
  assert(isNameUsed('Type', typeHole) === false, 'Type is a Sort, not a constant');
});

// ============================================================================
// Edge Cases Tests
// ============================================================================

test('handles Sort terms', () => {
  const term = mkType(1);
  assert(isNameUsed('a', term) === false, 'Sort has no names');
  assert(isNameUsed('Type', term) === false, 'Sort has no names');
});

test('case sensitivity', () => {
  const term = mkConst('ABC', TT_CONSTANTS.Real);
  assert(isNameUsed('ABC', term) === true, 'exact match');
  assert(isNameUsed('abc', term) === false, 'different case');
  assert(isNameUsed('Abc', term) === false, 'different case');
});

console.log('\n✅ All deletion safety tests passed!');

