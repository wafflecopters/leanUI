/**
 * Tests for Structural Recursion Analysis
 *
 * Tests the detection of safe (structurally recursive) and unsafe recursive calls
 * in term definitions.
 */

import { analyzeRecursion } from './tt-recursion-check';
import { TTerm, mkConst, mkApp, mkVar, mkType, mkPi, mkLambda, TPattern, TClause } from './tt-core';

// ============================================================================
// Test Helpers
// ============================================================================

/**
 * Run a test with description
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

/**
 * Assert that two numbers are equal
 */
function assertEqual(actual: number, expected: number, message?: string): void {
  if (actual !== expected) {
    const msg = message || `Expected ${expected}, got ${actual}`;
    throw new Error(msg);
  }
}

/**
 * Assert that a value is true
 */
function assertTrue(value: boolean, message?: string): void {
  if (!value) {
    throw new Error(message || 'Assertion failed');
  }
}

// ============================================================================
// Test Case Builders
// ============================================================================

const Type0 = mkType(0);
const Nat = mkConst('Nat', Type0);

/**
 * Build a simple recursive call: f x
 */
function makeSimpleRecursiveCall(fnName: string, argIndex: number): TTerm {
  return mkApp(mkConst(fnName, Type0), mkVar(argIndex));
}

/**
 * Build a nested application: f x y
 */
function makeNestedApp(fnName: string, arg1Index: number, arg2Index: number): TTerm {
  const fn = mkConst(fnName, Type0);
  const app1 = mkApp(fn, mkVar(arg1Index));
  return mkApp(app1, mkVar(arg2Index));
}

/**
 * Build a constructor pattern: Succ n
 */
function makeSuccPattern(): TPattern {
  return {
    tag: 'PCtor',
    name: 'Succ',
    args: [{ tag: 'PVar', name: 'n' }],
  };
}

/**
 * Build a zero pattern: Zero
 */
function makeZeroPattern(): TPattern {
  return {
    tag: 'PCtor',
    name: 'Zero',
    args: [],
  };
}

/**
 * Build a variable pattern: x
 */
function makeVarPattern(name: string): TPattern {
  return {
    tag: 'PVar',
    name,
  };
}

/**
 * Build a match expression
 */
function makeMatch(scrutinee: TTerm, clauses: TClause[]): TTerm {
  return {
    tag: 'Match',
    scrutinee,
    clauses,
  };
}

// ============================================================================
// Tests: Safe Structural Recursion
// ============================================================================

function runSafeRecursionTests(): void {
  console.log('=== Safe Structural Recursion ===');

  test('Detects safe recursion in pattern match', () => {
    // Simple case: match n with | Succ a => f a
    // where 'a' is pattern-bound, so recursion on 'a' is safe
    const recursiveCall = makeSimpleRecursiveCall('f', 0); // f a (a is at index 0)

    const clause: TClause = {
      patterns: [makeSuccPattern()], // Binds 'n' as variable
      rhs: recursiveCall,
    };

    const matchTerm = makeMatch(mkVar(0), [clause]);
    const analysis = analyzeRecursion('f', matchTerm);

    assertEqual(analysis.safeRecursion.length, 1, 'Should detect 1 safe recursive call');
    assertEqual(analysis.unsafeRecursion.length, 0, 'Should have no unsafe calls');
  });

  test('Multiple safe recursive calls', () => {
    // match n with | Succ a => plus (f a) (f a)
    const recursiveCall1 = makeSimpleRecursiveCall('f', 0);
    const recursiveCall2 = makeSimpleRecursiveCall('f', 0);

    const plusApp = mkApp(
      mkApp(mkConst('plus', Type0), recursiveCall1),
      recursiveCall2
    );

    const clause: TClause = {
      patterns: [makeSuccPattern()],
      rhs: plusApp,
    };

    const matchTerm = makeMatch(mkVar(0), [clause]);
    const analysis = analyzeRecursion('f', matchTerm);

    assertEqual(analysis.safeRecursion.length, 2, 'Should detect 2 safe recursive calls');
    assertEqual(analysis.unsafeRecursion.length, 0, 'Should have no unsafe calls');
  });

  test('Safe recursion with multiple arguments', () => {
    // plus : Nat → Nat → Nat
    // match a with | Succ n => plus n b
    // Both 'n' (pattern-bound) and 'b' are used
    const recursiveCall = makeNestedApp('plus', 0, 1); // plus n b

    const clause: TClause = {
      patterns: [makeSuccPattern()], // Binds n at index 0, b already at index 1
      rhs: recursiveCall,
    };

    const matchTerm = makeMatch(mkVar(1), [clause]); // Match on b (which is at index 1)
    const analysis = analyzeRecursion('plus', matchTerm);

    assertEqual(analysis.safeRecursion.length, 1, 'Should detect 1 safe recursive call');
    assertEqual(analysis.unsafeRecursion.length, 0, 'Should have no unsafe calls');
  });

  test('Safe recursion in nested match', () => {
    // Nested pattern matching
    const recursiveCall = makeSimpleRecursiveCall('f', 0);

    const innerClause: TClause = {
      patterns: [makeSuccPattern()],
      rhs: recursiveCall,
    };

    const innerMatch = makeMatch(mkVar(0), [innerClause]);

    const outerClause: TClause = {
      patterns: [makeSuccPattern()],
      rhs: innerMatch,
    };

    const outerMatch = makeMatch(mkVar(0), [outerClause]);
    const analysis = analyzeRecursion('f', outerMatch);

    assertEqual(analysis.safeRecursion.length, 1, 'Should detect 1 safe recursive call');
    assertEqual(analysis.unsafeRecursion.length, 0, 'Should have no unsafe calls');
  });
}

// ============================================================================
// Tests: Unsafe Recursion
// ============================================================================

function runUnsafeRecursionTests(): void {
  console.log('\n=== Unsafe Recursion ===');

  test('Detects recursion on same variable (infinite loop)', () => {
    // match n with | _ => f n
    // Recursing on 'n' (the scrutinee) is unsafe
    const recursiveCall = makeSimpleRecursiveCall('f', 1); // n is at index 1 (not pattern-bound)

    const clause: TClause = {
      patterns: [makeVarPattern('m')], // Binds m at index 0, but we use n at index 1
      rhs: recursiveCall,
    };

    const matchTerm = makeMatch(mkVar(0), [clause]);
    const analysis = analyzeRecursion('f', matchTerm);

    assertEqual(analysis.safeRecursion.length, 0, 'Should have no safe calls');
    assertEqual(analysis.unsafeRecursion.length, 1, 'Should detect 1 unsafe call');
    assertTrue(
      analysis.unsafeRecursion[0].error.includes('does not use pattern-matched'),
      'Error should mention non-pattern-matched variable'
    );
  });

  test('Detects recursion outside pattern match', () => {
    // Just: f x (not inside a match)
    const recursiveCall = makeSimpleRecursiveCall('f', 0);
    const analysis = analyzeRecursion('f', recursiveCall);

    assertEqual(analysis.safeRecursion.length, 0, 'Should have no safe calls');
    assertEqual(analysis.unsafeRecursion.length, 1, 'Should detect 1 unsafe call');
    assertTrue(
      analysis.unsafeRecursion[0].error.includes('outside of pattern matching'),
      'Error should mention missing pattern match context'
    );
  });

  test('Detects recursion on complex expression', () => {
    // match n with | Succ a => f (Succ a)
    // Recursing on (Succ a) instead of just a
    const succApp = mkApp(mkConst('Succ', Type0), mkVar(0));
    const recursiveCall = mkApp(mkConst('f', Type0), succApp);

    const clause: TClause = {
      patterns: [makeSuccPattern()],
      rhs: recursiveCall,
    };

    const matchTerm = makeMatch(mkVar(0), [clause]);
    const analysis = analyzeRecursion('f', matchTerm);

    assertEqual(analysis.safeRecursion.length, 0, 'Should have no safe calls');
    assertEqual(analysis.unsafeRecursion.length, 1, 'Should detect 1 unsafe call');
    assertTrue(
      analysis.unsafeRecursion[0].error.includes('complex expressions'),
      'Error should mention complex expression'
    );
  });

  test('Detects non-applied function reference', () => {
    // Just the constant 'f' without application
    const fnRef = mkConst('f', Type0);
    const analysis = analyzeRecursion('f', fnRef);

    assertEqual(analysis.safeRecursion.length, 0, 'Should have no safe calls');
    assertEqual(analysis.unsafeRecursion.length, 1, 'Should detect unsafe reference');
    assertTrue(
      analysis.unsafeRecursion[0].error.includes('Direct reference'),
      'Error should mention direct reference'
    );
  });

  test('Detects recursion with all complex arguments', () => {
    // match n with | Succ a => f (a + 1) (a * 2)
    const arg1 = mkApp(mkConst('add', Type0), mkVar(0));
    const arg2 = mkApp(mkConst('mul', Type0), mkVar(0));
    const recursiveCall = mkApp(
      mkApp(mkConst('f', Type0), arg1),
      arg2
    );

    const clause: TClause = {
      patterns: [makeSuccPattern()],
      rhs: recursiveCall,
    };

    const matchTerm = makeMatch(mkVar(0), [clause]);
    const analysis = analyzeRecursion('f', matchTerm);

    assertEqual(analysis.safeRecursion.length, 0, 'Should have no safe calls');
    assertEqual(analysis.unsafeRecursion.length, 1, 'Should detect 1 unsafe call');
    assertTrue(
      analysis.unsafeRecursion[0].error.includes('complex expressions'),
      'Error should mention complex expressions'
    );
  });
}

// ============================================================================
// Tests: Edge Cases
// ============================================================================

function runEdgeCaseTests(): void {
  console.log('\n=== Edge Cases ===');

  test('No recursion in term', () => {
    // match n with | Zero => 0 | Succ a => a
    // No recursive calls at all
    const clause1: TClause = {
      patterns: [makeZeroPattern()],
      rhs: mkConst('zero', Type0),
    };

    const clause2: TClause = {
      patterns: [makeSuccPattern()],
      rhs: mkVar(0),
    };

    const matchTerm = makeMatch(mkVar(0), [clause1, clause2]);
    const analysis = analyzeRecursion('f', matchTerm);

    assertEqual(analysis.safeRecursion.length, 0, 'Should have no recursive calls');
    assertEqual(analysis.unsafeRecursion.length, 0, 'Should have no unsafe calls');
  });

  test('Recursion in lambda body', () => {
    // λx. f x
    const recursiveCall = makeSimpleRecursiveCall('f', 0);
    const lambda = mkLambda(Nat, recursiveCall, 'x');
    const analysis = analyzeRecursion('f', lambda);

    // This is outside a pattern match, so it's unsafe
    assertEqual(analysis.safeRecursion.length, 0, 'Should have no safe calls');
    assertEqual(analysis.unsafeRecursion.length, 1, 'Should detect unsafe call in lambda');
  });

  test('Mixed safe and unsafe recursion', () => {
    // match n with
    // | Zero => f n        -- unsafe (n not pattern-bound in this branch)
    // | Succ a => f a      -- safe (a is pattern-bound)
    const clause1: TClause = {
      patterns: [makeZeroPattern()],
      rhs: makeSimpleRecursiveCall('f', 1), // n at index 1, not pattern-bound
    };

    const clause2: TClause = {
      patterns: [makeSuccPattern()],
      rhs: makeSimpleRecursiveCall('f', 0), // a at index 0, pattern-bound
    };

    const matchTerm = makeMatch(mkVar(0), [clause1, clause2]);
    const analysis = analyzeRecursion('f', matchTerm);

    assertEqual(analysis.safeRecursion.length, 1, 'Should detect 1 safe call');
    assertEqual(analysis.unsafeRecursion.length, 1, 'Should detect 1 unsafe call');
  });

  test('Empty match (no clauses)', () => {
    const matchTerm = makeMatch(mkVar(0), []);
    const analysis = analyzeRecursion('f', matchTerm);

    assertEqual(analysis.safeRecursion.length, 0, 'Should have no calls');
    assertEqual(analysis.unsafeRecursion.length, 0, 'Should have no calls');
  });

  test('Recursion in Pi type (unusual but possible)', () => {
    // (x : T) → f x
    // This is a type, not a term, but let's test it anyway
    const recursiveCall = makeSimpleRecursiveCall('f', 0);
    const piType = mkPi(Nat, recursiveCall, 'x');
    const analysis = analyzeRecursion('f', piType);

    // Recursion in a type is unusual and unsafe
    assertEqual(analysis.safeRecursion.length, 0, 'Should have no safe calls');
    assertEqual(analysis.unsafeRecursion.length, 1, 'Should detect unsafe call');
  });
}

// ============================================================================
// Run All Tests
// ============================================================================

function runTests(): void {
  console.log('Running Structural Recursion Analysis Tests...\n');

  runSafeRecursionTests();
  runUnsafeRecursionTests();
  runEdgeCaseTests();

  console.log('\n✅ All tests passed!');
}

// Run tests
runTests();
