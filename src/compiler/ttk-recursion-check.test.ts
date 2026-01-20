/**
 * Tests for TTK Structural Recursion Analysis
 */

import { analyzeRecursionTTK } from './ttk-recursion-check';
import { TTKTerm, TTKPattern, mkConst, mkApp, mkVar, mkType, mkLambda, mkHole } from './kernel';

function test(description: string, fn: () => void): void {
  try {
    fn();
    console.log(`✓ ${description}`);
  } catch (error) {
    console.error(`✗ ${description}`);
    throw error;
  }
}

function assertEqual(actual: number, expected: number, message?: string): void {
  if (actual !== expected) {
    throw new Error(message || `Expected ${expected}, got ${actual}`);
  }
}

function assertTrue(value: boolean, message?: string): void {
  if (!value) {
    throw new Error(message || 'Assertion failed');
  }
}

// ============================================================================
// Test Helpers
// ============================================================================

const Type0 = mkType(0);
const Nat = mkConst('Nat');

function makeSuccPattern(): TTKPattern {
  return { tag: 'PCtor', name: 'Succ', args: [{ tag: 'PVar', name: 'n' }] };
}

function makeZeroPattern(): TTKPattern {
  return { tag: 'PCtor', name: 'Zero', args: [] };
}

function makeVarPattern(name: string): TTKPattern {
  return { tag: 'PVar', name };
}

function makeMatch(scrutinee: TTKTerm, clauses: { patterns: TTKPattern[]; rhs: TTKTerm }[]): TTKTerm {
  return { tag: 'Match', scrutinee, clauses };
}

// ============================================================================
// Tests
// ============================================================================

console.log('=== TTK Structural Recursion Analysis Tests ===\n');

test('Detects unsafe recursion outside pattern match', () => {
  // plus (Succ a) b - no pattern match context
  const succApp = mkApp(mkConst('Succ'), mkVar(0));
  const plusApp = mkApp(mkApp(mkConst('plus'), succApp), mkVar(1));

  const analysis = analyzeRecursionTTK('plus', plusApp);
  assertEqual(analysis.unsafeRecursion.length, 1, 'Should detect 1 unsafe call');
  assertTrue(
    analysis.unsafeRecursion[0].error.includes('outside of pattern') ||
    analysis.unsafeRecursion[0].error.includes('does not decrease structurally'),
    `Error should mention issue: ${analysis.unsafeRecursion[0].error}`
  );
});

test('Detects safe recursion inside pattern match', () => {
  // match x with | Succ n => plus n y
  // 'n' is at index 0 (pattern-bound), 'y' is at index 1
  const plusCall = mkApp(mkApp(mkConst('plus'), mkVar(0)), mkVar(1));

  const matchTerm = makeMatch(mkVar(2), [
    { patterns: [makeSuccPattern()], rhs: plusCall }
  ]);

  const analysis = analyzeRecursionTTK('plus', matchTerm);
  assertEqual(analysis.safeRecursion.length, 1, 'Should detect 1 safe call');
  assertEqual(analysis.unsafeRecursion.length, 0, 'Should have no unsafe calls');
});

test('Detects unsafe recursion with complex expression inside pattern match', () => {
  // match x with | Succ n => plus (Succ n) y
  // (Succ n) is not structurally smaller - it's equal to the original!
  const succN = mkApp(mkConst('Succ'), mkVar(0));
  const plusCall = mkApp(mkApp(mkConst('plus'), succN), mkVar(1));

  const matchTerm = makeMatch(mkVar(2), [
    { patterns: [makeSuccPattern()], rhs: plusCall }
  ]);

  const analysis = analyzeRecursionTTK('plus', matchTerm);
  assertEqual(analysis.safeRecursion.length, 0, 'Should have no safe calls');
  assertEqual(analysis.unsafeRecursion.length, 1, 'Should detect 1 unsafe call');
  assertTrue(
    analysis.unsafeRecursion[0].error.includes('does not decrease structurally') ||
    analysis.unsafeRecursion[0].error.includes('not structurally smaller'),
    `Error should mention structural decrease: ${analysis.unsafeRecursion[0].error}`
  );
});

test('Non-recursive function has no recursion', () => {
  // match x with | Succ n => n | Zero => Zero
  const matchTerm = makeMatch(mkVar(0), [
    { patterns: [makeSuccPattern()], rhs: mkVar(0) },
    { patterns: [makeZeroPattern()], rhs: mkConst('Zero') }
  ]);

  const analysis = analyzeRecursionTTK('isZero', matchTerm);
  assertEqual(analysis.safeRecursion.length, 0, 'Should have no safe calls');
  assertEqual(analysis.unsafeRecursion.length, 0, 'Should have no unsafe calls');
});

test('Detects safe recursion with Hole scrutinee (top-level pattern match)', () => {
  // This simulates a function definition like:
  // plus Zero b = b
  // plus (Succ a) b = Succ (plus a b)
  // The scrutinee is a Hole because it represents the function arguments
  const plusCall = mkApp(mkApp(mkConst('plus'), mkVar(1)), mkVar(0));
  const succPlusCall = mkApp(mkConst('Succ'), plusCall);

  const matchTerm = makeMatch(mkHole('_scrutinee'), [
    { patterns: [makeZeroPattern(), makeVarPattern('b')], rhs: mkVar(0) },
    { patterns: [makeSuccPattern(), makeVarPattern('b')], rhs: succPlusCall }
  ]);

  const analysis = analyzeRecursionTTK('plus', matchTerm);
  assertEqual(analysis.safeRecursion.length, 1, 'Should detect 1 safe call');
  assertEqual(analysis.unsafeRecursion.length, 0, 'Should have no unsafe calls');
});

test('Detects unsafe recursion with non-decreasing argument', () => {
  // bad (Succ n) = bad (Succ (Succ n))
  // Recursive call with a LARGER argument
  const succSuccN = mkApp(mkConst('Succ'), mkApp(mkConst('Succ'), mkVar(0)));
  const badCall = mkApp(mkConst('bad'), succSuccN);

  const matchTerm = makeMatch(mkHole('_scrutinee'), [
    { patterns: [makeZeroPattern()], rhs: mkConst('Zero') },
    { patterns: [makeSuccPattern()], rhs: badCall }
  ]);

  const analysis = analyzeRecursionTTK('bad', matchTerm);
  assertEqual(analysis.safeRecursion.length, 0, 'Should have no safe calls');
  assertEqual(analysis.unsafeRecursion.length, 1, 'Should detect 1 unsafe call');
});

test('Multiple recursive calls - one safe, one unsafe', () => {
  // f (Succ n) = g (f n) (f (Succ n))
  // First call (f n) is safe, second call (f (Succ n)) is unsafe
  const fN = mkApp(mkConst('f'), mkVar(0));
  const succN = mkApp(mkConst('Succ'), mkVar(0));
  const fSuccN = mkApp(mkConst('f'), succN);
  const gCall = mkApp(mkApp(mkConst('g'), fN), fSuccN);

  const matchTerm = makeMatch(mkHole('_scrutinee'), [
    { patterns: [makeZeroPattern()], rhs: mkConst('Zero') },
    { patterns: [makeSuccPattern()], rhs: gCall }
  ]);

  const analysis = analyzeRecursionTTK('f', matchTerm);
  assertEqual(analysis.safeRecursion.length, 1, 'Should detect 1 safe call');
  assertEqual(analysis.unsafeRecursion.length, 1, 'Should detect 1 unsafe call');
});

test('Detects unsafe unapplied self-reference', () => {
  // f = f (directly referencing f without applying it)
  const directRef = mkConst('f');

  const analysis = analyzeRecursionTTK('f', directRef);
  assertEqual(analysis.unsafeRecursion.length, 1, 'Should detect 1 unsafe reference');
  assertTrue(
    analysis.unsafeRecursion[0].error.includes('without application'),
    `Error should mention unapplied reference: ${analysis.unsafeRecursion[0].error}`
  );
});

test('Safe recursion with nested pattern', () => {
  // f (Succ (Succ n)) = f n
  // n is doubly nested, still structurally smaller
  const nestedSuccPattern: TTKPattern = {
    tag: 'PCtor',
    name: 'Succ',
    args: [{ tag: 'PCtor', name: 'Succ', args: [{ tag: 'PVar', name: 'n' }] }]
  };

  const fN = mkApp(mkConst('f'), mkVar(0));

  const matchTerm = makeMatch(mkHole('_scrutinee'), [
    { patterns: [makeZeroPattern()], rhs: mkConst('Zero') },
    { patterns: [nestedSuccPattern], rhs: fN }
  ]);

  const analysis = analyzeRecursionTTK('f', matchTerm);
  assertEqual(analysis.safeRecursion.length, 1, 'Should detect 1 safe call');
  assertEqual(analysis.unsafeRecursion.length, 0, 'Should have no unsafe calls');
});

test('Two-argument function with recursion on first arg', () => {
  // plus (Succ a) b = Succ (plus a b)
  // Patterns: [Succ a, b] - 'a' is at index 1, 'b' is at index 0
  const plusCall = mkApp(mkApp(mkConst('plus'), mkVar(1)), mkVar(0));
  const succPlusCall = mkApp(mkConst('Succ'), plusCall);

  const matchTerm = makeMatch(mkHole('_scrutinee'), [
    { patterns: [makeZeroPattern(), makeVarPattern('b')], rhs: mkVar(0) },
    { patterns: [makeSuccPattern(), makeVarPattern('b')], rhs: succPlusCall }
  ]);

  const analysis = analyzeRecursionTTK('plus', matchTerm);
  assertEqual(analysis.safeRecursion.length, 1, 'Should detect 1 safe call');
  assertEqual(analysis.unsafeRecursion.length, 0, 'Should have no unsafe calls');
});

test('Recursion under lambda with pattern match', () => {
  // λx. match x with | Succ n => plus n y
  const plusCall = mkApp(mkApp(mkConst('plus'), mkVar(0)), mkVar(2));
  const matchTerm = makeMatch(mkVar(1), [
    { patterns: [makeSuccPattern()], rhs: plusCall }
  ]);
  const lambdaTerm = mkLambda(Nat, matchTerm, 'x');

  const analysis = analyzeRecursionTTK('plus', lambdaTerm);
  // The recursive call should be detected
  assertTrue(
    analysis.safeRecursion.length + analysis.unsafeRecursion.length >= 1,
    'Should detect the recursive call'
  );
});

console.log('\n✅ All TTK recursion tests passed!');
