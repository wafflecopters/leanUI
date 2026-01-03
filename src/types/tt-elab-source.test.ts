/**
 * Tests for elaboration with source position tracking
 */

import { mkVar, mkLambda, mkPi, mkType } from './tt-core';
import { elabToKernelWithMap, lookupSurfacePath } from './tt-elab-source';
import { deserializeIndexPath } from './source-position';

function test(description: string, fn: () => void): void {
  try {
    fn();
    console.log(`✓ ${description}`);
  } catch (error) {
    console.error(`✗ ${description}`);
    throw error;
  }
}

function assertEqual<T>(actual: T, expected: T, message?: string): void {
  const actualStr = JSON.stringify(actual);
  const expectedStr = JSON.stringify(expected);
  if (actualStr !== expectedStr) {
    throw new Error(`${message || 'Assertion failed'}\n  Expected: ${expectedStr}\n  Actual: ${actualStr}`);
  }
}

function assert(condition: boolean, message?: string): void {
  if (!condition) {
    throw new Error(message || 'Assertion failed');
  }
}

console.log('\n' + '='.repeat(80));
console.log('ELABORATION SOURCE TRACKING TESTS');
console.log('='.repeat(80) + '\n');

// ============================================================================
// Basic ElabMap Tests
// ============================================================================

test('elabToKernelWithMap creates ElabMap entry at root', () => {
  const term = mkVar(0);  // Simple variable
  const elabMap = new Map();

  elabToKernelWithMap(term, elabMap);

  // Should have at least the root entry
  assert(elabMap.has(''), 'Should have root path entry');
  assertEqual(elabMap.get(''), '', 'Root kernel path should map to root surface path');
});

test('elabToKernelWithMap produces valid kernel term', () => {
  const term = mkLambda(mkType(0), mkVar(0), 'x');
  const elabMap = new Map();

  const kernel = elabToKernelWithMap(term, elabMap);

  assert(kernel !== undefined, 'Should produce kernel term');
  assert(kernel.tag === 'Binder', 'Should be a Binder');
  if (kernel.tag === 'Binder') {
    assert(kernel.binderKind.tag === 'BLam', 'Should be a lambda binder');
  }
});

test('ElabMap is populated (even if shallow for now)', () => {
  const term = mkPi(mkType(0), mkVar(0), 'A');
  const elabMap = new Map();

  elabToKernelWithMap(term, elabMap);

  // At minimum, should have the root entry
  assert(elabMap.size >= 1, 'ElabMap should have at least one entry');
});

// ============================================================================
// lookupSurfacePath Tests
// ============================================================================

test('lookupSurfacePath finds exact match', () => {
  const elabMap = new Map();
  elabMap.set('domain', 'type');
  elabMap.set('body', 'value');

  const surfacePath = lookupSurfacePath(
    deserializeIndexPath('domain'),
    elabMap
  );

  assertEqual(surfacePath, 'type', 'Should find exact match');
});

test('lookupSurfacePath falls back to parent path', () => {
  const elabMap = new Map();
  elabMap.set('domain', 'type');
  // No entry for 'domain.subfield'

  const surfacePath = lookupSurfacePath(
    deserializeIndexPath('domain.subfield'),
    elabMap
  );

  assertEqual(surfacePath, 'type', 'Should fall back to parent path');
});

test('lookupSurfacePath returns undefined when not found', () => {
  const elabMap = new Map();
  elabMap.set('domain', 'type');

  const surfacePath = lookupSurfacePath(
    deserializeIndexPath('body'),
    elabMap
  );

  assertEqual(surfacePath, undefined, 'Should return undefined when not found');
});

test('lookupSurfacePath walks up to root if needed', () => {
  const elabMap = new Map();
  elabMap.set('', 'root');  // Only root entry

  const surfacePath = lookupSurfacePath(
    deserializeIndexPath('deeply.nested.path'),
    elabMap
  );

  assertEqual(surfacePath, 'root', 'Should fall back to root');
});

// ============================================================================
// Integration Tests
// ============================================================================

test('Elaborate and lookup round-trip', () => {
  const term = mkVar(0);
  const elabMap = new Map();

  elabToKernelWithMap(term, elabMap);

  // Look up the root path
  const surfacePath = lookupSurfacePath([], elabMap);
  assertEqual(surfacePath, '', 'Should map back to root surface path');
});

console.log('\n' + '='.repeat(80));
console.log('ALL ELABORATION SOURCE TRACKING TESTS PASSED! ✓');
console.log('='.repeat(80) + '\n');
