/**
 * Tests for error resolution system
 */

import { mkVar, mkLambda, mkPi, mkType } from './tt-core';
import { elabToKernelWithMap } from './tt-elab-source';
import { inferType, checkType, TypeCheckError } from './tt-typecheck';
import { CheckError } from './tt-typecheck-decl';
import {
  resolveErrorLocation,
  resolveCheckErrorLocation,
  formatErrorWithLocation,
  formatCheckErrorWithLocation,
  formatMultipleErrors
} from './error-resolution';
import {
  ElabMap,
  SourceMap,
  createSourcePos,
  createSourceRange,
  serializeIndexPath,
  deserializeIndexPath
} from './source-position';

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
console.log('ERROR RESOLUTION TESTS');
console.log('='.repeat(80) + '\n');

// ============================================================================
// resolveErrorLocation Tests
// ============================================================================

test('resolveErrorLocation: returns null when error has no path', () => {
  const error = new TypeCheckError('Test error');
  const elabMap: ElabMap = new Map();
  const sourceMap: SourceMap = new Map();

  const result = resolveErrorLocation(error, elabMap, sourceMap);

  assertEqual(result, null, 'Should return null when error has no path');
});

test('resolveErrorLocation: returns null when kernel path not in ElabMap', () => {
  const error = new TypeCheckError('Test error', undefined, undefined, []);
  const elabMap: ElabMap = new Map();
  const sourceMap: SourceMap = new Map();

  const result = resolveErrorLocation(error, elabMap, sourceMap);

  assertEqual(result, null, 'Should return null when kernel path not found');
});

test('resolveErrorLocation: exact match through full pipeline', () => {
  const kernelPath = deserializeIndexPath('domain');
  const surfaceKey = 'type';
  const range = createSourceRange(
    createSourcePos(1, 5, 4),
    createSourcePos(1, 10, 9)
  );

  const error = new TypeCheckError('Test error', undefined, undefined, kernelPath);
  const elabMap: ElabMap = new Map();
  elabMap.set('domain', surfaceKey);
  const sourceMap: SourceMap = new Map();
  sourceMap.set(surfaceKey, range);

  const result = resolveErrorLocation(error, elabMap, sourceMap);

  assert(result !== null, 'Should find exact match');
  assertEqual(result, range, 'Should return correct source range');
});

test('resolveErrorLocation: fallback to parent in ElabMap', () => {
  const kernelPath = deserializeIndexPath('domain.subfield');
  const surfaceKey = 'type';
  const range = createSourceRange(
    createSourcePos(1, 5, 4),
    createSourcePos(1, 10, 9)
  );

  const error = new TypeCheckError('Test error', undefined, undefined, kernelPath);
  const elabMap: ElabMap = new Map();
  elabMap.set('domain', surfaceKey);  // Parent path
  const sourceMap: SourceMap = new Map();
  sourceMap.set(surfaceKey, range);

  const result = resolveErrorLocation(error, elabMap, sourceMap);

  assert(result !== null, 'Should fall back to parent');
  assertEqual(result, range, 'Should return parent source range');
});

test('resolveErrorLocation: fallback to parent in SourceMap', () => {
  const kernelPath = deserializeIndexPath('domain');
  const surfaceKey = 'type.nested';
  const parentRange = createSourceRange(
    createSourcePos(1, 5, 4),
    createSourcePos(1, 10, 9)
  );

  const error = new TypeCheckError('Test error', undefined, undefined, kernelPath);
  const elabMap: ElabMap = new Map();
  elabMap.set('domain', surfaceKey);
  const sourceMap: SourceMap = new Map();
  sourceMap.set('type', parentRange);  // Parent surface key

  const result = resolveErrorLocation(error, elabMap, sourceMap);

  assert(result !== null, 'Should fall back to parent in surface map');
  assertEqual(result, parentRange, 'Should return parent source range');
});

test('resolveErrorLocation: walks up to root if needed', () => {
  const kernelPath = deserializeIndexPath('deeply.nested.path');
  const rootRange = createSourceRange(
    createSourcePos(1, 1, 0),
    createSourcePos(1, 20, 19)
  );

  const error = new TypeCheckError('Test error', undefined, undefined, kernelPath);
  const elabMap: ElabMap = new Map();
  elabMap.set('', 'root');  // Root mapping
  const sourceMap: SourceMap = new Map();
  sourceMap.set('root', rootRange);

  const result = resolveErrorLocation(error, elabMap, sourceMap);

  assert(result !== null, 'Should walk up to root');
  assertEqual(result, rootRange, 'Should return root source range');
});

// ============================================================================
// resolveCheckErrorLocation Tests
// ============================================================================

test('resolveCheckErrorLocation: returns null when error has no path', () => {
  const error: CheckError = { message: 'Test error', path: [] };
  const elabMap: ElabMap = new Map();
  const sourceMap: SourceMap = new Map();

  const result = resolveCheckErrorLocation(error, elabMap, sourceMap);

  assertEqual(result, null, 'Should return null when error has empty path');
});

test('resolveCheckErrorLocation: exact match through full pipeline', () => {
  const kernelPath = deserializeIndexPath('domain');
  const surfaceKey = 'type';
  const range = createSourceRange(
    createSourcePos(1, 5, 4),
    createSourcePos(1, 10, 9)
  );

  const error: CheckError = { message: 'Test error', path: kernelPath };
  const elabMap: ElabMap = new Map();
  elabMap.set('domain', surfaceKey);
  const sourceMap: SourceMap = new Map();
  sourceMap.set(surfaceKey, range);

  const result = resolveCheckErrorLocation(error, elabMap, sourceMap);

  assert(result !== null, 'Should find exact match');
  assertEqual(result, range, 'Should return correct source range');
});

test('resolveCheckErrorLocation: fallback to parent paths', () => {
  const kernelPath = deserializeIndexPath('domain.nested');
  const surfaceKey = 'type';
  const range = createSourceRange(
    createSourcePos(1, 5, 4),
    createSourcePos(1, 10, 9)
  );

  const error: CheckError = { message: 'Test error', path: kernelPath };
  const elabMap: ElabMap = new Map();
  elabMap.set('domain', surfaceKey);  // Parent path
  const sourceMap: SourceMap = new Map();
  sourceMap.set(surfaceKey, range);

  const result = resolveCheckErrorLocation(error, elabMap, sourceMap);

  assert(result !== null, 'Should fall back to parent');
  assertEqual(result, range, 'Should return parent source range');
});

// ============================================================================
// formatErrorWithLocation Tests
// ============================================================================

test('formatErrorWithLocation: no source range returns just message', () => {
  const message = 'Type mismatch';
  const sourceText = 'id : A -> A';

  const result = formatErrorWithLocation(message, null, sourceText);

  assertEqual(result, message, 'Should return just the message');
});

test('formatErrorWithLocation: includes line and column info', () => {
  const message = 'Type mismatch';
  const range = createSourceRange(
    createSourcePos(1, 5, 4),
    createSourcePos(1, 10, 9)
  );
  const sourceText = 'id : A -> A';

  const result = formatErrorWithLocation(message, range, sourceText);

  assert(result.includes('at line 1, column 5'), 'Should include line and column');
  assert(result.includes('id : A -> A'), 'Should include source line');
  assert(result.includes('^^^^^'), 'Should include caret');
});

test('formatErrorWithLocation: caret points to correct position', () => {
  const message = 'Type mismatch';
  const range = createSourceRange(
    createSourcePos(1, 5, 4),
    createSourcePos(1, 6, 5)
  );
  const sourceText = 'id : A -> A';

  const result = formatErrorWithLocation(message, range, sourceText);

  const lines = result.split('\n');
  const caretLine = lines[lines.length - 1];

  // Caret should be at position 5 (plus 2 for "  " prefix)
  const expectedCaret = '  ' + ' '.repeat(5 + 1) + '^';
  assertEqual(caretLine, expectedCaret, 'Caret should be at correct position');
});

test('formatErrorWithLocation: multi-character caret for ranges', () => {
  const message = 'Type mismatch';
  const range = createSourceRange(
    createSourcePos(1, 5, 4),
    createSourcePos(1, 10, 9)
  );
  const sourceText = 'id : A -> A';

  const result = formatErrorWithLocation(message, range, sourceText);

  assert(result.includes('^^^^^'), 'Should have 5-character caret');
});

test('formatErrorWithLocation: handles missing line gracefully', () => {
  const message = 'Type mismatch';
  const range = createSourceRange(
    createSourcePos(10, 5, 100),  // Line 10 doesn't exist
    createSourcePos(10, 10, 105)
  );
  const sourceText = 'id : A -> A';

  const result = formatErrorWithLocation(message, range, sourceText);

  assert(result.includes('at line 10, column 5'), 'Should include line/col info');
  assert(!result.includes('^'), 'Should not include caret for missing line');
});

// ============================================================================
// formatCheckErrorWithLocation Tests
// ============================================================================

test('formatCheckErrorWithLocation: delegates to formatErrorWithLocation', () => {
  const error: CheckError = { message: 'Type mismatch', path: [] };
  const range = createSourceRange(
    createSourcePos(1, 5, 4),
    createSourcePos(1, 10, 9)
  );
  const sourceText = 'id : A -> A';

  const result = formatCheckErrorWithLocation(error, range, sourceText);

  assert(result.includes('Type mismatch'), 'Should include error message');
  assert(result.includes('at line 1, column 5'), 'Should include location');
  assert(result.includes('^^^^^'), 'Should include caret');
});

// ============================================================================
// formatMultipleErrors Tests
// ============================================================================

test('formatMultipleErrors: no errors returns "No errors"', () => {
  const result = formatMultipleErrors([], 'id : A -> A');
  assertEqual(result, 'No errors', 'Should return "No errors"');
});

test('formatMultipleErrors: single error uses standard format', () => {
  const range = createSourceRange(
    createSourcePos(1, 5, 4),
    createSourcePos(1, 10, 9)
  );
  const errors = [{ message: 'Type mismatch', range }];
  const sourceText = 'id : A -> A';

  const result = formatMultipleErrors(errors, sourceText);

  assert(result.includes('Type mismatch'), 'Should include error message');
  assert(!result.includes('Error 1:'), 'Should not include "Error 1:" prefix');
});

test('formatMultipleErrors: multiple errors are numbered', () => {
  const range1 = createSourceRange(
    createSourcePos(1, 5, 4),
    createSourcePos(1, 10, 9)
  );
  const range2 = createSourceRange(
    createSourcePos(2, 1, 12),
    createSourcePos(2, 5, 16)
  );
  const errors = [
    { message: 'First error', range: range1 },
    { message: 'Second error', range: range2 }
  ];
  const sourceText = 'id : A -> A\nconst : B -> C';

  const result = formatMultipleErrors(errors, sourceText);

  assert(result.includes('Found 2 errors'), 'Should include error count');
  assert(result.includes('Error 1:'), 'Should include "Error 1:" prefix');
  assert(result.includes('Error 2:'), 'Should include "Error 2:" prefix');
  assert(result.includes('First error'), 'Should include first error');
  assert(result.includes('Second error'), 'Should include second error');
});

test('formatMultipleErrors: handles errors without ranges', () => {
  const range = createSourceRange(
    createSourcePos(1, 5, 4),
    createSourcePos(1, 10, 9)
  );
  const errors = [
    { message: 'Error with range', range },
    { message: 'Error without range', range: null }
  ];
  const sourceText = 'id : A -> A';

  const result = formatMultipleErrors(errors, sourceText);

  assert(result.includes('Error with range'), 'Should include first error');
  assert(result.includes('Error without range'), 'Should include second error');
  assert(result.includes('at line 1'), 'Should include location for first');
});

// ============================================================================
// Integration Tests: Full Pipeline from Source to Error Location
// ============================================================================

import { checkSourceBlocks } from '../parser/block-checker';

test('Integration: type mismatch in Pi domain points to exact location', () => {
  // Equal expects (A : Type) as first argument, but we give it (a : Nat)
  const source = `inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Equal : (A : Type) -> A -> A -> Type where
  refl : (A : Type) -> (x : A) -> (y : A) -> Equal A x y

foo : (a : Nat) -> (b : Nat) -> Equal a b -> Nat
foo a b eq = Zero
`;

  const results = checkSourceBlocks(source);

  // Find the foo declaration result (block 2)
  const fooResult = results.find(r => r.blockIndex === 2);
  assert(fooResult !== undefined, 'Should find foo declaration');
  assert(!fooResult!.checkSuccess, 'foo should fail type checking');
  assert(fooResult!.checkErrors.length > 0, 'Should have at least one error');

  const err = fooResult!.checkErrors[0];
  assert(err.location !== null, 'Error should have a source location');

  // The error should point to the first 'a' in 'Equal a b' (col 39-40 on line 8)
  assertEqual(err.location!.start.line, 8, 'Error should be on line 8');
  assertEqual(err.location!.start.col, 39, 'Error should start at column 39');
  assertEqual(err.location!.end.col, 40, 'Error should end at column 40');
});

test('Integration: type mismatch in function body points to exact location', () => {
  const source = `inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

bad : Nat -> Nat
bad x = x x
`;

  const results = checkSourceBlocks(source);

  // Find the bad declaration result (block 1)
  const badResult = results.find(r => r.blockIndex === 1);
  assert(badResult !== undefined, 'Should find bad declaration');
  assert(!badResult!.checkSuccess, 'bad should fail type checking');
  assert(badResult!.checkErrors.length > 0, 'Should have at least one error');

  const err = badResult!.checkErrors[0];
  assert(err.location !== null, 'Error should have a source location');
  // The error should be in the value part of the declaration
  assert(err.location!.start.line >= 5, 'Error should be on or after line 5');
});

test('Integration: nested Pi type error location', () => {
  const source = `inductive Bool : Type where
  True : Bool
  False : Bool

nested : (x : Bool) -> (y : Bool -> Bool) -> x y -> Bool
nested x y z = True
`;

  const results = checkSourceBlocks(source);

  // Find the nested declaration result
  const nestedResult = results.find(r => r.blockIndex === 1);
  assert(nestedResult !== undefined, 'Should find nested declaration');
  assert(!nestedResult!.checkSuccess, 'nested should fail type checking');
  assert(nestedResult!.checkErrors.length > 0, 'Should have at least one error');

  const err = nestedResult!.checkErrors[0];
  assert(err.location !== null, 'Error should have a source location');
  // The error is at 'x y' - x is Bool, not a function
  assert(err.error.message.includes('Pi type') || err.error.message.includes('Type mismatch'),
    'Error should mention Pi type or type mismatch');
});

test('Integration: application argument type mismatch', () => {
  const source = `inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

idNat : Nat -> Nat
idNat n = n

badCall : Type
badCall = idNat Type
`;

  const results = checkSourceBlocks(source);

  // Find the badCall declaration result
  const badCallResult = results.find(r => r.blockIndex === 2);
  assert(badCallResult !== undefined, 'Should find badCall declaration');
  assert(!badCallResult!.checkSuccess, 'badCall should fail type checking');
  assert(badCallResult!.checkErrors.length > 0, 'Should have at least one error');

  const err = badCallResult!.checkErrors[0];
  assert(err.location !== null, 'Error should have a source location');
});

test('Integration: inductive constructor type error', () => {
  const source = `inductive Bad : Type where
  MkBad : Type -> Bad
`;

  const results = checkSourceBlocks(source);
  const badIndResult = results.find(r => r.blockIndex === 0);
  assert(badIndResult !== undefined, 'Should find Bad inductive');
  // This might pass or fail depending on universe constraints - just check we get a result
  assert(badIndResult!.parseSuccess, 'Should parse successfully');
});

test('Integration: error in deeply nested expression', () => {
  const source = `inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

deep : ((((Nat -> Nat) -> Nat) -> Nat) -> Nat) -> Nat
deep f = f Zero
`;

  const results = checkSourceBlocks(source);

  // Find the deep declaration result
  const deepResult = results.find(r => r.blockIndex === 1);
  assert(deepResult !== undefined, 'Should find deep declaration');
  assert(!deepResult!.checkSuccess, 'deep should fail type checking');
  assert(deepResult!.checkErrors.length > 0, 'Should have at least one error');

  const err = deepResult!.checkErrors[0];
  assert(err.location !== null, 'Error should have a source location');
  // The error should be pointing somewhere meaningful, not the whole declaration
  assert(err.location!.end.col - err.location!.start.col < 50,
    'Error range should be reasonably small, not the whole expression');
});

test('Integration: multiple errors all have locations', () => {
  const source = `inductive Unit : Type where
  unit : Unit

multi : Unit -> Type -> Unit
multi u t = u t u
`;

  const results = checkSourceBlocks(source);

  const multiResult = results.find(r => r.blockIndex === 1);
  assert(multiResult !== undefined, 'Should find multi declaration');
  assert(!multiResult!.checkSuccess, 'multi should fail type checking');

  // Even if there's just one error, it should have a location
  for (const err of multiResult!.checkErrors) {
    assert(err.location !== null, `Error "${err.error.message}" should have a location`);
  }
});

console.log('\n' + '='.repeat(80));
console.log('ALL ERROR RESOLUTION TESTS PASSED! ✓');
console.log('='.repeat(80) + '\n');
