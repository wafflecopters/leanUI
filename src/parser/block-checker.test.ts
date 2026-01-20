/**
 * Tests for block-level type checking pipeline
 */

import { compileSource, summarizeResults } from '../test-utils';

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
console.log('BLOCK-LEVEL TYPE CHECKING TESTS');
console.log('='.repeat(80) + '\n');

// ============================================================================
// Basic Pipeline Tests
// ============================================================================

test('compileSource: empty source', () => {
  const results = compileSource('');
  assert(results.length === 0, 'Should return empty array for empty source');
});

test('compileSource: single well-formed definition', () => {
  const source = `id : Type -> Type
id x = x`;
  const results = compileSource(source);

  assert(results.length === 1, 'Should have 1 block');
  assert(results[0].parseSuccess === true, 'Parse should succeed');
  assert(results[0].checkSuccess === true, `Check should succeed. Errors: ${results[0].checkErrors.map(e => e.message).join(', ')}`);
  assert(results[0].blockType === 'Term', 'Should be a term');
  assert(results[0].name === 'id', 'Should have name "id"');
});

test('compileSource: well-formed inductive', () => {
  // Constructors must return the inductive type being defined, not Type!
  const source = `inductive Nat : Type where
  | Zero : Nat
  | Succ : Nat -> Nat`;

  const results = compileSource(source);

  assert(results.length === 1, 'Should have 1 block');
  assert(results[0].parseSuccess === true, 'Parse should succeed');
  assert(results[0].checkSuccess === true, `Check should succeed, got errors: ${results[0].checkErrors.map(e => e.message).join(', ')}`);
  assert(results[0].blockType === 'Inductive', 'Should be inductive');
  assert(results[0].name === 'Nat', 'Should have name "Nat"');
});

test('compileSource: comment block', () => {
  const source = `-- This is a comment
-- Another comment line`;

  const results = compileSource(source);

  assert(results.length === 1, 'Should have 1 block');
  assert(results[0].blockType === 'Comment', 'Should be a comment block');
  assert(results[0].parseSuccess === true, 'Comments are always parse success');
  assert(results[0].checkSuccess === true, 'Comments are always check success');
});

test('compileSource: multiple blocks', () => {
  const source = `id : Type -> Type
id x = x

const : Type -> Type -> Type
const x y = x`;

  const results = compileSource(source);

  assert(results.length === 2, 'Should have 2 blocks');
  assert(results[0].name === 'id', 'First block name');
  assert(results[1].name === 'const', 'Second block name');
  assert(results[0].checkSuccess === true, `First should succeed. Errors: ${results[0].checkErrors.map(e => e.message).join(', ')}`);
  assert(results[1].checkSuccess === true, `Second should succeed. Errors: ${results[1].checkErrors.map(e => e.message).join(', ')}`);
});

// ============================================================================
// Parse Error Tests
// ============================================================================

test('compileSource: parse error is captured', () => {
  const source = 'bad syntax @#$%';

  const results = compileSource(source);

  assert(results.length === 1, 'Should have 1 block');
  assert(results[0].parseSuccess === false, 'Parse should fail');
  assert(results[0].parseErrors.length > 0, 'Should have parse errors');
  assert(results[0].checkSuccess === false, 'Check should be marked as failed');
});

test('compileSource: parse error does not stop other blocks', () => {
  const source = `id : Type -> Type
id x = x

bad syntax @#$%

const : Type -> Type -> Type
const x y = x`;

  const results = compileSource(source);

  assert(results.length === 3, 'Should have 3 blocks');
  assert(results[0].parseSuccess === true, 'First block should parse');
  assert(results[1].parseSuccess === false, 'Second block should fail to parse');
  assert(results[2].parseSuccess === true, 'Third block should parse');
});

// ============================================================================
// Type Check Error Tests
// ============================================================================

test('compileSource: well-formed inductive (type checking passes)', () => {
  // NOTE: Testing actual type check FAILURES is difficult without being able to
  // construct ill-typed terms in the surface syntax. The parser rejects invalid
  // de Bruijn indices (#99), and most other malformed terms.
  //
  // For now, we test that well-formed inductives pass type checking.
  // The parallel error collection is tested in tt-typecheck-decl.test.ts directly.

  // Constructors must return the inductive type being defined, not Type!
  const source = `inductive Nat : Type where
  | Zero : Nat
  | Succ : Nat -> Nat`;

  const results = compileSource(source);

  assert(results.length === 1, 'Should have 1 block');
  assert(results[0].parseSuccess === true, 'Parse should succeed');
  assert(results[0].checkSuccess === true, `Check should succeed for well-formed inductive, got: ${results[0].checkErrors.map(e => e.message).join(', ')}`);
  assert(results[0].checkErrors.length === 0, 'Should have no errors');
});

// ============================================================================
// Mixed Success/Failure Tests
// ============================================================================

test('compileSource: mix of successes and parse errors', () => {
  const source = `-- Comment block

good1 : Type -> Type
good1 x = x

bad parse @#$%

good2 : Type -> Type -> Type
good2 x y = x

inductive Nat : Type where
  | Zero : Nat

good3 : Nat
good3 = Zero`;

  const results = compileSource(source);

  assert(results.length === 6, 'Should have 6 blocks');

  // Block 0: Comment
  assert(results[0].blockType === 'Comment', 'Block 0 is comment');
  assert(results[0].checkSuccess === true, 'Comments succeed');

  // Block 1: good1
  assert(results[1].name === 'good1', 'Block 1 name');
  assert(results[1].parseSuccess === true, 'Block 1 parse success');
  assert(results[1].checkSuccess === true, `Block 1 check success. Errors: ${results[1].checkErrors.map(e => e.message).join(', ')}`);

  // Block 2: parse error
  assert(results[2].parseSuccess === false, 'Block 2 parse fails');

  // Block 3: good2
  assert(results[3].name === 'good2', 'Block 3 name');
  assert(results[3].parseSuccess === true, 'Block 3 parse success');
  assert(results[3].checkSuccess === true, `Block 3 check success. Errors: ${results[3].checkErrors.map(e => e.message).join(', ')}`);

  // Block 4: good inductive
  assert(results[4].name === 'Nat', 'Block 4 name');
  assert(results[4].parseSuccess === true, 'Block 4 parse success');
  assert(results[4].checkSuccess === true, `Block 4 check success, got: ${results[4].checkErrors.map(e => e.message).join(', ')}`);

  // Block 5: good3
  assert(results[5].name === 'good3', 'Block 5 name');
  assert(results[5].parseSuccess === true, 'Block 5 parse success');
  assert(results[5].checkSuccess === true, `Block 5 check success. Errors: ${results[5].checkErrors.map(e => e.message).join(', ')}`);
});

// ============================================================================
// Error Location Tests
// ============================================================================

test('compileSource: parse errors include basic location info', () => {
  const source = `bad syntax @#$%`;

  const results = compileSource(source);

  assert(results.length === 1, 'Should have 1 block');
  assert(results[0].parseErrors.length > 0, 'Should have parse errors');

  // Parse errors should have line and column info
  const firstError = results[0].parseErrors[0];
  assert(firstError.message.length > 0, 'Error should have message');
  assert(firstError.line !== undefined, 'Error should have line');
  assert(firstError.col !== undefined, 'Error should have col');
});

// ============================================================================
// Summary Tests
// ============================================================================

test('summarizeResults: empty results', () => {
  const summary = summarizeResults([]);

  assert(summary.totalBlocks === 0, 'Total blocks');
  assert(summary.commentBlocks === 0, 'Comment blocks');
  assert(summary.successfulBlocks === 0, 'Successful blocks');
  assert(summary.parseErrorBlocks === 0, 'Parse error blocks');
  assert(summary.checkErrorBlocks === 0, 'Check error blocks');
  assert(summary.totalErrors === 0, 'Total errors');
});

test('summarizeResults: all successful', () => {
  const source = `id : Type -> Type
id x = x

const : Type -> Type -> Type
const x y = x`;

  const results = compileSource(source);
  const summary = summarizeResults(results);

  assert(summary.totalBlocks === 2, 'Total blocks');
  assert(summary.successfulBlocks === 2, `Successful blocks. Errors: ${results.flatMap(r => r.checkErrors.map(e => e.message)).join(', ')}`);
  assert(summary.parseErrorBlocks === 0, 'No parse errors');
  assert(summary.checkErrorBlocks === 0, 'No check errors');
  assert(summary.totalErrors === 0, 'No errors');
});

test('summarizeResults: mixed results with parse errors', () => {
  const source = `-- Comment

good : Type -> Type
good x = x

bad parse @#$%

good2 : Type -> Type
good2 x = x`;

  const results = compileSource(source);
  const summary = summarizeResults(results);

  assert(summary.totalBlocks === 4, 'Total blocks');
  assert(summary.commentBlocks === 1, 'Comment blocks');
  assert(summary.successfulBlocks === 3, `Successful blocks (comment + good + good2). Errors: ${results.flatMap(r => r.checkErrors.map(e => e.message)).join(', ')}`);
  assert(summary.parseErrorBlocks === 1, 'Parse error blocks');
  assert(summary.checkErrorBlocks === 0, 'No check error blocks');
  assert(summary.totalErrors >= 1, 'At least 1 parse error');
});

// ============================================================================
// Integration Tests
// ============================================================================

test('compileSource: real-world example', () => {
  // Note: Constructors must return the inductive type, not Type!
  const source = `-- Natural numbers
inductive Nat : Type where
  | Zero : Nat
  | Succ : Nat -> Nat

-- Identity function
id : Type -> Type
id x = x

-- Constant function
const : Type -> Type -> Type
const x y = x`;

  const results = compileSource(source);

  // Comments are attached to their following blocks, so we have 3 blocks total
  assert(results.length === 3, 'Should have 3 blocks');
  assert(results[0].blockType === 'Inductive', 'First is inductive (with comment)');
  assert(results[0].name === 'Nat', 'Inductive name');
  assert(results[1].blockType === 'Term', 'Second is term (with comment)');
  assert(results[1].name === 'id', 'Term name');
  assert(results[2].blockType === 'Term', 'Third is term (with comment)');
  assert(results[2].name === 'const', 'Term name');

  const summary = summarizeResults(results);
  assert(summary.successfulBlocks === 3, `All blocks succeed, got errors: ${results.flatMap(r => r.checkErrors.map(e => e.message)).join(', ')}`);
  assert(summary.totalErrors === 0, 'No errors');
});

// ============================================================================
// Inductive Type Validity Error Tests
// Note: The current compiler implementation doesn't fully validate all
// inductive type constraints (return types, positivity, universe levels).
// These tests document the current behavior, not the ideal behavior.
// ============================================================================

test('compileSource: undefined symbol in constructor type', () => {
  // Constructor references undefined type
  const source = `inductive Bad : Type where
  | mk : (Bad -> Undefined) -> Bad`;

  const results = compileSource(source);

  assert(results.length === 1, 'Should have 1 block');
  assert(results[0].parseSuccess === true, 'Parse should succeed');
  assert(results[0].checkSuccess === false, 'Check should FAIL for undefined symbol');
  assert(results[0].checkErrors.length > 0, 'Should have errors');
});

// ============================================================================
// Parameter/Index Inference Tests
// ============================================================================

test('compileSource: inductive with no params (Nat)', () => {
  const source = `inductive Nat : Type where
  | Zero : Nat
  | Succ : Nat -> Nat`;

  const results = compileSource(source);

  assert(results.length === 1, 'Should have 1 block');
  assert(results[0].checkSuccess === true, 'Check should succeed');
  // Nat has no type parameters
  assert(
    results[0].indexPositions === undefined || results[0].indexPositions.length === 0,
    `Nat should have no index positions, got: ${JSON.stringify(results[0].indexPositions)}`
  );
});

test('compileSource: inductive with param (List)', () => {
  // List : Type -> Type with constructors that pass A through uniformly
  const source = `inductive List : Type -> Type where
  | nil : (A : Type) -> List A
  | cons : (A : Type) -> A -> List A -> List A`;

  const results = compileSource(source);

  assert(results.length === 1, 'Should have 1 block');
  assert(results[0].checkSuccess === true, `Check should succeed. Got: ${results[0].checkErrors.map(e => e.message).join(', ')}`);
  // List has position 0 as parameter (not index)
  // indexPositions contains the INDEX positions, so if A is a parameter, it should NOT be in indexPositions
  assert(results[0].indexPositions !== undefined, 'List should have index positions info');
  assert(!results[0].indexPositions!.includes(0), 'Position 0 (A) should be a parameter, not an index');
});

test('compileSource: inductive with param and index (Vec)', () => {
  // Vec : Type -> Nat -> Type
  // A is a parameter (uniform), n is an index (varies)
  const source = `inductive Nat : Type where
  | Zero : Nat
  | Succ : Nat -> Nat

inductive Vec : Type -> Nat -> Type where
  | nil : (A : Type) -> Vec A Zero
  | cons : (A : Type) -> (n : Nat) -> A -> Vec A n -> Vec A (Succ n)`;

  const results = compileSource(source);

  assert(results.length === 2, 'Should have 2 blocks');
  assert(results[0].checkSuccess === true, `Nat should type check. Got: ${results[0].checkErrors.map(e => e.message).join(', ')}`);
  assert(results[1].checkSuccess === true, `Vec should type check. Got: ${results[1].checkErrors.map(e => e.message).join(', ')}`);
  assert(results[1].indexPositions !== undefined, 'Vec should have index positions info');

  // Position 0 (A) is a parameter, position 1 (n) is an index
  assert(!results[1].indexPositions!.includes(0), 'A should be a parameter (not in indexPositions)');
  assert(results[1].indexPositions!.includes(1), 'n should be an index (in indexPositions)');
});

// ============================================================================
// Structural Recursion Tests
// ============================================================================

test('compileSource: safe structural recursion (plus)', () => {
  // This should pass - the recursive call uses a structurally smaller argument
  const source = `inductive Nat : Type where
  | Zero : Nat
  | Succ : Nat -> Nat

plus : Nat -> Nat -> Nat
plus Zero b = b
plus (Succ a) b = Succ (plus a b)`;

  const results = compileSource(source);

  assert(results.length === 2, 'Should have 2 blocks');
  assert(results[0].checkSuccess === true, 'Nat should type check');
  assert(
    results[1].checkSuccess === true,
    `plus should type check with safe recursion. Got errors: ${results[1].checkErrors.map(e => e.message).join(', ')}`
  );
});

test('compileSource: unsafe recursion - same argument', () => {
  // This should FAIL - recursive call uses the same argument (Succ a) instead of a
  const source = `inductive Nat : Type where
  | Zero : Nat
  | Succ : Nat -> Nat

plus : Nat -> Nat -> Nat
plus Zero b = b
plus (Succ a) b = Succ (plus (Succ a) b)`;

  const results = compileSource(source);

  assert(results.length === 2, 'Should have 2 blocks');
  assert(results[0].checkSuccess === true, 'Nat should type check');
  assert(results[1].checkSuccess === false, 'plus should FAIL due to unsafe recursion');
  assert(results[1].checkErrors.length > 0, 'Should have recursion error');
  assert(
    results[1].checkErrors.some(e =>
      e.message.toLowerCase().includes('recursion') ||
      e.message.toLowerCase().includes('recursive')
    ),
    `Error should mention recursion. Got: ${results[1].checkErrors.map(e => e.message).join(', ')}`
  );
});

test('compileSource: unsafe recursion - non-decreasing argument', () => {
  // This should FAIL - recursive call on (Succ n) which is larger, not smaller
  const source = `inductive Nat : Type where
  | Zero : Nat
  | Succ : Nat -> Nat

bad : Nat -> Nat
bad Zero = Zero
bad (Succ n) = bad (Succ (Succ n))`;

  const results = compileSource(source);

  assert(results.length === 2, 'Should have 2 blocks');
  assert(results[0].checkSuccess === true, 'Nat should type check');
  assert(results[1].checkSuccess === false, 'bad should FAIL due to unsafe recursion');
  assert(results[1].checkErrors.length > 0, 'Should have recursion error');
});

test('compileSource: non-recursive function passes', () => {
  // Non-recursive functions should pass without issues
  const source = `inductive Nat : Type where
  | Zero : Nat
  | Succ : Nat -> Nat

isZero : Nat -> Nat
isZero Zero = Zero
isZero (Succ n) = Zero`;

  const results = compileSource(source);

  assert(results.length === 2, 'Should have 2 blocks');
  assert(results[0].checkSuccess === true, 'Nat should type check');
  assert(
    results[1].checkSuccess === true,
    `isZero should pass (no recursion). Got errors: ${results[1].checkErrors.map(e => e.message).join(', ')}`
  );
});

console.log('\n' + '='.repeat(80));
console.log('ALL BLOCK-LEVEL TYPE CHECKING TESTS PASSED! ✓');
console.log('='.repeat(80) + '\n');
