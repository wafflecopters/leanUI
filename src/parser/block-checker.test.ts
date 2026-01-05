/**
 * Tests for block-level type checking pipeline
 */

import { checkSourceBlocks, summarizeCheckResults } from './block-checker';

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

test('checkSourceBlocks: empty source', () => {
  const results = checkSourceBlocks('');
  assert(results.length === 0, 'Should return empty array for empty source');
});

test('checkSourceBlocks: single well-formed definition', () => {
  const source = 'id : Type -> Type';
  const results = checkSourceBlocks(source);

  assert(results.length === 1, 'Should have 1 block');
  assert(results[0].parseSuccess === true, 'Parse should succeed');
  assert(results[0].checkSuccess === true, 'Check should succeed');
  assert(results[0].blockType === 'Term', 'Should be a term');
  assert(results[0].name === 'id', 'Should have name "id"');
});

test('checkSourceBlocks: well-formed inductive', () => {
  // Constructors must return the inductive type being defined, not Type!
  const source = `inductive Nat : Type where
  | Zero : Nat
  | Succ : Nat -> Nat`;

  const results = checkSourceBlocks(source);

  assert(results.length === 1, 'Should have 1 block');
  assert(results[0].parseSuccess === true, 'Parse should succeed');
  assert(results[0].checkSuccess === true, `Check should succeed, got errors: ${results[0].checkErrors.map(e => e.error.message).join(', ')}`);
  assert(results[0].blockType === 'Inductive', 'Should be inductive');
  assert(results[0].name === 'Nat', 'Should have name "Nat"');
});

test('checkSourceBlocks: comment block', () => {
  const source = `-- This is a comment
-- Another comment line`;

  const results = checkSourceBlocks(source);

  assert(results.length === 1, 'Should have 1 block');
  assert(results[0].blockType === 'Comment', 'Should be a comment block');
  assert(results[0].parseSuccess === true, 'Comments are always parse success');
  assert(results[0].checkSuccess === true, 'Comments are always check success');
});

test('checkSourceBlocks: multiple blocks', () => {
  const source = `id : Type -> Type

const : Type -> Type -> Type`;

  const results = checkSourceBlocks(source);

  assert(results.length === 2, 'Should have 2 blocks');
  assert(results[0].name === 'id', 'First block name');
  assert(results[1].name === 'const', 'Second block name');
  assert(results[0].checkSuccess === true, 'First should succeed');
  assert(results[1].checkSuccess === true, 'Second should succeed');
});

// ============================================================================
// Parse Error Tests
// ============================================================================

test('checkSourceBlocks: parse error is captured', () => {
  const source = 'bad syntax @#$%';

  const results = checkSourceBlocks(source);

  assert(results.length === 1, 'Should have 1 block');
  assert(results[0].parseSuccess === false, 'Parse should fail');
  assert(results[0].parseErrors.length > 0, 'Should have parse errors');
  assert(results[0].checkSuccess === false, 'Check should be marked as failed');
});

test('checkSourceBlocks: parse error does not stop other blocks', () => {
  const source = `id : Type -> Type

bad syntax @#$%

const : Type -> Type -> Type`;

  const results = checkSourceBlocks(source);

  assert(results.length === 3, 'Should have 3 blocks');
  assert(results[0].parseSuccess === true, 'First block should parse');
  assert(results[1].parseSuccess === false, 'Second block should fail to parse');
  assert(results[2].parseSuccess === true, 'Third block should parse');
});

// ============================================================================
// Type Check Error Tests
// ============================================================================

test('checkSourceBlocks: well-formed inductive (type checking passes)', () => {
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

  const results = checkSourceBlocks(source);

  assert(results.length === 1, 'Should have 1 block');
  assert(results[0].parseSuccess === true, 'Parse should succeed');
  assert(results[0].checkSuccess === true, `Check should succeed for well-formed inductive, got: ${results[0].checkErrors.map(e => e.error.message).join(', ')}`);
  assert(results[0].checkErrors.length === 0, 'Should have no errors');
});

// ============================================================================
// Mixed Success/Failure Tests
// ============================================================================

test('checkSourceBlocks: mix of successes and parse errors', () => {
  const source = `-- Comment block

good1 : Type -> Type

bad parse @#$%

good2 : Type -> Type -> Type

inductive Nat : Type where
  | Zero : Nat

good3 : Type`;

  const results = checkSourceBlocks(source);

  assert(results.length === 6, 'Should have 6 blocks');

  // Block 0: Comment
  assert(results[0].blockType === 'Comment', 'Block 0 is comment');
  assert(results[0].checkSuccess === true, 'Comments succeed');

  // Block 1: good1
  assert(results[1].name === 'good1', 'Block 1 name');
  assert(results[1].parseSuccess === true, 'Block 1 parse success');
  assert(results[1].checkSuccess === true, 'Block 1 check success');

  // Block 2: parse error
  assert(results[2].parseSuccess === false, 'Block 2 parse fails');

  // Block 3: good2
  assert(results[3].name === 'good2', 'Block 3 name');
  assert(results[3].parseSuccess === true, 'Block 3 parse success');
  assert(results[3].checkSuccess === true, 'Block 3 check success');

  // Block 4: good inductive
  assert(results[4].name === 'Nat', 'Block 4 name');
  assert(results[4].parseSuccess === true, 'Block 4 parse success');
  assert(results[4].checkSuccess === true, `Block 4 check success, got: ${results[4].checkErrors.map(e => e.error.message).join(', ')}`);

  // Block 5: good3
  assert(results[5].name === 'good3', 'Block 5 name');
  assert(results[5].parseSuccess === true, 'Block 5 parse success');
  assert(results[5].checkSuccess === true, 'Block 5 check success');
});

// ============================================================================
// Error Location Tests
// ============================================================================

test('checkSourceBlocks: parse errors include basic location info', () => {
  const source = `bad syntax @#$%`;

  const results = checkSourceBlocks(source);

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

test('summarizeCheckResults: empty results', () => {
  const summary = summarizeCheckResults([]);

  assert(summary.totalBlocks === 0, 'Total blocks');
  assert(summary.commentBlocks === 0, 'Comment blocks');
  assert(summary.successfulBlocks === 0, 'Successful blocks');
  assert(summary.parseErrorBlocks === 0, 'Parse error blocks');
  assert(summary.checkErrorBlocks === 0, 'Check error blocks');
  assert(summary.totalErrors === 0, 'Total errors');
});

test('summarizeCheckResults: all successful', () => {
  const source = `id : Type -> Type

const : Type -> Type -> Type`;

  const results = checkSourceBlocks(source);
  const summary = summarizeCheckResults(results);

  assert(summary.totalBlocks === 2, 'Total blocks');
  assert(summary.successfulBlocks === 2, 'Successful blocks');
  assert(summary.parseErrorBlocks === 0, 'No parse errors');
  assert(summary.checkErrorBlocks === 0, 'No check errors');
  assert(summary.totalErrors === 0, 'No errors');
});

test('summarizeCheckResults: mixed results with parse errors', () => {
  const source = `-- Comment

good : Type -> Type

bad parse @#$%

good2 : Type -> Type`;

  const results = checkSourceBlocks(source);
  const summary = summarizeCheckResults(results);

  assert(summary.totalBlocks === 4, 'Total blocks');
  assert(summary.commentBlocks === 1, 'Comment blocks');
  assert(summary.successfulBlocks === 3, 'Successful blocks (comment + good + good2)');
  assert(summary.parseErrorBlocks === 1, 'Parse error blocks');
  assert(summary.checkErrorBlocks === 0, 'No check error blocks');
  assert(summary.totalErrors >= 1, 'At least 1 parse error');
});

// ============================================================================
// Integration Tests
// ============================================================================

test('checkSourceBlocks: real-world example', () => {
  // Note: Constructors must return the inductive type, not Type!
  const source = `-- Natural numbers
inductive Nat : Type where
  | Zero : Nat
  | Succ : Nat -> Nat

-- Identity function
id : Type -> Type

-- Constant function
const : Type -> Type -> Type`;

  const results = checkSourceBlocks(source);

  // Comments are attached to their following blocks, so we have 3 blocks total
  assert(results.length === 3, 'Should have 3 blocks');
  assert(results[0].blockType === 'Inductive', 'First is inductive (with comment)');
  assert(results[0].name === 'Nat', 'Inductive name');
  assert(results[1].blockType === 'Term', 'Second is term (with comment)');
  assert(results[1].name === 'id', 'Term name');
  assert(results[2].blockType === 'Term', 'Third is term (with comment)');
  assert(results[2].name === 'const', 'Term name');

  const summary = summarizeCheckResults(results);
  assert(summary.successfulBlocks === 3, `All blocks succeed, got errors: ${results.flatMap(r => r.checkErrors.map(e => e.error.message)).join(', ')}`);
  assert(summary.totalErrors === 0, 'No errors');
});

// ============================================================================
// Inductive Type Validity Error Tests
// ============================================================================

test('checkSourceBlocks: constructor wrong return type error', () => {
  // Constructor returns Type instead of the inductive type
  const source = `inductive Bad : Type where
  | wrong : Type`;

  const results = checkSourceBlocks(source);

  assert(results.length === 1, 'Should have 1 block');
  assert(results[0].parseSuccess === true, 'Parse should succeed');
  assert(results[0].checkSuccess === false, 'Check should FAIL for wrong return type');
  assert(results[0].checkErrors.length > 0, 'Should have errors');
  assert(
    results[0].checkErrors.some(e => e.error.message.includes('wrong') && e.error.message.includes('Bad')),
    `Error should mention wrong constructor and expected type. Got: ${results[0].checkErrors.map(e => e.error.message).join(', ')}`
  );
});

test('checkSourceBlocks: strict positivity violation error', () => {
  // (Bad -> X) -> Bad is a negative occurrence
  const source = `inductive Bad : Type where
  | mk : (Bad -> Nat) -> Bad`;

  const results = checkSourceBlocks(source);

  assert(results.length === 1, 'Should have 1 block');
  assert(results[0].parseSuccess === true, 'Parse should succeed');
  assert(results[0].checkSuccess === false, 'Check should FAIL for positivity violation');
  assert(results[0].checkErrors.length > 0, 'Should have errors');
  assert(
    results[0].checkErrors.some(e => e.error.message.includes('negative') || e.error.message.includes('positiv')),
    `Error should mention positivity. Got: ${results[0].checkErrors.map(e => e.error.message).join(', ')}`
  );
});

test('checkSourceBlocks: universe constraint violation error', () => {
  // Type in Type_0 inductive (without being polymorphic)
  const source = `inductive Big : Type where
  | mk : Type -> Big`;

  const results = checkSourceBlocks(source);

  assert(results.length === 1, 'Should have 1 block');
  assert(results[0].parseSuccess === true, 'Parse should succeed');
  assert(results[0].checkSuccess === false, 'Check should FAIL for universe violation');
  assert(results[0].checkErrors.length > 0, 'Should have errors');
  assert(
    results[0].checkErrors.some(e => e.error.message.includes('universe') || e.error.message.includes('Universe')),
    `Error should mention universe constraint. Got: ${results[0].checkErrors.map(e => e.error.message).join(', ')}`
  );
});

// ============================================================================
// Parameter/Index Inference Tests
// ============================================================================

test('checkSourceBlocks: inductive with no params (Nat)', () => {
  const source = `inductive Nat : Type where
  | Zero : Nat
  | Succ : Nat -> Nat`;

  const results = checkSourceBlocks(source);

  assert(results.length === 1, 'Should have 1 block');
  assert(results[0].checkSuccess === true, 'Check should succeed');
  // Nat has no type parameters
  assert(
    results[0].inductiveParams === undefined || results[0].inductiveParams.length === 0,
    `Nat should have no params, got: ${JSON.stringify(results[0].inductiveParams)}`
  );
});

test('checkSourceBlocks: inductive with param (List)', () => {
  // List : Type -> Type with constructors that pass A through uniformly
  const source = `inductive List : Type -> Type where
  | nil : (A : Type) -> List A
  | cons : (A : Type) -> A -> List A -> List A`;

  const results = checkSourceBlocks(source);

  assert(results.length === 1, 'Should have 1 block');
  // List has one type parameter A
  assert(results[0].inductiveParams !== undefined, 'List should have params info');
  assert(results[0].inductiveParams!.length === 1, `List should have 1 param, got ${results[0].inductiveParams!.length}`);
  assert(results[0].inductiveParams![0].isIndex === false, 'A should be a parameter, not index');
  assert(results[0].inductiveParams![0].type === 'Type', `A should have type Type, got ${results[0].inductiveParams![0].type}`);
});

test('checkSourceBlocks: inductive with param and index (Vec)', () => {
  // Vec : Type -> Nat -> Type
  // A is a parameter (uniform), n is an index (varies)
  const source = `inductive Vec : Type -> Nat -> Type where
  | nil : (A : Type) -> Vec A Zero
  | cons : (A : Type) -> (n : Nat) -> A -> Vec A n -> Vec A (Succ n)`;

  const results = checkSourceBlocks(source);

  assert(results.length === 1, 'Should have 1 block');
  assert(results[0].inductiveParams !== undefined, 'Vec should have params info');
  assert(results[0].inductiveParams!.length === 2, `Vec should have 2 params, got ${results[0].inductiveParams!.length}`);

  // First param: A is a parameter
  assert(results[0].inductiveParams![0].isIndex === false, 'A should be a parameter');
  assert(results[0].inductiveParams![0].type === 'Type', `A should have type Type`);

  // Second param: n is an index
  assert(results[0].inductiveParams![1].isIndex === true, 'n should be an index');
  assert(results[0].inductiveParams![1].type === 'Nat', `n should have type Nat`);
});

// ============================================================================
// Structural Recursion Tests
// ============================================================================

test('checkSourceBlocks: safe structural recursion (plus)', () => {
  // This should pass - the recursive call uses a structurally smaller argument
  const source = `inductive Nat : Type where
  | Zero : Nat
  | Succ : Nat -> Nat

plus : Nat -> Nat -> Nat
plus Zero b = b
plus (Succ a) b = Succ (plus a b)`;

  const results = checkSourceBlocks(source);

  assert(results.length === 2, 'Should have 2 blocks');
  assert(results[0].checkSuccess === true, 'Nat should type check');
  assert(
    results[1].checkSuccess === true,
    `plus should type check with safe recursion. Got errors: ${results[1].checkErrors.map(e => e.error.message).join(', ')}`
  );
});

test('checkSourceBlocks: unsafe recursion - same argument', () => {
  // This should FAIL - recursive call uses the same argument (Succ a) instead of a
  const source = `inductive Nat : Type where
  | Zero : Nat
  | Succ : Nat -> Nat

plus : Nat -> Nat -> Nat
plus Zero b = b
plus (Succ a) b = Succ (plus (Succ a) b)`;

  const results = checkSourceBlocks(source);

  assert(results.length === 2, 'Should have 2 blocks');
  assert(results[0].checkSuccess === true, 'Nat should type check');
  assert(results[1].checkSuccess === false, 'plus should FAIL due to unsafe recursion');
  assert(results[1].checkErrors.length > 0, 'Should have recursion error');
  assert(
    results[1].checkErrors.some(e =>
      e.error.message.toLowerCase().includes('recursion') ||
      e.error.message.toLowerCase().includes('recursive')
    ),
    `Error should mention recursion. Got: ${results[1].checkErrors.map(e => e.error.message).join(', ')}`
  );
});

test('checkSourceBlocks: unsafe recursion - non-decreasing argument', () => {
  // This should FAIL - recursive call on (Succ n) which is larger, not smaller
  const source = `inductive Nat : Type where
  | Zero : Nat
  | Succ : Nat -> Nat

bad : Nat -> Nat
bad Zero = Zero
bad (Succ n) = bad (Succ (Succ n))`;

  const results = checkSourceBlocks(source);

  assert(results.length === 2, 'Should have 2 blocks');
  assert(results[0].checkSuccess === true, 'Nat should type check');
  assert(results[1].checkSuccess === false, 'bad should FAIL due to unsafe recursion');
  assert(results[1].checkErrors.length > 0, 'Should have recursion error');
});

test('checkSourceBlocks: non-recursive function passes', () => {
  // Non-recursive functions should pass without issues
  const source = `inductive Nat : Type where
  | Zero : Nat
  | Succ : Nat -> Nat

isZero : Nat -> Nat
isZero Zero = Zero
isZero (Succ n) = Zero`;

  const results = checkSourceBlocks(source);

  assert(results.length === 2, 'Should have 2 blocks');
  assert(results[0].checkSuccess === true, 'Nat should type check');
  assert(
    results[1].checkSuccess === true,
    `isZero should pass (no recursion). Got errors: ${results[1].checkErrors.map(e => e.error.message).join(', ')}`
  );
});

console.log('\n' + '='.repeat(80));
console.log('ALL BLOCK-LEVEL TYPE CHECKING TESTS PASSED! ✓');
console.log('='.repeat(80) + '\n');
