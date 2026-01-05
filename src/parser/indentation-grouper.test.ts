/**
 * Tests for indentation-based source grouping
 */

import { groupByIndentation, parseBlock } from './indentation-grouper';

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

console.log('\n' + '='.repeat(80));
console.log('INDENTATION GROUPING TESTS');
console.log('='.repeat(80) + '\n');

test('Group single definition with pattern clauses', () => {
  const source = `plus : Nat -> Nat -> Nat
plus Zero b = b
plus (Succ a) b = Succ (plus a b)`;

  const blocks = groupByIndentation(source);
  assertEqual(blocks.length, 1);
  assertEqual(blocks[0].isInductive, false);
  assertEqual(blocks[0].lines.length, 3);
  assertEqual(blocks[0].lines[0], 'plus : Nat -> Nat -> Nat');
  assertEqual(blocks[0].lines[1], 'plus Zero b = b');
  assertEqual(blocks[0].lines[2], 'plus (Succ a) b = Succ (plus a b)');
});

test('Group definition with indented continuation', () => {
  const source = `plus : Nat
  -> Nat -> Nat
plus Zero b = b`;

  const blocks = groupByIndentation(source);
  assertEqual(blocks.length, 1);
  assertEqual(blocks[0].lines.length, 3);
  assertEqual(blocks[0].lines[0], 'plus : Nat');
  assertEqual(blocks[0].lines[1], '  -> Nat -> Nat');
  assertEqual(blocks[0].lines[2], 'plus Zero b = b');
});

test('Separate blocks with blank line', () => {
  const source = `plus : Nat -> Nat -> Nat
plus Zero b = b

twice : Nat -> Nat
twice n = plus n n`;

  const blocks = groupByIndentation(source);
  assertEqual(blocks.length, 2);
  assertEqual(blocks[0].lines.length, 2);
  assertEqual(blocks[1].lines.length, 2);
});

test('Group inductive definition', () => {
  const source = `inductive Nat : Type where
  | Zero : Nat
  | Succ : Nat -> Nat`;

  const blocks = groupByIndentation(source);
  assertEqual(blocks.length, 1);
  assertEqual(blocks[0].isInductive, true);
  assertEqual(blocks[0].lines.length, 3);
});

test('Separate inductive from regular definition', () => {
  const source = `inductive Nat : Type where
  | Zero : Nat

plus : Nat -> Nat -> Nat
plus Zero b = b`;

  const blocks = groupByIndentation(source);
  assertEqual(blocks.length, 2);
  assertEqual(blocks[0].isInductive, true);
  assertEqual(blocks[1].isInductive, false);
});

test('Handle line comments', () => {
  const source = `plus : Nat -> Nat -> Nat
-- This is the base case
plus Zero b = b
-- Recursive case
plus (Succ a) b = Succ (plus a b)`;

  const blocks = groupByIndentation(source);
  assertEqual(blocks.length, 1);
  assertEqual(blocks[0].lines.length, 5);
});

test('Blank line with only comment', () => {
  const source = `plus : Nat -> Nat -> Nat
plus Zero b = b
-- Just a comment

twice : Nat -> Nat`;

  const blocks = groupByIndentation(source);
  // The comment line should not prevent the blank line from separating blocks
  assertEqual(blocks.length, 2);
});

test('Indented continuation with comment', () => {
  const source = `plus : Nat -> Nat
  -- comment in signature
  -> Nat
plus Zero b = b`;

  const blocks = groupByIndentation(source);
  assertEqual(blocks.length, 1);
  assertEqual(blocks[0].lines.length, 4);
});

test('Pattern clause with indented body', () => {
  const source = `plus : Nat -> Nat -> Nat
plus Zero b =
  b
plus (Succ a) b =
  Succ (plus a b)`;

  const blocks = groupByIndentation(source);
  assertEqual(blocks.length, 1);
  assertEqual(blocks[0].lines.length, 5);
});

test('Parse block into signature and clauses', () => {
  const source = `plus : Nat -> Nat -> Nat
plus Zero b = b
plus (Succ a) b = Succ (plus a b)`;

  const blocks = groupByIndentation(source);
  const parsed = parseBlock(blocks[0]);

  assertEqual(parsed.signature, 'plus : Nat -> Nat -> Nat');
  assertEqual(parsed.clauses.length, 2);
  assertEqual(parsed.clauses[0], 'plus Zero b = b');
  assertEqual(parsed.clauses[1], 'plus (Succ a) b = Succ (plus a b)');
});

test('Parse block with indented continuation in signature', () => {
  const source = `plus : Nat
  -> Nat -> Nat
plus Zero b = b`;

  const blocks = groupByIndentation(source);
  const parsed = parseBlock(blocks[0]);

  assertEqual(parsed.signature, 'plus : Nat\n  -> Nat -> Nat');
  assertEqual(parsed.clauses.length, 1);
  assertEqual(parsed.clauses[0], 'plus Zero b = b');
});

test('Parse block with indented continuation in clause', () => {
  const source = `plus : Nat -> Nat -> Nat
plus Zero b = b
plus (Succ a) b =
  Succ (plus a b)`;

  const blocks = groupByIndentation(source);
  const parsed = parseBlock(blocks[0]);

  assertEqual(parsed.signature, 'plus : Nat -> Nat -> Nat');
  assertEqual(parsed.clauses.length, 2);
  assertEqual(parsed.clauses[0], 'plus Zero b = b');
  assertEqual(parsed.clauses[1], 'plus (Succ a) b =\n  Succ (plus a b)');
});

test('Parse inductive block', () => {
  const source = `inductive Nat : Type where
  | Zero : Nat
  | Succ : Nat -> Nat`;

  const blocks = groupByIndentation(source);
  const parsed = parseBlock(blocks[0]);

  // For inductive, everything is in signature
  assertEqual(parsed.signature, 'inductive Nat : Type where\n  | Zero : Nat\n  | Succ : Nat -> Nat');
  assertEqual(parsed.clauses.length, 0);
});

test('Multiple blocks with various indentations', () => {
  const source = `plus : Nat
  -> Nat
  -> Nat
plus Zero b = b
plus (Succ a) b =
  Succ
    (plus a b)

twice : Nat -> Nat
twice n =
  plus n n`;

  const blocks = groupByIndentation(source);
  assertEqual(blocks.length, 2);

  const parsed1 = parseBlock(blocks[0]);
  assertEqual(parsed1.signature, 'plus : Nat\n  -> Nat\n  -> Nat');
  assertEqual(parsed1.clauses.length, 2);

  const parsed2 = parseBlock(blocks[1]);
  assertEqual(parsed2.signature, 'twice : Nat -> Nat');
  assertEqual(parsed2.clauses.length, 1);
});

test('Block comments are their own blocks', () => {
  const source = `plus : Nat -> Nat -> Nat
plus Zero b = b

{-
const : (A : Type) -> A -> A
const A x = x
-}

twice : Nat -> Nat
twice n = plus n n`;

  const blocks = groupByIndentation(source);
  assertEqual(blocks.length, 3, 'Should find 3 blocks (plus, comment, twice)');
  assertEqual(blocks[0].lines[0], 'plus : Nat -> Nat -> Nat');
  assertEqual(blocks[1].isComment, true, 'Middle block should be a comment');
  assertEqual(blocks[2].lines[0], 'twice : Nat -> Nat');
});

test('Handle nested block comments', () => {
  const source = `inductive Nat : Type where
  Zero : Nat

{- Comment {- nested -} comment -}

plus : Nat -> Nat -> Nat
plus Zero b = b`;

  const blocks = groupByIndentation(source);
  assertEqual(blocks.length, 3, 'Should find 3 blocks (Nat, comment, plus)');
  assertEqual(blocks[0].isInductive, true);
  assertEqual(blocks[1].isComment, true, 'Second block is the nested comment');
  assertEqual(blocks[2].lines[0], 'plus : Nat -> Nat -> Nat');
});

test('Block comments spanning multiple blocks', () => {
  const source = `inductive Nat : Type where
  Zero : Nat

{-
twice : Nat -> Nat
twice n = plus n n

const : A -> B -> A
const x y = x
-}

id : A -> A
id x = x`;

  const blocks = groupByIndentation(source);
  assertEqual(blocks.length, 3, 'Should find 3 blocks (Nat, comment block, and id)');
  assertEqual(blocks[0].isInductive, true);
  assertEqual(blocks[1].isComment, true, 'Second block should be marked as comment');
  assertEqual(blocks[2].lines[0], 'id : A -> A');
});

test('Standalone line comment block (separated by blank lines)', () => {
  const source = `plus : Nat -> Nat -> Nat
plus Zero b = b

-- This is a standalone comment
-- that spans multiple lines

twice : Nat -> Nat
twice n = plus n n`;

  const blocks = groupByIndentation(source);
  assertEqual(blocks.length, 3, 'Should find 3 blocks (plus, comment, twice)');
  assertEqual(blocks[0].lines[0], 'plus : Nat -> Nat -> Nat');
  assertEqual(blocks[1].isComment, true, 'Middle block should be a comment');
  assertEqual(blocks[1].lines.length, 2, 'Comment block should have 2 lines');
  assertEqual(blocks[2].lines[0], 'twice : Nat -> Nat');
});

test('Inline comments are part of code block', () => {
  const source = `inductive Nat : Type where
  Zero : Nat  -- base case
  Succ : Nat -> Nat  -- successor`;

  const blocks = groupByIndentation(source);
  assertEqual(blocks.length, 1, 'Should be one block');
  assertEqual(blocks[0].isInductive, true);
  assertEqual(blocks[0].isComment || false, false, 'Should not be marked as comment');
  // The inline comments should still be in the lines
  const hasInlineComment = blocks[0].lines.some(line => line.includes('-- base case'));
  assertEqual(hasInlineComment, true, 'Inline comments should be preserved');
});

test('Mixed standalone and inline comments', () => {
  const source = `-- Header comment
-- explaining the module

inductive Nat : Type where
  Zero : Nat  -- inline comment

{- Block comment
   explaining plus -}

plus : Nat -> Nat -> Nat
plus Zero b = b`;

  const blocks = groupByIndentation(source);
  assertEqual(blocks.length, 4, 'Should find 4 blocks');
  assertEqual(blocks[0].isComment, true, 'First block is comment');
  assertEqual(blocks[1].isInductive, true, 'Second block is Nat');
  assertEqual(blocks[2].isComment, true, 'Third block is comment');
  assertEqual(blocks[3].lines[0], 'plus : Nat -> Nat -> Nat');
});

test('Attached line comment (no blank line before code)', () => {
  const source = `inductive Nat : Type where
  Zero : Nat

-- This comment is attached to plus
plus : Nat -> Nat -> Nat
plus Zero b = b

twice : Nat -> Nat
twice n = plus n n`;

  const blocks = groupByIndentation(source);
  assertEqual(blocks.length, 3, 'Should find 3 blocks (Nat, plus with comment, twice)');
  assertEqual(blocks[0].isInductive, true);
  assertEqual(blocks[1].isComment, false, 'Second block should be Term, not Comment');
  assertEqual(blocks[1].lines[0], '-- This comment is attached to plus', 'Comment should be first line of block');
  assertEqual(blocks[1].lines[1], 'plus : Nat -> Nat -> Nat', 'Signature should be second line');
  assertEqual(blocks[2].lines[0], 'twice : Nat -> Nat');
});

test('Attached block comment (no blank line before code)', () => {
  const source = `inductive Nat : Type where
  Zero : Nat

{- This comment explains plus -}
plus : Nat -> Nat -> Nat
plus Zero b = b`;

  const blocks = groupByIndentation(source);
  assertEqual(blocks.length, 2, 'Should find 2 blocks (Nat, plus with comment)');
  assertEqual(blocks[0].isInductive, true);
  assertEqual(blocks[1].isComment, false, 'Second block should be Term, not Comment');
  assertEqual(blocks[1].lines[0], '{- This comment explains plus -}', 'Comment should be first line');
  assertEqual(blocks[1].lines[1], 'plus : Nat -> Nat -> Nat', 'Signature should be second line');
});

test('Multi-line attached block comment', () => {
  const source = `{-
  This is a detailed explanation
  of the plus function
-}
plus : Nat -> Nat -> Nat
plus Zero b = b`;

  const blocks = groupByIndentation(source);
  assertEqual(blocks.length, 1, 'Should find 1 block (plus with attached comment)');
  assertEqual(blocks[0].isComment, false, 'Should be Term, not Comment');
  assertEqual(blocks[0].lines[0], '{-', 'Comment start should be first line');
  assertEqual(blocks[0].lines[blocks[0].lines.length - 2], 'plus : Nat -> Nat -> Nat', 'Signature should come after comment');
});

test('Multiple attached line comments', () => {
  const source = `-- Comment line 1
-- Comment line 2
-- Comment line 3
id : A -> A
id x = x`;

  const blocks = groupByIndentation(source);
  assertEqual(blocks.length, 1, 'Should find 1 block (id with attached comments)');
  assertEqual(blocks[0].isComment, false, 'Should be Term, not Comment');
  assertEqual(blocks[0].lines[0], '-- Comment line 1');
  assertEqual(blocks[0].lines[1], '-- Comment line 2');
  assertEqual(blocks[0].lines[2], '-- Comment line 3');
  assertEqual(blocks[0].lines[3], 'id : A -> A');
});

test('Stray indented lines after blank line form their own block', () => {
  // Regression test: indented lines after blank line should NOT be silently skipped
  // They should form their own block so parse errors are reported
  const source = `inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

  foo : Na
  ?
  ...`;

  const blocks = groupByIndentation(source);
  assertEqual(blocks.length, 2, 'Should find 2 blocks (Nat and stray indented lines)');
  assertEqual(blocks[0].isInductive, true);
  assertEqual(blocks[0].lines.length, 3, 'Inductive block should have 3 lines');
  assertEqual(blocks[1].isInductive, false);
  assertEqual(blocks[1].lines.length, 3, 'Stray indented block should have 3 lines');
  assertEqual(blocks[1].lines[0], '  foo : Na');
  assertEqual(blocks[1].lines[1], '  ?');
  assertEqual(blocks[1].lines[2], '  ...');
});

test('Multiple stray indented lines are grouped together', () => {
  const source = `plus : Nat -> Nat -> Nat
plus Zero b = b

  stray line 1
  stray line 2

twice : Nat -> Nat`;

  const blocks = groupByIndentation(source);
  assertEqual(blocks.length, 3, 'Should find 3 blocks');
  assertEqual(blocks[0].lines[0], 'plus : Nat -> Nat -> Nat');
  assertEqual(blocks[1].lines.length, 2, 'Stray block should have 2 lines');
  assertEqual(blocks[1].lines[0], '  stray line 1');
  assertEqual(blocks[2].lines[0], 'twice : Nat -> Nat');
});

console.log('\n' + '='.repeat(80));
console.log('ALL INDENTATION GROUPING TESTS PASSED! ✓');
console.log('='.repeat(80) + '\n');
