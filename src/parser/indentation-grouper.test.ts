/**
 * Tests for indentation-based source grouping
 */

import { describe, test, expect } from 'vitest';
import { groupByIndentation, parseBlock } from './indentation-grouper';

describe('Indentation Grouping', () => {
  describe('Basic Grouping', () => {
    test('group single definition with pattern clauses', () => {
      const source = `plus : Nat -> Nat -> Nat
plus Zero b = b
plus (Succ a) b = Succ (plus a b)`;

      const blocks = groupByIndentation(source);
      expect(blocks.length).toBe(1);
      expect(blocks[0].isInductive).toBe(false);
      expect(blocks[0].lines.length).toBe(3);
      expect(blocks[0].lines[0]).toBe('plus : Nat -> Nat -> Nat');
      expect(blocks[0].lines[1]).toBe('plus Zero b = b');
      expect(blocks[0].lines[2]).toBe('plus (Succ a) b = Succ (plus a b)');
    });

    test('group definition with indented continuation', () => {
      const source = `plus : Nat
  -> Nat -> Nat
plus Zero b = b`;

      const blocks = groupByIndentation(source);
      expect(blocks.length).toBe(1);
      expect(blocks[0].lines.length).toBe(3);
      expect(blocks[0].lines[0]).toBe('plus : Nat');
      expect(blocks[0].lines[1]).toBe('  -> Nat -> Nat');
      expect(blocks[0].lines[2]).toBe('plus Zero b = b');
    });

    test('separate blocks with blank line', () => {
      const source = `plus : Nat -> Nat -> Nat
plus Zero b = b

twice : Nat -> Nat
twice n = plus n n`;

      const blocks = groupByIndentation(source);
      expect(blocks.length).toBe(2);
      expect(blocks[0].lines.length).toBe(2);
      expect(blocks[1].lines.length).toBe(2);
    });
  });

  describe('Inductive Types', () => {
    test('group inductive definition', () => {
      const source = `inductive Nat : Type where
  | Zero : Nat
  | Succ : Nat -> Nat`;

      const blocks = groupByIndentation(source);
      expect(blocks.length).toBe(1);
      expect(blocks[0].isInductive).toBe(true);
      expect(blocks[0].lines.length).toBe(3);
    });

    test('separate inductive from regular definition', () => {
      const source = `inductive Nat : Type where
  | Zero : Nat

plus : Nat -> Nat -> Nat
plus Zero b = b`;

      const blocks = groupByIndentation(source);
      expect(blocks.length).toBe(2);
      expect(blocks[0].isInductive).toBe(true);
      expect(blocks[1].isInductive).toBe(false);
    });
  });

  describe('Comments', () => {
    test('handle line comments', () => {
      const source = `plus : Nat -> Nat -> Nat
-- This is the base case
plus Zero b = b
-- Recursive case
plus (Succ a) b = Succ (plus a b)`;

      const blocks = groupByIndentation(source);
      expect(blocks.length).toBe(1);
      expect(blocks[0].lines.length).toBe(5);
    });

    test('blank line with only comment', () => {
      const source = `plus : Nat -> Nat -> Nat
plus Zero b = b
-- Just a comment

twice : Nat -> Nat`;

      const blocks = groupByIndentation(source);
      // The comment line should not prevent the blank line from separating blocks
      expect(blocks.length).toBe(2);
    });

    test('indented continuation with comment', () => {
      const source = `plus : Nat -> Nat
  -- comment in signature
  -> Nat
plus Zero b = b`;

      const blocks = groupByIndentation(source);
      expect(blocks.length).toBe(1);
      expect(blocks[0].lines.length).toBe(4);
    });

    test('block comments are their own blocks', () => {
      const source = `plus : Nat -> Nat -> Nat
plus Zero b = b

{-
const : (A : Type) -> A -> A
const A x = x
-}

twice : Nat -> Nat
twice n = plus n n`;

      const blocks = groupByIndentation(source);
      expect(blocks.length).toBe(3);
      expect(blocks[0].lines[0]).toBe('plus : Nat -> Nat -> Nat');
      expect(blocks[1].isComment).toBe(true);
      expect(blocks[2].lines[0]).toBe('twice : Nat -> Nat');
    });

    test('handle nested block comments', () => {
      const source = `inductive Nat : Type where
  Zero : Nat

{- Comment {- nested -} comment -}

plus : Nat -> Nat -> Nat
plus Zero b = b`;

      const blocks = groupByIndentation(source);
      expect(blocks.length).toBe(3);
      expect(blocks[0].isInductive).toBe(true);
      expect(blocks[1].isComment).toBe(true);
      expect(blocks[2].lines[0]).toBe('plus : Nat -> Nat -> Nat');
    });

    test('block comments spanning multiple blocks', () => {
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
      expect(blocks.length).toBe(3);
      expect(blocks[0].isInductive).toBe(true);
      expect(blocks[1].isComment).toBe(true);
      expect(blocks[2].lines[0]).toBe('id : A -> A');
    });

    test('standalone line comment block (separated by blank lines)', () => {
      const source = `plus : Nat -> Nat -> Nat
plus Zero b = b

-- This is a standalone comment
-- that spans multiple lines

twice : Nat -> Nat
twice n = plus n n`;

      const blocks = groupByIndentation(source);
      expect(blocks.length).toBe(3);
      expect(blocks[0].lines[0]).toBe('plus : Nat -> Nat -> Nat');
      expect(blocks[1].isComment).toBe(true);
      expect(blocks[1].lines.length).toBe(2);
      expect(blocks[2].lines[0]).toBe('twice : Nat -> Nat');
    });

    test('inline comments are part of code block', () => {
      const source = `inductive Nat : Type where
  Zero : Nat  -- base case
  Succ : Nat -> Nat  -- successor`;

      const blocks = groupByIndentation(source);
      expect(blocks.length).toBe(1);
      expect(blocks[0].isInductive).toBe(true);
      expect(blocks[0].isComment || false).toBe(false);
      // The inline comments should still be in the lines
      const hasInlineComment = blocks[0].lines.some(line => line.includes('-- base case'));
      expect(hasInlineComment).toBe(true);
    });

    test('mixed standalone and inline comments', () => {
      const source = `-- Header comment
-- explaining the module

inductive Nat : Type where
  Zero : Nat  -- inline comment

{- Block comment
   explaining plus -}

plus : Nat -> Nat -> Nat
plus Zero b = b`;

      const blocks = groupByIndentation(source);
      expect(blocks.length).toBe(4);
      expect(blocks[0].isComment).toBe(true);
      expect(blocks[1].isInductive).toBe(true);
      expect(blocks[2].isComment).toBe(true);
      expect(blocks[3].lines[0]).toBe('plus : Nat -> Nat -> Nat');
    });

    test('attached line comment (no blank line before code)', () => {
      const source = `inductive Nat : Type where
  Zero : Nat

-- This comment is attached to plus
plus : Nat -> Nat -> Nat
plus Zero b = b

twice : Nat -> Nat
twice n = plus n n`;

      const blocks = groupByIndentation(source);
      expect(blocks.length).toBe(3);
      expect(blocks[0].isInductive).toBe(true);
      expect(blocks[1].isComment).toBe(false);
      expect(blocks[1].lines[0]).toBe('-- This comment is attached to plus');
      expect(blocks[1].lines[1]).toBe('plus : Nat -> Nat -> Nat');
      expect(blocks[2].lines[0]).toBe('twice : Nat -> Nat');
    });

    test('attached block comment (no blank line before code)', () => {
      const source = `inductive Nat : Type where
  Zero : Nat

{- This comment explains plus -}
plus : Nat -> Nat -> Nat
plus Zero b = b`;

      const blocks = groupByIndentation(source);
      expect(blocks.length).toBe(2);
      expect(blocks[0].isInductive).toBe(true);
      expect(blocks[1].isComment).toBe(false);
      expect(blocks[1].lines[0]).toBe('{- This comment explains plus -}');
      expect(blocks[1].lines[1]).toBe('plus : Nat -> Nat -> Nat');
    });

    test('multi-line attached block comment', () => {
      const source = `{-
  This is a detailed explanation
  of the plus function
-}
plus : Nat -> Nat -> Nat
plus Zero b = b`;

      const blocks = groupByIndentation(source);
      expect(blocks.length).toBe(1);
      expect(blocks[0].isComment).toBe(false);
      expect(blocks[0].lines[0]).toBe('{-');
      expect(blocks[0].lines[blocks[0].lines.length - 2]).toBe('plus : Nat -> Nat -> Nat');
    });

    test('multiple attached line comments', () => {
      const source = `-- Comment line 1
-- Comment line 2
-- Comment line 3
id : A -> A
id x = x`;

      const blocks = groupByIndentation(source);
      expect(blocks.length).toBe(1);
      expect(blocks[0].isComment).toBe(false);
      expect(blocks[0].lines[0]).toBe('-- Comment line 1');
      expect(blocks[0].lines[1]).toBe('-- Comment line 2');
      expect(blocks[0].lines[2]).toBe('-- Comment line 3');
      expect(blocks[0].lines[3]).toBe('id : A -> A');
    });
  });

  describe('Indented Patterns', () => {
    test('pattern clause with indented body', () => {
      const source = `plus : Nat -> Nat -> Nat
plus Zero b =
  b
plus (Succ a) b =
  Succ (plus a b)`;

      const blocks = groupByIndentation(source);
      expect(blocks.length).toBe(1);
      expect(blocks[0].lines.length).toBe(5);
    });

    test('multiple blocks with various indentations', () => {
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
      expect(blocks.length).toBe(2);

      const parsed1 = parseBlock(blocks[0]);
      expect(parsed1.signature).toBe('plus : Nat\n  -> Nat\n  -> Nat');
      expect(parsed1.clauses.length).toBe(2);

      const parsed2 = parseBlock(blocks[1]);
      expect(parsed2.signature).toBe('twice : Nat -> Nat');
      expect(parsed2.clauses.length).toBe(1);
    });
  });

  describe('Stray Indented Lines', () => {
    test('stray indented lines after blank line form their own block', () => {
      // Regression test: indented lines after blank line should NOT be silently skipped
      // They should form their own block so parse errors are reported
      const source = `inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

  foo : Na
  ?
  ...`;

      const blocks = groupByIndentation(source);
      expect(blocks.length).toBe(2);
      expect(blocks[0].isInductive).toBe(true);
      expect(blocks[0].lines.length).toBe(3);
      expect(blocks[1].isInductive).toBe(false);
      expect(blocks[1].lines.length).toBe(3);
      expect(blocks[1].lines[0]).toBe('  foo : Na');
      expect(blocks[1].lines[1]).toBe('  ?');
      expect(blocks[1].lines[2]).toBe('  ...');
    });

    test('multiple stray indented lines are grouped together', () => {
      const source = `plus : Nat -> Nat -> Nat
plus Zero b = b

  stray line 1
  stray line 2

twice : Nat -> Nat`;

      const blocks = groupByIndentation(source);
      expect(blocks.length).toBe(3);
      expect(blocks[0].lines[0]).toBe('plus : Nat -> Nat -> Nat');
      expect(blocks[1].lines.length).toBe(2);
      expect(blocks[1].lines[0]).toBe('  stray line 1');
      expect(blocks[2].lines[0]).toBe('twice : Nat -> Nat');
    });
  });

  describe('parseBlock', () => {
    test('parse block into signature and clauses', () => {
      const source = `plus : Nat -> Nat -> Nat
plus Zero b = b
plus (Succ a) b = Succ (plus a b)`;

      const blocks = groupByIndentation(source);
      const parsed = parseBlock(blocks[0]);

      expect(parsed.signature).toBe('plus : Nat -> Nat -> Nat');
      expect(parsed.clauses.length).toBe(2);
      expect(parsed.clauses[0]).toBe('plus Zero b = b');
      expect(parsed.clauses[1]).toBe('plus (Succ a) b = Succ (plus a b)');
    });

    test('parse block with indented continuation in signature', () => {
      const source = `plus : Nat
  -> Nat -> Nat
plus Zero b = b`;

      const blocks = groupByIndentation(source);
      const parsed = parseBlock(blocks[0]);

      expect(parsed.signature).toBe('plus : Nat\n  -> Nat -> Nat');
      expect(parsed.clauses.length).toBe(1);
      expect(parsed.clauses[0]).toBe('plus Zero b = b');
    });

    test('parse block with indented continuation in clause', () => {
      const source = `plus : Nat -> Nat -> Nat
plus Zero b = b
plus (Succ a) b =
  Succ (plus a b)`;

      const blocks = groupByIndentation(source);
      const parsed = parseBlock(blocks[0]);

      expect(parsed.signature).toBe('plus : Nat -> Nat -> Nat');
      expect(parsed.clauses.length).toBe(2);
      expect(parsed.clauses[0]).toBe('plus Zero b = b');
      expect(parsed.clauses[1]).toBe('plus (Succ a) b =\n  Succ (plus a b)');
    });

    test('parse inductive block', () => {
      const source = `inductive Nat : Type where
  | Zero : Nat
  | Succ : Nat -> Nat`;

      const blocks = groupByIndentation(source);
      const parsed = parseBlock(blocks[0]);

      // For inductive, everything is in signature
      expect(parsed.signature).toBe('inductive Nat : Type where\n  | Zero : Nat\n  | Succ : Nat -> Nat');
      expect(parsed.clauses.length).toBe(0);
    });
  });
});
