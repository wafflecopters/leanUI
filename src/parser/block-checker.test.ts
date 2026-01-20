/**
 * Tests for block-level type checking pipeline
 */

import { describe, test, expect } from 'vitest';
import { compileSource, summarizeResults } from '../test-utils';

describe('Block-Level Type Checking', () => {
  describe('Basic Pipeline', () => {
    test('empty source', () => {
      const results = compileSource('');
      expect(results.length).toBe(0);
    });

    test('single well-formed definition', () => {
      const source = `id : Type -> Type
id x = x`;
      const results = compileSource(source);

      expect(results.length).toBe(1);
      expect(results[0].parseSuccess).toBe(true);
      expect(results[0].checkSuccess).toBe(true);
      expect(results[0].blockType).toBe('Term');
      expect(results[0].name).toBe('id');
    });

    test('well-formed inductive', () => {
      const source = `inductive Nat : Type where
  | Zero : Nat
  | Succ : Nat -> Nat`;

      const results = compileSource(source);

      expect(results.length).toBe(1);
      expect(results[0].parseSuccess).toBe(true);
      expect(results[0].checkSuccess).toBe(true);
      expect(results[0].blockType).toBe('Inductive');
      expect(results[0].name).toBe('Nat');
    });

    test('comment block', () => {
      const source = `-- This is a comment
-- Another comment line`;

      const results = compileSource(source);

      expect(results.length).toBe(1);
      expect(results[0].blockType).toBe('Comment');
      expect(results[0].parseSuccess).toBe(true);
      expect(results[0].checkSuccess).toBe(true);
    });

    test('multiple blocks', () => {
      const source = `id : Type -> Type
id x = x

const : Type -> Type -> Type
const x y = x`;

      const results = compileSource(source);

      expect(results.length).toBe(2);
      expect(results[0].name).toBe('id');
      expect(results[1].name).toBe('const');
      expect(results[0].checkSuccess).toBe(true);
      expect(results[1].checkSuccess).toBe(true);
    });
  });

  describe('Parse Errors', () => {
    test('parse error is captured', () => {
      const source = 'bad syntax @#$%';

      const results = compileSource(source);

      expect(results.length).toBe(1);
      expect(results[0].parseSuccess).toBe(false);
      expect(results[0].parseErrors.length).toBeGreaterThan(0);
      expect(results[0].checkSuccess).toBe(false);
    });

    test('parse error does not stop other blocks', () => {
      const source = `id : Type -> Type
id x = x

bad syntax @#$%

const : Type -> Type -> Type
const x y = x`;

      const results = compileSource(source);

      expect(results.length).toBe(3);
      expect(results[0].parseSuccess).toBe(true);
      expect(results[1].parseSuccess).toBe(false);
      expect(results[2].parseSuccess).toBe(true);
    });
  });

  describe('Type Check Errors', () => {
    test('well-formed inductive passes type checking', () => {
      const source = `inductive Nat : Type where
  | Zero : Nat
  | Succ : Nat -> Nat`;

      const results = compileSource(source);

      expect(results.length).toBe(1);
      expect(results[0].parseSuccess).toBe(true);
      expect(results[0].checkSuccess).toBe(true);
      expect(results[0].checkErrors.length).toBe(0);
    });
  });

  describe('Mixed Success/Failure', () => {
    test('mix of successes and parse errors', () => {
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

      expect(results.length).toBe(6);

      // Block 0: Comment
      expect(results[0].blockType).toBe('Comment');
      expect(results[0].checkSuccess).toBe(true);

      // Block 1: good1
      expect(results[1].name).toBe('good1');
      expect(results[1].parseSuccess).toBe(true);
      expect(results[1].checkSuccess).toBe(true);

      // Block 2: parse error
      expect(results[2].parseSuccess).toBe(false);

      // Block 3: good2
      expect(results[3].name).toBe('good2');
      expect(results[3].parseSuccess).toBe(true);
      expect(results[3].checkSuccess).toBe(true);

      // Block 4: good inductive
      expect(results[4].name).toBe('Nat');
      expect(results[4].parseSuccess).toBe(true);
      expect(results[4].checkSuccess).toBe(true);

      // Block 5: good3
      expect(results[5].name).toBe('good3');
      expect(results[5].parseSuccess).toBe(true);
      expect(results[5].checkSuccess).toBe(true);
    });
  });

  describe('Error Location', () => {
    test('parse errors include basic location info', () => {
      const source = `bad syntax @#$%`;

      const results = compileSource(source);

      expect(results.length).toBe(1);
      expect(results[0].parseErrors.length).toBeGreaterThan(0);

      // Parse errors should have line and column info
      const firstError = results[0].parseErrors[0];
      expect(firstError.message.length).toBeGreaterThan(0);
      expect(firstError.line).toBeDefined();
      expect(firstError.col).toBeDefined();
    });
  });

  describe('Summary', () => {
    test('empty results', () => {
      const summary = summarizeResults([]);

      expect(summary.totalBlocks).toBe(0);
      expect(summary.commentBlocks).toBe(0);
      expect(summary.successfulBlocks).toBe(0);
      expect(summary.parseErrorBlocks).toBe(0);
      expect(summary.checkErrorBlocks).toBe(0);
      expect(summary.totalErrors).toBe(0);
    });

    test('all successful', () => {
      const source = `id : Type -> Type
id x = x

const : Type -> Type -> Type
const x y = x`;

      const results = compileSource(source);
      const summary = summarizeResults(results);

      expect(summary.totalBlocks).toBe(2);
      expect(summary.successfulBlocks).toBe(2);
      expect(summary.parseErrorBlocks).toBe(0);
      expect(summary.checkErrorBlocks).toBe(0);
      expect(summary.totalErrors).toBe(0);
    });

    test('mixed results with parse errors', () => {
      const source = `-- Comment

good : Type -> Type
good x = x

bad parse @#$%

good2 : Type -> Type
good2 x = x`;

      const results = compileSource(source);
      const summary = summarizeResults(results);

      expect(summary.totalBlocks).toBe(4);
      expect(summary.commentBlocks).toBe(1);
      expect(summary.successfulBlocks).toBe(3);
      expect(summary.parseErrorBlocks).toBe(1);
      expect(summary.checkErrorBlocks).toBe(0);
      expect(summary.totalErrors).toBeGreaterThanOrEqual(1);
    });
  });

  describe('Integration', () => {
    test('real-world example', () => {
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
      expect(results.length).toBe(3);
      expect(results[0].blockType).toBe('Inductive');
      expect(results[0].name).toBe('Nat');
      expect(results[1].blockType).toBe('Term');
      expect(results[1].name).toBe('id');
      expect(results[2].blockType).toBe('Term');
      expect(results[2].name).toBe('const');

      const summary = summarizeResults(results);
      expect(summary.successfulBlocks).toBe(3);
      expect(summary.totalErrors).toBe(0);
    });
  });

  describe('Inductive Type Validity Errors', () => {
    test('undefined symbol in constructor type', () => {
      const source = `inductive Bad : Type where
  | mk : (Bad -> Undefined) -> Bad`;

      const results = compileSource(source);

      expect(results.length).toBe(1);
      expect(results[0].parseSuccess).toBe(true);
      expect(results[0].checkSuccess).toBe(false);
      expect(results[0].checkErrors.length).toBeGreaterThan(0);
    });
  });

  describe('Parameter/Index Inference', () => {
    test('inductive with no params (Nat)', () => {
      const source = `inductive Nat : Type where
  | Zero : Nat
  | Succ : Nat -> Nat`;

      const results = compileSource(source);

      expect(results.length).toBe(1);
      expect(results[0].checkSuccess).toBe(true);
      // Nat has no type parameters
      expect(
        results[0].indexPositions === undefined || results[0].indexPositions.length === 0
      ).toBe(true);
    });

    test('inductive with param (List)', () => {
      const source = `inductive List : Type -> Type where
  | nil : (A : Type) -> List A
  | cons : (A : Type) -> A -> List A -> List A`;

      const results = compileSource(source);

      expect(results.length).toBe(1);
      expect(results[0].checkSuccess).toBe(true);
      // List has position 0 as parameter (not index)
      expect(results[0].indexPositions).toBeDefined();
      expect(results[0].indexPositions!.includes(0)).toBe(false);
    });

    test('inductive with param and index (Vec)', () => {
      const source = `inductive Nat : Type where
  | Zero : Nat
  | Succ : Nat -> Nat

inductive Vec : Type -> Nat -> Type where
  | nil : (A : Type) -> Vec A Zero
  | cons : (A : Type) -> (n : Nat) -> A -> Vec A n -> Vec A (Succ n)`;

      const results = compileSource(source);

      expect(results.length).toBe(2);
      expect(results[0].checkSuccess).toBe(true);
      expect(results[1].checkSuccess).toBe(true);
      expect(results[1].indexPositions).toBeDefined();

      // Position 0 (A) is a parameter, position 1 (n) is an index
      expect(results[1].indexPositions!.includes(0)).toBe(false);
      expect(results[1].indexPositions!.includes(1)).toBe(true);
    });
  });

  describe('Structural Recursion', () => {
    test('safe structural recursion (plus)', () => {
      const source = `inductive Nat : Type where
  | Zero : Nat
  | Succ : Nat -> Nat

plus : Nat -> Nat -> Nat
plus Zero b = b
plus (Succ a) b = Succ (plus a b)`;

      const results = compileSource(source);

      expect(results.length).toBe(2);
      expect(results[0].checkSuccess).toBe(true);
      expect(results[1].checkSuccess).toBe(true);
    });

    test('unsafe recursion - same argument', () => {
      const source = `inductive Nat : Type where
  | Zero : Nat
  | Succ : Nat -> Nat

plus : Nat -> Nat -> Nat
plus Zero b = b
plus (Succ a) b = Succ (plus (Succ a) b)`;

      const results = compileSource(source);

      expect(results.length).toBe(2);
      expect(results[0].checkSuccess).toBe(true);
      expect(results[1].checkSuccess).toBe(false);
      expect(results[1].checkErrors.length).toBeGreaterThan(0);
      expect(
        results[1].checkErrors.some(e =>
          e.message.toLowerCase().includes('recursion') ||
          e.message.toLowerCase().includes('recursive')
        )
      ).toBe(true);
    });

    test('unsafe recursion - non-decreasing argument', () => {
      const source = `inductive Nat : Type where
  | Zero : Nat
  | Succ : Nat -> Nat

bad : Nat -> Nat
bad Zero = Zero
bad (Succ n) = bad (Succ (Succ n))`;

      const results = compileSource(source);

      expect(results.length).toBe(2);
      expect(results[0].checkSuccess).toBe(true);
      expect(results[1].checkSuccess).toBe(false);
      expect(results[1].checkErrors.length).toBeGreaterThan(0);
    });

    test('non-recursive function passes', () => {
      const source = `inductive Nat : Type where
  | Zero : Nat
  | Succ : Nat -> Nat

isZero : Nat -> Nat
isZero Zero = Zero
isZero (Succ n) = Zero`;

      const results = compileSource(source);

      expect(results.length).toBe(2);
      expect(results[0].checkSuccess).toBe(true);
      expect(results[1].checkSuccess).toBe(true);
    });
  });
});
