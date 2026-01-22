/**
 * Unit tests for sourceMap adjustment during compilation
 * These tests verify that source positions remain valid after adjustments
 */

import { describe, test, expect } from 'vitest';
import { compileSource, TestBlockResult } from '../test-utils';
import { SourceRange, SourceMap } from '../types/source-position';

/**
 * Validate that a source range is valid for the given source text
 */
function validateRange(source: string, range: SourceRange, path: string): void {
  const lines = source.split('\n');

  // Check start position
  if (range.start.line < 1 || range.start.line > lines.length) {
    throw new Error(
      `Invalid range for path "${path}": start line ${range.start.line} out of bounds (1-${lines.length})`
    );
  }
  const startLineText = lines[range.start.line - 1];
  if (range.start.col < 1 || range.start.col > startLineText.length + 1) {
    throw new Error(
      `Invalid range for path "${path}": start col ${range.start.col} out of bounds (1-${startLineText.length + 1})\n` +
      `Line ${range.start.line}: "${startLineText}"`
    );
  }

  // Check end position
  if (range.end.line < 1 || range.end.line > lines.length) {
    throw new Error(
      `Invalid range for path "${path}": end line ${range.end.line} out of bounds (1-${lines.length})`
    );
  }
  const endLineText = lines[range.end.line - 1];
  if (range.end.col < 1 || range.end.col > endLineText.length + 1) {
    throw new Error(
      `Invalid range for path "${path}": end col ${range.end.col} out of bounds (1-${endLineText.length + 1})\n` +
      `Line ${range.end.line}: "${endLineText}"`
    );
  }
}

/**
 * Validate all ranges in a sourceMap against the full source
 */
function validateSourceMap(source: string, sourceMap: SourceMap): void {
  for (const [path, range] of sourceMap) {
    validateRange(source, range, path);
  }
}

/**
 * Get the compiled declarations with their source maps
 */
function compileAndValidate(source: string): TestBlockResult[] {
  const results = compileSource(source);
  for (const result of results) {
    for (const decl of result.declarations) {
      if (decl.sourceMap) {
        validateSourceMap(source, decl.sourceMap);
      }
    }
  }
  return results;
}

describe('SourceMap Adjustment Tests', () => {
  describe('Single block - no adjustment needed', () => {
    test('simple definition at line 1', () => {
      const source = 'x : Nat';
      const results = compileAndValidate(source);
      expect(results.length).toBe(1);
    });

    test('inductive type starting at line 1', () => {
      const source = `inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat`;
      const results = compileAndValidate(source);
      expect(results.length).toBe(1);
    });
  });

  describe('Multiple blocks - adjustment needed', () => {
    test('two definitions separated by blank line', () => {
      const source = `inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

x : Nat
x = Zero`;
      const results = compileAndValidate(source);
      expect(results.length).toBe(2);
    });

    test('three blocks with comments', () => {
      const source = `-- First block
inductive Bool : Type where
  True : Bool
  False : Bool

-- Second block
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

-- Third block
not : Bool -> Bool
not True = False
not False = True`;
      const results = compileAndValidate(source);
      // Comments are separate blocks, so we should have 3 declaration blocks
      expect(results.filter(r => r.name).length).toBeGreaterThanOrEqual(3);
    });
  });

  describe('Named arguments - the problematic case', () => {
    test('named parameter in type', () => {
      const source = `id : { A : Type } -> A -> A
id {A} x = x`;
      const results = compileAndValidate(source);
      expect(results.length).toBe(1);
      expect(results[0].checkSuccess).toBe(true);
    });

    test('inductive with named parameter - error case', () => {
      const source = `inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Vec : { A : Type } -> Nat -> Type where
  VNil : (A : Type) -> Vec A Zero`;

      const results = compileAndValidate(source);
      expect(results.length).toBe(2);

      // Vec should fail due to positional arg to named param
      const vecResult = results.find(r => r.name === 'Vec');
      expect(vecResult).toBeDefined();
      expect(vecResult!.checkSuccess).toBe(false);

      // The error should point to line 6 (VNil line)
      const vecDecl = vecResult!.declarations.find(d => d.name === 'Vec');
      if (vecDecl && vecDecl.checkErrors.length > 0 && vecDecl.sourceMap) {
        // Validate the error path points to valid source
        validateSourceMap(source, vecDecl.sourceMap);
      }
    });

    test('named argument application in second block', () => {
      const source = `id : { A : Type } -> A -> A
id {A} x = x

useId : { T : Type } -> T -> T
useId {T} x = id { A := T } x`;

      const results = compileAndValidate(source);
      expect(results.length).toBe(2);
      expect(results[0].checkSuccess).toBe(true);
      expect(results[1].checkSuccess).toBe(true);
    });
  });

  describe('Edge cases', () => {
    test('block starting after many blank lines', () => {
      const source = `


inductive Nat : Type where
  Zero : Nat`;
      const results = compileAndValidate(source);
      // Note: blank lines at start may or may not create a separate block
      expect(results.length).toBeGreaterThanOrEqual(1);
    });

    test('definition with long type signature', () => {
      const source = `compose : { A : Type } -> { B : Type } -> { C : Type } -> (B -> C) -> (A -> B) -> A -> C
compose {A} {B} {C} g f x = g (f x)`;
      const results = compileAndValidate(source);
      expect(results.length).toBe(1);
      expect(results[0].checkSuccess).toBe(true);
    });
  });
});

describe('Specific Range Validation', () => {
  test('error range points to correct expression', () => {
    const source = `inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Vec : { A : Type } -> Nat -> Type where
  VNil : (A : Type) -> Vec A Zero`;

    const results = compileSource(source);
    const vecResult = results.find(r => r.name === 'Vec');
    const vecDecl = vecResult?.declarations.find(d => d.name === 'Vec');

    if (vecDecl && vecDecl.elabErrorPath && vecDecl.sourceMap) {
      const errorRange = vecDecl.sourceMap.get(vecDecl.elabErrorPath);
      if (errorRange) {
        // Validate the error range
        validateRange(source, errorRange, vecDecl.elabErrorPath);

        // The error should be on line 6 (the VNil constructor line)
        const lines = source.split('\n');
        const errorLine = lines[errorRange.start.line - 1];
        expect(errorLine).toContain('Vec A Zero');
      }
    }
  });

  test('all sourceMap ranges are within source bounds', () => {
    const source = `inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

id : { A : Type } -> A -> A
id {A} x = x

const : { A : Type } -> { B : Type } -> A -> B -> A
const {A} {B} a b = a`;

    const results = compileSource(source);

    for (const result of results) {
      for (const decl of result.declarations) {
        if (decl.sourceMap) {
          for (const [path, range] of decl.sourceMap) {
            // This should not throw
            validateRange(source, range, path);
          }
        }
      }
    }
  });
});
