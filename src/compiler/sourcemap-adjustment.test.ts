/**
 * Unit tests for sourceMap adjustment during compilation
 * These tests verify that source positions remain valid after adjustments
 */

import { describe, test, expect } from 'vitest';
import { compileSource, TestBlockResult } from '../test-utils';
import { compileTTFromText } from './compile';
import { SourceRange, SourceMap, serializeIndexPath } from '../types/source-position';

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

describe('@syntax annotation source map offset', () => {
  test('error range points to declaration line, not @syntax or comment line', () => {
    // Bug: when @syntax annotation precedes a declaration, error squiggly
    // appears on the comment/syntax line instead of the declaration line.
    const source = `inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

-- a comment about limitAdd
@syntax \\lim(f + g) = L + M
limitAdd : Nat -> Nat
limitAdd = Zero`;

    const results = compileSource(source);

    // Find the limitAdd declaration
    const limitAddResult = results.find(r => r.name === 'limitAdd');
    expect(limitAddResult).toBeDefined();

    const limitAddDecl = limitAddResult!.declarations.find(d => d.name === 'limitAdd');
    expect(limitAddDecl).toBeDefined();

    if (limitAddDecl?.sourceMap) {
      // The 'name' path in the sourceMap should point to line 7 (limitAdd : ...)
      // NOT line 5 (-- a comment) or line 6 (@syntax)
      const nameRange = limitAddDecl.sourceMap.get('name');
      expect(nameRange).toBeDefined();

      const lines = source.split('\n');
      // Line 7 is "limitAdd : Nat -> Nat"
      expect(lines[6]).toContain('limitAdd');
      expect(nameRange!.start.line).toBe(7);

      // Validate all ranges are within bounds
      validateSourceMap(source, limitAddDecl.sourceMap);
    }
  });

  test('codeStartLine with @syntax should point to declaration, not comment', () => {
    // The compiled block codeStartLine should be useful as a fallback error position.
    // When @syntax/comments are attached, startLine includes them,
    // but codeStartLine should point to the DECLARATION line, not the comment.
    const source = `inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

-- a comment about limitAdd
@syntax \\lim(f + g) = L + M
limitAdd : Nat -> Nat
limitAdd = Zero`;

    const fullResult = compileTTFromText(source);

    // Find the block containing limitAdd
    const limitAddBlock = fullResult.blocks.find(b =>
      b.declarations.some(d => d.name === 'limitAdd')
    );
    expect(limitAddBlock).toBeDefined();

    const lines = source.split('\n');
    const commentLine = 5; // "-- a comment about limitAdd"
    const syntaxLine = 6;  // "@syntax ..."
    const declLine = 7;    // "limitAdd : Nat -> Nat"

    expect(lines[commentLine - 1]).toContain('-- a comment');
    expect(lines[syntaxLine - 1]).toContain('@syntax');
    expect(lines[declLine - 1]).toContain('limitAdd');

    // block.startLine includes the comment (for block bounds / cursor detection)
    expect(limitAddBlock!.startLine).toBe(commentLine);

    // block.codeStartLine skips comments and @syntax lines (for error fallback)
    expect(limitAddBlock!.codeStartLine).toBe(declLine);
  });

  test('type-check error fallback with @syntax uses codeStartLine', () => {
    // Test that when a type-check error occurs and the source map lookup fails,
    // the fallback (codeStartLine) points to the declaration, not the comment/@syntax.
    const source = `inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Bool : Type where
  True : Bool
  False : Bool

-- wrong type for myFunc
@syntax \\text{bad}
myFunc : Nat -> Bool
myFunc = True`;

    const fullResult = compileTTFromText(source);

    // Find the block containing myFunc
    const myFuncBlock = fullResult.blocks.find(b =>
      b.declarations.some(d => d.name === 'myFunc')
    );
    expect(myFuncBlock).toBeDefined();

    const myFuncDecl = myFuncBlock!.declarations.find(d => d.name === 'myFunc');
    expect(myFuncDecl).toBeDefined();
    expect(myFuncDecl!.checkSuccess).toBe(false);

    // block.startLine includes the comment (line 9)
    // block.codeStartLine skips to the declaration (line 11)
    const lines = source.split('\n');
    const commentLineIdx = lines.findIndex(l => l.includes('-- wrong type'));
    const declLineIdx = lines.findIndex(l => l.startsWith('myFunc'));
    const commentLine = commentLineIdx + 1; // 1-based
    const declLine = declLineIdx + 1; // 1-based

    expect(myFuncBlock!.startLine).toBe(commentLine);
    expect(myFuncBlock!.codeStartLine).toBe(declLine);
    expect(myFuncBlock!.codeStartLine).toBeGreaterThan(myFuncBlock!.startLine);
  });

  test('tactic error with @syntax points to correct line', () => {
    const source = `inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Equal : {A : Type} -> A -> A -> Type where
  refl : {A : Type} -> {a : A} -> Equal a a

-- theorem about equality
@syntax \\text{bad proof}
badProof : Equal (Succ Zero) (Succ Zero) := by
  exact Zero`;

    const result = compileSource(source);

    // Find badProof
    const badProofResult = result.find(r => r.name === 'badProof');
    expect(badProofResult).toBeDefined();
    expect(badProofResult!.checkSuccess).toBe(false);

    const badProofDecl = badProofResult!.declarations.find(d => d.name === 'badProof');
    expect(badProofDecl).toBeDefined();

    if (badProofDecl?.sourceMap) {
      // The 'name' path should be on line 10 (badProof : Equal ...)
      const nameRange = badProofDecl.sourceMap.get('name');
      expect(nameRange).toBeDefined();

      const lines = source.split('\n');
      // Line 10 is "badProof : Equal (Succ Zero) (Succ Zero) := by"
      expect(lines[9]).toContain('badProof');
      expect(nameRange!.start.line).toBe(10);

      validateSourceMap(source, badProofDecl.sourceMap);
    }
  });

  test('declaration without @syntax has correct source map', () => {
    // Baseline: without @syntax, the source map should already be correct
    const source = `inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

-- a comment about limitAdd
limitAdd : Nat -> Nat
limitAdd = Zero`;

    const results = compileSource(source);
    const limitAddResult = results.find(r => r.name === 'limitAdd');
    expect(limitAddResult).toBeDefined();

    const limitAddDecl = limitAddResult!.declarations.find(d => d.name === 'limitAdd');
    expect(limitAddDecl).toBeDefined();

    if (limitAddDecl?.sourceMap) {
      const nameRange = limitAddDecl.sourceMap.get('name');
      expect(nameRange).toBeDefined();

      const lines = source.split('\n');
      // Line 6 is "limitAdd : Nat -> Nat"
      expect(lines[5]).toContain('limitAdd');
      expect(nameRange!.start.line).toBe(6);

      validateSourceMap(source, limitAddDecl.sourceMap);
    }
  });

  test('@syntax only (no comment) has correct source map', () => {
    const source = `inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

@syntax f + g
myAdd : Nat -> Nat -> Nat
myAdd x y = x`;

    const results = compileSource(source);
    const myAddResult = results.find(r => r.name === 'myAdd');
    expect(myAddResult).toBeDefined();

    const myAddDecl = myAddResult!.declarations.find(d => d.name === 'myAdd');
    expect(myAddDecl).toBeDefined();

    if (myAddDecl?.sourceMap) {
      const nameRange = myAddDecl.sourceMap.get('name');
      expect(nameRange).toBeDefined();

      const lines = source.split('\n');
      // Line 6 is "myAdd : Nat -> Nat -> Nat"
      expect(lines[5]).toContain('myAdd');
      expect(nameRange!.start.line).toBe(6);

      validateSourceMap(source, myAddDecl.sourceMap);
    }
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
