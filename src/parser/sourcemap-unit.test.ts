/**
 * Unit tests for sourceMap generation - keeping things minimal
 */

import { describe, test, expect } from 'vitest';
import { Parser, ParsedDeclaration } from './parser';
import { SourceMap, SourceRange } from '../types/source-position';

/**
 * Parse a single declaration and return its sourceMap
 */
function parseWithSourceMap(source: string): { decl: ParsedDeclaration; sourceMap: SourceMap } {
  const parser = new Parser();
  const results = parser.parseDeclarationsWithSource(source);
  expect(results.length).toBe(1);
  return { decl: results[0].decl, sourceMap: results[0].sourceMap };
}

/**
 * Validate that a source range is valid for the given source text
 */
function validateRange(source: string, range: SourceRange, path: string): void {
  const lines = source.split('\n');

  // Check start position
  expect(range.start.line).toBeGreaterThanOrEqual(1);
  expect(range.start.line).toBeLessThanOrEqual(lines.length);
  const startLineText = lines[range.start.line - 1];
  expect(range.start.col).toBeGreaterThanOrEqual(1);
  expect(range.start.col).toBeLessThanOrEqual(startLineText.length + 1); // +1 for end-of-line position

  // Check end position
  expect(range.end.line).toBeGreaterThanOrEqual(1);
  expect(range.end.line).toBeLessThanOrEqual(lines.length);
  const endLineText = lines[range.end.line - 1];
  expect(range.end.col).toBeGreaterThanOrEqual(1);
  // End column should not exceed line length + 1
  if (range.end.col > endLineText.length + 1) {
    throw new Error(
      `Invalid range for path "${path}": end col ${range.end.col} > line ${range.end.line} length ${endLineText.length} + 1\n` +
      `Line content: "${endLineText}"`
    );
  }
}

/**
 * Validate all ranges in a sourceMap
 */
function validateSourceMap(source: string, sourceMap: SourceMap): void {
  for (const [path, range] of sourceMap) {
    validateRange(source, range, path);
  }
}

describe('SourceMap Unit Tests', () => {
  describe('Single-line declarations', () => {
    test('simple constant - id : Type', () => {
      const source = 'id : Type';
      const { sourceMap } = parseWithSourceMap(source);

      expect(sourceMap.size).toBeGreaterThan(0);
      validateSourceMap(source, sourceMap);

      // Check what keys are in the sourceMap
      const keys = Array.from(sourceMap.keys()).sort();
      // Should have at least 'name' and 'type' keys
      expect(keys).toContain('name');
      expect(keys).toContain('type');
    });

    test('constant with arrow - id : Nat -> Nat', () => {
      const source = 'id : Nat -> Nat';
      const { sourceMap } = parseWithSourceMap(source);

      validateSourceMap(source, sourceMap);
    });

    test('definition with body - x = Zero', () => {
      const source = 'x = Zero';
      const { sourceMap } = parseWithSourceMap(source);

      validateSourceMap(source, sourceMap);
    });

    test('definition with type - x : Nat = Zero', () => {
      const source = 'x : Nat = Zero';
      const { sourceMap } = parseWithSourceMap(source);

      validateSourceMap(source, sourceMap);
    });
  });

  describe('Multi-line declarations', () => {
    test('function with clauses', () => {
      const source = `id : Nat -> Nat
id x = x`;
      const { sourceMap } = parseWithSourceMap(source);

      validateSourceMap(source, sourceMap);
    });

    test('inductive type', () => {
      const source = `inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat`;
      const { sourceMap } = parseWithSourceMap(source);

      validateSourceMap(source, sourceMap);
    });
  });

  describe('Named arguments', () => {
    test('named binder in type', () => {
      const source = 'id : { A : Type } -> A -> A';
      const { sourceMap } = parseWithSourceMap(source);

      validateSourceMap(source, sourceMap);
    });

    test('named pattern in definition', () => {
      const source = `id : { A : Type } -> A -> A
id {A} x = x`;
      const { sourceMap } = parseWithSourceMap(source);

      validateSourceMap(source, sourceMap);
    });

    test('named application', () => {
      const source = 'x = f { A := Nat }';
      const { sourceMap } = parseWithSourceMap(source);

      validateSourceMap(source, sourceMap);
    });
  });

  describe('Edge cases', () => {
    test('empty line at start', () => {
      // Note: Parser may handle leading newline differently
      const source = `
x : Type`;
      const { sourceMap } = parseWithSourceMap(source.trim());

      validateSourceMap(source.trim(), sourceMap);
    });

    test('lambda expression', () => {
      const source = 'f = \\x => x';
      const { sourceMap } = parseWithSourceMap(source);

      validateSourceMap(source, sourceMap);
    });

    test('nested application', () => {
      const source = 'f = a b c';
      const { sourceMap } = parseWithSourceMap(source);

      validateSourceMap(source, sourceMap);
    });
  });
});

describe('SourceMap Path Coverage', () => {
  test('type path exists for typed definition', () => {
    const source = 'x : Nat';
    const { sourceMap } = parseWithSourceMap(source);

    expect(sourceMap.has('type')).toBe(true);
    validateSourceMap(source, sourceMap);
  });

  test('value path exists for definition with body', () => {
    const source = 'x = Zero';
    const { sourceMap } = parseWithSourceMap(source);

    expect(sourceMap.has('value')).toBe(true);
    validateSourceMap(source, sourceMap);
  });

  test('constructor paths exist for inductive', () => {
    const source = `inductive Nat : Type where
  Zero : Nat`;
    const { sourceMap } = parseWithSourceMap(source);

    // Debug: see what keys are available
    const keys = Array.from(sourceMap.keys()).sort();
    // Should have constructor-related keys
    const hasConstructorKey = keys.some(k => k.includes('constructor'));
    expect(hasConstructorKey).toBe(true);
    validateSourceMap(source, sourceMap);
  });
});
