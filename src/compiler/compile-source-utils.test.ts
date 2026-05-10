import { describe, expect, test } from 'vitest';
import {
  adjustSourceMapToAbsolute,
  computeCodeStartLine,
  lineToCharOffset,
  serializePathForLookup,
} from './compile-source-utils';

describe('compile-source-utils', () => {
  test('adjustSourceMapToAbsolute offsets lines and positions', () => {
    const sourceMap = new Map([
      ['type', {
        start: { line: 1, col: 3, pos: 2 },
        end: { line: 1, col: 6, pos: 5 },
      }],
    ]);

    const adjusted = adjustSourceMapToAbsolute(sourceMap, 4, 20);
    expect(adjusted.get('type')).toEqual({
      start: { line: 4, col: 3, pos: 22 },
      end: { line: 4, col: 6, pos: 25 },
    });
  });

  test('computeCodeStartLine skips comments, blanks, and directives', () => {
    expect(computeCodeStartLine([
      '',
      '-- comment',
      '@syntax foo',
      'term : Type',
    ], 10)).toBe(13);
  });

  test('lineToCharOffset returns the start of the requested 1-based line', () => {
    const source = 'alpha\nbeta\ngamma';
    expect(lineToCharOffset(source, 1)).toBe(0);
    expect(lineToCharOffset(source, 2)).toBe(6);
    expect(lineToCharOffset(source, 3)).toBe(11);
    expect(lineToCharOffset(source, 5)).toBe(source.length);
  });

  test('serializePathForLookup matches sourceMap path formatting', () => {
    expect(serializePathForLookup(['value', 'clauses', 1, 'rhs'])).toBe('value.clauses[1].rhs');
  });
});
