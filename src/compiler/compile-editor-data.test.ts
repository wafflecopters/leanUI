import { describe, expect, test } from 'vitest';
import {
  extractDirectiveTokens,
  extractHoleLocations,
} from './compile-editor-data';

describe('compile-editor-data', () => {
  test('extractDirectiveTokens highlights directives, values, and @becomes', () => {
    const source = `@assumeK false
@syntax plus @becomes "+"
-- @test success`;

    const tokens = extractDirectiveTokens(source);

    expect(tokens).toEqual(expect.arrayContaining([
      expect.objectContaining({ line: 1, type: 'directive' }),
      expect.objectContaining({ line: 1, type: 'directiveValue' }),
      expect.objectContaining({ line: 2, type: 'directive' }),
      expect.objectContaining({ line: 2, type: 'directiveValue' }),
    ]));
    expect(tokens.some(token => token.line === 2 && token.length === '@becomes'.length)).toBe(true);
    expect(tokens.some(token => token.line === 3 && token.type === 'directive')).toBe(true);
  });

  test('extractHoleLocations skips wildcard holes and with auxiliaries', () => {
    const result = {
      blocks: [{
        declarations: [
          {
            sourceMap: new Map([
              ['value', {
                start: { line: 4, col: 10, pos: 30 },
                end: { line: 4, col: 16, pos: 36 },
              }],
              ['type', {
                start: { line: 3, col: 1, pos: 10 },
                end: { line: 3, col: 2, pos: 11 },
              }],
            ]),
            surfaceType: { tag: 'Hole', id: '_', type: { tag: 'Sort', level: { tag: 'ULit', n: 0 } } },
            surfaceValue: { tag: 'Hole', id: 'sorry', type: { tag: 'Sort', level: { tag: 'ULit', n: 0 } } },
          },
          {
            isWithAuxiliary: true,
            sourceMap: new Map([
              ['value', {
                start: { line: 6, col: 10, pos: 50 },
                end: { line: 6, col: 15, pos: 55 },
              }],
            ]),
            surfaceValue: { tag: 'Hole', id: 'aux', type: { tag: 'Sort', level: { tag: 'ULit', n: 0 } } },
          },
        ],
      }],
    } as any;

    expect(extractHoleLocations(result)).toEqual([
      { line: 4, column: 10, endColumn: 16, id: 'sorry' },
    ]);
  });
});
