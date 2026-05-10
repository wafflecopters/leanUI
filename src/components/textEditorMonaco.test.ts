import { describe, expect, test } from 'vitest';
import { findUnicodeAbbreviationReplacement, toCursorInfo } from './textEditorMonaco';

describe('textEditorMonaco', () => {
  test('findUnicodeAbbreviationReplacement prefers the longest matching suffix', () => {
    expect(findUnicodeAbbreviationReplacement('foo \\rightarrow', 16)).toEqual({
      startColumn: 5,
      endColumn: 16,
      text: '→',
    });
  });

  test('findUnicodeAbbreviationReplacement returns null when there is no suffix match', () => {
    expect(findUnicodeAbbreviationReplacement('foo \\nope', 10)).toBeNull();
  });

  test('toCursorInfo normalizes selection payloads for the editor state', () => {
    expect(toCursorInfo({
      positionLineNumber: 3,
      positionColumn: 7,
      startLineNumber: 3,
      startColumn: 2,
      endLineNumber: 4,
      endColumn: 5,
    })).toEqual({
      lineNumber: 3,
      column: 7,
      selStartLine: 3,
      selStartCol: 2,
      selEndLine: 4,
      selEndCol: 5,
    });
  });
});
