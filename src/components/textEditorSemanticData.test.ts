import { describe, expect, test } from 'vitest';
import {
  buildWildcardInlayHintData,
  encodeSemanticTokensForMonaco,
  TEXT_EDITOR_SEMANTIC_TOKEN_TYPES,
} from './textEditorSemanticData';

describe('textEditorSemanticData', () => {
  test('buildWildcardInlayHintData filters to requested visible line range', () => {
    const hints = [
      { line: 1, column: 3, name: 'a' },
      { line: 3, column: 5, name: 'b' },
      { line: 5, column: 7, name: 'c' },
    ];

    expect(buildWildcardInlayHintData(hints, { startLineNumber: 2, endLineNumber: 4 })).toEqual([
      { lineNumber: 3, column: 5, label: 'b' },
    ]);
  });

  test('encodeSemanticTokensForMonaco sorts tokens and delta-encodes positions', () => {
    const encoded = encodeSemanticTokensForMonaco(
      [
        { line: 3, column: 2, length: 4, type: 'constName' },
        { line: 1, column: 5, length: 2, type: 'termName' },
        { line: 3, column: 8, length: 1, type: 'patternVar' },
      ],
      {
        getLineCount: () => 4,
        getLineLength: () => 20,
      }
    );

    expect(Array.from(encoded)).toEqual([
      0, 4, 2, TEXT_EDITOR_SEMANTIC_TOKEN_TYPES.indexOf('termName'), 0,
      2, 1, 4, TEXT_EDITOR_SEMANTIC_TOKEN_TYPES.indexOf('constName'), 0,
      0, 6, 1, TEXT_EDITOR_SEMANTIC_TOKEN_TYPES.indexOf('patternVar'), 0,
    ]);
  });

  test('encodeSemanticTokensForMonaco clamps token length to line boundary', () => {
    const encoded = encodeSemanticTokensForMonaco(
      [{ line: 2, column: 4, length: 10, type: 'directive' }],
      {
        getLineCount: () => 3,
        getLineLength: (lineNumber) => (lineNumber === 2 ? 6 : 0),
      }
    );

    expect(Array.from(encoded)).toEqual([
      1, 3, 3, TEXT_EDITOR_SEMANTIC_TOKEN_TYPES.indexOf('directive'), 0,
    ]);
  });

  test('encodeSemanticTokensForMonaco skips tokens on invalid or empty lines', () => {
    const encoded = encodeSemanticTokensForMonaco(
      [
        { line: 0, column: 1, length: 1, type: 'termName' },
        { line: 2, column: 1, length: 1, type: 'constName' },
        { line: 3, column: 6, length: 1, type: 'patternVar' },
        { line: 4, column: 1, length: 1, type: 'absurd' },
      ],
      {
        getLineCount: () => 3,
        getLineLength: (lineNumber) => (lineNumber === 2 ? 0 : 5),
      }
    );

    expect(Array.from(encoded)).toEqual([]);
  });
});
