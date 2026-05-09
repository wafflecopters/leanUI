import { describe, expect, test } from 'vitest';
import { deserializeIndexPath } from '../types/source-position';
import { buildCompileMarkers } from './textEditorDiagnostics';

describe('textEditorDiagnostics', () => {
  test('strips parser prefixes and clamps parser end columns to line length', () => {
    const markers = buildCompileMarkers(
      {
        blocks: [{
          parseErrors: [{
            line: 2,
            col: 5,
            message: 'Parse error at line 2, col 5: unexpected token',
          }],
          nameResolutionErrors: [],
          declarations: [],
        }],
      } as any,
      [],
      {
        getLineContent: (lineNumber) => (lineNumber === 2 ? 'abc' : ''),
      }
    );

    expect(markers).toEqual([{
      severity: 'error',
      message: 'unexpected token',
      startLineNumber: 2,
      startColumn: 5,
      endLineNumber: 2,
      endColumn: 6,
      source: 'TT Parser',
    }]);
  });

  test('maps name-resolution errors to exact declaration source ranges and falls back to block line', () => {
    const markers = buildCompileMarkers(
      {
        blocks: [{
          parseErrors: [],
          codeStartLine: 9,
          nameResolutionErrors: [
            { message: 'unknown x', path: 'value', declarationIndex: 0 },
            { message: 'fallback name error' },
          ],
          declarations: [{
            sourceMap: new Map([['value', {
              start: { line: 4, col: 3 },
              end: { line: 4, col: 8 },
            }]]),
          }],
        }],
      } as any,
      [],
      {
        getLineContent: (lineNumber) => (lineNumber === 9 ? 'fallback line' : ''),
      }
    );

    expect(markers).toEqual([
      {
        severity: 'error',
        message: 'unknown x',
        startLineNumber: 4,
        startColumn: 3,
        endLineNumber: 4,
        endColumn: 8,
        source: 'TT Name Resolution',
      },
      {
        severity: 'error',
        message: 'fallback name error',
        startLineNumber: 9,
        startColumn: 1,
        endLineNumber: 9,
        endColumn: 14,
        source: 'TT Name Resolution',
      },
    ]);
  });

  test('maps check errors through declaration elab maps and preserves warning severity', () => {
    const markers = buildCompileMarkers(
      {
        blocks: [{
          parseErrors: [],
          nameResolutionErrors: [],
          codeStartLine: 3,
          declarations: [{
            checkErrors: [{
              message: 'bad application',
              severity: 'warning',
              env: { indexPath: deserializeIndexPath('type.body.body.body.domain.fn.arg.arg') },
            }],
            elabMap: new Map([
              ['type.body.body.body.domain.fn', 'type.body.body.domain.fn'],
            ]),
            sourceMap: new Map([
              ['type.body.body.domain.fn.arg.arg', {
                start: { line: 7, col: 2 },
                end: { line: 7, col: 11 },
              }],
            ]),
          }],
        }],
      } as any,
      [],
      { getLineContent: () => '' }
    );

    expect(markers).toEqual([{
      severity: 'warning',
      message: 'bad application',
      startLineNumber: 7,
      startColumn: 2,
      endLineNumber: 7,
      endColumn: 11,
      source: 'TT Type Checker',
    }]);
  });

  test('maps promoted with-clause errors through withClauseElabMap instead of direct sourceMap lookup', () => {
    const markers = buildCompileMarkers(
      {
        blocks: [{
          parseErrors: [],
          nameResolutionErrors: [],
          codeStartLine: 20,
          declarations: [{
            checkErrors: [],
            sourceMap: new Map([
              ['value.clauses[0].rhs', {
                start: { line: 40, col: 1 },
                end: { line: 40, col: 5 },
              }],
              ['value.clauses[1].rhs', {
                start: { line: 41, col: 3 },
                end: { line: 41, col: 9 },
              }],
            ]),
            withClauseElabMap: new Map([
              ['value.clauses[0].rhs', 'value.clauses[1].rhs'],
            ]),
            withClauseErrors: [{
              message: 'with failure',
              env: { indexPath: deserializeIndexPath('value.clauses[0].rhs') },
            }],
          }],
        }],
      } as any,
      [],
      { getLineContent: () => '' }
    );

    expect(markers).toEqual([{
      severity: 'error',
      message: 'with failure',
      startLineNumber: 41,
      startColumn: 3,
      endLineNumber: 41,
      endColumn: 9,
      source: 'TT Type Checker',
    }]);
  });

  test('adds hole warnings after compiler errors', () => {
    const markers = buildCompileMarkers(
      {
        blocks: [{
          parseErrors: [],
          nameResolutionErrors: [],
          declarations: [],
        }],
      } as any,
      [{
        line: 12,
        column: 7,
        endColumn: 8,
        id: '?hole',
      }],
      { getLineContent: () => '' }
    );

    expect(markers).toEqual([{
      severity: 'warning',
      message: 'Holes are unsound.',
      startLineNumber: 12,
      startColumn: 7,
      endLineNumber: 12,
      endColumn: 8,
      source: 'TT Holes',
    }]);
  });
});
