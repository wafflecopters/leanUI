import { describe, expect, test } from 'vitest';
import {
  extractParamIndexInfo,
  getCompileResultsErrorCount,
  getDeclarationStatusSummary,
} from './textEditorResultsModel';

describe('textEditorResultsModel', () => {
  test('sums compile errors across parse, name, and check phases', () => {
    expect(getCompileResultsErrorCount({
      totalParseErrors: 2,
      totalNameErrors: 1,
      totalCheckErrors: 3,
    } as any)).toBe(6);
  });

  test('extracts parameter and index annotations from Pi binders', () => {
    const info = extractParamIndexInfo({
      tag: 'Binder',
      binderKind: { tag: 'BPi' },
      name: 'A',
      domain: { tag: 'Const', name: 'Type' },
      body: {
        tag: 'Binder',
        binderKind: { tag: 'BPi' },
        name: 'n',
        domain: { tag: 'Const', name: 'Nat' },
        body: { tag: 'Const', name: 'Vec' },
      },
    } as any, [1]);

    expect(info).toEqual([
      { name: 'A', type: 'Type', isIndex: false },
      { name: 'n', type: 'Nat', isIndex: true },
    ]);
  });

  test('formats success, warning-only, and mixed failure summaries', () => {
    expect(getDeclarationStatusSummary({
      checkSuccess: true,
      checkErrors: [],
    } as any)).toEqual({ kind: 'success', text: 'OK' });

    expect(getDeclarationStatusSummary({
      checkSuccess: false,
      checkErrors: [{ severity: 'warning', message: 'careful' }],
    } as any)).toEqual({ kind: 'warning', text: '1 warning' });

    expect(getDeclarationStatusSummary({
      checkSuccess: false,
      checkErrors: [
        { severity: 'error', message: 'bad' },
        { severity: 'error', message: 'worse' },
        { severity: 'warning', message: 'careful' },
      ],
    } as any)).toEqual({ kind: 'error', text: '2 errors, 1 warning' });
  });
});
