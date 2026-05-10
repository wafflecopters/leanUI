import { beforeEach, describe, expect, test, vi } from 'vitest';
import {
  applyCompileMarkers,
  compileTextEditorCode,
  syncCompilerProviderState,
} from './textEditorCompiler';

const { compileIncrementalTT, buildCompileMarkers } = vi.hoisted(() => ({
  compileIncrementalTT: vi.fn(),
  buildCompileMarkers: vi.fn(),
}));

vi.mock('../compiler/compile', () => ({
  compileIncrementalTT,
}));

vi.mock('./textEditorDiagnostics', () => ({
  buildCompileMarkers,
}));

describe('textEditorCompiler', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  test('compileTextEditorCode delegates to incremental compilation with the provided cache', () => {
    const cache = { cache: true } as any;
    const result = { success: true };
    compileIncrementalTT.mockReturnValue(result);

    expect(compileTextEditorCode('foo = Zero', cache)).toBe(result);
    expect(compileIncrementalTT).toHaveBeenCalledWith('foo = Zero', cache);
  });

  test('syncCompilerProviderState updates refs and fires semantic token refresh events', () => {
    const wildcardHintsRef = { current: [] as any[] };
    const semanticTokensRef = { current: [] as any[] };
    const fire = vi.fn();

    syncCompilerProviderState({
      wildcardHintsRef,
      semanticTokensRef,
      semanticTokensEventControllerRef: { current: { fire } },
      wildcardHints: [{ line: 1, column: 2, name: 'x' }] as any,
      semanticTokens: [{ line: 3, column: 4, length: 1, type: 'termName' }] as any,
    });

    expect(wildcardHintsRef.current).toEqual([{ line: 1, column: 2, name: 'x' }]);
    expect(semanticTokensRef.current).toEqual([{ line: 3, column: 4, length: 1, type: 'termName' }]);
    expect(fire).toHaveBeenCalledTimes(1);
  });

  test('applyCompileMarkers maps severities to Monaco marker severities', () => {
    buildCompileMarkers.mockReturnValue([
      {
        severity: 'warning',
        message: 'hole',
        startLineNumber: 1,
        startColumn: 2,
        endLineNumber: 1,
        endColumn: 3,
        source: 'TT Holes',
      },
      {
        severity: 'error',
        message: 'bad term',
        startLineNumber: 4,
        startColumn: 1,
        endLineNumber: 4,
        endColumn: 5,
        source: 'TT Type Checker',
      },
    ]);

    const setModelMarkers = vi.fn();
    const model = {
      getLineContent: (lineNumber: number) => lineNumber === 1 ? '?x' : 'bad',
    } as any;

    applyCompileMarkers({
      monaco: {
        MarkerSeverity: { Warning: 17, Error: 99 },
        editor: { setModelMarkers },
      },
      model,
      compileResult: {} as any,
      holeLocations: [],
    });

    expect(setModelMarkers).toHaveBeenCalledWith(model, 'tt-compiler', [
      expect.objectContaining({ severity: 17, message: 'hole' }),
      expect.objectContaining({ severity: 99, message: 'bad term' }),
    ]);
  });
});
