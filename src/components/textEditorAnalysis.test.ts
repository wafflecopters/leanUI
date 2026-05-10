import { beforeEach, describe, expect, test, vi } from 'vitest';
import { deriveTextEditorAnalysis } from './textEditorAnalysis';

const {
  collectCompiledDeclEntries,
  collectAllCompiledDeclarations,
  getTypeInfoAtCursor,
  extractWildcardInlayHints,
  extractSemanticTokens,
  extractHoleLocations,
} = vi.hoisted(() => ({
  collectCompiledDeclEntries: vi.fn(),
  collectAllCompiledDeclarations: vi.fn(),
  getTypeInfoAtCursor: vi.fn(),
  extractWildcardInlayHints: vi.fn(),
  extractSemanticTokens: vi.fn(),
  extractHoleLocations: vi.fn(),
}));

vi.mock('./textEditorModel', () => ({
  collectCompiledDeclEntries,
  collectAllCompiledDeclarations,
  getTypeInfoAtCursor,
}));

vi.mock('../compiler/compile', () => ({
  extractWildcardInlayHints,
  extractSemanticTokens,
  extractHoleLocations,
}));

describe('textEditorAnalysis', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  test('coalesces declaration-derived editor state when declarations are enabled', () => {
    const compileResult = { blocks: [] } as any;
    const cursorInfo = { lineNumber: 3, column: 8 } as any;
    const entries = [
      { decl: { name: 'foo' }, blockSource: 'foo : Nat', blockStartLine: 1 },
      { decl: { name: 'bar' }, blockSource: 'bar : Nat', blockStartLine: 5 },
    ];
    const allDeclarations = [{ name: 'foo' }, { name: 'bar' }, { name: 'aux' }];
    const wildcardHints = [{ line: 2, column: 4, name: 'x' }];
    const semanticTokens = [{ line: 1, column: 1, length: 3, type: 'termName' }];
    const holeLocations = [{ line: 9, column: 2, endColumn: 3, id: '?hole' }];
    const typeInfo = { kind: 'term', info: { prettyType: 'Nat', context: [], surfacePath: [] }, expression: 'foo' };

    collectCompiledDeclEntries.mockReturnValue(entries);
    collectAllCompiledDeclarations.mockReturnValue(allDeclarations);
    extractWildcardInlayHints.mockReturnValue(wildcardHints);
    extractSemanticTokens.mockReturnValue(semanticTokens);
    extractHoleLocations.mockReturnValue(holeLocations);
    getTypeInfoAtCursor.mockReturnValue(typeInfo);

    expect(deriveTextEditorAnalysis({
      compileResult,
      code: 'foo\nbar',
      showDeclarations: true,
      cursorInfo,
    })).toEqual({
      compiledDeclsWithSource: entries,
      compiledDeclarations: [{ name: 'foo' }, { name: 'bar' }],
      declarationSources: ['foo : Nat', 'bar : Nat'],
      allCompiledDeclarations: allDeclarations,
      wildcardHints,
      semanticTokens,
      holeLocations,
      typeInfoAtCursor: typeInfo,
    });

    expect(collectCompiledDeclEntries).toHaveBeenCalledWith(compileResult, true);
    expect(collectAllCompiledDeclarations).toHaveBeenCalledWith(compileResult, true);
    expect(extractWildcardInlayHints).toHaveBeenCalledWith(compileResult);
    expect(extractSemanticTokens).toHaveBeenCalledWith(compileResult, 'foo\nbar');
    expect(extractHoleLocations).toHaveBeenCalledWith(compileResult);
    expect(getTypeInfoAtCursor).toHaveBeenCalledWith(cursorInfo, compileResult, 'foo\nbar');
  });

  test('still derives non-declaration data when declaration panels are disabled', () => {
    const compileResult = { blocks: [] } as any;

    collectCompiledDeclEntries.mockReturnValue([]);
    collectAllCompiledDeclarations.mockReturnValue([]);
    extractWildcardInlayHints.mockReturnValue([{ line: 1, column: 1, name: 'implicit' }]);
    extractSemanticTokens.mockReturnValue([{ line: 2, column: 3, length: 1, type: 'constName' }]);
    extractHoleLocations.mockReturnValue([]);
    getTypeInfoAtCursor.mockReturnValue(undefined);

    const analysis = deriveTextEditorAnalysis({
      compileResult,
      code: 'x',
      showDeclarations: false,
      cursorInfo: null,
    });

    expect(analysis.compiledDeclsWithSource).toEqual([]);
    expect(analysis.compiledDeclarations).toEqual([]);
    expect(analysis.declarationSources).toEqual([]);
    expect(analysis.allCompiledDeclarations).toEqual([]);
    expect(analysis.wildcardHints).toEqual([{ line: 1, column: 1, name: 'implicit' }]);
    expect(analysis.semanticTokens).toEqual([{ line: 2, column: 3, length: 1, type: 'constName' }]);
    expect(analysis.typeInfoAtCursor).toBeUndefined();
    expect(collectCompiledDeclEntries).toHaveBeenCalledWith(compileResult, false);
    expect(collectAllCompiledDeclarations).toHaveBeenCalledWith(compileResult, false);
  });
});
