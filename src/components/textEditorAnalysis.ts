import {
  extractHoleLocations,
  extractSemanticTokens,
  extractWildcardInlayHints,
  type CompileResult,
  type CompiledDeclaration,
} from '../compiler/compile';
import {
  collectAllCompiledDeclarations,
  collectCompiledDeclEntries,
  getTypeInfoAtCursor,
  type CompiledDeclEntry,
  type CursorInfoAtPosition,
  type EditorCursorInfo,
} from './textEditorModel';

export interface TextEditorAnalysis {
  compiledDeclsWithSource: CompiledDeclEntry[];
  compiledDeclarations: CompiledDeclaration[];
  declarationSources: string[];
  allCompiledDeclarations: CompiledDeclaration[];
  wildcardHints: ReturnType<typeof extractWildcardInlayHints>;
  semanticTokens: ReturnType<typeof extractSemanticTokens>;
  holeLocations: ReturnType<typeof extractHoleLocations>;
  typeInfoAtCursor: CursorInfoAtPosition | undefined;
}

export interface DeriveTextEditorAnalysisOptions {
  compileResult: CompileResult;
  code: string;
  showDeclarations: boolean;
  cursorInfo: EditorCursorInfo | null;
}

export function deriveTextEditorAnalysis({
  compileResult,
  code,
  showDeclarations,
  cursorInfo,
}: DeriveTextEditorAnalysisOptions): TextEditorAnalysis {
  const compiledDeclsWithSource = collectCompiledDeclEntries(compileResult, showDeclarations);
  const compiledDeclarations = compiledDeclsWithSource.map(entry => entry.decl);
  const declarationSources = compiledDeclsWithSource.map(entry => entry.blockSource);

  return {
    compiledDeclsWithSource,
    compiledDeclarations,
    declarationSources,
    allCompiledDeclarations: collectAllCompiledDeclarations(compileResult, showDeclarations),
    wildcardHints: extractWildcardInlayHints(compileResult),
    semanticTokens: extractSemanticTokens(compileResult, code),
    holeLocations: extractHoleLocations(compileResult),
    typeInfoAtCursor: getTypeInfoAtCursor(cursorInfo, compileResult, code),
  };
}
