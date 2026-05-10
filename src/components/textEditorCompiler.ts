import type { editor as MonacoEditor } from 'monaco-editor';
import {
  compileIncrementalTT,
  type CompileResult,
  type HoleLocation,
  type SemanticToken,
  type WildcardInlayHint,
} from '../compiler/compile';
import type { IncrementalCache } from '../compiler/incremental';
import { buildCompileMarkers } from './textEditorDiagnostics';

export interface SemanticTokensEventControllerRef {
  current: { fire: () => void } | null;
}

export interface MutableRef<T> {
  current: T;
}

export function compileTextEditorCode(code: string, cache: IncrementalCache): CompileResult {
  return compileIncrementalTT(code, cache);
}

export function syncCompilerProviderState(options: {
  wildcardHintsRef: MutableRef<WildcardInlayHint[]>;
  semanticTokensRef: MutableRef<SemanticToken[]>;
  semanticTokensEventControllerRef: SemanticTokensEventControllerRef;
  wildcardHints: WildcardInlayHint[];
  semanticTokens: SemanticToken[];
}): void {
  const {
    wildcardHintsRef,
    semanticTokensRef,
    semanticTokensEventControllerRef,
    wildcardHints,
    semanticTokens,
  } = options;

  wildcardHintsRef.current = wildcardHints;
  semanticTokensRef.current = semanticTokens;
  semanticTokensEventControllerRef.current?.fire();
}

export function applyCompileMarkers(options: {
  monaco: {
    MarkerSeverity: { Warning: number; Error: number };
    editor: {
      setModelMarkers: (
        model: MonacoEditor.ITextModel,
        owner: string,
        markers: MonacoEditor.IMarkerData[]
      ) => void;
    };
  };
  model: MonacoEditor.ITextModel;
  compileResult: CompileResult;
  holeLocations: HoleLocation[];
}): void {
  const { monaco, model, compileResult, holeLocations } = options;

  const markers: MonacoEditor.IMarkerData[] = buildCompileMarkers(
    compileResult,
    holeLocations,
    { getLineContent: (lineNumber) => model.getLineContent(lineNumber) }
  ).map(marker => ({
    ...marker,
    severity: marker.severity === 'warning'
      ? monaco.MarkerSeverity.Warning
      : monaco.MarkerSeverity.Error,
  }));

  monaco.editor.setModelMarkers(model, 'tt-compiler', markers);
}
