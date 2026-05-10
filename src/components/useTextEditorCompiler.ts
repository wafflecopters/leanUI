import { useCallback, useEffect, useMemo, useRef, useState } from 'react';
import type { OnMount } from '@monaco-editor/react';
import type { CompileResult, SemanticToken, WildcardInlayHint } from '../compiler/compile';
import type { IncrementalCache } from '../compiler/incremental';
import { deriveTextEditorAnalysis } from './textEditorAnalysis';
import {
  applyCompileMarkers,
  compileTextEditorCode,
  syncCompilerProviderState,
} from './textEditorCompiler';
import {
  configureTextEditorMonaco,
  type IStandaloneCodeEditor,
  type Monaco,
  type SemanticTokensEventController,
} from './textEditorMonaco';
import type { EditorCursorInfo } from './textEditorModel';

export function useTextEditorCompiler(options: {
  code: string;
  showDeclarations: boolean;
  cursorInfo: EditorCursorInfo | null;
  incrementalCacheRef: React.MutableRefObject<IncrementalCache>;
  editorRef: React.MutableRefObject<IStandaloneCodeEditor | null>;
  monacoRef: React.MutableRefObject<Monaco | null>;
  setCursorInfo: React.Dispatch<React.SetStateAction<EditorCursorInfo | null>>;
}) {
  const {
    code,
    showDeclarations,
    cursorInfo,
    incrementalCacheRef,
    editorRef,
    monacoRef,
    setCursorInfo,
  } = options;

  const [compileResult, setCompileResult] = useState<CompileResult>(() => {
    return compileTextEditorCode(code, incrementalCacheRef.current);
  });

  const wildcardHintsRef = useRef<WildcardInlayHint[]>([]);
  const semanticTokensRef = useRef<SemanticToken[]>([]);
  const semanticTokensEventRef = useRef<SemanticTokensEventController | null>(null);

  useEffect(() => {
    const timerId = setTimeout(() => {
      setCompileResult(compileTextEditorCode(code, incrementalCacheRef.current));
    }, 300);
    return () => clearTimeout(timerId);
  }, [code, incrementalCacheRef]);

  const analysis = useMemo(
    () => deriveTextEditorAnalysis({
      compileResult,
      code,
      showDeclarations,
      cursorInfo,
    }),
    [compileResult, code, showDeclarations, cursorInfo]
  );

  useEffect(() => {
    syncCompilerProviderState({
      wildcardHintsRef,
      semanticTokensRef,
      semanticTokensEventControllerRef: semanticTokensEventRef,
      wildcardHints: analysis.wildcardHints,
      semanticTokens: analysis.semanticTokens,
    });
  }, [analysis.wildcardHints, analysis.semanticTokens]);

  useEffect(() => {
    const monaco = monacoRef.current;
    const editor = editorRef.current;
    if (!monaco || !editor) return;

    const model = editor.getModel();
    if (!model) return;

    applyCompileMarkers({
      monaco,
      model,
      compileResult,
      holeLocations: analysis.holeLocations,
    });
  }, [compileResult, analysis.holeLocations, editorRef, monacoRef]);

  const handleEditorDidMount: OnMount = useCallback((editor, monaco) => {
    editorRef.current = editor;
    monacoRef.current = monaco;
    configureTextEditorMonaco({
      monaco,
      editor,
      getWildcardHints: () => wildcardHintsRef.current,
      getSemanticTokens: () => semanticTokensRef.current,
      setCursorInfo,
      setSemanticTokensEventController: (controller) => {
        semanticTokensEventRef.current = controller;
      },
    });
  }, [editorRef, monacoRef, setCursorInfo]);

  return {
    compileResult,
    analysis,
    handleEditorDidMount,
  };
}
