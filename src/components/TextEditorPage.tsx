/**
 * TextEditorPage - A page for editing code and viewing compilation results
 */
import React, { useRef, useMemo, useState, useCallback, useEffect } from 'react';
import { useSearchParams } from 'react-router-dom';
import Editor, { OnChange } from '@monaco-editor/react';
import { createIncrementalCache, IncrementalCache } from '../compiler/incremental';
import { WYSIWYGPanel } from './WYSIWYGPanel';
import { PRESETS } from '../presets';
import { TextEditorHeader } from './TextEditorHeader';
import { TextEditorResultsPanel } from './TextEditorResultsPanel';
import { TextEditorTypeInfoPanel } from './TextEditorTypeInfoPanel';
import { MONACO_WIDGET_STYLES, type IStandaloneCodeEditor, type Monaco } from './textEditorMonaco';
import {
  toggleWysiwygRouteState,
  withEditorParams,
  withPresetParam,
} from './textEditorUrlState';
import { useTextEditorCompiler } from './useTextEditorCompiler';
import {
  replaceDeclarationNameInSource,
  resolveInitialEditorCode,
  slugifyPresetName,
  type EditorCursorInfo,
} from './textEditorModel';

// Presets are imported from src/presets/

// Styles
const styles = {
  container: {
    height: '100vh',
    width: '100%',
    backgroundColor: '#0d1117',
    display: 'flex',
    flexDirection: 'column' as const,
    overflow: 'hidden',
  },
  mainContent: {
    flex: 1,
    display: 'flex',
    flexDirection: 'column' as const,
    overflow: 'hidden',
  },
  editorSection: {
    flex: 1,
    minHeight: 0,
    borderBottom: '1px solid #30363d',
    display: 'flex',
    flexDirection: 'column' as const,
  },
  sectionHeader: {
    padding: '8px 16px',
    fontSize: '11px',
    fontWeight: 600,
    color: '#8b949e',
    textTransform: 'uppercase' as const,
    letterSpacing: '0.5px',
    backgroundColor: '#161b22',
    borderBottom: '1px solid #30363d',
  },
  editorWrapper: {
    flex: 1,
    overflow: 'hidden',
  },
};


export function TextEditorPage() {
  const [searchParams, setSearchParams] = useSearchParams();
  const editorRef = useRef<IStandaloneCodeEditor | null>(null);
  const monacoRef = useRef<Monaco | null>(null);
  const [code, setCode] = useState(() => {
    return resolveInitialEditorCode(PRESETS, searchParams.get('preset'));
  });
  const [presetMenuOpen, setPresetMenuOpen] = useState(false);
  const [showWYSIWYG, setShowWYSIWYG] = useState(() => searchParams.get('editor') === 'true');
  const [expandedSymbol, setExpandedSymbol] = useState<string | null>(() => searchParams.get('symbol'));
  // Rendering options for pretty-printed output
  const [showNamedArgsWithLabels, setShowNamedArgsWithLabels] = useState(true);
  const [showNamedParamsWithBraces, setShowNamedParamsWithBraces] = useState(false);
  // Cursor position for type-at-cursor panel
  // Cursor/selection position for type-at-cursor panel
  const [cursorInfo, setCursorInfo] = useState<EditorCursorInfo | null>(null);
  // Incremental compilation cache (persists across renders)
  const incrementalCacheRef = useRef<IncrementalCache>(createIncrementalCache());

  // Set editor value imperatively (for external changes like preset loading).
  // This preserves cursor position better than feeding value back through React props.
  const setEditorValue = useCallback((newCode: string) => {
    setCode(newCode);
    const editor = editorRef.current;
    if (editor) {
      const model = editor.getModel();
      if (model && model.getValue() !== newCode) {
        model.setValue(newCode);
      }
    }
  }, []);

  // Helper function to load a preset and update URL
  const loadPreset = useCallback((presetName: string) => {
    const preset = PRESETS.find(p => p.name === presetName);
    if (preset) {
      setEditorValue(preset.code);
      setSearchParams(prev => {
        return withPresetParam(prev, slugifyPresetName(preset.name));
      }, { replace: true });
      setPresetMenuOpen(false);
    }
  }, [setSearchParams, setEditorValue]);

  // Sync editor/symbol URL params when they change
  const updateEditorParams = useCallback((editor: boolean, symbol: string | null) => {
    setSearchParams(prev => {
      return withEditorParams(prev, editor, symbol);
    }, { replace: true });
  }, [setSearchParams]);

  const handleToggleWYSIWYG = useCallback(() => {
    const nextState = toggleWysiwygRouteState({
      showWysiwyg: showWYSIWYG,
      expandedSymbol,
    });
    setShowWYSIWYG(nextState.showWysiwyg);
    setExpandedSymbol(nextState.expandedSymbol);
    updateEditorParams(nextState.showWysiwyg, nextState.expandedSymbol);
  }, [showWYSIWYG, expandedSymbol, updateEditorParams]);

  const handleExpandedSymbolChange = useCallback((symbol: string | null) => {
    setExpandedSymbol(symbol);
    updateEditorParams(showWYSIWYG, symbol);
  }, [showWYSIWYG, updateEditorParams]);

  // Inject Monaco widget z-index styles on mount
  useEffect(() => {
    const styleId = 'monaco-widget-z-index-fix';
    if (!document.getElementById(styleId)) {
      const style = document.createElement('style');
      style.id = styleId;
      style.textContent = MONACO_WIDGET_STYLES;
      document.head.appendChild(style);
    }
    return () => {
      const style = document.getElementById(styleId);
      if (style) {
        style.remove();
      }
    };
  }, []);

  const {
    compileResult,
    analysis: {
      compiledDeclsWithSource,
      compiledDeclarations,
      declarationSources,
      allCompiledDeclarations,
      typeInfoAtCursor,
    },
    handleEditorDidMount,
  } = useTextEditorCompiler({
    code,
    showDeclarations: showWYSIWYG,
    cursorInfo,
    incrementalCacheRef,
    editorRef,
    monacoRef,
    setCursorInfo,
  });

  // Handle name changes from WYSIWYG panel — write back to TT source
  const handleWYSIWYGNameChange = useCallback((declIndex: number, newName: string) => {
    const entry = compiledDeclsWithSource[declIndex];
    setEditorValue(replaceDeclarationNameInSource(code, entry, newName));
  }, [compiledDeclsWithSource, code, setEditorValue]);

  const handleEditorChange: OnChange = useCallback((value) => {
    setCode(value || '');
  }, []);

  return (
    <div style={styles.container}>
      <TextEditorHeader
        presets={PRESETS}
        showWYSIWYG={showWYSIWYG}
        presetMenuOpen={presetMenuOpen}
        onToggleWYSIWYG={handleToggleWYSIWYG}
        onTogglePresetMenu={() => setPresetMenuOpen(open => !open)}
        onLoadPreset={loadPreset}
      />

      <div style={{
        ...styles.mainContent,
        flexDirection: showWYSIWYG ? 'row' as const : 'column' as const,
      }}>
        {/* Left side: editor + type info + results */}
        <div style={{
          flex: 1,
          display: 'flex',
          flexDirection: 'column' as const,
          overflow: 'hidden',
          minWidth: 0,
        }}>
          {/* Source Code Editor - Top Half */}
          <div style={styles.editorSection}>
            <div style={styles.sectionHeader}>Source Code</div>
            <div style={styles.editorWrapper}>
              <Editor
                height="100%"
                defaultLanguage="tt"
                defaultValue={code}
                onChange={handleEditorChange}
                onMount={handleEditorDidMount}
                options={{
                  minimap: { enabled: false },
                  fontSize: 13,
                  lineNumbers: 'on',
                  scrollBeyondLastLine: false,
                  automaticLayout: true,
                  wordWrap: 'off',
                  folding: true,
                  renderWhitespace: 'selection',
                  fixedOverflowWidgets: true,
                  'semanticHighlighting.enabled': true,
                }}
              />
            </div>
          </div>

          <TextEditorTypeInfoPanel typeInfoAtCursor={typeInfoAtCursor} />

          <TextEditorResultsPanel
            compileResult={compileResult}
            showNamedArgsWithLabels={showNamedArgsWithLabels}
            showNamedParamsWithBraces={showNamedParamsWithBraces}
            setShowNamedArgsWithLabels={setShowNamedArgsWithLabels}
            setShowNamedParamsWithBraces={setShowNamedParamsWithBraces}
          />
        </div>{/* end left side */}

        {/* Right side: WYSIWYG panel */}
        {showWYSIWYG && (
          <div style={{
            flex: 1,
            borderLeft: '1px solid #30363d',
            overflow: 'hidden',
            backgroundColor: '#0d1117',
            minWidth: 0,
            display: 'flex',
            flexDirection: 'column',
          }}>
            <WYSIWYGPanel
              declarations={compiledDeclarations}
              allDeclarations={allCompiledDeclarations}
              compilerDefinitions={compileResult.definitions}
              onNameChange={handleWYSIWYGNameChange}
              declarationSources={declarationSources}
              expandedSymbol={expandedSymbol}
              onExpandedSymbolChange={handleExpandedSymbolChange}
            />
          </div>
        )}
      </div>
    </div>
  );
}
