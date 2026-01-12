/**
 * TmpDebugPage - A debug page for viewing code and compilation results
 */
import React, { useRef, useMemo, useState, useCallback, useEffect } from 'react';
import Editor, { OnMount, OnChange } from '@monaco-editor/react';
import type { editor as MonacoEditor } from 'monaco-editor';
import { compileTTFromText, CompileResult, CompiledBlock } from '../compiler/compile';
import { serializeIndexPath, IndexPath, SourceRange, ElabMap, SourceMap } from '../types/source-position';
import { TTKTerm, prettyPrint as prettyPrintTTK } from '../types/tt-kernel';

// Color palette for syntax highlighting (matches TextEditorPage)
const SYNTAX_COLORS = {
  keyword: '569cd6',        // Blue - for inductive, where, def, etc.
  keywordOperator: '94d0ff', // Light blue - for ->, =>
  typeKeyword: 'cf92cd',    // Light purple/pink - for Type, Prop
  comment: '6a9955',        // Green - for comments (-- and {- -})
  string: 'ce9178',         // Orange
  number: 'b5cea8',         // Light green
  identifier: 'd4d4d4',     // Light gray
  delimiter: 'e5c995',      // Light tan/gold - for (, ), {, }, etc.
  hole: '4fc1ff',           // Bright cyan for holes
};

// Monaco theme matching TextEditorPage
const MONACO_THEME: MonacoEditor.IStandaloneThemeData = {
  base: 'vs-dark',
  inherit: true,
  rules: [
    { token: 'comment', foreground: SYNTAX_COLORS.comment, fontStyle: 'italic' },
    { token: 'keyword', foreground: SYNTAX_COLORS.keyword },
    { token: 'keyword.operator', foreground: SYNTAX_COLORS.keywordOperator },
    { token: 'type.identifier', foreground: SYNTAX_COLORS.typeKeyword },
    { token: 'string', foreground: SYNTAX_COLORS.string },
    { token: 'number', foreground: SYNTAX_COLORS.number },
    { token: 'identifier', foreground: SYNTAX_COLORS.identifier },
    { token: 'delimiter', foreground: SYNTAX_COLORS.delimiter },
    { token: 'delimiter.bracket', foreground: SYNTAX_COLORS.delimiter },
    { token: 'variable.predefined', foreground: SYNTAX_COLORS.hole },
  ],
  colors: {
    'editor.background': '#161b22',
    'editor.foreground': '#c9d1d9',
    'editor.lineHighlightBackground': '#161b22',
    'editor.selectionBackground': '#264f78',
    'editorCursor.foreground': '#58a6ff',
    'editorLineNumber.foreground': '#6e7681',
    'editorLineNumber.activeForeground': '#c9d1d9',
    'editorIndentGuide.background': '#21262d',
    'editorIndentGuide.activeBackground': '#30363d',
    'editorBracketMatch.background': '#2d333b',
    'editorBracketMatch.border': '#58a6ff',
  },
};

/**
 * Map an error path to a source range using the elab and source maps.
 * Returns null if mapping fails.
 */
function mapErrorPathToSourceRange(
  errorPath: IndexPath,
  elabMap: ElabMap | undefined,
  sourceMap: SourceMap | undefined,
  blockStartLine: number
): SourceRange | null {
  if (!elabMap || !sourceMap) return null;

  const kernelPathStr = serializeIndexPath(errorPath);

  // Look up the surface path via elabMap
  const surfacePathStr = elabMap.get(kernelPathStr);
  if (!surfacePathStr) {
    // Try progressively shorter paths (walk up the tree)
    let currentPath = errorPath;
    while (currentPath.length > 0) {
      currentPath = currentPath.slice(0, -1);
      const shorterPathStr = serializeIndexPath(currentPath);
      const shorterSurfacePath = elabMap.get(shorterPathStr);
      if (shorterSurfacePath) {
        const range = sourceMap.get(shorterSurfacePath);
        if (range) {
          return {
            start: { ...range.start, line: range.start.line + blockStartLine - 1 },
            end: { ...range.end, line: range.end.line + blockStartLine - 1 }
          };
        }
      }
    }
    return null;
  }

  // Look up the source range via sourceMap
  const range = sourceMap.get(surfacePathStr);
  if (!range) return null;

  // Adjust line numbers to account for block offset
  return {
    start: { ...range.start, line: range.start.line + blockStartLine - 1 },
    end: { ...range.end, line: range.end.line + blockStartLine - 1 }
  };
}

/**
 * Extract parameter/index info from an inductive type's kernel type.
 * Returns array of { name, type, isIndex } for each position.
 */
function extractParamIndexInfo(
  kernelType: TTKTerm | undefined,
  indexPositions: number[] | undefined
): Array<{ name: string; type: string; isIndex: boolean }> {
  if (!kernelType) return [];

  const indexSet = new Set(indexPositions ?? []);
  const result: Array<{ name: string; type: string; isIndex: boolean }> = [];
  let current = kernelType;
  let position = 0;

  while (current.tag === 'Binder' && current.binderKind.tag === 'BPi') {
    const name = current.name || '_';
    const type = prettyPrintTTK(current.domain);
    const isIndex = indexSet.has(position);
    result.push({ name, type, isIndex });
    current = current.body;
    position++;
  }

  return result;
}

// Monaco type helpers
type Monaco = typeof import('monaco-editor');
type IStandaloneCodeEditor = MonacoEditor.IStandaloneCodeEditor;

// CSS to ensure Monaco widgets render above everything
const MONACO_WIDGET_STYLES = `
  .monaco-hover,
  .monaco-editor .suggest-widget,
  .monaco-editor .parameter-hints-widget,
  .monaco-editor-overlaymessage,
  .monaco-editor .monaco-hover-content {
    z-index: 10001 !important;
  }
`;

const SAMPLE_CODE = `inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

plus : Nat -> Nat -> Nat
plus Zero b = b
plus (Succ a) b = Succ (plus a b)

inductive Vec : Type -> Nat -> Type where
  VNil : (A: Type) -> Vec A Zero
  VCons : (A : Type) -> (n : Nat) -> A -> Vec A n -> Vec A (Succ n)

swap : (A : Type) -> (B : Type) -> (C : Type) -> (f : A -> B -> C) -> B -> A -> C
swap _ _ _ f = \\x y => f y x

vecConcat : (A : Type) -> (a : Nat) -> (b : Nat) -> Vec A a -> Vec A b -> Vec A (plus a b)
vecConcat _ _ _ (VNil _) v = v
vecConcat A (Succ p) _ (VCons _ _ h tail) v = VCons _ _ h (vecConcat A p _ tail v)

vecConcat' : (A : Type) -> (a : Nat) -> (b : Nat) -> Vec A a -> Vec A b -> Vec A (plus a b)
vecConcat' _ _ _ (VNil _) v = v
vecConcat' A (Succ p) _ (VCons _ _ h tail) v = (swap _ (VCons _ _)) (vecConcat' A ((\\d x => x) Zero p) _ tail v) h`;

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
  header: {
    padding: '16px 20px',
    color: '#c9d1d9',
    borderBottom: '1px solid #30363d',
    flexShrink: 0,
  },
  title: {
    margin: 0,
    marginBottom: '4px',
    fontSize: '18px',
    fontWeight: 600,
  },
  subtitle: {
    margin: 0,
    fontSize: '13px',
    color: '#8b949e',
  },
  mainContent: {
    flex: 1,
    display: 'flex',
    flexDirection: 'column' as const,
    overflow: 'hidden',
  },
  editorSection: {
    height: '50%',
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
  resultsSection: {
    height: '50%',
    display: 'flex',
    flexDirection: 'column' as const,
    overflow: 'hidden',
  },
  resultsContent: {
    flex: 1,
    overflow: 'auto',
    padding: '16px',
    fontFamily: "'JetBrains Mono', 'Fira Code', 'Consolas', monospace",
    fontSize: '13px',
  },
  blockCard: {
    backgroundColor: '#161b22',
    border: '1px solid #30363d',
    borderRadius: '6px',
    marginBottom: '12px',
    overflow: 'hidden',
  },
  blockHeader: {
    padding: '8px 12px',
    backgroundColor: '#21262d',
    borderBottom: '1px solid #30363d',
    display: 'flex',
    alignItems: 'center',
    gap: '8px',
  },
  blockBadge: {
    padding: '2px 8px',
    borderRadius: '4px',
    fontSize: '11px',
    fontWeight: 600,
  },
  blockBadgeInductive: {
    backgroundColor: 'rgba(136, 198, 190, 0.2)',
    color: '#88c6be',
  },
  blockBadgeTerm: {
    backgroundColor: 'rgba(88, 166, 255, 0.2)',
    color: '#58a6ff',
  },
  blockBadgeComment: {
    backgroundColor: 'rgba(110, 118, 129, 0.2)',
    color: '#6e7681',
  },
  blockBadgeError: {
    backgroundColor: 'rgba(248, 81, 73, 0.2)',
    color: '#f85149',
  },
  blockBody: {
    padding: '12px',
  },
  declSection: {
    marginBottom: '12px',
  },
  declName: {
    color: '#e6edf3',
    fontWeight: 600,
    marginBottom: '4px',
  },
  typeRow: {
    display: 'flex',
    gap: '8px',
    marginBottom: '4px',
  },
  typeLabel: {
    color: '#8b949e',
    minWidth: '50px',
  },
  typeValue: {
    color: '#7ee787',
  },
  valueValue: {
    color: '#d2a8ff',
  },
  ctorRow: {
    marginLeft: '16px',
    marginBottom: '2px',
  },
  ctorName: {
    color: '#ffa657',
  },
  errorText: {
    color: '#f85149',
  },
};

// Block renderer component
function BlockRenderer({ block }: { block: CompiledBlock }) {
  if (block.isComment) {
    return (
      <div style={styles.blockCard}>
        <div style={styles.blockHeader}>
          <span style={{ ...styles.blockBadge, ...styles.blockBadgeComment }}>Comment</span>
        </div>
        <div style={styles.blockBody}>
          <pre style={{ margin: 0, color: '#6e7681' }}>
            {block.sourceLines.join('\n')}
          </pre>
        </div>
      </div>
    );
  }

  if (!block.parseSuccess) {
    return (
      <div style={styles.blockCard}>
        <div style={styles.blockHeader}>
          <span style={{ ...styles.blockBadge, ...styles.blockBadgeError }}>Parse Error</span>
        </div>
        <div style={styles.blockBody}>
          {block.parseErrors.map((err, i) => (
            <div key={i} style={styles.errorText}>
              Line {err.line}, Col {err.col}: {err.message}
            </div>
          ))}
        </div>
      </div>
    );
  }

  if (!block.nameResolutionSuccess) {
    return (
      <div style={styles.blockCard}>
        <div style={styles.blockHeader}>
          <span style={{ ...styles.blockBadge, ...styles.blockBadgeError }}>Name Error</span>
        </div>
        <div style={styles.blockBody}>
          {block.nameResolutionErrors.map((err, i) => (
            <div key={i} style={styles.errorText}>{err}</div>
          ))}
        </div>
      </div>
    );
  }

  return (
    <div style={styles.blockCard}>
      {block.declarations.map((decl, i) => {
        // Extract param/index info for inductive types
        const paramIndexInfo = decl.kind === 'inductive'
          ? extractParamIndexInfo(decl.kernelType, decl.indexPositions)
          : [];

        return (
        <div key={i}>
          <div style={styles.blockHeader}>
            <span style={{
              ...styles.blockBadge,
              ...(decl.kind === 'inductive' ? styles.blockBadgeInductive : styles.blockBadgeTerm)
            }}>
              {decl.kind === 'inductive' ? 'Inductive' : 'Term'}
            </span>
            {decl.name && <span style={styles.declName}>{decl.name}</span>}
            {/* Display param/index info for inductive types */}
            {paramIndexInfo.length > 0 && (
              <span style={{ marginLeft: '12px', fontSize: '11px', color: '#8b949e' }}>
                {paramIndexInfo.map((info, j) => (
                  <span key={j} style={{ marginRight: '8px' }}>
                    <span style={{ color: info.isIndex ? '#f0883e' : '#7ee787' }}>
                      [{info.isIndex ? 'index' : 'param'} {info.name} : {info.type}]
                    </span>
                  </span>
                ))}
              </span>
            )}
            {decl.checkSuccess ? (
              <span style={{ marginLeft: 'auto', color: '#3fb950', fontSize: '12px' }}>OK</span>
            ) : decl.checkErrors && decl.checkErrors.length > 0 ? (
              <span style={{ marginLeft: 'auto', color: '#f85149', fontSize: '12px' }}>
                {decl.checkErrors.length} error(s)
              </span>
            ) : null}
          </div>
          <div style={styles.blockBody}>
            {decl.prettyType && (
              <div style={styles.typeRow}>
                <span style={styles.typeLabel}>Type:</span>
                <span style={styles.typeValue}>{decl.prettyType}</span>
              </div>
            )}
            {decl.prettyValue && (
              <div style={styles.typeRow}>
                <span style={styles.typeLabel}>Value:</span>
                <span style={styles.valueValue}>{decl.prettyValue}</span>
              </div>
            )}
            {decl.prettyConstructors && decl.prettyConstructors.length > 0 && (
              <div>
                <div style={{ ...styles.typeLabel, marginBottom: '4px' }}>Constructors:</div>
                {decl.prettyConstructors.map((ctor, j) => (
                  <div key={j} style={styles.ctorRow}>
                    <span style={styles.ctorName}>{ctor.name}</span>
                    <span style={{ color: '#8b949e' }}> : </span>
                    <span style={styles.typeValue}>{ctor.prettyType}</span>
                  </div>
                ))}
              </div>
            )}
            {decl.checkErrors && decl.checkErrors.length > 0 && (
              <div style={{ marginTop: '8px' }}>
                {decl.checkErrors.map((err, j) => (
                  <div key={j} style={styles.errorText}>{err.message}</div>
                ))}
              </div>
            )}
          </div>
        </div>
        );
      })}
    </div>
  );
}

export function TmpDebugPage() {
  const editorRef = useRef<IStandaloneCodeEditor | null>(null);
  const monacoRef = useRef<Monaco | null>(null);
  const [code, setCode] = useState(SAMPLE_CODE);

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

  // Compile and type check the source code
  const compileResult = useMemo<CompileResult>(() => {
    return compileTTFromText(code);
  }, [code]);

  const handleEditorChange: OnChange = useCallback((value) => {
    setCode(value || '');
  }, []);

  // Update Monaco markers with compile errors
  useEffect(() => {
    const monaco = monacoRef.current;
    const editor = editorRef.current;
    if (!monaco || !editor) return;

    const model = editor.getModel();
    if (!model) return;

    const markers: MonacoEditor.IMarkerData[] = [];

    // Add markers for all block errors
    for (const block of compileResult.blocks) {
      // Parse errors
      for (const error of block.parseErrors) {
        const lineContent = model.getLineContent(error.line);
        const endCol = Math.max(error.col + 1, lineContent.length + 1);

        markers.push({
          severity: monaco.MarkerSeverity.Error,
          message: (error.message || 'Parse error').replace(/^Parse error at line \d+, col \d+: /, ''),
          startLineNumber: error.line,
          startColumn: error.col,
          endLineNumber: error.line,
          endColumn: endCol,
          source: 'TT Parser',
        });
      }

      // Type check errors from declarations
      for (const decl of block.declarations) {
        if (decl.checkErrors && decl.checkErrors.length > 0) {
          for (const err of decl.checkErrors) {
            // Try to map error path to precise source location
            const sourceRange = mapErrorPathToSourceRange(
              err.path,
              decl.elabMap,
              decl.sourceMap,
              block.startLine
            );

            if (sourceRange) {
              // Use the mapped source range
              markers.push({
                severity: monaco.MarkerSeverity.Error,
                message: err.message,
                startLineNumber: sourceRange.start.line,
                startColumn: sourceRange.start.col,
                endLineNumber: sourceRange.end.line,
                endColumn: sourceRange.end.col,
                source: 'TT Type Checker',
              });
            } else {
              // Fallback: mark the first line of the block
              const firstLine = block.startLine;
              markers.push({
                severity: monaco.MarkerSeverity.Error,
                message: err.message,
                startLineNumber: firstLine,
                startColumn: 1,
                endLineNumber: firstLine,
                endColumn: model.getLineContent(firstLine).length + 1,
                source: 'TT Type Checker',
              });
            }
          }
        }
      }
    }

    monaco.editor.setModelMarkers(model, 'tt-compiler', markers);
  }, [compileResult]);

  const handleEditorDidMount: OnMount = (editor, monaco) => {
    editorRef.current = editor;
    monacoRef.current = monaco;

    // Register TT language
    monaco.languages.register({ id: 'tt' });

    // Define TT language syntax (matches TextEditorPage)
    monaco.languages.setMonarchTokensProvider('tt', {
      keywords: [
        'inductive', 'where', 'def', 'theorem', 'axiom', 'let', 'in', 'fun'
      ],
      typeKeywords: [
        'Type', 'Prop'
      ],
      tokenizer: {
        root: [
          // Comments - multiline {- -} must come FIRST
          [/\{-/, 'comment', '@comment'],
          [/--.*$/, 'comment'],

          // Type keywords (Type, Prop)
          [/\b(Type|Prop)\b/, 'type.identifier'],

          // Regular keywords
          [/\b(inductive|where|def|theorem|axiom|let|in|fun)\b/, 'keyword'],

          // Holes
          [/\?[a-zA-Z_][a-zA-Z0-9_']*/, 'variable.predefined'],

          // Identifiers
          [/[a-zA-Z_][a-zA-Z0-9_']*/, 'identifier'],

          // Numbers
          [/\d+/, 'number'],

          // Operators
          [/->|=>/, 'keyword.operator'],
          [/[=:+\-*/\\|<>!]+/, 'delimiter'],

          // Brackets and delimiters
          [/[()[\]{}]/, 'delimiter.bracket'],
          [/[,.]/, 'delimiter'],

          // Whitespace
          [/\s+/, 'white'],
        ],
        comment: [
          [/[^{-]+/, 'comment'],
          [/-\}/, 'comment', '@pop'],
          [/[{-]/, 'comment'],
        ],
      }
    });

    // Define and apply custom theme
    monaco.editor.defineTheme('tt-dark', MONACO_THEME);
    monaco.editor.setTheme('tt-dark');

    // Set the model language
    const model = editor.getModel();
    if (model) {
      monaco.editor.setModelLanguage(model, 'tt');
    }
  };

  return (
    <div style={styles.container}>
      <div style={styles.header}>
        <h2 style={styles.title}>Debug View</h2>
        <p style={styles.subtitle}>Source code and elaborated TTK output</p>
      </div>

      <div style={styles.mainContent}>
        {/* Source Code Editor - Top Half */}
        <div style={styles.editorSection}>
          <div style={styles.sectionHeader}>Source Code</div>
          <div style={styles.editorWrapper}>
            <Editor
              height="100%"
              defaultLanguage="tt"
              value={code}
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
              }}
            />
          </div>
        </div>

        {/* Compile Results - Bottom Half */}
        <div style={styles.resultsSection}>
          <div style={styles.sectionHeader}>
            Compile Results
            {!compileResult.success && (
              <span style={{ marginLeft: '8px', color: '#f85149' }}>
                ({compileResult.totalParseErrors + compileResult.totalNameErrors + compileResult.totalCheckErrors} errors)
              </span>
            )}
          </div>
          <div style={styles.resultsContent}>
            {compileResult.blocks.map((block, i) => (
              <BlockRenderer key={i} block={block} />
            ))}
          </div>
        </div>
      </div>
    </div>
  );
}
