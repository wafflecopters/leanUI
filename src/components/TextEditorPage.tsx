/**
 * TextEditorPage - A page for editing TT language expressions with Monaco editor
 *
 * Features:
 * - Monaco editor with syntax highlighting (plain text for now)
 * - Live parsing with inline diagnostics
 * - Type checking/inference results
 * - AST visualization
 */

import React, { useState, useCallback, useMemo, useRef, useEffect } from 'react';
import Editor, { OnMount, OnChange } from '@monaco-editor/react';
import type { editor as MonacoEditor } from 'monaco-editor';
import { checkSourceBlocks, BlockCheckResult, summarizeCheckResults } from '../parser/block-checker';

// ============================================================================
// Types
// ============================================================================

// Monaco type helpers
type Monaco = typeof import('monaco-editor');
type IStandaloneCodeEditor = MonacoEditor.IStandaloneCodeEditor;

// ============================================================================
// Styles
// ============================================================================

const styles = {
  container: {
    display: 'flex',
    flexDirection: 'column' as const,
    height: 'calc(100vh - 60px)',
    backgroundColor: '#0d1117',
    color: '#c9d1d9',
    fontFamily: "'JetBrains Mono', 'Fira Code', 'Consolas', monospace",
  },
  editorSection: {
    flex: '0 0 auto',
    padding: '20px',
    borderBottom: '1px solid #30363d',
  },
  editorWrapper: {
    border: '1px solid #30363d',
    borderRadius: '8px',
    overflow: 'hidden',
  },
  resultsSection: {
    flex: '1 1 auto',
    overflow: 'auto',
    padding: '20px',
  },
  sectionTitle: {
    margin: '0 0 12px 0',
    fontSize: '13px',
    fontWeight: 600,
    color: '#8b949e',
    textTransform: 'uppercase' as const,
    letterSpacing: '0.5px',
  },
  panel: {
    backgroundColor: '#161b22',
    border: '1px solid #30363d',
    borderRadius: '8px',
    padding: '16px',
    marginBottom: '16px',
  },
  errorPanel: {
    backgroundColor: 'rgba(248, 81, 73, 0.1)',
    border: '1px solid rgba(248, 81, 73, 0.4)',
  },
  successPanel: {
    backgroundColor: 'rgba(63, 185, 80, 0.1)',
    border: '1px solid rgba(63, 185, 80, 0.4)',
  },
  errorText: {
    color: '#f85149',
    fontWeight: 500,
  },
  successText: {
    color: '#3fb950',
    fontWeight: 500,
  },
  declCard: {
    backgroundColor: '#0d1117',
    border: '1px solid #30363d',
    borderRadius: '6px',
    padding: '12px 16px',
    marginBottom: '12px',
  },
  declKind: {
    display: 'inline-block',
    padding: '2px 8px',
    borderRadius: '4px',
    fontSize: '11px',
    fontWeight: 600,
    textTransform: 'uppercase' as const,
    marginRight: '8px',
  },
  kindDef: {
    backgroundColor: 'rgba(136, 198, 190, 0.2)',
    color: '#88c6be',
  },
  kindTheorem: {
    backgroundColor: 'rgba(198, 146, 214, 0.2)',
    color: '#c692d6',
  },
  kindAxiom: {
    backgroundColor: 'rgba(255, 198, 109, 0.2)',
    color: '#ffc66d',
  },
  kindExpr: {
    backgroundColor: 'rgba(88, 166, 255, 0.2)',
    color: '#58a6ff',
  },
  declName: {
    fontWeight: 600,
    color: '#e6edf3',
  },
  codeBlock: {
    backgroundColor: '#0d1117',
    borderRadius: '4px',
    padding: '8px 12px',
    marginTop: '8px',
    fontSize: '13px',
    overflow: 'auto' as const,
    border: '1px solid #21262d',
  },
  typeLabel: {
    color: '#8b949e',
    marginRight: '8px',
  },
  typeValue: {
    color: '#7ee787',
  },
  astTree: {
    fontFamily: "'JetBrains Mono', 'Fira Code', 'Consolas', monospace",
    fontSize: '12px',
    lineHeight: '1.5',
    whiteSpace: 'pre' as const,
  },
  helpText: {
    fontSize: '12px',
    color: '#6e7681',
    marginTop: '8px',
  },
  twoColumn: {
    display: 'grid',
    gridTemplateColumns: '1fr 1fr',
    gap: '20px',
  },
  statusBar: {
    display: 'flex',
    justifyContent: 'space-between',
    alignItems: 'center',
    marginTop: '12px',
    fontSize: '12px',
    color: '#6e7681',
  },
  badge: {
    display: 'inline-flex',
    alignItems: 'center',
    gap: '4px',
    padding: '2px 8px',
    borderRadius: '10px',
    fontSize: '11px',
    fontWeight: 500,
  },
  badgeSuccess: {
    backgroundColor: 'rgba(63, 185, 80, 0.2)',
    color: '#3fb950',
  },
  badgeError: {
    backgroundColor: 'rgba(248, 81, 73, 0.2)',
    color: '#f85149',
  },
  examplesButton: {
    padding: '6px 12px',
    backgroundColor: '#21262d',
    color: '#c9d1d9',
    border: '1px solid #30363d',
    borderRadius: '6px',
    cursor: 'pointer',
    fontSize: '12px',
    marginRight: '8px',
  },
  modalOverlay: {
    position: 'fixed' as const,
    top: 0,
    left: 0,
    right: 0,
    bottom: 0,
    backgroundColor: 'rgba(0, 0, 0, 0.7)',
    display: 'flex',
    alignItems: 'center',
    justifyContent: 'center',
    zIndex: 1000,
  },
  modal: {
    backgroundColor: '#0d1117',
    border: '1px solid #30363d',
    borderRadius: '8px',
    padding: '24px',
    maxWidth: '800px',
    maxHeight: '80vh',
    overflow: 'auto',
    width: '90%',
  },
  modalHeader: {
    display: 'flex',
    justifyContent: 'space-between',
    alignItems: 'center',
    marginBottom: '16px',
    paddingBottom: '12px',
    borderBottom: '1px solid #30363d',
  },
  modalTitle: {
    margin: 0,
    fontSize: '18px',
    color: '#e6edf3',
    fontWeight: 600,
  },
  closeButton: {
    padding: '4px 12px',
    backgroundColor: '#21262d',
    color: '#c9d1d9',
    border: '1px solid #30363d',
    borderRadius: '6px',
    cursor: 'pointer',
    fontSize: '14px',
  },
  blockBox: {
    backgroundColor: '#161b22',
    border: '1px solid #30363d',
    borderRadius: '6px',
    padding: '12px 16px',
    marginBottom: '12px',
  },
  blockHeader: {
    display: 'flex',
    alignItems: 'center',
    gap: '8px',
    fontSize: '13px',
  },
  blockTypeLabel: {
    display: 'inline-block',
    padding: '3px 10px',
    borderRadius: '4px',
    fontSize: '12px',
    fontWeight: 600,
  },
  blockTypeInductive: {
    backgroundColor: 'rgba(136, 198, 190, 0.2)',
    color: '#88c6be',
  },
  blockTypeTerm: {
    backgroundColor: 'rgba(88, 166, 255, 0.2)',
    color: '#58a6ff',
  },
  blockTypeUnknown: {
    backgroundColor: 'rgba(255, 198, 109, 0.2)',
    color: '#ffc66d',
  },
  blockTypeComment: {
    backgroundColor: 'rgba(110, 118, 129, 0.2)',
    color: '#6e7681',
  },
  blockName: {
    color: '#e6edf3',
    fontWeight: 500,
  },
  blockStatusFailed: {
    color: '#f85149',
    fontSize: '12px',
  },
  blockErrorText: {
    color: '#f0883e',
    fontSize: '12px',
    marginTop: '8px',
    fontFamily: "'JetBrains Mono', monospace",
  },
};

// ============================================================================
// Example Code
// ============================================================================

const EXAMPLE_CODE = `-- Natural Numbers
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

plus : Nat -> Nat -> Nat
plus Zero b = b
plus (Succ a) b = Succ (plus a b)

inductive Vec : Nat -> Type where
  VNil : (A: Type) -> Vec Zero A
  VCons : (A : Type) -> (n : Nat) -> A -> Vec A n -> Vec A (Succ n)

inductive Equal : (A: Type) -> A -> A -> Type where
  refl : (A : Type) -> (x : A) -> Equal A x x

{-
const : (A : Type) -> (B : Type) -> A -> B -> A
const = A B x y => x

twice' = Nat -> Nat
twice' n = plus n n

twice : Nat -> Nat
twice = 
 => plus n n

vecConcat : (A : Type) -> (a, b : Nat) -> Vec A a -> Vec A b -> Vec A (plus a b)
vecConcat _ _ _ (VNil _) v = v
vecConcat _ _ _ (VCons _ _ h tail) v = VCons _ _ h (vecConcat _ _ _ tail v)
-}
`

/*
const EXAMPLE_CODE = `-- Example TT Language Expressions

-- Type signature, then definition on next line
id : (A : Type) -> A -> A
id = \\(A : Type) (x : A) => x

const : (A : Type) -> (B : Type) -> A -> B -> A
const = \\A B x y => x

-- Natural number operations
double : ℕ -> ℕ
double = \\n => n + n

-- Type signature only (proof goal / axiom)
add_comm : (a : ℕ) -> (b : ℕ) -> a + b = b + a

-- Function extensionality axiom
funext : (A : Type) -> (B : Type) -> (f : A -> B) -> (g : A -> B) -> f = g

-- Definition without type (will be inferred)
increment = \\x => x + 1

-- Standalone expressions
\\x => x + 1

(a + b) * c = a * c + b * c
`;
*/

// ============================================================================
// Helper Functions
// ============================================================================
// (Old helper functions removed - using block-checker.ts instead)

// ============================================================================
// Monaco Editor Configuration
// ============================================================================

// Color palette for syntax highlighting (changeable later)
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

// Define a custom dark theme that matches our UI
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

// Editor options
const MONACO_OPTIONS: MonacoEditor.IStandaloneEditorConstructionOptions = {
  fontSize: 14,
  fontFamily: "'JetBrains Mono', 'Fira Code', 'Consolas', monospace",
  lineHeight: 1.6,
  minimap: { enabled: false },
  scrollBeyondLastLine: false,
  wordWrap: 'on',
  automaticLayout: true,
  tabSize: 2,
  insertSpaces: true,
  renderLineHighlight: 'line',
  cursorBlinking: 'smooth',
  smoothScrolling: true,
  padding: { top: 16, bottom: 16 },
  folding: true,
  lineNumbers: 'on',
  glyphMargin: true,
  renderWhitespace: 'selection',
  bracketPairColorization: { enabled: true },
  // Ensure tooltips/hover widgets render above other page elements
  fixedOverflowWidgets: true,
};

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

// ============================================================================
// Components
// ============================================================================

interface EnhancedBlockCardProps {
  result: BlockCheckResult;
  index: number;
}

const EnhancedBlockCard: React.FC<EnhancedBlockCardProps> = ({ result }) => {
  const [showErrors, setShowErrors] = useState(true);

  const getTypeStyle = () => {
    switch (result.blockType) {
      case 'Inductive': return styles.blockTypeInductive;
      case 'Term': return styles.blockTypeTerm;
      case 'Unknown': return styles.blockTypeUnknown;
      case 'Comment': return styles.blockTypeComment;
    }
  };

  const getStatusIcon = () => {
    if (result.blockType === 'Comment') return '📝';
    if (!result.parseSuccess) return '⚠';
    if (!result.nameResolutionSuccess) return '✗';
    if (!result.checkSuccess) return '✗';
    return '✓';
  };

  const getStatusColor = () => {
    if (result.blockType === 'Comment') return '#8b949e';
    if (!result.parseSuccess) return '#f0883e';
    if (!result.nameResolutionSuccess) return '#f85149';
    if (!result.checkSuccess) return '#f85149';
    return '#3fb950';
  };

  const typeLabel = result.blockType;
  const nameDisplay = result.name ? `: ${result.name}` : '';

  return (
    <div style={styles.blockBox}>
      <div style={styles.blockHeader}>
        <span style={{ color: getStatusColor(), marginRight: '8px', fontSize: '14px' }}>
          {getStatusIcon()}
        </span>
        <span style={{ ...styles.blockTypeLabel, ...getTypeStyle() }}>
          {typeLabel}{nameDisplay}
        </span>
      </div>

      {/* Parse errors */}
      {!result.parseSuccess && result.parseErrors.length > 0 && (
        <div style={styles.blockErrorText}>
          <div style={{ fontWeight: 600, marginBottom: '4px' }}>Parse Errors:</div>
          {result.parseErrors.map((error, i) => (
            <div key={i} style={{ marginLeft: '12px' }}>
              Line {error.line}, Col {error.col}: {error.message}
            </div>
          ))}
        </div>
      )}

      {/* Name resolution errors */}
      {result.parseSuccess && !result.nameResolutionSuccess && result.nameResolutionErrors.length > 0 && (
        <div style={styles.blockErrorText}>
          <div style={{ fontWeight: 600, marginBottom: '4px' }}>
            Name Resolution Errors ({result.nameResolutionErrors.length}):
          </div>
          {result.nameResolutionErrors.map((nameError, i) => (
            <div key={i} style={{ marginLeft: '12px' }}>
              {nameError.error.message}
              {nameError.location && (
                <span style={{ fontSize: '11px', color: '#8b949e', marginLeft: '8px' }}>
                  (line {nameError.location.start.line}, col {nameError.location.start.col})
                </span>
              )}
            </div>
          ))}
        </div>
      )}

      {/* Type check errors */}
      {result.parseSuccess && result.nameResolutionSuccess && !result.checkSuccess && result.checkErrors.length > 0 && (
        <div>
          <div
            style={{
              ...styles.blockErrorText,
              cursor: 'pointer',
              display: 'flex',
              alignItems: 'center',
              justifyContent: 'space-between'
            }}
            onClick={() => setShowErrors(!showErrors)}
          >
            <span style={{ fontWeight: 600 }}>
              Type Errors ({result.checkErrors.length})
            </span>
            <span style={{ fontSize: '11px' }}>
              {showErrors ? '▼' : '▶'}
            </span>
          </div>
          {showErrors && (
            <div style={{ marginTop: '8px' }}>
              {result.checkErrors.map((checkError, i) => (
                <div key={i} style={{ marginLeft: '12px', marginBottom: '8px' }}>
                  <div style={{ color: '#f85149' }}>{checkError.error.message}</div>
                  {checkError.location && (
                    <div style={{ color: '#8b949e', fontSize: '11px', marginTop: '2px' }}>
                      at line {checkError.location.start.line}, column {checkError.location.start.col}
                    </div>
                  )}
                </div>
              ))}
            </div>
          )}
        </div>
      )}
    </div>
  );
};

// ============================================================================
// Main Component
// ============================================================================

export const TextEditorPage: React.FC = () => {
  const [code, setCode] = useState(EXAMPLE_CODE);
  const editorRef = useRef<IStandaloneCodeEditor | null>(null);
  const monacoRef = useRef<Monaco | null>(null);

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

  // Check all blocks with full type checking pipeline
  const blockCheckResults = useMemo((): BlockCheckResult[] => {
    if (!code.trim()) return [];
    return checkSourceBlocks(code);
  }, [code]);

  // Calculate block statistics
  const blockStats = useMemo(() => {
    return summarizeCheckResults(blockCheckResults);
  }, [blockCheckResults]);

  // Track whether editor has been mounted
  const [editorMounted, setEditorMounted] = useState(false);

  // Update Monaco markers with parse and type check errors
  useEffect(() => {
    const monaco = monacoRef.current;
    const editor = editorRef.current;
    if (!monaco || !editor) return;

    const model = editor.getModel();
    if (!model) return;

    const markers: MonacoEditor.IMarkerData[] = [];

    // Add markers for all block errors
    for (const blockResult of blockCheckResults) {
      // Parse errors
      for (const error of blockResult.parseErrors) {
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

      // Name resolution errors with source locations
      for (const nameError of blockResult.nameResolutionErrors) {
        if (nameError.location) {
          // Use precise source location
          markers.push({
            severity: monaco.MarkerSeverity.Error,
            message: nameError.error.message,
            startLineNumber: nameError.location.start.line,
            startColumn: nameError.location.start.col,
            endLineNumber: nameError.location.end.line,
            endColumn: nameError.location.end.col,
            source: 'TT Name Resolution',
          });
        } else {
          // Fallback: mark entire first line if location not available
          const firstLine = blockResult.block.startLine;
          const lineContent = model.getLineContent(firstLine);
          markers.push({
            severity: monaco.MarkerSeverity.Error,
            message: nameError.error.message,
            startLineNumber: firstLine,
            startColumn: 1,
            endLineNumber: firstLine,
            endColumn: lineContent.length + 1,
            source: 'TT Name Resolution',
          });
        }
      }

      // Type check errors with source locations
      for (const checkError of blockResult.checkErrors) {
        if (checkError.location) {
          markers.push({
            severity: monaco.MarkerSeverity.Error,
            message: checkError.error.message,
            startLineNumber: checkError.location.start.line,
            startColumn: checkError.location.start.col,
            endLineNumber: checkError.location.end.line,
            endColumn: checkError.location.end.col,
            source: 'TT Type Checker',
          });
        }
      }
    }

    monaco.editor.setModelMarkers(model, 'tt-checker', markers);
  }, [blockCheckResults, editorMounted]);

  // Editor mount handler
  const handleEditorMount: OnMount = useCallback((editor, monaco) => {
    editorRef.current = editor;
    monacoRef.current = monaco;

    // Register TT language
    monaco.languages.register({ id: 'tt' });

    // Define TT language syntax
    monaco.languages.setMonarchTokensProvider('tt', {
      keywords: [
        'inductive', 'where', 'def', 'theorem', 'axiom', 'let', 'in', 'fun'
      ],
      typeKeywords: [
        'Type', 'Prop'
      ],
      operators: [
        '->', '=>', ':=', ':', '=', '+', '-', '*', '/', '\\',
        '|', '(', ')', '{', '}', ',', '.'
      ],
      tokenizer: {
        root: [
          // Comments - multiline {- -} must come FIRST before any other tokenization
          [/\{-/, 'comment', '@comment'],
          [/--.*$/, 'comment'],

          // Type keywords (Type, Prop) - must come before regular keywords
          [/\b(Type|Prop)\b/, 'type.identifier'],

          // Regular keywords
          [/\b(inductive|where|def|theorem|axiom|let|in|fun)\b/, 'keyword'],

          // Holes
          [/\?[a-zA-Z_][a-zA-Z0-9_']*/, 'variable.predefined'],

          // Identifiers
          [/[a-zA-Z_][a-zA-Z0-9_']*/, 'identifier'],

          // Numbers
          [/\d+/, 'number'],

          // Structural operators (arrows)
          [/->|=>/, 'keyword.operator'],

          // Assignment and type annotation
          [/:=|:/, 'delimiter'],

          // Pipe (for constructors)
          [/\|/, 'delimiter.bracket'],

          // Other operators
          [/[+\-*/=\\(){},.;]/, 'delimiter'],

          // Whitespace
          [/\s+/, 'white'],
        ],
        comment: [
          [/-\}/, 'comment', '@pop'],  // End comment - pop state (must come first!)
          [/\{-/, 'comment', '@push'], // Nested comment - push state
          [/./, 'comment'],             // Match any single character as comment
        ],
      },
    });

    // Define and apply custom theme
    monaco.editor.defineTheme('tt-dark', MONACO_THEME);
    monaco.editor.setTheme('tt-dark');

    // Set the model language to 'tt'
    const model = editor.getModel();
    if (model) {
      monaco.editor.setModelLanguage(model, 'tt');
    }

    // Focus the editor
    editor.focus();

    // Trigger diagnostics update
    setEditorMounted(true);
  }, []);

  // Editor change handler
  const handleEditorChange: OnChange = useCallback((value) => {
    setCode(value || '');
  }, []);

  const handleExampleClick = useCallback(() => {
    setCode(EXAMPLE_CODE);
  }, []);

  const handleClearClick = useCallback(() => {
    setCode('');
  }, []);

  return (
    <div style={styles.container}>
      {/* Editor Section */}
      <div style={styles.editorSection}>
        <h2 style={styles.sectionTitle}>TT Language Editor</h2>
        <div style={styles.editorWrapper}>
          <Editor
            height="300px"
            defaultLanguage="tt"
            value={code}
            onChange={handleEditorChange}
            onMount={handleEditorMount}
            options={MONACO_OPTIONS}
            loading={
              <div style={{
                backgroundColor: '#161b22',
                height: '300px',
                display: 'flex',
                alignItems: 'center',
                justifyContent: 'center',
                color: '#8b949e'
              }}>
                Loading editor...
              </div>
            }
          />
        </div>

        <div style={styles.statusBar}>
          <div>
            <button style={styles.examplesButton} onClick={handleExampleClick}>
              Load Examples
            </button>
            <button style={styles.examplesButton} onClick={handleClearClick}>
              Clear
            </button>
          </div>

          <div style={{ display: 'flex', gap: '12px' }}>
            <span>{blockCheckResults.length} block{blockCheckResults.length !== 1 ? 's' : ''}</span>
            {blockStats.successfulBlocks > 0 && (
              <span style={{ ...styles.badge, ...styles.badgeSuccess }}>
                ✓ {blockStats.successfulBlocks} OK
              </span>
            )}
            {blockStats.totalErrors > 0 && (
              <span style={{ ...styles.badge, ...styles.badgeError }}>
                ⚠ {blockStats.totalErrors} error{blockStats.totalErrors !== 1 ? 's' : ''}
              </span>
            )}
          </div>
        </div>
      </div>

      {/* Results Section */}
      <div style={styles.resultsSection}>
        {/* Block Check Results Display */}
        {blockCheckResults.length > 0 ? (
          <div>
            <h3 style={styles.sectionTitle}>
              Type-Checked Blocks ({blockCheckResults.length}) -
              {blockStats.successfulBlocks > 0 && ` ✓ ${blockStats.successfulBlocks} OK`}
              {blockStats.parseErrorBlocks > 0 && ` ⚠ ${blockStats.parseErrorBlocks} Parse Errors`}
              {blockStats.checkErrorBlocks > 0 && ` ✗ ${blockStats.checkErrorBlocks} Type Errors`}
            </h3>
            {blockCheckResults.map((blockResult, index) => (
              <EnhancedBlockCard key={index} result={blockResult} index={index} />
            ))}
          </div>
        ) : (
          <div style={{
            ...styles.panel,
            textAlign: 'center',
            color: '#8b949e',
            padding: '40px',
          }}>
            <div style={{ fontSize: '48px', marginBottom: '16px' }}>λ</div>
            <div style={{ fontSize: '16px', marginBottom: '8px' }}>No code yet</div>
            <div style={{ fontSize: '12px' }}>
              Type some TT language expressions above, or click "Load Examples"
            </div>
          </div>
        )}
      </div>
    </div>
  );
};

export default TextEditorPage;
