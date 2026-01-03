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
import {
  parseDeclarations,
  ParseError,
  ParseErrors,
  ParsedDeclaration,
  DEFAULT_OPERATORS,
} from '../parser/tt-parser';
import { TTerm, prettyPrint, TContext } from '../types/tt-core';
import { inferType, TypeCheckError } from '../types/tt-typecheck';
import { groupByIndentation, SourceBlock, parseBlock } from '../parser/indentation-grouper';
import { checkSourceBlocks, BlockCheckResult, summarizeCheckResults } from '../parser/block-checker';

// ============================================================================
// Types
// ============================================================================

interface ParseResult {
  success: true;
  declarations: ParsedDeclaration[];
}

interface ParseFailure {
  success: false;
  errors: ParseError[];
}

interface TypeCheckResult {
  declIndex: number;
  name?: string;
  kind: string;
  inferredType?: string;
  error?: string;
}

interface BlockParseResult {
  block: SourceBlock;
  type: 'Inductive' | 'Term' | 'Unknown' | 'Comment';
  name?: string;
  parseSuccess: boolean;
  parseError?: string;
}

type ParseOutcome = ParseResult | ParseFailure;

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

function getKindStyle(kind: string): React.CSSProperties {
  switch (kind) {
    case 'def': return styles.kindDef;
    case 'theorem': return styles.kindTheorem;
    case 'axiom': return styles.kindAxiom;
    default: return styles.kindExpr;
  }
}

function formatAst(term: TTerm, indent: number = 0): string {
  const pad = '  '.repeat(indent);

  switch (term.tag) {
    case 'Var':
      return `${pad}Var(${term.index})`;

    case 'Sort':
      return `${pad}Sort(level: ${term.level}) ${term.level === 0 ? '-- Prop' : `-- Type_${term.level}`}`;

    case 'Const':
      return `${pad}Const("${term.name}")`;

    case 'Hole':
      return `${pad}Hole("${term.id}")`;

    case 'Binder': {
      const kind = term.binderKind.tag === 'BPi' ? 'Π' :
        term.binderKind.tag === 'BLam' ? 'λ' : 'let';
      let result = `${pad}Binder(${kind}, name: "${term.name}")\n`;
      result += `${pad}  domain:\n${formatAst(term.domain, indent + 2)}\n`;
      if (term.binderKind.tag === 'BLet') {
        result += `${pad}  defVal:\n${formatAst(term.binderKind.defVal, indent + 2)}\n`;
      }
      result += `${pad}  body:\n${formatAst(term.body, indent + 2)}`;
      return result;
    }

    case 'App':
      return `${pad}App\n${pad}  fn:\n${formatAst(term.fn, indent + 2)}\n${pad}  arg:\n${formatAst(term.arg, indent + 2)}`;

    case 'Annot':
      return `${pad}Annot\n${pad}  term:\n${formatAst(term.term, indent + 2)}\n${pad}  type:\n${formatAst(term.type, indent + 2)}`;

    default:
      return `${pad}Unknown`;
  }
}

function tryInferType(term: TTerm, ctx: TContext = []): { success: true; type: string } | { success: false; error: string } {
  try {
    const inferredType = inferType(term, ctx);
    return { success: true, type: prettyPrint(inferredType) };
  } catch (e) {
    if (e instanceof TypeCheckError) {
      return { success: false, error: e.message };
    }
    return { success: false, error: String(e) };
  }
}

function analyzeSourceBlock(block: SourceBlock): BlockParseResult {
  const blockSource = block.lines.join('\n');

  // Check if this is a comment block
  if (block.isComment) {
    return {
      block,
      type: 'Comment',
      parseSuccess: true
    };
  }

  // Try to parse the block
  try {
    const declarations = parseDeclarations(blockSource);

    if (declarations.length === 0) {
      return {
        block,
        type: 'Unknown',
        parseSuccess: false,
        parseError: 'No declarations found'
      };
    }

    const firstDecl = declarations[0];

    // Determine block type
    if (block.isInductive || firstDecl.kind === 'inductive') {
      return {
        block,
        type: 'Inductive',
        name: firstDecl.name,
        parseSuccess: true
      };
    }

    if (firstDecl.kind === 'def' || firstDecl.kind === 'axiom' || firstDecl.kind === 'theorem' || firstDecl.kind === 'expr') {
      return {
        block,
        type: 'Term',
        name: firstDecl.name,
        parseSuccess: true
      };
    }

    return {
      block,
      type: 'Unknown',
      name: firstDecl.name,
      parseSuccess: true
    };

  } catch (e) {
    // Parse failed
    let errorMsg = 'Parse error';

    if (e instanceof ParseErrors) {
      errorMsg = e.errors.map(err => err.message).join('; ');
    } else if (e instanceof ParseError) {
      errorMsg = e.message;
    } else {
      errorMsg = String(e);
    }

    // Try to determine type from the source text
    const trimmed = blockSource.trim();
    if (trimmed.startsWith('inductive ')) {
      const match = trimmed.match(/^inductive\s+([a-zA-Z_][a-zA-Z0-9_']*)/);
      return {
        block,
        type: 'Inductive',
        name: match?.[1],
        parseSuccess: false,
        parseError: errorMsg
      };
    }

    // Try to extract name from signature line
    const firstLine = block.lines[0]?.trim() || '';
    const nameMatch = firstLine.match(/^([a-zA-Z_][a-zA-Z0-9_']*)\s*:/);

    return {
      block,
      type: nameMatch ? 'Term' : 'Unknown',
      name: nameMatch?.[1],
      parseSuccess: false,
      parseError: errorMsg
    };
  }
}

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

interface ASTViewerProps {
  term: TTerm;
  title?: string;
}

const ASTViewer: React.FC<ASTViewerProps> = ({ term, title }) => {
  const [expanded, setExpanded] = useState(true);

  return (
    <div>
      <div
        style={{
          display: 'flex',
          alignItems: 'center',
          gap: '8px',
          cursor: 'pointer',
          marginBottom: '8px',
        }}
        onClick={() => setExpanded(!expanded)}
      >
        <span style={{ color: '#6e7681' }}>{expanded ? '▼' : '▶'}</span>
        {title && <span style={{ color: '#8b949e', fontSize: '12px' }}>{title}</span>}
      </div>
      {expanded && (
        <div style={{ ...styles.codeBlock, ...styles.astTree }}>
          {formatAst(term)}
        </div>
      )}
    </div>
  );
};

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
    if (!result.checkSuccess) return '✗';
    return '✓';
  };

  const getStatusColor = () => {
    if (result.blockType === 'Comment') return '#8b949e';
    if (!result.parseSuccess) return '#f0883e';
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

      {/* Type check errors */}
      {result.parseSuccess && !result.checkSuccess && result.checkErrors.length > 0 && (
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

interface DeclarationCardProps {
  decl: ParsedDeclaration;
  index: number;
  typeResult: TypeCheckResult;
}

const DeclarationCard: React.FC<DeclarationCardProps> = ({ decl, index, typeResult }) => {
  const [showAst, setShowAst] = useState(false);

  return (
    <div style={styles.declCard}>
      <div style={{ display: 'flex', alignItems: 'center', justifyContent: 'space-between' }}>
        <div>
          <span style={{ ...styles.declKind, ...getKindStyle(decl.kind) }}>
            {decl.kind}
          </span>
          {decl.name && (
            <span style={styles.declName}>{decl.name}</span>
          )}
          {!decl.name && decl.kind === 'expr' && (
            <span style={{ color: '#8b949e', fontStyle: 'italic' }}>expression #{index + 1}</span>
          )}
        </div>
        <button
          onClick={() => setShowAst(!showAst)}
          style={{
            ...styles.examplesButton,
            padding: '4px 8px',
            fontSize: '11px',
          }}
        >
          {showAst ? 'Hide AST' : 'Show AST'}
        </button>
      </div>

      {/* Type information */}
      <div style={styles.codeBlock}>
        {typeResult.error ? (
          <div>
            <span style={styles.errorText}>⚠ Type Error: </span>
            <span style={{ color: '#f0883e' }}>{typeResult.error}</span>
          </div>
        ) : typeResult.inferredType ? (
          <div>
            <span style={styles.typeLabel}>Type:</span>
            <span style={styles.typeValue}>{typeResult.inferredType}</span>
          </div>
        ) : (
          <span style={{ color: '#6e7681' }}>No type information available</span>
        )}
      </div>

      {/* AST visualization */}
      {showAst && decl.value && (
        <div style={{ marginTop: '12px' }}>
          <ASTViewer term={decl.value} title="Value AST" />
          {decl.type && <ASTViewer term={decl.type} title="Type AST" />}
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
  const [showParseTree, setShowParseTree] = useState(false);
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

  // Parse the code
  const parseOutcome = useMemo((): ParseOutcome => {
    if (!code.trim()) {
      return { success: true, declarations: [] };
    }

    try {
      const declarations = parseDeclarations(code);
      return { success: true, declarations };
    } catch (e) {
      if (e instanceof ParseErrors) {
        return { success: false, errors: e.errors };
      }
      if (e instanceof ParseError) {
        return { success: false, errors: [e] };
      }
      throw e;
    }
  }, [code]);

  // Check all blocks with full type checking pipeline
  const blockCheckResults = useMemo((): BlockCheckResult[] => {
    if (!code.trim()) return [];
    return checkSourceBlocks(code);
  }, [code]);

  // Calculate block statistics
  const blockStats = useMemo(() => {
    return summarizeCheckResults(blockCheckResults);
  }, [blockCheckResults]);

  // Type check each declaration
  const typeCheckResults = useMemo((): TypeCheckResult[] => {
    if (!parseOutcome.success) return [];

    return parseOutcome.declarations.map((decl, index) => {
      const result: TypeCheckResult = {
        declIndex: index,
        name: decl.name,
        kind: decl.kind,
      };

      // Determine the type to display:
      // 1. If there's an explicit type annotation, use it (it's already parsed correctly)
      // 2. Otherwise, if there's a value, try to infer its type
      if (decl.type) {
        // Use the explicitly declared type
        result.inferredType = prettyPrint(decl.type);
      } else if (decl.value) {
        // No type annotation - infer from value
        const typeResult = tryInferType(decl.value);
        if (typeResult.success) {
          result.inferredType = typeResult.type;
        } else {
          result.error = typeResult.error;
        }
      }

      return result;
    });
  }, [parseOutcome]);

  // Calculate statistics
  const stats = useMemo(() => {
    if (!parseOutcome.success) return null;

    const total = parseOutcome.declarations.length;
    const withErrors = typeCheckResults.filter(r => r.error).length;
    const successful = total - withErrors;

    return { total, successful, withErrors };
  }, [parseOutcome, typeCheckResults]);

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
          message: error.message.replace(/^Parse error at line \d+, col \d+: /, ''),
          startLineNumber: error.line,
          startColumn: error.col,
          endLineNumber: error.line,
          endColumn: endCol,
          source: 'TT Parser',
        });
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

  const handleParseTreeClick = useCallback(() => {
    setShowParseTree(true);
  }, []);

  const handleCloseModal = useCallback(() => {
    setShowParseTree(false);
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
            <button style={styles.examplesButton} onClick={handleParseTreeClick}>
              Parse Tree
            </button>
          </div>

          {parseOutcome.success && stats && (
            <div style={{ display: 'flex', gap: '12px' }}>
              <span>{stats.total} declaration{stats.total !== 1 ? 's' : ''}</span>
              {stats.successful > 0 && (
                <span style={{ ...styles.badge, ...styles.badgeSuccess }}>
                  ✓ {stats.successful} typed
                </span>
              )}
              {stats.withErrors > 0 && (
                <span style={{ ...styles.badge, ...styles.badgeError }}>
                  ⚠ {stats.withErrors} error{stats.withErrors !== 1 ? 's' : ''}
                </span>
              )}
            </div>
          )}

          {!parseOutcome.success && (
            <span style={{ ...styles.badge, ...styles.badgeError }}>
              ⚠ {parseOutcome.errors.length} Parse Error{parseOutcome.errors.length !== 1 ? 's' : ''}
            </span>
          )}
        </div>
      </div>

      {/* Results Section */}
      <div style={styles.resultsSection}>
        {/* Parse Error Display (redundant with inline markers, but useful for details) */}
        {!parseOutcome.success && (
          <div style={{ ...styles.panel, ...styles.errorPanel }}>
            <h3 style={{ ...styles.sectionTitle, color: '#f85149', marginTop: 0 }}>
              Parse Error{parseOutcome.errors.length !== 1 ? 's' : ''} ({parseOutcome.errors.length})
            </h3>
            {parseOutcome.errors.map((error, idx) => (
              <div key={idx} style={{ marginBottom: idx < parseOutcome.errors.length - 1 ? '12px' : 0 }}>
                <div style={styles.errorText}>
                  Line {error.line}, Column {error.col}
                </div>
                <div style={{ marginTop: '4px' }}>{error.message}</div>
              </div>
            ))}
          </div>
        )}

        {/* Block Check Results Display */}
        {blockCheckResults.length > 0 && (
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
        )}

        {/* Success Results */}
        {parseOutcome.success && parseOutcome.declarations.length > 0 && (
          <div style={styles.twoColumn}>
            {/* Type Check Results */}
            <div>
              <h3 style={styles.sectionTitle}>Type Check Results</h3>
              {parseOutcome.declarations.map((decl, index) => (
                <DeclarationCard
                  key={index}
                  decl={decl}
                  index={index}
                  typeResult={typeCheckResults[index]}
                />
              ))}
            </div>

            {/* Quick Reference */}
            <div>
              <h3 style={styles.sectionTitle}>Operator Precedence</h3>
              <div style={styles.panel}>
                <table style={{ width: '100%', fontSize: '12px', borderCollapse: 'collapse' }}>
                  <thead>
                    <tr style={{ borderBottom: '1px solid #30363d' }}>
                      <th style={{ textAlign: 'left', padding: '4px 8px', color: '#8b949e' }}>Op</th>
                      <th style={{ textAlign: 'left', padding: '4px 8px', color: '#8b949e' }}>Prec</th>
                      <th style={{ textAlign: 'left', padding: '4px 8px', color: '#8b949e' }}>Assoc</th>
                    </tr>
                  </thead>
                  <tbody>
                    {Object.entries(DEFAULT_OPERATORS)
                      .sort((a, b) => b[1].precedence - a[1].precedence)
                      .slice(0, 12)
                      .map(([symbol, info]) => (
                        <tr key={symbol} style={{ borderBottom: '1px solid #21262d' }}>
                          <td style={{ padding: '4px 8px', color: '#7ee787' }}>{symbol}</td>
                          <td style={{ padding: '4px 8px', color: '#c9d1d9' }}>{info.precedence}</td>
                          <td style={{ padding: '4px 8px', color: '#8b949e' }}>{info.associativity}</td>
                        </tr>
                      ))}
                  </tbody>
                </table>
                <div style={{ marginTop: '12px', fontSize: '11px', color: '#6e7681' }}>
                  <div>Application: 100 (left)</div>
                  <div>Arrow (→): 25 (right)</div>
                </div>
              </div>

              <h3 style={{ ...styles.sectionTitle, marginTop: '24px' }}>Syntax Reference</h3>
              <div style={styles.panel}>
                <div style={{ fontSize: '12px', lineHeight: '1.8' }}>
                  <div><code style={{ color: '#7ee787' }}>\(x : T) =&gt; body</code> — Lambda</div>
                  <div><code style={{ color: '#7ee787' }}>(x : A) -&gt; B</code> — Pi type</div>
                  <div><code style={{ color: '#7ee787' }}>A -&gt; B</code> — Function type</div>
                  <div><code style={{ color: '#7ee787' }}>let x := v in e</code> — Let binding</div>
                  <div><code style={{ color: '#7ee787' }}>f x y</code> — Application</div>
                  <div><code style={{ color: '#7ee787' }}>?name</code> — Hole</div>
                  <div><code style={{ color: '#7ee787' }}>def n : T := v</code> — Definition</div>
                  <div><code style={{ color: '#7ee787' }}>theorem n : T := p</code> — Theorem</div>
                  <div><code style={{ color: '#7ee787' }}>axiom n : T</code> — Axiom</div>
                </div>
              </div>
            </div>
          </div>
        )}

        {/* Empty State */}
        {parseOutcome.success && parseOutcome.declarations.length === 0 && (
          <div style={{
            ...styles.panel,
            textAlign: 'center',
            color: '#8b949e',
            padding: '40px',
          }}>
            <div style={{ fontSize: '48px', marginBottom: '16px' }}>λ</div>
            <div style={{ fontSize: '16px', marginBottom: '8px' }}>No expressions yet</div>
            <div style={{ fontSize: '12px' }}>
              Type some TT language expressions above, or click "Load Examples"
            </div>
          </div>
        )}
      </div>

      {/* Parse Tree Modal */}
      {showParseTree && (
        <div style={styles.modalOverlay} onClick={handleCloseModal}>
          <div style={styles.modal} onClick={(e) => e.stopPropagation()}>
            <div style={styles.modalHeader}>
              <h2 style={styles.modalTitle}>Parse Tree</h2>
              <button style={styles.closeButton} onClick={handleCloseModal}>
                Close
              </button>
            </div>
            <div>
              {!parseOutcome.success ? (
                <div style={{ ...styles.panel, ...styles.errorPanel }}>
                  <div style={styles.errorText}>
                    Parse Error{parseOutcome.errors.length !== 1 ? 's' : ''} ({parseOutcome.errors.length})
                  </div>
                  {parseOutcome.errors.map((error, idx) => (
                    <div key={idx} style={{ marginTop: '12px' }}>
                      <div style={{ color: '#c9d1d9' }}>
                        Line {error.line}, Column {error.col}
                      </div>
                      <div style={{ marginTop: '4px', color: '#c9d1d9' }}>
                        {error.message}
                      </div>
                    </div>
                  ))}
                </div>
              ) : parseOutcome.declarations.length === 0 ? (
                <div style={{ ...styles.panel, textAlign: 'center', padding: '40px' }}>
                  <div style={{ color: '#8b949e' }}>No declarations to display</div>
                </div>
              ) : (
                <div>
                  {parseOutcome.declarations.map((decl, index) => (
                    <div key={index} style={{ marginBottom: '24px' }}>
                      <div style={{
                        marginBottom: '12px',
                        paddingBottom: '8px',
                        borderBottom: '1px solid #30363d',
                      }}>
                        <span style={{ ...styles.declKind, ...getKindStyle(decl.kind) }}>
                          {decl.kind}
                        </span>
                        {decl.name && (
                          <span style={styles.declName}>{decl.name}</span>
                        )}
                        {!decl.name && decl.kind === 'expr' && (
                          <span style={{ color: '#8b949e', fontStyle: 'italic' }}>
                            expression #{index + 1}
                          </span>
                        )}
                      </div>

                      {decl.kind === 'inductive' && decl.constructors && (
                        <div style={{ marginBottom: '16px' }}>
                          <div style={{ color: '#8b949e', fontSize: '12px', marginBottom: '8px' }}>
                            Constructors:
                          </div>
                          {decl.constructors.map((ctor, ctorIdx) => (
                            <div key={ctorIdx} style={styles.codeBlock}>
                              <div style={{ color: '#7ee787', marginBottom: '4px' }}>
                                {ctor.name}
                              </div>
                              <ASTViewer term={ctor.type} title={`Constructor Type AST`} />
                            </div>
                          ))}
                        </div>
                      )}

                      {decl.type && (
                        <div style={{ marginBottom: '12px' }}>
                          <ASTViewer term={decl.type} title="Type AST" />
                        </div>
                      )}

                      {decl.value && (
                        <div>
                          <ASTViewer term={decl.value} title="Value AST" />
                        </div>
                      )}
                    </div>
                  ))}
                </div>
              )}
            </div>
          </div>
        </div>
      )}
    </div>
  );
};

export default TextEditorPage;
