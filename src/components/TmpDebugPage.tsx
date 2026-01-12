/**
 * TmpDebugPage - A debug page for viewing code and compilation results
 */
import React, { useRef, useMemo, useState, useCallback } from 'react';
import Editor, { OnMount, OnChange } from '@monaco-editor/react';
import type { editor as MonacoEditor } from 'monaco-editor';
import { compileTTFromText, CompileResult, CompiledBlock } from '../compiler/compile';

// Monaco type helpers
type Monaco = typeof import('monaco-editor');
type IStandaloneCodeEditor = MonacoEditor.IStandaloneCodeEditor;

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
      {block.declarations.map((decl, i) => (
        <div key={i}>
          <div style={styles.blockHeader}>
            <span style={{
              ...styles.blockBadge,
              ...(decl.kind === 'inductive' ? styles.blockBadgeInductive : styles.blockBadgeTerm)
            }}>
              {decl.kind === 'inductive' ? 'Inductive' : 'Term'}
            </span>
            {decl.name && <span style={styles.declName}>{decl.name}</span>}
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
                  <div key={j} style={styles.errorText}>{err}</div>
                ))}
              </div>
            )}
          </div>
        </div>
      ))}
    </div>
  );
}

export function TmpDebugPage() {
  const editorRef = useRef<IStandaloneCodeEditor | null>(null);
  const [code, setCode] = useState(SAMPLE_CODE);

  // Compile and type check the source code
  const compileResult = useMemo<CompileResult>(() => {
    return compileTTFromText(code);
  }, [code]);

  const handleEditorChange: OnChange = useCallback((value) => {
    setCode(value || '');
  }, []);

  const handleEditorDidMount: OnMount = (editor, monaco) => {
    editorRef.current = editor;

    // Register TT language
    monaco.languages.register({ id: 'tt' });
    monaco.languages.setMonarchTokensProvider('tt', {
      tokenizer: {
        root: [
          [/\b(inductive|where|Type)\b/, 'keyword'],
          [/--.*$/, 'comment'],
          [/"([^"\\]|\\.)*$/, 'string.invalid'],
          [/"/, 'string', '@string'],
          [/\d+/, 'number'],
          [/[=><!~?:&|+\-*/^%]+/, 'operator'],
          [/[;,.]/, 'delimiter'],
          [/[()[\]{}]/, '@brackets'],
          [/[A-Z]\w*/, 'type.identifier'],
          [/[a-z_]\w*/, 'identifier'],
          [/_/, 'keyword.control'],
        ],
        string: [
          [/[^\\"]+/, 'string'],
          [/\\./, 'string.escape'],
          [/"/, 'string', '@pop']
        ],
      }
    });

    monaco.editor.defineTheme('tt-dark', {
      base: 'vs-dark',
      inherit: true,
      rules: [
        { token: 'keyword', foreground: 'ff79c6', fontStyle: 'bold' },
        { token: 'keyword.control', foreground: 'ff79c6' },
        { token: 'type.identifier', foreground: '8be9fd' },
        { token: 'identifier', foreground: 'f8f8f2' },
        { token: 'operator', foreground: 'ff79c6' },
        { token: 'number', foreground: 'bd93f9' },
        { token: 'string', foreground: 'f1fa8c' },
        { token: 'comment', foreground: '6272a4', fontStyle: 'italic' },
      ],
      colors: {
        'editor.background': '#0d1117',
        'editor.foreground': '#c9d1d9',
        'editor.lineHighlightBackground': '#161b22',
        'editorCursor.foreground': '#c9d1d9',
        'editor.selectionBackground': '#264f78',
        'editorLineNumber.foreground': '#6e7681',
      }
    });

    monaco.editor.setTheme('tt-dark');
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
