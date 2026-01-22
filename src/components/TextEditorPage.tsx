/**
 * TextEditorPage - A page for editing code and viewing compilation results
 */
import React, { useRef, useMemo, useState, useCallback, useEffect } from 'react';
import Editor, { OnMount, OnChange } from '@monaco-editor/react';
import type { editor as MonacoEditor } from 'monaco-editor';
import { compileTTFromText, CompileResult, CompiledBlock, extractWildcardInlayHints, WildcardInlayHint, extractSemanticTokens, SemanticToken, extractHoleLocations, HoleLocation, CaseTree, TotalityResult } from '../compiler/compile';
import { serializeIndexPath, IndexPath, SourceRange, ElabMap, SourceMap } from '../types/source-position';
import { TTKTerm, prettyPrint as prettyPrintTTK } from '../compiler/kernel';

// Color palette for syntax highlighting (matches TextEditorPage)
const SYNTAX_COLORS = {
  keyword: '569cd6',        // Blue - for inductive, where, def, etc.
  keywordOperator: '94d0ff', // Light blue - for ->, =>
  typeKeyword: 'cf92cd',    // Light purple/pink - for Type, Prop
  comment: '6a9955',        // Green - for comments (-- and {- -})
  string: 'ce9178',         // Orange
  number: 'b5cea8',         // Light green
  identifier: 'd4d4d4',     // Light gray - default
  constName: '4ec9b0',      // Teal - for types/constructors (Nat, Vec, Zero, Cons)
  termName: 'e5b387',       // Warm yellow/tan - for function names (plus, nth)
  patternVar: '9cdcfe',     // Light blue - for pattern variables (x, n, h)
  delimiter: 'e5c995',      // Light tan/gold - for (, ), etc.
  namedBrace: '6e7681',     // Dark grey - for { } in named arguments/binders
  hole: 'f85149',           // Red for holes (unfinished code)
  absurd: '4fc1ff',         // Bright cyan - for #absurd marker
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
    { token: 'identifier.const', foreground: SYNTAX_COLORS.constName },
    { token: 'identifier.term', foreground: SYNTAX_COLORS.termName },
    { token: 'identifier.pattern', foreground: SYNTAX_COLORS.patternVar },
    { token: 'delimiter', foreground: SYNTAX_COLORS.delimiter },
    { token: 'delimiter.bracket', foreground: SYNTAX_COLORS.delimiter },
    { token: 'variable.predefined', foreground: SYNTAX_COLORS.hole },
    { token: 'variable.wildcard', foreground: SYNTAX_COLORS.patternVar },
    // Semantic token rules (override lexical highlighting)
    { token: 'termName', foreground: SYNTAX_COLORS.termName },
    { token: 'constName', foreground: SYNTAX_COLORS.constName },
    { token: 'boundVar', foreground: SYNTAX_COLORS.patternVar },
    { token: 'patternVar', foreground: SYNTAX_COLORS.patternVar },
    { token: 'absurd', foreground: SYNTAX_COLORS.absurd },
    { token: 'namedBrace', foreground: SYNTAX_COLORS.namedBrace },
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
    // Warning squiggle color matches hole color (bright cyan)
    'editorWarning.foreground': '#' + SYNTAX_COLORS.hole,
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
  _blockStartLine: number  // Note: unused - sourceMap already has absolute positions
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
          // sourceMap already has absolute positions (adjusted in compile.ts)
          return range;
        }
      }
    }
    return null;
  }

  // Look up the source range via sourceMap
  const range = sourceMap.get(surfacePathStr);
  if (!range) return null;

  // sourceMap already has absolute positions (adjusted in compile.ts)
  return range;
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

inductive Fin : Nat -> Type where
  FZero : (n : Nat) -> Fin (Succ n)
  FSucc : (n : Nat) -> Fin n -> Fin (Succ n)

nth : (A : Type) -> (n : Nat) -> Vec A n -> Fin n -> A
nth A _ (VCons _ _ h _) (FZero _) = h
nth A _ (VCons _ (Succ _) h tail) (FSucc _ f) = nth _ _ tail f

inductive Void : Type where

absurd : (A : Type) -> Void -> A

inductive Equal : (A : Type) -> A -> A -> Type where
  refl : (A : Type) -> (a : A) -> Equal A a a

zeroNeqSucc : (n : Nat) -> Equal Nat Zero (Succ n) -> Void
zeroNeqSucc Z (refl _ _) = #absurd

double : Nat -> Nat
double n = ?sorry

right : (A : Type) -> (B : Type) -> B -> A -> B
right A B b = \\(x: A) => b

qux : Type
qux = Nat

qux' : Nat -> Type
qux' n = Nat

const : (A : Type) -> (B : Type) -> A -> B -> A
const _ _ a = \\ _ => a

swap : (A : Type) -> (B : Type) -> (C : Type) -> (f : A -> B -> C) -> B -> A -> C
swap _ _ _ f = \\ x y => f y x

{-
vecConcat : (A : Type) -> (a : Nat) -> (b : Nat) -> Vec A a -> Vec A b -> Vec A (plus a b)
vecConcat _ _ _ (VNil _) v = v
vecConcat A (Succ p) _ (VCons _ _ h tail) v = VCons _ _ h (vecConcat A p _ tail v)
-}

{-
vecConcat' : (A : Type) -> (a : Nat) -> (b : Nat) -> Vec A a -> Vec A b -> Vec A (plus a b)
vecConcat' _ _ _ (VNil _) v = v
vecConcat' A (Succ p) _ (VCons _ _ h tail) v = (swap _ (VCons _ _)) (vecConcat' A ((\\ d x => x) Zero p) _ tail v) h
-}

sym : (A : Type) -> (u : A) -> (v : A) -> Equal A u v -> Equal A v u
sym A u _ (refl _ _) = refl _ _

`;

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
    whiteSpace: 'pre-wrap',
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

// ============================================================================
// Case Tree Visualization
// ============================================================================

const caseTreeStyles = {
  container: {
    marginTop: '12px',
    padding: '12px',
    backgroundColor: '#0d1117',
    borderRadius: '4px',
    border: '1px solid #30363d',
    fontSize: '12px',
    fontFamily: "'JetBrains Mono', 'Fira Code', monospace",
  },
  header: {
    display: 'flex',
    alignItems: 'center',
    gap: '8px',
    marginBottom: '8px',
    color: '#8b949e',
    fontSize: '11px',
    fontWeight: 600,
    textTransform: 'uppercase' as const,
    letterSpacing: '0.5px',
  },
  exhaustiveBadge: {
    padding: '2px 6px',
    borderRadius: '3px',
    fontSize: '10px',
    fontWeight: 600,
  },
  exhaustiveYes: {
    backgroundColor: 'rgba(63, 185, 80, 0.2)',
    color: '#3fb950',
  },
  exhaustiveNo: {
    backgroundColor: 'rgba(248, 81, 73, 0.2)',
    color: '#f85149',
  },
  treeNode: {
    paddingLeft: '16px',
    borderLeft: '1px solid #30363d',
    marginLeft: '4px',
  },
  splitLabel: {
    color: '#8b949e',
    marginBottom: '4px',
  },
  branchRow: {
    display: 'flex',
    alignItems: 'flex-start',
    marginBottom: '4px',
  },
  ctorName: {
    color: '#ffa657',
    minWidth: '80px',
  },
  leafClause: {
    color: '#7ee787',
  },
  uncovered: {
    color: '#f85149',
    fontStyle: 'italic' as const,
  },
  absurd: {
    color: '#8b949e',
    fontStyle: 'italic' as const,
  },
  unreachableWarning: {
    marginTop: '8px',
    padding: '8px',
    backgroundColor: 'rgba(248, 81, 73, 0.1)',
    borderRadius: '4px',
    color: '#f85149',
    fontSize: '11px',
  },
};

/**
 * Render a case tree node recursively.
 * @param tree The case tree node
 * @param depth Current nesting depth (for indentation)
 */
function CaseTreeNode({ tree, depth = 0 }: { tree: CaseTree; depth?: number }): JSX.Element {
  if (tree.tag === 'Leaf') {
    return <span style={caseTreeStyles.leafClause}>→ clause {tree.clauseIndex}</span>;
  }

  if (tree.tag === 'Uncovered') {
    return <span style={caseTreeStyles.uncovered}>→ MISSING</span>;
  }

  if (tree.tag === 'Absurd') {
    return <span style={caseTreeStyles.absurd}>→ absurd</span>;
  }

  // Split node - all constructors are enumerated
  const branches = Array.from(tree.branches.entries());

  return (
    <div style={depth > 0 ? caseTreeStyles.treeNode : undefined}>
      {branches.map(([ctorName, subTree]) => (
        <div key={ctorName} style={caseTreeStyles.branchRow}>
          <span style={caseTreeStyles.ctorName}>{ctorName}:</span>
          <CaseTreeNode tree={subTree} depth={depth + 1} />
        </div>
      ))}
    </div>
  );
}

/**
 * Render totality checking results with case tree visualization
 */
function TotalityResultView({ result }: { result: TotalityResult }): JSX.Element | null {
  if (!result.caseTree) {
    return null;
  }

  return (
    <div style={caseTreeStyles.container}>
      <div style={caseTreeStyles.header}>
        <span>Case Tree</span>
        <span style={{
          ...caseTreeStyles.exhaustiveBadge,
          ...(result.isExhaustive ? caseTreeStyles.exhaustiveYes : caseTreeStyles.exhaustiveNo)
        }}>
          {result.isExhaustive ? 'Exhaustive' : 'Non-exhaustive'}
        </span>
      </div>
      <CaseTreeNode tree={result.caseTree} />
      {result.unreachableClauses.length > 0 && (
        <div style={caseTreeStyles.unreachableWarning}>
          Warning: Unreachable clause(s): {result.unreachableClauses.map(i => i + 1).join(', ')}
        </div>
      )}
    </div>
  );
}

// Block renderer component
function BlockRenderer({ block }: { block: CompiledBlock }) {
  let blockHeaderContent: React.ReactNode = null;
  let blockBodyContent: React.ReactNode = null;

  if (block.isComment) {
    blockHeaderContent = <span style={{ ...styles.blockBadge, ...styles.blockBadgeComment }}>Comment</span>;
    blockBodyContent = <pre style={{ margin: 0, color: '#6e7681' }}>
      {block.sourceLines.join('\n')}
    </pre>;
  }

  if (!block.parseSuccess) {
    blockHeaderContent = <span style={{ ...styles.blockBadge, ...styles.blockBadgeError }}>Parse Error</span>;
    blockBodyContent = block.parseErrors.map((err, i) => (
      <div key={i} style={styles.errorText}>
        Line {err.line}, Col {err.col}: {err.message}
      </div>
    ));
  }

  if (!block.nameResolutionSuccess) {
    blockHeaderContent = <span style={{ ...styles.blockBadge, ...styles.blockBadgeError }}>Name Error</span>;
    blockBodyContent = block.nameResolutionErrors.map((err, i) => (
      <div key={i} style={styles.errorText}>{err}</div>
    ));
  }

  if (blockHeaderContent && blockBodyContent) {
    return (
      <BlockCard header={blockHeaderContent} body={blockBodyContent} initiallyExpanded={false} />
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
          <BlockCard
            key={i}
            initiallyExpanded={decl.kind === 'term'}
            header={
              <>
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
              </>
            }
            body={
              <>
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
                {decl.totalityResult && (
                  <TotalityResultView result={decl.totalityResult} />
                )}</>
            }
          />
        )
      })}
    </div>
  );
}

function BlockCard(props: { header: React.ReactNode, body: React.ReactNode, initiallyExpanded?: boolean }) {
  const [expanded, setExpanded] = useState(props.initiallyExpanded ?? true)

  return (
    <div style={styles.blockCard}>
      <div style={styles.blockHeader} onClick={() => setExpanded(e => !e)}>
        {props.header}
      </div>
      {expanded && <div style={styles.blockBody}>
        {props.body}
      </div>}
    </div>
  )
}

export function TextEditorPage() {
  const editorRef = useRef<IStandaloneCodeEditor | null>(null);
  const monacoRef = useRef<Monaco | null>(null);
  const [code, setCode] = useState(SAMPLE_CODE);
  const [editorReady, setEditorReady] = useState(false);
  // Ref to store current wildcard hints (updated from compileResult)
  const wildcardHintsRef = useRef<WildcardInlayHint[]>([]);
  // Ref to store current semantic tokens (updated from compileResult)
  const semanticTokensRef = useRef<SemanticToken[]>([]);
  // Event emitter for semantic tokens changes
  const semanticTokensEventRef = useRef<{
    fire: () => void;
    event: import('monaco-editor').IEvent<void>;
  } | null>(null);

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

  // Extract wildcard hints from compile result
  const wildcardHints = useMemo(() => {
    return extractWildcardInlayHints(compileResult);
  }, [compileResult]);

  // Extract semantic tokens from compile result
  const semanticTokens = useMemo(() => {
    return extractSemanticTokens(compileResult);
  }, [compileResult]);

  // Extract hole locations from compile result for warning markers
  const holeLocations = useMemo(() => {
    return extractHoleLocations(compileResult);
  }, [compileResult]);

  // Keep the refs in sync with the latest data
  // Monaco's providers will read from these refs when they need to render
  useEffect(() => {
    wildcardHintsRef.current = wildcardHints;
  }, [wildcardHints]);

  useEffect(() => {
    semanticTokensRef.current = semanticTokens;
    // Signal Monaco to refresh semantic tokens
    if (semanticTokensEventRef.current) {
      semanticTokensEventRef.current.fire();
    }
  }, [semanticTokens]);

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
              err.env.indexPath,
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

    // Add warning markers for holes (user-created holes are unsound)
    for (const hole of holeLocations) {
      markers.push({
        severity: monaco.MarkerSeverity.Warning,
        message: `Holes are unsound.`,
        startLineNumber: hole.line,
        startColumn: hole.column,
        endLineNumber: hole.line,
        endColumn: hole.endColumn,
        source: 'TT Holes',
      });
    }

    monaco.editor.setModelMarkers(model, 'tt-compiler', markers);
  }, [compileResult, editorReady, holeLocations]);

  const handleEditorDidMount: OnMount = (editor, monaco) => {
    editorRef.current = editor;
    monacoRef.current = monaco;
    setEditorReady(true);

    // Register TT language
    monaco.languages.register({ id: 'tt' });

    // Simplified tokenizer - semantic tokens from parse tree handle identifier classification
    monaco.languages.setMonarchTokensProvider('tt', {
      tokenizer: {
        root: [
          // Comments - multiline {- -} must come FIRST
          [/\{-/, 'comment', '@comment'],
          [/--.*$/, 'comment'],

          // Type keywords (Type, Prop)
          [/\b(Type|Prop)\b/, 'type.identifier'],

          // Keywords
          [/\b(inductive|where|let|in|fun)\b/, 'keyword'],

          // Holes (unfinished code that needs attention)
          [/\?[a-zA-Z_][a-zA-Z0-9_']*/, 'variable.predefined'],

          // Wildcards (will be solved during elaboration)
          [/_/, 'variable.wildcard'],

          // Identifiers - semantic tokens will override with proper classification
          [/[a-zA-Z_][a-zA-Z0-9_']*/, 'identifier'],

          // Numbers
          [/\d+/, 'number'],

          // Operators
          [/->|=>/, 'keyword.operator'],
          [/[=:+\-*/\\<>!|]+/, 'delimiter'],

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

    // Register inlay hints provider for wildcard names
    monaco.languages.registerInlayHintsProvider('tt', {
      provideInlayHints: (_model: MonacoEditor.ITextModel, range: { startLineNumber: number; endLineNumber: number }) => {
        const hints = wildcardHintsRef.current;
        const inlayHints: import('monaco-editor').languages.InlayHint[] = [];

        for (const hint of hints) {
          // Check if hint is within the requested range
          if (hint.line >= range.startLineNumber && hint.line <= range.endLineNumber) {
            inlayHints.push({
              kind: monaco.languages.InlayHintKind.Parameter,
              position: { lineNumber: hint.line, column: hint.column },
              label: hint.name,
              paddingLeft: false,
              paddingRight: false,
            });
          }
        }

        return { hints: inlayHints, dispose: () => { } };
      }
    });

    // Register semantic tokens provider for precise highlighting
    // This overrides lexical highlighting with semantic information from the compiler
    const tokenTypes = ['termName', 'constName', 'boundVar', 'patternVar', 'absurd', 'namedBrace'];
    const tokenModifiers: string[] = [];

    // Create an event emitter for signaling token changes
    const emitter = new monaco.Emitter<void>();
    semanticTokensEventRef.current = {
      fire: () => emitter.fire(),
      event: emitter.event
    };

    monaco.languages.registerDocumentSemanticTokensProvider('tt', {
      getLegend: () => ({
        tokenTypes,
        tokenModifiers
      }),
      onDidChange: emitter.event,
      provideDocumentSemanticTokens: (_model: MonacoEditor.ITextModel) => {
        const tokens = semanticTokensRef.current;

        // Monaco expects delta-encoded tokens:
        // [deltaLine, deltaStartChar, length, tokenType, tokenModifiers]
        // Tokens must be sorted by line, then column
        const sortedTokens = [...tokens].sort((a, b) => {
          if (a.line !== b.line) return a.line - b.line;
          return a.column - b.column;
        });

        const data: number[] = [];
        let prevLine = 0;
        let prevCol = 0;

        for (const token of sortedTokens) {
          const tokenTypeIndex = tokenTypes.indexOf(token.type);
          if (tokenTypeIndex === -1) continue;

          const deltaLine = token.line - 1 - prevLine;  // Monaco is 0-indexed
          const deltaCol = deltaLine === 0 ? token.column - 1 - prevCol : token.column - 1;

          data.push(deltaLine, deltaCol, token.length, tokenTypeIndex, 0);

          prevLine = token.line - 1;
          prevCol = token.column - 1;
        }

        return {
          data: new Uint32Array(data),
          resultId: undefined
        };
      },
      releaseDocumentSemanticTokens: () => { }
    });
  };

  return (
    <div style={styles.container}>
      <div style={styles.header}>
        <h2 style={styles.title}>Text Editor</h2>
        <p style={styles.subtitle}>Edit code and view compilation results</p>
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
                'semanticHighlighting.enabled': true,
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
