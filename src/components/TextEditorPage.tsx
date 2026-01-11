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
import { generateEliminator } from '../types/tt-eliminator';
import { InductiveTypeDef } from '../types/tt-examples';
import { prettyPrint } from '../types/tt-core';
import { prettyPrint as prettyPrintTTK } from '../types/tt-kernel';
import { useSelectionTypeInfo } from '../hooks/useSelectionTypeInfo';
import { SplitTreeViewer } from './SplitTreeViewer';
import { PatternElabStepperViewer } from './PatternElabStepperViewer';
import { ConstructorInfo as StepperConstructorInfo } from '../types/pattern-elab-stepper';
import { TTKTerm } from '../types/tt-kernel';
import { IndexPath } from '../types/source-position';
import { resolveCheckErrorLocation } from '../types/error-resolution';

// ============================================================================
// Types
// ============================================================================

// Monaco type helpers
type Monaco = typeof import('monaco-editor');
type IStandaloneCodeEditor = MonacoEditor.IStandaloneCodeEditor;

// ============================================================================
// Utilities
// ============================================================================

/**
 * Replace underscores in source with named metas (#1, #2, etc.)
 * Returns the modified source and a count of metas found.
 *
 * Uses smart naming: standalone underscores become #1, #2, etc.
 * Underscores in identifiers (like some_var) are preserved.
 */
function nameUnderscoresInSource(source: string): { namedSource: string; metaCount: number } {
  let count = 0;
  // Match standalone underscores (not part of identifiers)
  // A standalone _ is preceded by non-identifier char (or start) and followed by non-identifier char (or end)
  const namedSource = source.replace(/(?<![a-zA-Z0-9_α-ωΑ-Ω])_(?![a-zA-Z0-9_α-ωΑ-Ω])/g, () => {
    count++;
    return `#${count}`;
  });
  return { namedSource, metaCount: count };
}

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
  typeInfoPanel: {
    backgroundColor: '#161b22',
    border: '1px solid #30363d',
    borderRadius: '6px',
    padding: '12px 16px',
    marginTop: '12px',
    fontFamily: "'JetBrains Mono', 'Fira Code', 'Consolas', monospace",
  },
  typeInfoLabel: {
    fontSize: '11px',
    fontWeight: 600,
    color: '#8b949e',
    textTransform: 'uppercase' as const,
    letterSpacing: '0.5px',
    marginBottom: '8px',
  },
  typeInfoCode: {
    color: '#e6edf3',
    fontSize: '13px',
  },
  typeInfoType: {
    color: '#7ee787',
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

inductive Vec : Type -> Nat -> Type where
  VNil : (A: Type) -> Vec A Zero
  VCons : (A : Type) -> (n : Nat) -> A -> Vec A n -> Vec A (Succ n)

inductive Equal : (A: Type) -> A -> A -> Type where
  refl : (A : Type) -> (x : A) -> Equal A x x

swap : (A : Type) -> (f : A -> A -> A) -> (A -> A -> A)
swap A = \\f => \\(x: A) (y: A) => f y x

swap_ : (A : Type) -> (f : A -> A -> A) -> (A -> A -> A)
swap_ a = \\f => \\x y => f y x

swap' : (A : Type) -> (f : A -> A -> A) -> (A -> A -> A)
swap' a f = \\x y => f y x

swap'' : (A : Type) -> (f : A -> A -> A) -> (A -> A -> A)
swap'' a f x = \\y => f y x

swap''' : (A : Type) -> (f : A -> A -> A) -> (A -> A -> A)
swap''' a f x y = f y x

const : (A : Type) -> (B : Type) -> A -> B -> A
const = \\ A B x y => x

twice' : Nat -> Nat
twice' n = plus n n

twice : Nat -> Nat
twice = \\ n => plus n n

vecConcat : (A : Type) -> (a : Nat) -> (b : Nat) -> Vec A a -> Vec A b -> Vec A (plus a b)
vecConcat _ _ _ (VNil _) v = v
vecConcat _ _ _ (VCons _ _ h tail) v = VCons _ _ h (vecConcat _ _ _ tail v)
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
  onStepperError?: (error: string, blockIndex: number, clauseIndex: number, patternIndex?: number) => void;
}

const EnhancedBlockCard: React.FC<EnhancedBlockCardProps> = ({ result, index, onStepperError }) => {
  const [showErrors, setShowErrors] = useState(true);
  const [showElimModal, setShowElimModal] = useState(false);
  const [showCompileInfoModal, setShowCompileInfoModal] = useState(false);
  const [showStepperModal, setShowStepperModal] = useState(false);

  // Generate eliminator on-the-fly when modal is open
  const eliminatorType = useMemo(() => {
    if (!showElimModal) return null;
    if (result.blockType !== 'Inductive' || !result.checkSuccess) return null;

    // Get the first declaration (the inductive type)
    const decl = result.declarations[0];
    if (!decl || decl.kind !== 'inductive' || !decl.type || !decl.constructors || !decl.name) {
      return null;
    }

    // Build InductiveTypeDef from the parsed declaration
    const inductiveDef: InductiveTypeDef = {
      name: decl.name,
      type: decl.type,
      constructors: decl.constructors.map(c => ({ name: c.name, type: c.type }))
    };

    try {
      const elimType = generateEliminator(inductiveDef);
      return prettyPrint(elimType);
    } catch (e) {
      return `Error generating eliminator: ${e instanceof Error ? e.message : String(e)}`;
    }
  }, [showElimModal, result]);

  // Generate compile info on-the-fly when modal is open
  const compileInfo = useMemo(() => {
    if (!showCompileInfoModal) return null;

    const rawSource = result.block.lines.join('\n');
    // Replace underscores with named metas (#1, #2, etc.)
    const { namedSource: source } = nameUnderscoresInSource(rawSource);
    const decl = result.declarations[0];

    // Parsed TT (surface syntax)
    let parsedTT = '';
    if (decl) {
      if (decl.name) {
        parsedTT += `${decl.name}`;
      }
      if (decl.type) {
        parsedTT += ` : ${prettyPrint(decl.type)}`;
      }
      if (decl.value) {
        parsedTT += `\n${decl.name || '_'} = ${prettyPrint(decl.value)}`;
      }
      if (decl.kind === 'inductive' && decl.constructors) {
        parsedTT += '\nConstructors:';
        for (const ctor of decl.constructors) {
          parsedTT += `\n  ${ctor.name} : ${prettyPrint(ctor.type)}`;
        }
      }
    } else {
      parsedTT = '(no declaration parsed)';
    }

    // Elaborated TTK (kernel syntax)
    let elabTTK = '';
    const queryData = result.typeQueryData;
    if (queryData) {
      const contextNames = queryData.context.map(b => b.name);
      if (queryData.kernelType) {
        elabTTK += `Type: ${prettyPrintTTK(queryData.kernelType, contextNames)}`;
      }
      if (queryData.kernelValue) {
        elabTTK += `\nValue: ${prettyPrintTTK(queryData.kernelValue, contextNames)}`;
      }
    } else {
      elabTTK = '(no elaboration data available)';
    }

    // Checked TTK (after type checking)
    // Show the substitution/resolution list from pattern matching
    let checkedTTK = '';
    if (queryData?.clauseResults && queryData.clauseResults.length > 0) {
      const contextNames = queryData.context.map(b => b.name);
      const lines: string[] = [];

      for (let clauseIdx = 0; clauseIdx < queryData.clauseResults.length; clauseIdx++) {
        const clauseResult = queryData.clauseResults[clauseIdx];

        if (queryData.clauseResults.length > 1) {
          lines.push(`Clause ${clauseIdx + 1}:`);
        }

        // Show solved bindings (pattern variables with their types)
        // Generate display names: use actual name if not '_', otherwise generate #N
        let wildcardCounter = 1;
        const displayNames: string[] = [];
        for (const binding of clauseResult.solvedBindings) {
          if (binding.name === '_') {
            displayNames.push(`#${wildcardCounter++}`);
          } else {
            displayNames.push(binding.name);
          }
        }

        if (clauseResult.solvedBindings.length > 0) {
          lines.push('  Pattern bindings:');
          for (let i = 0; i < clauseResult.solvedBindings.length; i++) {
            const binding = clauseResult.solvedBindings[i];
            const typeStr = prettyPrintTTK(binding.type, contextNames);
            lines.push(`    ${displayNames[i]} : ${typeStr}`);
          }
        }

        // Show substitution (unified metas)
        if (clauseResult.substitution.size > 0) {
          lines.push('  Resolutions:');
          // Build context for printing substitution values
          // De Bruijn indices are reversed: index 0 = most recent binding
          // So we need to reverse displayNames for prettyPrint context
          const reversedDisplayNames = [...displayNames].reverse();
          const fullContext = [...reversedDisplayNames, ...contextNames];

          for (const [key, value] of clauseResult.substitution) {
            // Skip internal debug entries (name:X entries are for debugging only)
            if (key.startsWith('name:')) {
              continue;
            }

            const valueStr = prettyPrintTTK(value, fullContext);
            // Convert var:N keys to more readable form
            if (key.startsWith('var:')) {
              const deBruijnIdx = parseInt(key.slice(4), 10);
              // Convert De Bruijn index to binding order index
              // De Bruijn index N in a context of length L corresponds to binding at position (L - 1 - N)
              const bindingIdx = displayNames.length - 1 - deBruijnIdx;
              // Try to find a name for this variable
              const name = bindingIdx >= 0 && bindingIdx < displayNames.length
                ? displayNames[bindingIdx]
                : `#${deBruijnIdx + 1}`;
              lines.push(`    ${name} = ${valueStr}`);
            } else {
              // Show hole substitutions (like ?x = term)
              lines.push(`    ${key} = ${valueStr}`);
            }
          }
        }

        if (clauseIdx < queryData.clauseResults.length - 1) {
          lines.push('');
        }
      }

      checkedTTK = lines.length > 0 ? lines.join('\n') : '(no resolutions)';
    } else {
      checkedTTK = '(no pattern matching data)';
    }

    return { source, parsedTT, elabTTK, checkedTTK };
  }, [showCompileInfoModal, result]);

  // Generate stepper data from actual parsed data
  const stepperData = useMemo(() => {
    if (!showStepperModal) return null;
    if (!result.name) return null;

    const queryData = result.typeQueryData;
    if (!queryData?.kernelType || !queryData?.kernelValue) {
      return null;
    }

    const fnType = queryData.kernelType;
    const fnValue = queryData.kernelValue;

    // Only support Match expressions (functions with pattern matching)
    if (fnValue.tag !== 'Match' || fnValue.clauses.length === 0) {
      return null;
    }

    // Build constructor environment from the typing context
    // Each constructor in context has type like: Zero : Nat or Succ : Nat -> Nat
    const env = new Map<string, StepperConstructorInfo>();

    // Helper to unwrap Pi types and extract params + return type
    const unwrapPi = (type: TTKTerm): { params: Array<{ name: string; type: TTKTerm }>; returnType: TTKTerm } => {
      const params: Array<{ name: string; type: TTKTerm }> = [];
      let curr = type;
      while (curr.tag === 'Binder' && curr.binderKind.tag === 'BPi') {
        params.push({ name: curr.name, type: curr.domain });
        curr = curr.body;
      }
      return { params, returnType: curr };
    };

    // Helper to check if a type looks like it returns an inductive type (not Type/Sort)
    const isConstructorType = (type: TTKTerm): boolean => {
      const { returnType } = unwrapPi(type);
      // Constructors return applications or constants, not Sort/Type
      return returnType.tag === 'App' || returnType.tag === 'Const';
    };

    // Extract constructors from context
    for (const binding of queryData.context) {
      if (isConstructorType(binding.type)) {
        const { params, returnType } = unwrapPi(binding.type);
        env.set(binding.name, {
          name: binding.name,
          params,
          returnType
        });
      }
    }

    // Build typing context from all bindings (for RHS type inference)
    const typingContext = queryData.context.map(binding => ({
      name: binding.name,
      type: binding.type
    }));

    return {
      clauses: fnValue.clauses,
      fnType,
      fnName: result.name,
      env,
      typingContext
    };
  }, [showStepperModal, result]);

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

  // Build param/index display for inductive types
  const paramDisplay = result.inductiveParams && result.inductiveParams.length > 0
    ? result.inductiveParams.map(p =>
      `[${p.isIndex ? 'index' : 'param'} ${p.name} : ${p.type}]`
    ).join(' ')
    : null;

  return (
    <div style={styles.blockBox}>
      <div style={styles.blockHeader}>
        <span style={{ color: getStatusColor(), marginRight: '8px', fontSize: '14px' }}>
          {getStatusIcon()}
        </span>
        <span style={{ ...styles.blockTypeLabel, ...getTypeStyle() }}>
          {typeLabel}{nameDisplay}
        </span>
        {paramDisplay && (
          <span style={{
            marginLeft: '8px',
            fontSize: '11px',
            color: '#8b949e',
            fontFamily: 'monospace'
          }}>
            {paramDisplay}
          </span>
        )}
        {/* Show Elim button for successfully typechecked inductive types */}
        {result.blockType === 'Inductive' && result.checkSuccess && (
          <button
            onClick={() => setShowElimModal(true)}
            style={{
              marginLeft: '12px',
              padding: '2px 8px',
              backgroundColor: '#21262d',
              color: '#58a6ff',
              border: '1px solid #30363d',
              borderRadius: '4px',
              cursor: 'pointer',
              fontSize: '11px',
              fontWeight: 500,
            }}
          >
            Show Elim
          </button>
        )}
        {/* Compile Info button - available when parsing succeeded */}
        {result.parseSuccess && result.declarations.length > 0 && (
          <button
            onClick={() => setShowCompileInfoModal(true)}
            style={{
              marginLeft: '8px',
              padding: '2px 8px',
              backgroundColor: '#21262d',
              color: '#8b949e',
              border: '1px solid #30363d',
              borderRadius: '4px',
              cursor: 'pointer',
              fontSize: '11px',
              fontWeight: 500,
            }}
          >
            Compile Info
          </button>
        )}
        {/* Stepper button - available for Term blocks (functions with pattern matching) */}
        {result.blockType === 'Term' && (
          <button
            onClick={() => setShowStepperModal(true)}
            style={{
              marginLeft: '8px',
              padding: '2px 8px',
              backgroundColor: '#21262d',
              color: '#d2a8ff',
              border: '1px solid #30363d',
              borderRadius: '4px',
              cursor: 'pointer',
              fontSize: '11px',
              fontWeight: 500,
            }}
          >
            ▶ Stepper
          </button>
        )}
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

      {/* Split Tree Viewer for pattern matching functions */}
      {result.splitTree && (
        <SplitTreeViewer
          tree={result.splitTree}
          functionName={result.name}
        />
      )}

      {/* Eliminator Modal */}
      {showElimModal && (
        <div style={styles.modalOverlay} onClick={() => setShowElimModal(false)}>
          <div style={styles.modal} onClick={(e) => e.stopPropagation()}>
            <div style={styles.modalHeader}>
              <h3 style={styles.modalTitle}>
                {result.name}Elim
              </h3>
              <button
                style={styles.closeButton}
                onClick={() => setShowElimModal(false)}
              >
                Close
              </button>
            </div>
            <div style={styles.codeBlock}>
              <code style={{ color: '#7ee787', whiteSpace: 'pre-wrap', wordBreak: 'break-word' }}>
                {result.name}Elim : {eliminatorType || 'Unable to generate eliminator'}
              </code>
            </div>
          </div>
        </div>
      )}

      {/* Compile Info Modal */}
      {showCompileInfoModal && compileInfo && (
        <div style={styles.modalOverlay} onClick={() => setShowCompileInfoModal(false)}>
          <div style={{ ...styles.modal, maxWidth: '900px' }} onClick={(e) => e.stopPropagation()}>
            <div style={styles.modalHeader}>
              <h3 style={styles.modalTitle}>
                Compile Info: {result.name || 'anonymous'}
              </h3>
              <button
                style={styles.closeButton}
                onClick={() => setShowCompileInfoModal(false)}
              >
                Close
              </button>
            </div>

            {/* Source */}
            <div style={{ marginBottom: '16px' }}>
              <div style={{
                fontSize: '12px',
                fontWeight: 600,
                color: '#58a6ff',
                marginBottom: '8px',
                textTransform: 'uppercase',
                letterSpacing: '0.5px'
              }}>
                Source
              </div>
              <div style={styles.codeBlock}>
                <pre style={{ margin: 0, color: '#c9d1d9', whiteSpace: 'pre-wrap', wordBreak: 'break-word' }}>
                  {compileInfo.source}
                </pre>
              </div>
            </div>

            {/* Parsed TT */}
            <div style={{ marginBottom: '16px' }}>
              <div style={{
                fontSize: '12px',
                fontWeight: 600,
                color: '#3fb950',
                marginBottom: '8px',
                textTransform: 'uppercase',
                letterSpacing: '0.5px'
              }}>
                Parsed TT (Surface Syntax)
              </div>
              <div style={styles.codeBlock}>
                <pre style={{ margin: 0, color: '#7ee787', whiteSpace: 'pre-wrap', wordBreak: 'break-word' }}>
                  {compileInfo.parsedTT}
                </pre>
              </div>
            </div>

            {/* Elaborated TTK */}
            <div style={{ marginBottom: '16px' }}>
              <div style={{
                fontSize: '12px',
                fontWeight: 600,
                color: '#d29922',
                marginBottom: '8px',
                textTransform: 'uppercase',
                letterSpacing: '0.5px'
              }}>
                Elaborated TTK (Kernel)
              </div>
              <div style={styles.codeBlock}>
                <pre style={{ margin: 0, color: '#ffc66d', whiteSpace: 'pre-wrap', wordBreak: 'break-word' }}>
                  {compileInfo.elabTTK}
                </pre>
              </div>
            </div>

            {/* Checked TTK */}
            <div>
              <div style={{
                fontSize: '12px',
                fontWeight: 600,
                color: '#a371f7',
                marginBottom: '8px',
                textTransform: 'uppercase',
                letterSpacing: '0.5px'
              }}>
                Checked TTK (After Type Checking)
              </div>
              <div style={styles.codeBlock}>
                <pre style={{ margin: 0, color: '#d2a8ff', whiteSpace: 'pre-wrap', wordBreak: 'break-word' }}>
                  {compileInfo.checkedTTK}
                </pre>
              </div>
            </div>
          </div>
        </div>
      )}

      {/* Stepper Modal */}
      {showStepperModal && stepperData && (
        <div style={styles.modalOverlay} onClick={() => setShowStepperModal(false)}>
          <div style={{ ...styles.modal, maxWidth: '1000px', width: '900px', height: '80vh', overflow: 'auto' }} onClick={(e) => e.stopPropagation()}>
            <PatternElabStepperViewer
              clauses={stepperData.clauses}
              fnType={stepperData.fnType}
              fnName={stepperData.fnName}
              env={stepperData.env}
              typingContext={stepperData.typingContext}
              onClose={() => setShowStepperModal(false)}
              onError={onStepperError ? (error, clauseIndex, patternIndex) => onStepperError(error, index, clauseIndex, patternIndex) : undefined}
            />
          </div>
        </div>
      )}
      {showStepperModal && !stepperData && (
        <div style={styles.modalOverlay} onClick={() => setShowStepperModal(false)}>
          <div style={{ ...styles.modal, maxWidth: '400px', padding: '20px' }} onClick={(e) => e.stopPropagation()}>
            <div style={{ color: '#c9d1d9', marginBottom: '16px' }}>
              <strong>Stepper not available</strong>
            </div>
            <div style={{ color: '#8b949e', fontSize: '14px' }}>
              Pattern elaboration stepper is only available for functions with pattern matching clauses.
            </div>
            <button
              onClick={() => setShowStepperModal(false)}
              style={{
                marginTop: '16px',
                padding: '6px 12px',
                backgroundColor: '#21262d',
                color: '#c9d1d9',
                border: '1px solid #30363d',
                borderRadius: '4px',
                cursor: 'pointer',
              }}
            >
              Close
            </button>
          </div>
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

  // Track stepper errors for bubbling to markers
  // Key: "blockIndex-clauseIndex-patternIndex", Value: error message and indices
  const [stepperErrors, setStepperErrors] = useState<Map<string, { error: string; blockIndex: number; clauseIndex: number; patternIndex?: number }>>(new Map());

  // Clear stepper errors when code changes (so stale errors don't persist)
  useEffect(() => {
    setStepperErrors(new Map());
  }, [code]);

  // Handler for stepper errors - adds them to the marker system
  const handleStepperError = useCallback((error: string, blockIndex: number, clauseIndex: number, patternIndex?: number) => {
    const key = `${blockIndex}-${clauseIndex}-${patternIndex ?? 'none'}`;
    setStepperErrors(prev => {
      const next = new Map(prev);
      next.set(key, { error, blockIndex, clauseIndex, patternIndex });
      return next;
    });
  }, []);

  // Type information for the current cursor position/selection
  const selectionTypeInfo = useSelectionTypeInfo(editorRef.current, blockCheckResults, code);

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

    // Add stepper errors (bubbled from pattern elaboration stepper)
    for (const [, { error, blockIndex, clauseIndex, patternIndex }] of stepperErrors) {
      const blockResult = blockCheckResults[blockIndex];
      if (blockResult && blockResult.typeQueryData) {
        // Construct path to the specific pattern within the clause
        // Path: value.clauses[clauseIndex].patterns[patternIndex] (if patternIndex available)
        // Otherwise: value.clauses[clauseIndex]
        const errorPath: IndexPath = [
          { kind: 'field', name: 'value' },
          { kind: 'field', name: 'clauses' },
          { kind: 'array', index: clauseIndex }
        ];

        // If we have a pattern index, add it to get more specific location
        if (patternIndex !== undefined) {
          errorPath.push({ kind: 'field', name: 'patterns' });
          errorPath.push({ kind: 'array', index: patternIndex });
        }

        // Try to resolve the location using the source maps
        const location = resolveCheckErrorLocation(
          { message: error, path: errorPath },
          blockResult.typeQueryData.elabMap,
          blockResult.typeQueryData.sourceMap
        );

        if (location) {
          markers.push({
            severity: monaco.MarkerSeverity.Error,
            message: `Pattern elaboration: ${error}`,
            startLineNumber: location.start.line,
            startColumn: location.start.col,
            endLineNumber: location.end.line,
            endColumn: location.end.col,
            source: 'TT Pattern Stepper',
          });
        } else {
          // Fallback to first line of block if location can't be resolved
          const firstLine = blockResult.block.startLine;
          const lineContent = model.getLineContent(firstLine);
          markers.push({
            severity: monaco.MarkerSeverity.Error,
            message: `Pattern elaboration: ${error}`,
            startLineNumber: firstLine,
            startColumn: 1,
            endLineNumber: firstLine,
            endColumn: lineContent.length + 1,
            source: 'TT Pattern Stepper',
          });
        }
      }
    }

    monaco.editor.setModelMarkers(model, 'tt-checker', markers);
  }, [blockCheckResults, editorMounted, stepperErrors]);

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

    // Add toggle comment action (Cmd+/ or Ctrl+/)
    editor.addAction({
      id: 'toggle-line-comment',
      label: 'Toggle Line Comment',
      keybindings: [
        monaco.KeyMod.CtrlCmd | monaco.KeyCode.Slash,
      ],
      run: (ed) => {
        const model = ed.getModel();
        const selection = ed.getSelection();
        if (!model || !selection) return;

        const startLine = selection.startLineNumber;
        // If selection ends at column 1, the last line wasn't actually selected
        // (user just selected up to the newline, which extends to next line at col 1)
        const endLine = selection.endColumn === 1 && selection.endLineNumber > selection.startLineNumber
          ? selection.endLineNumber - 1
          : selection.endLineNumber;

        // Get all lines in selection
        const lines: string[] = [];
        for (let i = startLine; i <= endLine; i++) {
          lines.push(model.getLineContent(i));
        }

        // Check if all non-empty lines start with '--' (ignoring leading whitespace)
        const allCommented = lines.every(line => {
          const trimmed = line.trimStart();
          return trimmed === '' || trimmed.startsWith('--');
        });

        // Build edits
        const edits: MonacoEditor.IIdentifiedSingleEditOperation[] = [];

        if (allCommented) {
          // Uncomment: remove the first '--' from each line (preserving leading whitespace)
          for (let i = startLine; i <= endLine; i++) {
            const line = model.getLineContent(i);
            const trimmed = line.trimStart();
            if (trimmed.startsWith('--')) {
              const leadingWhitespace = line.length - trimmed.length;
              // Remove '-- ' if present, otherwise just '--'
              const removeLen = trimmed.startsWith('-- ') ? 3 : 2;
              edits.push({
                range: new monaco.Range(i, leadingWhitespace + 1, i, leadingWhitespace + 1 + removeLen),
                text: '',
              });
            }
          }
        } else {
          // Comment: prepend '-- ' to each line (after leading whitespace)
          for (let i = startLine; i <= endLine; i++) {
            const line = model.getLineContent(i);
            const leadingWhitespace = line.length - line.trimStart().length;
            edits.push({
              range: new monaco.Range(i, leadingWhitespace + 1, i, leadingWhitespace + 1),
              text: '-- ',
            });
          }
        }

        // Apply all edits
        if (edits.length > 0) {
          ed.executeEdits('toggle-comment', edits);
        }
      },
    });

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

        {/* Type Info Panel - shows type at cursor position */}
        {selectionTypeInfo.hasInfo && (
          <div style={styles.typeInfoPanel}>
            <div style={styles.typeInfoLabel}>Type at Cursor</div>
            <div>
              <span style={styles.typeInfoCode}>{selectionTypeInfo.selectedCode}</span>
              <span style={{ color: '#8b949e' }}> : </span>
              <span style={styles.typeInfoType}>{selectionTypeInfo.typeString}</span>
            </div>
          </div>
        )}
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
              <EnhancedBlockCard key={index} result={blockResult} index={index} onStepperError={handleStepperError} />
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
