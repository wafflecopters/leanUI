/**
 * PatternElabStepperViewer - React component to visualize pattern elaboration step-by-step
 *
 * Shows the step-by-step process of pattern matching elaboration with:
 * - Forward/backward navigation
 * - Current state visualization (metavariables, bindings, constraints)
 * - History of steps taken
 */

import React, { useState, useMemo } from 'react';
import {
  PatternElabStepper,
  ElabState,
  StepRecord,
  MetaState,
  prettyTerm,
  prettyPattern,
  prettyPhase,
  ConstructorInfo
} from '../types/pattern-elab-stepper';
import { TTKTerm, TTKPattern, TTKClause } from '../types/tt-kernel';

// ============================================================================
// Styles
// ============================================================================

const styles = {
  container: {
    fontFamily: "'JetBrains Mono', 'Fira Code', 'Consolas', monospace",
    fontSize: '12px',
    color: '#c9d1d9',
    display: 'flex',
    flexDirection: 'column' as const,
    height: '100%',
  },
  header: {
    display: 'flex',
    justifyContent: 'space-between',
    alignItems: 'center',
    marginBottom: '16px',
    paddingBottom: '12px',
    borderBottom: '1px solid #30363d',
  },
  title: {
    margin: 0,
    fontSize: '14px',
    fontWeight: 600,
    color: '#58a6ff',
  },
  controls: {
    display: 'flex',
    gap: '8px',
    alignItems: 'center',
  },
  button: {
    padding: '4px 12px',
    backgroundColor: '#21262d',
    color: '#c9d1d9',
    border: '1px solid #30363d',
    borderRadius: '4px',
    cursor: 'pointer',
    fontSize: '12px',
    fontWeight: 500,
  },
  buttonDisabled: {
    opacity: 0.5,
    cursor: 'not-allowed',
  },
  buttonPrimary: {
    backgroundColor: '#238636',
    borderColor: '#238636',
  },
  stepCounter: {
    color: '#8b949e',
    fontSize: '12px',
  },
  section: {
    marginBottom: '16px',
  },
  sectionTitle: {
    fontSize: '11px',
    fontWeight: 600,
    color: '#8b949e',
    textTransform: 'uppercase' as const,
    letterSpacing: '0.5px',
    marginBottom: '8px',
  },
  phaseBox: {
    backgroundColor: '#161b22',
    border: '1px solid #30363d',
    borderRadius: '6px',
    padding: '12px',
    marginBottom: '12px',
  },
  phaseName: {
    fontSize: '13px',
    fontWeight: 600,
    color: '#7ee787',
    marginBottom: '4px',
  },
  phaseNameError: {
    fontSize: '13px',
    fontWeight: 600,
    color: '#f85149',
    marginBottom: '4px',
  },
  phaseBoxError: {
    backgroundColor: '#2d1b1b',
    border: '1px solid #f85149',
    borderRadius: '6px',
    padding: '12px',
    marginBottom: '12px',
  },
  phaseDescription: {
    color: '#c9d1d9',
    fontSize: '12px',
  },
  metaList: {
    listStyle: 'none',
    padding: 0,
    margin: 0,
  },
  metaItem: {
    padding: '4px 8px',
    backgroundColor: '#0d1117',
    borderRadius: '4px',
    marginBottom: '4px',
    fontFamily: 'monospace',
  },
  metaId: {
    color: '#d2a8ff',
    fontWeight: 500,
  },
  metaType: {
    color: '#7ee787',
  },
  metaSolution: {
    color: '#ffc66d',
  },
  metaReason: {
    color: '#6e7681',
    fontSize: '11px',
    marginLeft: '8px',
  },
  bindingList: {
    listStyle: 'none',
    padding: 0,
    margin: 0,
  },
  bindingItem: {
    padding: '4px 8px',
    backgroundColor: '#0d1117',
    borderRadius: '4px',
    marginBottom: '4px',
    fontFamily: 'monospace',
  },
  bindingName: {
    color: '#58a6ff',
    fontWeight: 500,
  },
  bindingIndex: {
    color: '#8b949e',
    marginRight: '8px',
  },
  constraintList: {
    listStyle: 'none',
    padding: 0,
    margin: 0,
  },
  constraintItem: {
    padding: '4px 8px',
    backgroundColor: '#0d1117',
    borderRadius: '4px',
    marginBottom: '4px',
    fontFamily: 'monospace',
  },
  constraintLhs: {
    color: '#d2a8ff',
  },
  constraintRhs: {
    color: '#7ee787',
  },
  patternTermList: {
    listStyle: 'none',
    padding: 0,
    margin: 0,
  },
  patternTermItem: {
    padding: '4px 8px',
    backgroundColor: '#0d1117',
    borderRadius: '4px',
    marginBottom: '4px',
    fontFamily: 'monospace',
    display: 'flex',
    gap: '8px',
  },
  patternIndex: {
    color: '#8b949e',
    minWidth: '20px',
  },
  patternText: {
    color: '#c9d1d9',
  },
  patternArrow: {
    color: '#6e7681',
  },
  patternTerm: {
    color: '#ffc66d',
  },
  historyContainer: {
    flex: 1,
    minHeight: '100px',
    overflow: 'auto',
    backgroundColor: '#0d1117',
    borderRadius: '6px',
    padding: '8px',
  },
  historySection: {
    flex: 1,
    display: 'flex',
    flexDirection: 'column' as const,
    minHeight: 0,
  },
  historyItem: {
    padding: '4px 8px',
    borderBottom: '1px solid #21262d',
    fontSize: '11px',
  },
  historyItemCurrent: {
    backgroundColor: 'rgba(88, 166, 255, 0.1)',
  },
  historyItemError: {
    backgroundColor: 'rgba(248, 81, 73, 0.15)',
    borderLeft: '3px solid #f85149',
  },
  historyStep: {
    color: '#8b949e',
    marginRight: '8px',
  },
  historyAction: {
    color: '#58a6ff',
    marginRight: '8px',
  },
  historyDescription: {
    color: '#c9d1d9',
  },
  emptyState: {
    textAlign: 'center' as const,
    color: '#6e7681',
    padding: '24px',
  },
  returnTypeBox: {
    backgroundColor: 'rgba(126, 231, 135, 0.1)',
    border: '1px solid rgba(126, 231, 135, 0.3)',
    borderRadius: '6px',
    padding: '12px',
    marginTop: '12px',
  },
  returnTypeLabel: {
    color: '#7ee787',
    fontWeight: 600,
    fontSize: '11px',
    textTransform: 'uppercase' as const,
    marginBottom: '4px',
  },
  returnTypeValue: {
    color: '#7ee787',
    fontFamily: 'monospace',
    fontSize: '13px',
  },
  sourceView: {
    backgroundColor: '#0d1117',
    border: '1px solid #30363d',
    borderRadius: '6px',
    padding: '12px 16px',
    marginBottom: '16px',
    fontFamily: "'JetBrains Mono', 'Fira Code', 'Consolas', monospace",
    fontSize: '13px',
    lineHeight: 1.5,
  },
  sourceKeyword: {
    color: '#ff7b72',
  },
  sourceName: {
    color: '#d2a8ff',
  },
  sourceType: {
    color: '#7ee787',
  },
  sourceMeta: {
    color: '#ffa657',
    fontWeight: 600,
  },
  sourceMetaSolved: {
    color: '#7ee787',
    fontWeight: 600,
  },
  sourceVar: {
    color: '#79c0ff',
  },
  sourceCtor: {
    color: '#ff7b72',
  },
  sourceRhs: {
    color: '#c9d1d9',
  },
};

// ============================================================================
// Types
// ============================================================================

interface StepperSnapshot {
  state: ElabState;
  record: StepRecord;
}

interface PatternElabStepperViewerProps {
  /** Single clause (legacy) or array of clauses */
  clause?: TTKClause;
  clauses?: TTKClause[];
  fnType: TTKTerm;
  fnName?: string;
  env: Map<string, ConstructorInfo>;
  /** Typing context for looking up constant/function types during RHS inference */
  typingContext?: Array<{ name: string; type: TTKTerm }>;
  onClose?: () => void;
  /** Callback when the stepper encounters an error - for bubbling errors to the main UI */
  onError?: (error: string, clauseIndex: number, patternIndex?: number) => void;
}

// ============================================================================
// Helper: check if pattern is a wildcard
// ============================================================================

function isWildcard(p: TTKPattern): boolean {
  return p.tag === 'PVar' && (p.name === '_' || p.name.startsWith('_w'));
}

// ============================================================================
// Source View Helper - renders clause with metas filled in
// ============================================================================

/**
 * Render a pattern with metavariables shown (either as ?name or as their solution)
 */
function renderPatternWithMetas(
  pattern: TTKPattern,
  _patternTerm: TTKTerm | undefined,
  metaState: MetaState,
  subPatternTerms: Map<string, TTKTerm>,
  patternIndex: number,
  subPath: number[] = [],
  bindings?: Array<{ name: string }>
): React.ReactNode {
  // NOTE: We DON'T use _patternTerm because the stepper uses array indices in patternTerms,
  // not De Bruijn indices. The pattern.name is already correct for PVar patterns.
  // For constructor patterns, we look up subterms from the subPatternTerms map.

  switch (pattern.tag) {
    case 'PVar':
      if (isWildcard(pattern)) {
        return <span style={styles.sourceMeta}>_</span>;
      }
      return <span style={styles.sourceVar}>{pattern.name}</span>;
    case 'PCtor': {
      if (pattern.args.length === 0) {
        return <span style={styles.sourceCtor}>{pattern.name}</span>;
      }
      return (
        <span>
          <span style={styles.sourceCtor}>(</span>
          <span style={styles.sourceCtor}>{pattern.name}</span>
          {pattern.args.map((arg: TTKPattern, i: number) => {
            // Look up the sub-pattern's elaborated term
            // Path format: "patternIndex.argIndex" for single-level nesting
            const subPatternPath = `${patternIndex}.${i}`;
            const subTerm = subPatternTerms.get(subPatternPath);
            return (
              <span key={i}>
                {' '}
                {renderPatternWithMetas(arg, subTerm, metaState, subPatternTerms, patternIndex, [...subPath, i], bindings)}
              </span>
            );
          })}
          <span style={styles.sourceCtor}>)</span>
        </span>
      );
    }
  }
}

/**
 * Render a TTKTerm with metavariables colored appropriately
 * @param bindings - Optional array of bindings for looking up variable names by De Bruijn index
 */
function renderTermSpan(term: TTKTerm, metaState: MetaState, bindings?: Array<{ name: string }>): React.ReactNode {
  switch (term.tag) {
    case 'Hole': {
      const info = metaState.metas.get(term.id);
      if (info?.solution) {
        // Solved - show the solution in green
        return (
          <span style={styles.sourceMetaSolved} title={`${term.id} = ${prettyTerm(info.solution, metaState)}`}>
            {prettyTerm(info.solution, metaState)}
          </span>
        );
      }
      // Unsolved - show meta name in orange
      return <span style={styles.sourceMeta} title="unsolved metavariable">{term.id}</span>;
    }
    case 'Var': {
      // Look up variable name from bindings if available
      // De Bruijn index 0 = most recent binding = bindings[length-1]
      if (bindings && term.index < bindings.length) {
        const bindingIndex = bindings.length - 1 - term.index;
        const name = bindings[bindingIndex]?.name;
        if (name && name !== '_') {
          return <span style={styles.sourceVar} title={`#${term.index}`}>{name}</span>;
        }
      }
      return <span style={styles.sourceVar}>{`#${term.index}`}</span>;
    }
    case 'Sort':
      return <span style={styles.sourceType}>{term.level === 0 ? 'Prop' : `Type${term.level > 1 ? term.level : ''}`}</span>;
    case 'Const':
      // Check if it's a constructor (starts with uppercase)
      const isConstructor = /^[A-Z]/.test(term.name);
      return <span style={isConstructor ? styles.sourceCtor : styles.sourceName}>{term.name}</span>;
    case 'App': {
      // Collect all args for nicer printing
      const args: TTKTerm[] = [];
      let fn: TTKTerm = term;
      while (fn.tag === 'App') {
        args.unshift(fn.arg);
        fn = fn.fn;
      }
      return (
        <span>
          <span>(</span>
          {renderTermSpan(fn, metaState, bindings)}
          {args.map((arg: TTKTerm, i: number) => (
            <span key={i}> {renderTermSpan(arg, metaState, bindings)}</span>
          ))}
          <span>)</span>
        </span>
      );
    }
    case 'Binder': {
      // For binders, add a new binding to the context for the body
      // Bindings are stored oldest-first, so we append to maintain the order
      // (De Bruijn index 0 = most recent = bindings[length-1])
      const extendedBindings = bindings ? [...bindings, { name: term.name }] : [{ name: term.name }];
      const dom = renderTermSpan(term.domain, metaState, bindings);
      const bod = renderTermSpan(term.body, metaState, extendedBindings);
      if (term.binderKind.tag === 'BPi') {
        if (term.name === '_') {
          return <span>({dom} → {bod})</span>;
        }
        return <span>(<span style={styles.sourceVar}>{term.name}</span> : {dom}) → {bod}</span>;
      } else if (term.binderKind.tag === 'BLam') {
        return (
          <span>
            λ<span style={styles.sourceVar}>{term.name}</span>. {bod}
          </span>
        );
      } else {
        // BLet
        const val = renderTermSpan(term.binderKind.defVal, metaState, bindings);
        return (
          <span>
            let <span style={styles.sourceVar}>{term.name}</span> = {val} in {bod}
          </span>
        );
      }
    }
    case 'Annot':
      return (
        <span>
          ({renderTermSpan(term.term, metaState, bindings)} : {renderTermSpan(term.type, metaState, bindings)})
        </span>
      );
    case 'Match':
      return <span>match {renderTermSpan(term.scrutinee, metaState, bindings)} {'{ ... }'}</span>;
  }
}

/**
 * Extract the return type from a function type (after all Pi binders)
 */
function getReturnTypeFromFnType(fnType: TTKTerm, numArgs: number): TTKTerm {
  let t = fnType;
  for (let i = 0; i < numArgs && t.tag === 'Binder' && t.binderKind.tag === 'BPi'; i++) {
    t = t.body;
  }
  return t;
}

/**
 * Extract binding names from function type Pi binders.
 * Used for displaying indices in the return type.
 */
function getBindingsFromFnType(fnType: TTKTerm, numArgs: number): Array<{ name: string }> {
  const bindings: Array<{ name: string }> = [];
  let t = fnType;
  for (let i = 0; i < numArgs && t.tag === 'Binder' && t.binderKind.tag === 'BPi'; i++) {
    bindings.push({ name: t.name });
    t = t.body;
  }
  return bindings;
}

/**
 * Extract binding names from patterns.
 * Used for displaying indices in the RHS.
 * Traverses patterns recursively to collect all variable bindings.
 */
function getBindingsFromPatterns(patterns: TTKPattern[]): Array<{ name: string }> {
  const bindings: Array<{ name: string }> = [];

  function extractFromPattern(pattern: TTKPattern) {
    switch (pattern.tag) {
      case 'PVar':
        bindings.push({ name: pattern.name });
        break;
      case 'PCtor':
        // Constructor patterns bind their arguments
        for (const arg of pattern.args) {
          extractFromPattern(arg);
        }
        break;
    }
  }

  for (const p of patterns) {
    extractFromPattern(p);
  }

  return bindings;
}

/**
 * Component to render the source view of the clause at current step
 */
const SourceView: React.FC<{
  state: ElabState;
  fnName?: string;
}> = ({ state, fnName = 'f' }) => {
  const { clause, fnType, metaState, patternTerms, returnType, subPatternTerms } = state;

  // Get the return type to display:
  // - If we have a computed returnType, use that (it's refined)
  // - Otherwise extract from the function type signature
  const displayReturnType = returnType || getReturnTypeFromFnType(fnType, clause.patterns.length);
  const isRefined = returnType !== null;

  // Build bindings from patterns for RHS display (pattern context)
  const patternBindings = getBindingsFromPatterns(clause.patterns);

  // Build bindings from function type for return type display (fn arg context)
  const fnTypeBindings = getBindingsFromFnType(fnType, clause.patterns.length);

  return (
    <div style={styles.sourceView}>
      {/* Function signature */}
      <div style={{ marginBottom: '8px', opacity: 0.7 }}>
        <span style={styles.sourceName}>{fnName}</span>
        <span> : </span>
        {renderTermSpan(fnType, metaState)}
      </div>

      {/* Clause with patterns filled in */}
      <div>
        <span style={styles.sourceName}>{fnName}</span>
        {clause.patterns.map((pattern: TTKPattern, i: number) => (
          <span key={i}>
            {' '}
            {renderPatternWithMetas(pattern, patternTerms[i], metaState, subPatternTerms, i, [], patternBindings)}
          </span>
        ))}
        <span style={{ color: '#6e7681' }}> = </span>
        {/* RHS expression */}
        {renderTermSpan(clause.rhs, metaState, patternBindings)}
        {/* Return type annotation */}
        <span style={{ marginLeft: '8px' }} title={isRefined ? "Refined return type (RHS must have this type)" : "Return type from signature (not yet refined)"}>
          <span style={{ color: '#6e7681' }}>:</span>
          <span style={{ marginLeft: '4px', opacity: 0.8, ...(isRefined ? styles.sourceMetaSolved : styles.sourceMeta) }}>
            {renderTermSpan(displayReturnType, metaState, fnTypeBindings)}
          </span>
        </span>
      </div>
    </div>
  );
};

// ============================================================================
// Component
// ============================================================================

export const PatternElabStepperViewer: React.FC<PatternElabStepperViewerProps> = ({
  clause,
  clauses,
  fnType,
  fnName = 'f',
  env,
  typingContext = [],
  onClose,
  onError
}) => {
  // Normalize to array of clauses
  const allClauses = useMemo(() => {
    if (clauses && clauses.length > 0) return clauses;
    if (clause) return [clause];
    return [];
  }, [clause, clauses]);

  // Track which clause is selected
  const [selectedClauseIndex, setSelectedClauseIndex] = useState(0);
  const currentClause = allClauses[selectedClauseIndex];

  // Deep copy an ElabState to prevent shared references between snapshots
  const copyElabState = (s: ElabState): ElabState => ({
    ...s,
    metaState: {
      ...s.metaState,
      metas: new Map(Array.from(s.metaState.metas.entries()).map(
        ([k, v]) => [k, { ...v }]
      ))
    },
    argTypes: [...s.argTypes],
    patternTerms: [...s.patternTerms],
    subPatternTerms: new Map(s.subPatternTerms),
    bindings: s.bindings.map(b => ({ ...b })),
    constraints: s.constraints.map(c => ({ ...c })),
    solvedConstraints: s.solvedConstraints.map(c => ({ ...c })),
    history: [...s.history],
    typingContext: [...s.typingContext]
  });

  // Run the stepper to completion and collect all snapshots for current clause
  const { snapshots, finalState } = useMemo(() => {
    if (!currentClause) {
      return { snapshots: [], finalState: null };
    }
    const stepper = new PatternElabStepper(currentClause, fnType, env, typingContext);
    const snaps: StepperSnapshot[] = [];

    // Capture initial state - deep copy to prevent shared references
    snaps.push({
      state: copyElabState(stepper.getState() as ElabState),
      record: { stepNumber: -1, description: 'Initial state', phase: { tag: 'Init' }, action: 'none', metaChanges: [] }
    });

    while (!stepper.isDone()) {
      const record = stepper.step();
      // Deep copy state at each step
      snaps.push({
        state: copyElabState(stepper.getState() as ElabState),
        record
      });
    }

    return {
      snapshots: snaps,
      finalState: stepper.getState()
    };
  }, [currentClause, fnType, env, typingContext]);

  // Track which errors we've already reported to avoid infinite loops
  const reportedErrorRef = React.useRef<string | null>(null);

  // Notify parent of errors for bubbling to main UI
  React.useEffect(() => {
    if (finalState && finalState.phase.tag === 'Error' && onError) {
      const patternIndex = finalState.phase.patternIndex;
      const errorKey = `${selectedClauseIndex}-${patternIndex}-${finalState.phase.message}`;
      if (reportedErrorRef.current !== errorKey) {
        reportedErrorRef.current = errorKey;
        onError(finalState.phase.message, selectedClauseIndex, patternIndex);
      }
    }
  }, [finalState, selectedClauseIndex, onError]);

  const [currentStep, setCurrentStep] = useState(0);

  // Reset step when clause changes
  React.useEffect(() => {
    setCurrentStep(snapshots.length - 1);
  }, [selectedClauseIndex, snapshots.length]);

  // Clamp currentStep to valid range (handles race condition when clause changes)
  const safeCurrentStep = Math.max(0, Math.min(currentStep, snapshots.length - 1));

  // Handle empty state
  if (snapshots.length === 0 || !currentClause) {
    return (
      <div style={styles.container}>
        <div style={styles.header}>
          <h4 style={styles.title}>Pattern Elaboration Stepper</h4>
          {onClose && <button style={styles.button} onClick={onClose}>Close</button>}
        </div>
        <div style={{ color: '#8b949e', textAlign: 'center', padding: '24px' }}>
          No clause data available
        </div>
      </div>
    );
  }

  const currentSnapshot = snapshots[safeCurrentStep];
  const { state, record } = currentSnapshot;

  const handlePrevious = () => {
    if (safeCurrentStep > 0) {
      setCurrentStep(safeCurrentStep - 1);
    }
  };

  const handleNext = () => {
    if (safeCurrentStep < snapshots.length - 1) {
      setCurrentStep(safeCurrentStep + 1);
    }
  };

  const handleFirst = () => setCurrentStep(0);
  const handleLast = () => setCurrentStep(snapshots.length - 1);

  const isDone = state.phase.tag === 'Done' || state.phase.tag === 'Error';

  return (
    <div style={styles.container}>
      {/* Clause selector (if multiple clauses) */}
      {allClauses.length > 1 && (
        <div style={{
          display: 'flex',
          gap: '8px',
          marginBottom: '12px',
          paddingBottom: '12px',
          borderBottom: '1px solid #30363d',
        }}>
          <span style={{ color: '#8b949e', fontSize: '12px', alignSelf: 'center' }}>Clause:</span>
          {allClauses.map((c: TTKClause, i: number) => (
            <button
              key={i}
              onClick={() => setSelectedClauseIndex(i)}
              style={i === selectedClauseIndex
                ? { ...styles.button, backgroundColor: '#238636', border: '1px solid #238636' }
                : styles.button
              }
            >
              {i + 1}. {fnName} {c.patterns.map((p: TTKPattern) => prettyPattern(p)).join(' ')}
            </button>
          ))}
        </div>
      )}

      {/* Header with controls */}
      <div style={styles.header}>
        <h4 style={styles.title}>Pattern Elaboration Stepper{allClauses.length > 1 ? ` (Clause ${selectedClauseIndex + 1}/${allClauses.length})` : ''}</h4>
        <div style={styles.controls}>
          <button
            style={{ ...styles.button, ...(safeCurrentStep === 0 ? styles.buttonDisabled : {}) }}
            onClick={handleFirst}
            disabled={safeCurrentStep === 0}
          >
            ⏮ First
          </button>
          <button
            style={{ ...styles.button, ...(safeCurrentStep === 0 ? styles.buttonDisabled : {}) }}
            onClick={handlePrevious}
            disabled={safeCurrentStep === 0}
          >
            ◀ Prev
          </button>
          <span style={styles.stepCounter}>
            Step {safeCurrentStep} / {snapshots.length - 1}
          </span>
          <button
            style={{ ...styles.button, ...(safeCurrentStep === snapshots.length - 1 ? styles.buttonDisabled : {}) }}
            onClick={handleNext}
            disabled={safeCurrentStep === snapshots.length - 1}
          >
            Next ▶
          </button>
          <button
            style={{ ...styles.button, ...(safeCurrentStep === snapshots.length - 1 ? styles.buttonDisabled : {}) }}
            onClick={handleLast}
            disabled={safeCurrentStep === snapshots.length - 1}
          >
            Last ⏭
          </button>
          {onClose && (
            <button style={styles.button} onClick={onClose}>
              Close
            </button>
          )}
        </div>
      </div>

      {/* Current phase and action */}
      <div style={state.phase.tag === 'Error' ? styles.phaseBoxError : styles.phaseBox}>
        <div style={state.phase.tag === 'Error' ? styles.phaseNameError : styles.phaseName}>
          {state.phase.tag === 'Error' ? '❌ ' : ''}{prettyPhase(state.phase)}
        </div>
        {record.stepNumber >= 0 && (
          <div style={styles.phaseDescription}>
            <strong style={{ color: state.phase.tag === 'Error' ? '#f85149' : '#58a6ff' }}>{record.action}:</strong> {record.description}
          </div>
        )}
      </div>

      {/* Source view - clause with metas filled in */}
      <div style={styles.section}>
        <div style={styles.sectionTitle}>Source (with metas filled in)</div>
        <SourceView state={state} fnName={fnName} />
      </div>

      {/* Pattern terms */}
      {state.patternTerms.length > 0 && (
        <div style={styles.section}>
          <div style={styles.sectionTitle}>Pattern Terms</div>
          <ul style={styles.patternTermList}>
            {state.patternTerms.map((term: TTKTerm, i: number) => (
              <li key={i} style={styles.patternTermItem}>
                <span style={styles.patternIndex}>{i + 1}.</span>
                <span style={styles.patternText}>{prettyPattern(state.clause.patterns[i])}</span>
                <span style={styles.patternArrow}>→</span>
                <span style={styles.patternTerm}>{prettyTerm(term, state.metaState)}</span>
              </li>
            ))}
          </ul>
        </div>
      )}

      {/* Metavariables */}
      {state.metaState.metas.size > 0 && (
        <div style={styles.section}>
          <div style={styles.sectionTitle}>Metavariables ({state.metaState.metas.size})</div>
          <ul style={styles.metaList}>
            {Array.from(state.metaState.metas.entries()).map(([id, info]) => (
              <li key={id} style={styles.metaItem}>
                <span style={styles.metaId}>{id}</span>
                <span style={{ color: '#8b949e' }}> : </span>
                <span style={styles.metaType}>{prettyTerm(info.type, state.metaState)}</span>
                <span style={{ color: '#8b949e' }}> = </span>
                <span style={styles.metaSolution}>
                  {info.solution ? prettyTerm(info.solution, state.metaState) : '?'}
                </span>
                <span style={styles.metaReason}>({info.createdAt})</span>
              </li>
            ))}
          </ul>
        </div>
      )}

      {/* Bindings */}
      {state.bindings.length > 0 && (
        <div style={styles.section}>
          <div style={styles.sectionTitle}>Bindings ({state.bindings.length})</div>
          <ul style={styles.bindingList}>
            {state.bindings.map((binding, i) => (
              <li key={i} style={styles.bindingItem}>
                <span style={styles.bindingIndex}>#{i}</span>
                <span style={styles.bindingName}>{binding.name}</span>
                <span style={{ color: '#8b949e' }}> : </span>
                <span style={styles.metaType}>{prettyTerm(binding.type, state.metaState)}</span>
                <span style={styles.metaReason}>({binding.introducedBy})</span>
              </li>
            ))}
          </ul>
        </div>
      )}

      {/* Pending constraints */}
      {state.constraints.length > 0 && (
        <div style={styles.section}>
          <div style={styles.sectionTitle}>Pending Constraints ({state.constraints.length})</div>
          <ul style={styles.constraintList}>
            {state.constraints.map((constraint, i) => (
              <li key={i} style={styles.constraintItem}>
                <span style={styles.constraintLhs}>{prettyTerm(constraint.lhs, state.metaState)}</span>
                <span style={{ color: '#6e7681' }}> =?= </span>
                <span style={styles.constraintRhs}>{prettyTerm(constraint.rhs, state.metaState)}</span>
                <span style={styles.metaReason}>({constraint.reason})</span>
              </li>
            ))}
          </ul>
        </div>
      )}

      {/* Return type (when available) */}
      {state.returnType && isDone && (
        <div style={styles.returnTypeBox}>
          <div style={styles.returnTypeLabel}>Return Type</div>
          <div style={styles.returnTypeValue}>{prettyTerm(state.returnType, state.metaState)}</div>
        </div>
      )}

      {/* Step history */}
      <div style={styles.historySection}>
        <div style={styles.sectionTitle}>Step History</div>
        <div style={styles.historyContainer}>
          {snapshots.map((snap, i) => {
            const isError = snap.record.action === 'Error';
            return (
              <div
                key={i}
                style={{
                  ...styles.historyItem,
                  ...(i === safeCurrentStep ? styles.historyItemCurrent : {}),
                  ...(isError ? styles.historyItemError : {}),
                  cursor: 'pointer',
                }}
                onClick={() => setCurrentStep(i)}
              >
                <span style={styles.historyStep}>[{i}]</span>
                <span style={{ ...styles.historyAction, color: isError ? '#f85149' : '#58a6ff' }}>
                  {isError ? '❌ ' : ''}{snap.record.action}
                </span>
                <span style={{ ...styles.historyDescription, color: isError ? '#f85149' : '#c9d1d9' }}>
                  {snap.record.description}
                </span>
              </div>
            );
          })}
        </div>
      </div>
    </div>
  );
};

export default PatternElabStepperViewer;
