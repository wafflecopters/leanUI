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
  prettyTerm,
  prettyPattern,
  prettyPhase,
  Clause,
  Term,
  ConstructorInfo
} from '../types/pattern-elab-stepper';

// ============================================================================
// Styles
// ============================================================================

const styles = {
  container: {
    fontFamily: "'JetBrains Mono', 'Fira Code', 'Consolas', monospace",
    fontSize: '12px',
    color: '#c9d1d9',
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
    maxHeight: '200px',
    overflow: 'auto',
    backgroundColor: '#0d1117',
    borderRadius: '6px',
    padding: '8px',
  },
  historyItem: {
    padding: '4px 8px',
    borderBottom: '1px solid #21262d',
    fontSize: '11px',
  },
  historyItemCurrent: {
    backgroundColor: 'rgba(88, 166, 255, 0.1)',
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
};

// ============================================================================
// Types
// ============================================================================

interface StepperSnapshot {
  state: ElabState;
  record: StepRecord;
}

interface PatternElabStepperViewerProps {
  clause: Clause;
  fnType: Term;
  env: Map<string, ConstructorInfo>;
  onClose?: () => void;
}

// ============================================================================
// Component
// ============================================================================

export const PatternElabStepperViewer: React.FC<PatternElabStepperViewerProps> = ({
  clause,
  fnType,
  env,
  onClose
}) => {
  // Run the stepper to completion and collect all snapshots
  const { snapshots, finalState } = useMemo(() => {
    const stepper = new PatternElabStepper(clause, fnType, env);
    const snaps: StepperSnapshot[] = [];

    // Capture initial state
    snaps.push({
      state: { ...stepper.getState() } as ElabState,
      record: { stepNumber: -1, description: 'Initial state', phase: { tag: 'Init' }, action: 'none', metaChanges: [] }
    });

    while (!stepper.isDone()) {
      const record = stepper.step();
      snaps.push({
        state: { ...stepper.getState() } as ElabState,
        record
      });
    }

    return {
      snapshots: snaps,
      finalState: stepper.getState()
    };
  }, [clause, fnType, env]);

  const [currentStep, setCurrentStep] = useState(snapshots.length - 1);

  const currentSnapshot = snapshots[currentStep];
  const { state, record } = currentSnapshot;

  const handlePrevious = () => {
    if (currentStep > 0) {
      setCurrentStep(currentStep - 1);
    }
  };

  const handleNext = () => {
    if (currentStep < snapshots.length - 1) {
      setCurrentStep(currentStep + 1);
    }
  };

  const handleFirst = () => setCurrentStep(0);
  const handleLast = () => setCurrentStep(snapshots.length - 1);

  const isDone = state.phase.tag === 'Done' || state.phase.tag === 'Error';

  return (
    <div style={styles.container}>
      {/* Header with controls */}
      <div style={styles.header}>
        <h4 style={styles.title}>Pattern Elaboration Stepper</h4>
        <div style={styles.controls}>
          <button
            style={{ ...styles.button, ...(currentStep === 0 ? styles.buttonDisabled : {}) }}
            onClick={handleFirst}
            disabled={currentStep === 0}
          >
            ⏮ First
          </button>
          <button
            style={{ ...styles.button, ...(currentStep === 0 ? styles.buttonDisabled : {}) }}
            onClick={handlePrevious}
            disabled={currentStep === 0}
          >
            ◀ Prev
          </button>
          <span style={styles.stepCounter}>
            Step {currentStep} / {snapshots.length - 1}
          </span>
          <button
            style={{ ...styles.button, ...(currentStep === snapshots.length - 1 ? styles.buttonDisabled : {}) }}
            onClick={handleNext}
            disabled={currentStep === snapshots.length - 1}
          >
            Next ▶
          </button>
          <button
            style={{ ...styles.button, ...(currentStep === snapshots.length - 1 ? styles.buttonDisabled : {}) }}
            onClick={handleLast}
            disabled={currentStep === snapshots.length - 1}
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
      <div style={styles.phaseBox}>
        <div style={styles.phaseName}>{prettyPhase(state.phase)}</div>
        {record.stepNumber >= 0 && (
          <div style={styles.phaseDescription}>
            <strong style={{ color: '#58a6ff' }}>{record.action}:</strong> {record.description}
          </div>
        )}
      </div>

      {/* Pattern terms */}
      {state.patternTerms.length > 0 && (
        <div style={styles.section}>
          <div style={styles.sectionTitle}>Pattern Terms</div>
          <ul style={styles.patternTermList}>
            {state.patternTerms.map((term, i) => (
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
      <div style={styles.section}>
        <div style={styles.sectionTitle}>Step History</div>
        <div style={styles.historyContainer}>
          {snapshots.map((snap, i) => (
            <div
              key={i}
              style={{
                ...styles.historyItem,
                ...(i === currentStep ? styles.historyItemCurrent : {}),
                cursor: 'pointer',
              }}
              onClick={() => setCurrentStep(i)}
            >
              <span style={styles.historyStep}>[{i}]</span>
              <span style={styles.historyAction}>{snap.record.action}</span>
              <span style={styles.historyDescription}>{snap.record.description}</span>
            </div>
          ))}
        </div>
      </div>
    </div>
  );
};

export default PatternElabStepperViewer;
