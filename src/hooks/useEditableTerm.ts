/**
 * React hook for managing EditableTerm state.
 *
 * This provides a flux-like interface for editing a term definition:
 * - State is immutable (EditableTerm)
 * - Updates return new instances
 * - React state is minimal (just the current EditableTerm)
 *
 * Usage:
 *   const { term, dispatch } = useEditableTerm(initialTerm);
 *   dispatch({ type: 'addHypothesis', index: 0, name: 'a', hypothesisType: Real });
 */

import { useState, useCallback, useMemo } from 'react';
import { EditableTerm, TTerm, TermDefinition } from '../types/tt-core';

// ============================================================================
// Action Types
// ============================================================================

export type EditableTermAction =
  | { type: 'addHypothesis'; index: number; name: string; hypothesisType: TTerm }
  | { type: 'removeHypothesis'; index: number }
  | { type: 'updateHypothesis'; index: number; name?: string; hypothesisType?: TTerm }
  | { type: 'updateGoal'; goal: TTerm }
  | { type: 'updateBody'; body: TTerm }
  | { type: 'updateBodyAt'; path: any[]; term: TTerm }
  | { type: 'replaceAll'; term: EditableTerm };

// ============================================================================
// Hook
// ============================================================================

export interface UseEditableTermResult {
  /** Current term state */
  term: EditableTerm;

  /** Dispatch an action to update the term */
  dispatch: (action: EditableTermAction) => void;

  /** Get the current term as a TermDefinition */
  toTermDefinition: () => TermDefinition;

  /** Replace the entire term */
  setTerm: (term: EditableTerm) => void;

  /** Undo last change (if history is enabled) */
  undo?: () => void;

  /** Redo last undone change (if history is enabled) */
  redo?: () => void;

  /** Check if can undo */
  canUndo?: boolean;

  /** Check if can redo */
  canRedo?: boolean;
}

export interface UseEditableTermOptions {
  /** Enable undo/redo history */
  enableHistory?: boolean;

  /** Maximum history size */
  maxHistorySize?: number;

  /** Callback when term changes */
  onChange?: (term: EditableTerm) => void;
}

export function useEditableTerm(
  initialTerm: EditableTerm,
  options: UseEditableTermOptions = {}
): UseEditableTermResult {
  const { enableHistory = false, maxHistorySize = 50, onChange } = options;

  const [term, setTermInternal] = useState<EditableTerm>(initialTerm);
  const [history, setHistory] = useState<EditableTerm[]>([]);
  const [historyIndex, setHistoryIndex] = useState(-1);

  const setTerm = useCallback(
    (newTerm: EditableTerm) => {
      setTermInternal(newTerm);

      if (enableHistory) {
        // Add to history
        setHistory((prev) => {
          const newHistory = prev.slice(0, historyIndex + 1);
          newHistory.push(newTerm);
          if (newHistory.length > maxHistorySize) {
            newHistory.shift();
          }
          return newHistory;
        });
        setHistoryIndex((prev) => Math.min(prev + 1, maxHistorySize - 1));
      }

      onChange?.(newTerm);
    },
    [enableHistory, historyIndex, maxHistorySize, onChange]
  );

  const dispatch = useCallback(
    (action: EditableTermAction) => {
      let newTerm: EditableTerm;

      switch (action.type) {
        case 'addHypothesis':
          newTerm = term.addHypothesis(action.index, action.name, action.hypothesisType);
          break;

        case 'removeHypothesis':
          newTerm = term.removeHypothesis(action.index);
          break;

        case 'updateHypothesis':
          newTerm = term.updateHypothesis(action.index, action.name, action.hypothesisType);
          break;

        case 'updateGoal':
          newTerm = term.updateGoal(action.goal);
          break;

        case 'updateBody':
          newTerm = term.updateBody(action.body);
          break;

        case 'updateBodyAt':
          newTerm = term.updateBodyAt(action.path, action.term);
          break;

        case 'replaceAll':
          newTerm = action.term;
          break;

        default:
          throw new Error(`Unknown action type: ${(action as any).type}`);
      }

      setTerm(newTerm);
    },
    [term, setTerm]
  );

  const toTermDefinition = useCallback(() => {
    return term.toTermDefinition();
  }, [term]);

  const undo = useCallback(() => {
    if (enableHistory && historyIndex > 0) {
      setHistoryIndex(historyIndex - 1);
      setTermInternal(history[historyIndex - 1]);
      onChange?.(history[historyIndex - 1]);
    }
  }, [enableHistory, historyIndex, history, onChange]);

  const redo = useCallback(() => {
    if (enableHistory && historyIndex < history.length - 1) {
      setHistoryIndex(historyIndex + 1);
      setTermInternal(history[historyIndex + 1]);
      onChange?.(history[historyIndex + 1]);
    }
  }, [enableHistory, historyIndex, history, onChange]);

  const canUndo = enableHistory && historyIndex > 0;
  const canRedo = enableHistory && historyIndex < history.length - 1;

  return useMemo(
    () => ({
      term,
      dispatch,
      toTermDefinition,
      setTerm,
      ...(enableHistory
        ? {
            undo,
            redo,
            canUndo,
            canRedo,
          }
        : {}),
    }),
    [term, dispatch, toTermDefinition, setTerm, enableHistory, undo, redo, canUndo, canRedo]
  );
}
