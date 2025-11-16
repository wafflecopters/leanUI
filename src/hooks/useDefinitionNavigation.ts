/**
 * React hook for managing navigation within a term definition.
 *
 * This provides keyboard-driven navigation between:
 * - Hypotheses (by index)
 * - Goal
 * - Body
 *
 * Plus deep navigation within each section using TermPath.
 */

import { useState, useCallback, useEffect } from 'react';
import {
  DefinitionFocus,
  NavigationController,
  describeFocus,
  selectByNumber,
} from '../types/definition-focus';

// ============================================================================
// Hook
// ============================================================================

export interface UseDefinitionNavigationOptions {
  /** Number of hypotheses (for validation) */
  numHypotheses: number;

  /** Initial focus */
  initialFocus?: DefinitionFocus | null;

  /** Callback when focus changes */
  onFocusChange?: (focus: DefinitionFocus | null) => void;

  /** Enable keyboard shortcuts */
  enableKeyboard?: boolean;

  /** Callback to check if keyboard input should be handled */
  shouldHandleKeyboard?: () => boolean;
}

export interface UseDefinitionNavigationResult {
  /** Current focus */
  focus: DefinitionFocus | null;

  /** Set focus directly */
  setFocus: (focus: DefinitionFocus | null) => void;

  /** Focus on a hypothesis by index */
  focusHypothesis: (index: number) => void;

  /** Focus on the goal */
  focusGoal: () => void;

  /** Focus on the body */
  focusBody: () => void;

  /** Cycle to next section */
  cycleNext: () => void;

  /** Cycle to previous section */
  cyclePrevious: () => void;

  /** Navigate deeper (add to path) */
  navigateInto: (step: any) => void;

  /** Navigate up (remove from path) */
  navigateUp: () => void;

  /** Clear focus */
  clearFocus: () => void;

  /** Get human-readable description of current focus */
  getFocusDescription: () => string;

  /** Select by numeric index */
  selectByNumber: (num: number) => void;

  /** Current section ('hypothesis' | 'goal' | 'body' | null) */
  currentSection: 'hypothesis' | 'goal' | 'body' | null;

  /** Current hypothesis index (if focused on hypothesis) */
  currentHypothesisIndex: number | null;
}

export function useDefinitionNavigation(
  options: UseDefinitionNavigationOptions
): UseDefinitionNavigationResult {
  const {
    numHypotheses,
    initialFocus = null,
    onFocusChange,
    enableKeyboard = true,
    shouldHandleKeyboard = () => true,
  } = options;

  const [controller, setController] = useState(() =>
    new NavigationController(numHypotheses, initialFocus)
  );

  // Update controller when numHypotheses changes
  useEffect(() => {
    setController((prev) => prev.setNumHypotheses(numHypotheses));
  }, [numHypotheses]);

  const focus = controller.getFocus();

  const updateController = useCallback(
    (newController: NavigationController) => {
      setController(newController);
      const newFocus = newController.getFocus();
      if (onFocusChange) {
        onFocusChange(newFocus);
      }
    },
    [onFocusChange]
  );

  const setFocus = useCallback(
    (newFocus: DefinitionFocus | null) => {
      updateController(controller.setFocus(newFocus));
    },
    [controller, updateController]
  );

  const focusHypothesis = useCallback(
    (index: number) => {
      updateController(controller.focusHypothesisAt(index));
    },
    [controller, updateController]
  );

  const focusGoal = useCallback(() => {
    updateController(controller.focusGoal());
  }, [controller, updateController]);

  const focusBody = useCallback(() => {
    updateController(controller.focusBody());
  }, [controller, updateController]);

  const cycleNext = useCallback(() => {
    updateController(controller.cycleNext());
  }, [controller, updateController]);

  const cyclePrevious = useCallback(() => {
    updateController(controller.cyclePrevious());
  }, [controller, updateController]);

  const navigateInto = useCallback(
    (step: any) => {
      updateController(controller.navigateInto(step));
    },
    [controller, updateController]
  );

  const navigateUp = useCallback(() => {
    updateController(controller.navigateUp());
  }, [controller, updateController]);

  const clearFocus = useCallback(() => {
    updateController(controller.clearFocus());
  }, [controller, updateController]);

  const getFocusDescription = useCallback(() => {
    return focus ? describeFocus(focus) : 'No focus';
  }, [focus]);

  const handleSelectByNumber = useCallback(
    (num: number) => {
      const newFocus = selectByNumber(num, numHypotheses);
      if (newFocus) {
        setFocus(newFocus);
      }
    },
    [numHypotheses, setFocus]
  );

  // Keyboard handler
  useEffect(() => {
    if (!enableKeyboard) return;

    const handleKeyDown = (e: KeyboardEvent) => {
      if (!shouldHandleKeyboard()) return;

      // Don't handle if in input/textarea
      const target = e.target as HTMLElement;
      if (target.tagName === 'INPUT' || target.tagName === 'TEXTAREA') {
        return;
      }

      // Arrow keys or j/k for cycling
      if (e.key === 'ArrowDown' || e.key === 'j') {
        cycleNext();
        e.preventDefault();
        return;
      }

      if (e.key === 'ArrowUp' || e.key === 'k') {
        cyclePrevious();
        e.preventDefault();
        return;
      }

      // Numeric keys for direct selection
      if (/^[0-9]$/.test(e.key)) {
        const num = parseInt(e.key, 10);
        handleSelectByNumber(num);
        e.preventDefault();
        return;
      }

      // Escape to clear focus
      if (e.key === 'Escape') {
        clearFocus();
        e.preventDefault();
        return;
      }
    };

    window.addEventListener('keydown', handleKeyDown);
    return () => window.removeEventListener('keydown', handleKeyDown);
  }, [
    enableKeyboard,
    shouldHandleKeyboard,
    cycleNext,
    cyclePrevious,
    clearFocus,
    handleSelectByNumber,
  ]);

  return {
    focus,
    setFocus,
    focusHypothesis,
    focusGoal,
    focusBody,
    cycleNext,
    cyclePrevious,
    navigateInto,
    navigateUp,
    clearFocus,
    getFocusDescription,
    selectByNumber: handleSelectByNumber,
    currentSection: controller.getCurrentSection(),
    currentHypothesisIndex: controller.getCurrentHypothesisIndex(),
  };
}
