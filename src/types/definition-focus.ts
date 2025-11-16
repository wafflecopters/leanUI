/**
 * DefinitionFocus: Unified focus system for term definitions
 *
 * This module provides a clean focus model where the entire workspace
 * is represented as an EditableTerm, and focus is a path into one of
 * three sections: hypotheses, goal, or body.
 *
 * Focus Structure:
 * - Section: which part of the term we're focused on
 * - TermPath: path into the term structure (from tt-core)
 *
 * Example:
 *   { section: 'hypothesis', hypothesisIndex: 0, path: ['domain'] }
 *   = focusing on the type of the first hypothesis
 *
 *   { section: 'goal', path: [] }
 *   = focusing on the entire goal term
 *
 *   { section: 'body', path: ['body', 'defVal'] }
 *   = focusing on a let-binding value in the body
 */

import { TermPath } from './tt-core';

// ============================================================================
// Focus Types
// ============================================================================

/**
 * Focus on a hypothesis (Pi-binder in the type signature).
 */
export interface HypothesisFocus {
  tag: 'hypothesis';
  /** Index of the hypothesis (0-based) */
  hypothesisIndex: number;
  /** Path within the hypothesis (e.g., ['domain'] for the type, [] for the whole binder) */
  path: TermPath;
}

/**
 * Focus on the goal (final return type of the signature).
 */
export interface GoalFocus {
  tag: 'goal';
  /** Path within the goal term */
  path: TermPath;
}

/**
 * Focus on the body (proof term / definition value).
 */
export interface BodyFocus {
  tag: 'body';
  /** Path within the body term */
  path: TermPath;
}

/**
 * Unified focus type for a term definition.
 */
export type DefinitionFocus = HypothesisFocus | GoalFocus | BodyFocus;

// ============================================================================
// Focus Utilities
// ============================================================================

/**
 * Create a focus on a hypothesis.
 */
export function focusHypothesis(index: number, path: TermPath = []): HypothesisFocus {
  return { tag: 'hypothesis', hypothesisIndex: index, path };
}

/**
 * Create a focus on the goal.
 */
export function focusGoal(path: TermPath = []): GoalFocus {
  return { tag: 'goal', path };
}

/**
 * Create a focus on the body.
 */
export function focusBody(path: TermPath = []): BodyFocus {
  return { tag: 'body', path };
}

/**
 * Get a human-readable description of a focus.
 */
export function describeFocus(focus: DefinitionFocus): string {
  switch (focus.tag) {
    case 'hypothesis':
      const pathStr = focus.path.length > 0 ? ` / ${focus.path.join('.')}` : '';
      return `Hypothesis #${focus.hypothesisIndex}${pathStr}`;
    case 'goal':
      return focus.path.length > 0 ? `Goal / ${focus.path.join('.')}` : 'Goal';
    case 'body':
      return focus.path.length > 0 ? `Body / ${focus.path.join('.')}` : 'Body';
  }
}

/**
 * Check if two focuses are equal.
 */
export function focusEquals(a: DefinitionFocus, b: DefinitionFocus): boolean {
  if (a.tag !== b.tag) return false;

  switch (a.tag) {
    case 'hypothesis':
      return (
        b.tag === 'hypothesis' &&
        a.hypothesisIndex === b.hypothesisIndex &&
        pathEquals(a.path, b.path)
      );
    case 'goal':
      return b.tag === 'goal' && pathEquals(a.path, b.path);
    case 'body':
      return b.tag === 'body' && pathEquals(a.path, b.path);
  }
}

function pathEquals(a: TermPath, b: TermPath): boolean {
  if (a.length !== b.length) return false;
  return a.every((step, i) => step === b[i]);
}

// ============================================================================
// Navigation Controller
// ============================================================================

/**
 * NavigationController manages focus navigation within a term definition.
 *
 * It provides methods for:
 * - Moving between sections (hypotheses, goal, body)
 * - Navigating within sections (up/down paths)
 * - Selecting items by index
 */
export class NavigationController {
  private focus: DefinitionFocus | null = null;
  private numHypotheses: number = 0;

  constructor(numHypotheses: number = 0, initialFocus: DefinitionFocus | null = null) {
    this.numHypotheses = numHypotheses;
    this.focus = initialFocus;
  }

  /**
   * Get the current focus.
   */
  getFocus(): DefinitionFocus | null {
    return this.focus;
  }

  /**
   * Set the focus.
   */
  setFocus(focus: DefinitionFocus | null): NavigationController {
    return new NavigationController(this.numHypotheses, focus);
  }

  /**
   * Update the number of hypotheses (needed for validation).
   */
  setNumHypotheses(num: number): NavigationController {
    return new NavigationController(num, this.focus);
  }

  /**
   * Focus on a specific hypothesis by index.
   */
  focusHypothesisAt(index: number, path: TermPath = []): NavigationController {
    if (index < 0 || index >= this.numHypotheses) {
      throw new Error(`Invalid hypothesis index: ${index}`);
    }
    return this.setFocus(focusHypothesis(index, path));
  }

  /**
   * Focus on the goal.
   */
  focusGoal(path: TermPath = []): NavigationController {
    return this.setFocus(focusGoal(path));
  }

  /**
   * Focus on the body.
   */
  focusBody(path: TermPath = []): NavigationController {
    return this.setFocus(focusBody(path));
  }

  /**
   * Cycle to the next section.
   * Order: hypotheses (0, 1, 2, ...) -> goal -> body -> hypotheses[0]
   */
  cycleNext(): NavigationController {
    if (!this.focus) {
      // No focus, start at first hypothesis or goal
      if (this.numHypotheses > 0) {
        return this.focusHypothesisAt(0);
      }
      return this.focusGoal();
    }

    switch (this.focus.tag) {
      case 'hypothesis':
        // Move to next hypothesis, or to goal if at last
        if (this.focus.hypothesisIndex < this.numHypotheses - 1) {
          return this.focusHypothesisAt(this.focus.hypothesisIndex + 1);
        }
        return this.focusGoal();

      case 'goal':
        return this.focusBody();

      case 'body':
        // Wrap to first hypothesis or goal
        if (this.numHypotheses > 0) {
          return this.focusHypothesisAt(0);
        }
        return this.focusGoal();
    }
  }

  /**
   * Cycle to the previous section.
   */
  cyclePrevious(): NavigationController {
    if (!this.focus) {
      // No focus, start at body
      return this.focusBody();
    }

    switch (this.focus.tag) {
      case 'hypothesis':
        // Move to previous hypothesis, or to body if at first
        if (this.focus.hypothesisIndex > 0) {
          return this.focusHypothesisAt(this.focus.hypothesisIndex - 1);
        }
        return this.focusBody();

      case 'goal':
        // Move to last hypothesis or to body
        if (this.numHypotheses > 0) {
          return this.focusHypothesisAt(this.numHypotheses - 1);
        }
        return this.focusBody();

      case 'body':
        return this.focusGoal();
    }
  }

  /**
   * Navigate deeper into the focused term (append to path).
   */
  navigateInto(step: TermPath[number]): NavigationController {
    if (!this.focus) {
      throw new Error('No focus to navigate into');
    }

    const newPath = [...this.focus.path, step];

    switch (this.focus.tag) {
      case 'hypothesis':
        return this.focusHypothesisAt(this.focus.hypothesisIndex, newPath);
      case 'goal':
        return this.setFocus(focusGoal(newPath));
      case 'body':
        return this.setFocus(focusBody(newPath));
    }
  }

  /**
   * Navigate up one level (pop from path).
   */
  navigateUp(): NavigationController {
    if (!this.focus || this.focus.path.length === 0) {
      // Already at top level, can't go up
      return this;
    }

    const newPath = this.focus.path.slice(0, -1);

    switch (this.focus.tag) {
      case 'hypothesis':
        return this.focusHypothesisAt(this.focus.hypothesisIndex, newPath);
      case 'goal':
        return this.setFocus(focusGoal(newPath));
      case 'body':
        return this.setFocus(focusBody(newPath));
    }
  }

  /**
   * Clear the focus.
   */
  clearFocus(): NavigationController {
    return this.setFocus(null);
  }

  /**
   * Get the current section (without path details).
   */
  getCurrentSection(): 'hypothesis' | 'goal' | 'body' | null {
    return this.focus?.tag || null;
  }

  /**
   * Get the current hypothesis index (if focused on a hypothesis).
   */
  getCurrentHypothesisIndex(): number | null {
    return this.focus?.tag === 'hypothesis' ? this.focus.hypothesisIndex : null;
  }
}

// ============================================================================
// Focus Selection Helpers
// ============================================================================

/**
 * Helper to determine which section and item is selected based on
 * numeric input (for keyboard navigation).
 *
 * Numbering scheme:
 * - 0..numHypotheses-1: Hypotheses
 * - numHypotheses: Goal
 * - numHypotheses+1: Body
 */
export function selectByNumber(
  num: number,
  numHypotheses: number
): DefinitionFocus | null {
  if (num < 0) {
    return null;
  }

  if (num < numHypotheses) {
    return focusHypothesis(num);
  }

  if (num === numHypotheses) {
    return focusGoal();
  }

  if (num === numHypotheses + 1) {
    return focusBody();
  }

  return null;
}

/**
 * Get the numeric index for a focus (inverse of selectByNumber).
 */
export function focusToNumber(
  focus: DefinitionFocus,
  numHypotheses: number
): number {
  switch (focus.tag) {
    case 'hypothesis':
      return focus.hypothesisIndex;
    case 'goal':
      return numHypotheses;
    case 'body':
      return numHypotheses + 1;
  }
}
