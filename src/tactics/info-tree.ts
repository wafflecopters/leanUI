/**
 * InfoTree: Goal state recording for IDE integration
 *
 * Phase 3 of tactics redesign: Record proof state after each tactic
 * application, enabling IDE features like:
 * - Display goal state at cursor position
 * - Hover to see tactic effects
 * - Navigate to hypothesis definitions
 *
 * Based on Lean 4's InfoTree architecture.
 */

import { GoalState } from './proof-state';
import { TacticExpr } from './apply-tactic';

/**
 * SourcePosition: Location in source code
 */
export interface SourcePosition {
  line: number;
  col: number;
  endLine?: number;
  endCol?: number;
}

/**
 * TacticInfoNode: Recorded information about a single tactic application
 */
export interface TacticInfoNode {
  /** Source position of this tactic */
  position: SourcePosition;

  /** Goals before applying this tactic */
  goalsBefore: GoalState[];

  /** Goals after applying this tactic */
  goalsAfter: GoalState[];

  /** The tactic that was applied */
  tactic: TacticExpr;

  /** Optional error if tactic failed */
  error?: string;

  /** Child nodes (for structured tactics like case branches) */
  children: TacticInfoNode[];
}

/**
 * TacticInfoTree: Complete tree of tactic execution info
 *
 * This tree records the entire proof execution, allowing IDE to inspect
 * goal state at any point in the proof.
 */
export class TacticInfoTree {
  constructor(public readonly root: TacticInfoNode) {}

  /**
   * Find the info node at the given cursor position.
   *
   * Returns the most specific (deepest) node that contains the position,
   * along with the goals that are active at that position.
   */
  findGoalsAtPosition(line: number, col: number): GoalState[] | null {
    // First try exact position match (searches recursively)
    for (const child of this.root.children) {
      const node = this.findNodeAtPosition(child, line, col);
      if (node) return node.goalsAfter;
    }

    // Fallback: if cursor is on the same line as any tactic (anywhere in tree), return that tactic's goals
    // This handles the case where cursor is on tactic arguments/terms after the keyword
    const allNodes = this.getAllNodes();
    for (const node of allNodes) {
      if (node.position.line === line) {
        return node.goalsAfter;
      }
    }

    return null;
  }

  /**
   * Find the most specific node containing the position.
   */
  findNodeAtPosition(
    node: TacticInfoNode,
    line: number,
    col: number
  ): TacticInfoNode | null {
    // Check if cursor is in this node's range
    if (!this.positionContains(node.position, line, col)) {
      return null;
    }

    // Search children first (more specific)
    for (const child of node.children) {
      const result = this.findNodeAtPosition(child, line, col);
      if (result) return result;
    }

    // No child contains it, return this node
    return node;
  }

  /**
   * Check if a position range contains a point
   */
  private positionContains(
    range: SourcePosition,
    line: number,
    col: number
  ): boolean {
    // Start position check
    if (line < range.line) return false;
    if (line === range.line && col < range.col) return false;

    // End position check (if available)
    if (range.endLine !== undefined) {
      if (line > range.endLine) return false;
      if (line === range.endLine && range.endCol !== undefined && col > range.endCol) {
        return false;
      }
    }

    return true;
  }

  /**
   * Get all tactic nodes in order (depth-first)
   */
  getAllNodes(): TacticInfoNode[] {
    const result: TacticInfoNode[] = [];

    function visit(node: TacticInfoNode) {
      result.push(node);
      for (const child of node.children) {
        visit(child);
      }
    }

    if (this.root.children.length > 0) {
      for (const child of this.root.children) {
        visit(child);
      }
    }

    return result;
  }

  /**
   * Get summary statistics about the proof
   */
  getStatistics(): {
    totalTactics: number;
    successfulTactics: number;
    failedTactics: number;
    maxGoalsAtOnce: number;
  } {
    const nodes = this.getAllNodes();

    return {
      totalTactics: nodes.length,
      successfulTactics: nodes.filter(n => !n.error).length,
      failedTactics: nodes.filter(n => n.error).length,
      maxGoalsAtOnce: Math.max(
        ...nodes.map(n => n.goalsAfter.length),
        0
      )
    };
  }
}

/**
 * Create an empty root node for an InfoTree
 */
export function createRootInfoNode(initialGoals: GoalState[]): TacticInfoNode {
  return {
    position: { line: 0, col: 0 },
    goalsBefore: initialGoals,
    goalsAfter: initialGoals,
    tactic: { tag: 'Intro' } as any, // Dummy tactic for root
    children: []
  };
}

/**
 * Create an InfoTree with just a root node
 */
export function createEmptyInfoTree(initialGoals: GoalState[]): TacticInfoTree {
  return new TacticInfoTree(createRootInfoNode(initialGoals));
}
