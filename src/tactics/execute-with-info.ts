/**
 * Execute tactics with InfoTree recording (Phase 3)
 *
 * This module provides functions to execute tactics while building an InfoTree
 * that records goal state at each step. This enables IDE features like
 * cursor-based goal inspection.
 */

import { ProofState, extractGoalStates } from './proof-state';
import { TacticExpr, applyTacticToState, ProofStateResult } from './apply-tactic';
import {
  TacticInfoTree,
  TacticInfoNode,
  SourcePosition,
  createEmptyInfoTree
} from './info-tree';

/**
 * TacticWithPosition: A tactic expression with source location
 */
export interface TacticWithPosition {
  expr: TacticExpr;
  position: SourcePosition;
}

/**
 * ExecutionResult: Result of executing tactics with InfoTree recording
 */
export interface ExecutionResult {
  /** Final proof state (may be incomplete if error occurred) */
  finalState: ProofState;

  /** InfoTree recording all tactic applications */
  infoTree: TacticInfoTree;

  /** Error message if execution failed */
  error?: string;

  /** Position where error occurred */
  errorPosition?: SourcePosition;
}

/**
 * Execute tactics and build InfoTree for IDE inspection.
 *
 * This is the primary function for running tactic proofs with full IDE support.
 * It applies each tactic in sequence and records the goal state before/after
 * each application.
 *
 * @param initialState - Starting proof state
 * @param tactics - List of tactics with source positions
 * @returns Execution result with final state and InfoTree
 */
export function executeTacticsWithInfo(
  initialState: ProofState,
  tactics: TacticWithPosition[]
): ExecutionResult {
  const rootNode: TacticInfoNode = {
    position: { line: 0, col: 0 },
    goalsBefore: extractGoalStates(initialState),
    goalsAfter: extractGoalStates(initialState),
    tactic: { tag: 'Intro' } as any, // Dummy for root
    children: []
  };

  let currentState = initialState;

  for (const { expr, position } of tactics) {
    const goalsBefore = extractGoalStates(currentState);

    // Apply tactic
    const result = applyTacticToState(currentState, expr);

    if (!result.success) {
      // Record failed tactic
      const errorNode: TacticInfoNode = {
        position,
        goalsBefore,
        goalsAfter: goalsBefore, // Goals unchanged on error
        tactic: expr,
        error: result.error,
        children: []
      };
      rootNode.children.push(errorNode);

      return {
        finalState: currentState,
        infoTree: new TacticInfoTree(rootNode),
        error: result.error,
        errorPosition: position
      };
    }

    currentState = result.newState;
    const goalsAfter = extractGoalStates(currentState);

    // Record successful tactic
    const tacticNode: TacticInfoNode = {
      position,
      goalsBefore,
      goalsAfter,
      tactic: expr,
      children: []
    };
    rootNode.children.push(tacticNode);
  }

  return {
    finalState: currentState,
    infoTree: new TacticInfoTree(rootNode)
  };
}

/**
 * Execute a single tactic and return updated state with new InfoTree node.
 *
 * This is useful for interactive/incremental proof development where tactics
 * are added one at a time.
 */
export function executeSingleTacticWithInfo(
  state: ProofState,
  tactic: TacticExpr,
  position: SourcePosition
): { result: ProofStateResult; node: TacticInfoNode } {
  const goalsBefore = extractGoalStates(state);
  const result = applyTacticToState(state, tactic);

  const node: TacticInfoNode = {
    position,
    goalsBefore,
    goalsAfter: result.success ? extractGoalStates(result.newState) : goalsBefore,
    tactic,
    error: result.success ? undefined : result.error,
    children: []
  };

  return { result, node };
}

/**
 * Replay tactics from an InfoTree.
 *
 * This can be used to re-execute a proof and verify the InfoTree is still valid,
 * or to continue from a partially complete proof.
 */
export function replayFromInfoTree(
  initialState: ProofState,
  infoTree: TacticInfoTree
): ExecutionResult {
  const nodes = infoTree.getAllNodes();
  const tactics: TacticWithPosition[] = nodes.map(node => ({
    expr: node.tactic,
    position: node.position
  }));

  return executeTacticsWithInfo(initialState, tactics);
}
