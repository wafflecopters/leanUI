/**
 * Unified Tactic Application API
 *
 * This module provides a single entry point for applying tactics to proof states.
 * All tactic applications go through the `applyTactic` function, enabling:
 * - Clear input/output contracts
 * - Easy unit testing of single steps
 * - Future InfoTree recording for IDE integration
 *
 * Phase 1 (completed): Wrapper around existing tactics (no behavior change)
 * Phase 2 (current): ProofState type support (backward compatible)
 * Phase 3 (future): InfoTree recording, cases support
 */

import { TTKTerm } from '../compiler/kernel';
import {
  Tactic,
  TacticResult,
  IntroTactic,
  IntrosTactic,
  ExactTactic,
  AssumptionTactic,
  ApplyTactic
} from './tactic';
import { CasesTactic } from './cases-tactic';
import { TacticEngine } from './tacticsEngine';
import {
  ProofState,
  engineToProofState,
  proofStateToEngine,
  getFocusedGoal,
  getFocusedGoalId,
  isProofComplete as isProofStateComplete
} from './proof-state';

/**
 * Surface syntax for tactics
 *
 * Represents a tactic as parsed from source code (before elaboration).
 */
export type TacticExpr =
  | { tag: 'Intro'; name?: string }
  | { tag: 'Intros'; names?: string[] }
  | { tag: 'Exact'; term: TTKTerm }
  | { tag: 'Apply'; fn: TTKTerm }
  | { tag: 'Assumption' }
  | { tag: 'Cases'; scrutinee: TTKTerm };

/**
 * Apply a tactic to the current proof state.
 *
 * This is the ONLY way tactics should modify proof state (eventually).
 * Currently this is a wrapper around existing Tactic.apply methods.
 *
 * @param engine - Current proof state (TacticEngine)
 * @param tacticExpr - Tactic to apply
 * @returns Updated proof state or error
 */
export function applyTactic(
  engine: TacticEngine,
  tacticExpr: TacticExpr
): TacticResult {
  // Get current goal
  const goal = engine.getFocusedGoal();
  const goalId = engine.getFocusedGoalId();

  if (!goal || !goalId) {
    return {
      success: false,
      error: 'applyTactic: no focused goal'
    };
  }

  // Dispatch to appropriate tactic implementation
  let tactic: Tactic;

  switch (tacticExpr.tag) {
    case 'Intro':
      tactic = new IntroTactic(tacticExpr.name);
      break;

    case 'Intros':
      tactic = new IntrosTactic(tacticExpr.names);
      break;

    case 'Exact':
      tactic = new ExactTactic(tacticExpr.term);
      break;

    case 'Apply':
      tactic = new ApplyTactic(tacticExpr.fn);
      break;

    case 'Assumption':
      tactic = new AssumptionTactic();
      break;

    case 'Cases':
      tactic = new CasesTactic(tacticExpr.scrutinee);
      break;

    default:
      // TypeScript exhaustiveness check
      const _exhaustive: never = tacticExpr;
      return {
        success: false,
        error: `applyTactic: unknown tactic ${(_exhaustive as any).tag}`
      };
  }

  // Apply the tactic
  return tactic.apply(engine, goal, goalId);
}

/**
 * Apply multiple tactics in sequence.
 *
 * Stops at the first error.
 *
 * @param engine - Initial proof state
 * @param tactics - List of tactics to apply
 * @returns Final proof state or error
 */
export function applyTactics(
  engine: TacticEngine,
  tactics: TacticExpr[]
): TacticResult {
  let current = engine;

  for (const tacticExpr of tactics) {
    const result = applyTactic(current, tacticExpr);
    if (!result.success) {
      return result;
    }
    current = result.newEngine;
  }

  return { success: true, newEngine: current };
}

/**
 * Verify a proof is complete (all goals solved).
 */
export function isProofComplete(engine: TacticEngine): boolean {
  return engine.isComplete();
}

/**
 * Extract the final proof term (zonking to resolve metas).
 */
export function extractProofTerm(engine: TacticEngine): TTKTerm {
  return engine.zonk();
}

// =============================================================================
// Phase 2: ProofState-based API (new, preferred)
// =============================================================================

/**
 * ProofStateResult: Result of applying a tactic to ProofState
 */
export type ProofStateResult =
  | { success: true; newState: ProofState }
  | { success: false; error: string; cause?: Error };

/**
 * Apply a tactic to ProofState (Phase 2 API)
 *
 * This is the preferred API going forward. It works with ProofState instead
 * of TacticEngine, preparing for future InfoTree and cases support.
 *
 * @param state - Current proof state
 * @param tacticExpr - Tactic to apply
 * @returns Updated proof state or error
 */
export function applyTacticToState(
  state: ProofState,
  tacticExpr: TacticExpr
): ProofStateResult {
  // Convert to engine, apply tactic, convert back
  const engine = proofStateToEngine(state);
  const result = applyTactic(engine, tacticExpr);

  if (!result.success) {
    return {
      success: false,
      error: result.error,
      cause: result.cause
    };
  }

  return {
    success: true,
    newState: engineToProofState(result.newEngine)
  };
}

/**
 * Apply multiple tactics in sequence to ProofState (Phase 2 API)
 *
 * @param state - Initial proof state
 * @param tactics - List of tactics to apply
 * @returns Final proof state or error
 */
export function applyTacticsToState(
  state: ProofState,
  tactics: TacticExpr[]
): ProofStateResult {
  let current = state;

  for (const tacticExpr of tactics) {
    const result = applyTacticToState(current, tacticExpr);
    if (!result.success) {
      return result;
    }
    current = result.newState;
  }

  return { success: true, newState: current };
}

/**
 * Extract final proof term from ProofState
 */
export function extractProofTermFromState(state: ProofState): TTKTerm {
  const engine = proofStateToEngine(state);
  return engine.zonk();
}
