/**
 * ProofState: Explicit, immutable proof state representation
 *
 * Phase 2 of tactics redesign: Introduce ProofState as a first-class type
 * that wraps TacticEngine. This makes the proof state explicit and prepares
 * for future InfoTree recording and cases support.
 *
 * Currently this is a thin wrapper around TacticEngine. Future phases will
 * expand this to include InfoTree metadata and support for branching.
 */

import { TTKTerm, TTKContext } from '../compiler/kernel';
import { MetaVar, Constraint, DefinitionsMap } from '../compiler/term';
import { TacticEngine } from './tacticsEngine';

/**
 * ProofState: Complete proof state at any point in a tactic proof
 *
 * This is the primary type for proof state throughout the tactics system.
 * Currently wraps TacticEngine, but future phases may change representation.
 */
export interface ProofState {
  /** The proof term being built (contains Meta nodes for unsolved goals) */
  readonly term: TTKTerm;

  /** All metavariables (solved and unsolved) */
  readonly metaVars: Map<string, MetaVar>;

  /** Ordered list of goal IDs (unsolved metas we're working on) */
  readonly goals: GoalId[];

  /** Which goal has focus (index into goals array) */
  readonly focusIndex: number;

  /** Active constraint set */
  readonly constraints: Constraint[];

  /** Global definitions */
  readonly definitions: DefinitionsMap;
}

/**
 * GoalId: Identifier for a goal (metavariable ID)
 */
export type GoalId = string;

/**
 * GoalState: Displayable goal state for IDE/user
 *
 * This is what gets shown to the user (hypotheses + target).
 * Extracted from internal MetaVar representation.
 */
export interface GoalState {
  /** Goal ID */
  id: GoalId;

  /** Hypothesis list: name : type */
  hypotheses: Array<{ name: string; type: TTKTerm }>;

  /** Target type we're trying to prove */
  target: TTKTerm;

  /** Optional: tag for case branches ("Zero", "Succ", etc.) */
  caseTag?: string;
}

// =============================================================================
// ProofState Operations
// =============================================================================

/**
 * Create initial proof state for a goal
 */
export function createProofState(
  goalType: TTKTerm,
  context: TTKContext,
  definitions: DefinitionsMap,
  goalId: string = '?goal0'
): ProofState {
  const initialGoal: MetaVar = {
    ctx: context,
    type: goalType,
    solution: undefined
  };

  return {
    term: { tag: 'Meta', id: goalId },
    metaVars: new Map([[goalId, initialGoal]]),
    goals: [goalId],
    focusIndex: 0,
    constraints: [],
    definitions
  };
}

/**
 * Get the focused goal's metavar
 */
export function getFocusedGoal(state: ProofState): MetaVar | null {
  const goalId = state.goals[state.focusIndex];
  return goalId ? state.metaVars.get(goalId) ?? null : null;
}

/**
 * Get the focused goal's ID
 */
export function getFocusedGoalId(state: ProofState): GoalId | null {
  return state.goals[state.focusIndex] ?? null;
}

/**
 * Get all unsolved goals
 */
export function getUnsolvedGoals(state: ProofState): MetaVar[] {
  return state.goals
    .map(id => state.metaVars.get(id))
    .filter((mv): mv is MetaVar => mv !== undefined && mv.solution === undefined);
}

/**
 * Check if proof is complete (no unsolved goals)
 */
export function isProofComplete(state: ProofState): boolean {
  return getUnsolvedGoals(state).length === 0;
}

/**
 * Extract displayable goal states for IDE/debugging
 */
export function extractGoalStates(state: ProofState): GoalState[] {
  return state.goals.map(id => {
    const meta = state.metaVars.get(id)!;
    return {
      id,
      hypotheses: meta.ctx.map(b => ({
        name: b.name,
        type: b.type
      })),
      target: meta.type,
      caseTag: meta.caseTag // Constructor tag from cases tactic
    };
  });
}

/**
 * Update proof state immutably
 */
export function updateProofState(
  state: ProofState,
  updates: Partial<ProofState>
): ProofState {
  return {
    term: updates.term ?? state.term,
    metaVars: updates.metaVars ?? state.metaVars,
    goals: updates.goals ?? state.goals,
    focusIndex: updates.focusIndex ?? state.focusIndex,
    constraints: updates.constraints ?? state.constraints,
    definitions: updates.definitions ?? state.definitions
  };
}

// =============================================================================
// Conversion to/from TacticEngine (Phase 2 compatibility)
// =============================================================================

/**
 * Convert TacticEngine to ProofState
 *
 * This is a compatibility layer for Phase 2. Existing code uses TacticEngine,
 * new code uses ProofState. This function bridges the gap.
 */
export function engineToProofState(engine: TacticEngine): ProofState {
  return {
    term: engine.term,
    metaVars: engine.metaVars,
    goals: engine.goals,
    focusIndex: engine.focusIndex,
    constraints: engine.constraints,
    definitions: engine.definitions
  };
}

/**
 * Convert ProofState to TacticEngine
 *
 * This is a compatibility layer for Phase 2. Once all code is migrated to
 * ProofState, we can remove this and TacticEngine entirely.
 */
export function proofStateToEngine(state: ProofState): TacticEngine {
  return new TacticEngine(
    state.term,
    state.metaVars,
    state.constraints,
    state.definitions,
    state.goals,
    state.focusIndex
  );
}
