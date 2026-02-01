/**
 * Tactics Engine: Immutable proof state manager
 *
 * The TacticEngine tracks the proof term being built, maintains unsolved goals
 * (as metavariables), and provides an immutable API for tactic transformations.
 *
 * Key Principle: Tactics build terms with typed holes. Each goal is simply an
 * unsolved metavariable. Solving a goal means assigning a term to that meta.
 */

import { TTKTerm, TTKContext } from '../compiler/kernel';
import { MetaVar, Constraint, DefinitionsMap, TCEnv } from '../compiler/term';
import { solveConstraints } from '../compiler/meta';

/**
 * TacticEngine: Immutable proof state
 */
export class TacticEngine {
  constructor(
    /** The proof term being built (may contain Metas) */
    public readonly term: TTKTerm,

    /** All metavariables (goals + solved) */
    public readonly metaVars: Map<string, MetaVar>,

    /** Active constraint set */
    public readonly constraints: Constraint[],

    /** Global definitions (inductive types, constants) */
    public readonly definitions: DefinitionsMap,

    /** Ordered list of goal IDs (unsolved metas) */
    public readonly goals: string[],

    /** Focus: which goal are we working on? (index into goals) */
    public readonly focusIndex: number
  ) {}

  // --- Query Methods ---

  /**
   * Get the current focused goal
   */
  getFocusedGoal(): MetaVar | null {
    const goalId = this.goals[this.focusIndex];
    return goalId ? this.metaVars.get(goalId) ?? null : null;
  }

  /**
   * Get the ID of the focused goal
   */
  getFocusedGoalId(): string | null {
    return this.goals[this.focusIndex] ?? null;
  }

  /**
   * Get all unsolved goals
   */
  getUnsolvedGoals(): MetaVar[] {
    return this.goals
      .map(id => this.metaVars.get(id))
      .filter((mv): mv is MetaVar => mv !== undefined && mv.solution === undefined);
  }

  /**
   * Check if proof is complete (no unsolved goals)
   */
  isComplete(): boolean {
    return this.getUnsolvedGoals().length === 0;
  }

  /**
   * Substitute solved metas in term (zonking)
   */
  zonk(): TTKTerm {
    // Create a minimal TCEnv for zonking
    const env = new TCEnv(
      [],  // Empty context
      this.definitions,
      this.metaVars,
      this.constraints,
      [],
      [],
      this.term,
      new Map(),
      { mode: 'check' }
    );
    return env.zonkTerm(this.term);
  }

  // --- State Transformation Methods ---

  /**
   * Create a new engine with updated state (immutable update)
   */
  withUpdates(updates: Partial<{
    term: TTKTerm;
    metaVars: Map<string, MetaVar>;
    constraints: Constraint[];
    goals: string[];
    focusIndex: number;
  }>): TacticEngine {
    return new TacticEngine(
      updates.term ?? this.term,
      updates.metaVars ?? this.metaVars,
      updates.constraints ?? this.constraints,
      this.definitions,
      updates.goals ?? this.goals,
      updates.focusIndex ?? this.focusIndex
    );
  }

  /**
   * Solve constraints and update metavar solutions
   */
  solveConstraints(): TacticEngine {
    const result = solveConstraints(
      this.metaVars,
      this.constraints,
      undefined,
      this.definitions
    );
    return this.withUpdates({
      metaVars: result.metaVars,
      constraints: result.constraints
    });
  }

  /**
   * Move focus to next goal
   */
  focusNext(): TacticEngine {
    if (this.goals.length === 0) return this;
    const nextIndex = (this.focusIndex + 1) % this.goals.length;
    return this.withUpdates({ focusIndex: nextIndex });
  }

  /**
   * Move focus to previous goal
   */
  focusPrev(): TacticEngine {
    if (this.goals.length === 0) return this;
    const prevIndex = this.focusIndex === 0
      ? this.goals.length - 1
      : this.focusIndex - 1;
    return this.withUpdates({ focusIndex: prevIndex });
  }

  /**
   * Set focus to specific goal by ID
   */
  focusGoal(goalId: string): TacticEngine {
    const index = this.goals.indexOf(goalId);
    if (index === -1) return this;
    return this.withUpdates({ focusIndex: index });
  }

  /**
   * Set focus to specific goal by index
   */
  focusGoalAt(index: number): TacticEngine {
    if (index < 0 || index >= this.goals.length) return this;
    return this.withUpdates({ focusIndex: index });
  }
}

/**
 * Create an initial TacticEngine for a proof goal
 */
export function createInitialEngine(
  goalType: TTKTerm,
  context: TTKContext,
  definitions: DefinitionsMap,
  goalId: string = '?goal0'
): TacticEngine {
  const initialGoal: MetaVar = {
    ctx: context,
    type: goalType,
    solution: undefined
  };

  return new TacticEngine(
    { tag: 'Meta', id: goalId },
    new Map([[goalId, initialGoal]]),
    [],
    definitions,
    [goalId],
    0
  );
}

/**
 * Helper to get zonked metavar map (for inspection/debugging)
 */
export function getZonkedMetas(engine: TacticEngine): Map<string, TTKTerm | undefined> {
  const zonked = new Map<string, TTKTerm | undefined>();

  // Create a minimal TCEnv for zonking
  const env = new TCEnv(
    [],
    engine.definitions,
    engine.metaVars,
    engine.constraints,
    [],
    [],
    { tag: 'Const', name: 'dummy' },
    new Map(),
    { mode: 'check' }
  );

  for (const [id, meta] of engine.metaVars.entries()) {
    if (meta.solution) {
      zonked.set(id, env.zonkTerm(meta.solution));
    } else {
      zonked.set(id, undefined);
    }
  }

  return zonked;
}
