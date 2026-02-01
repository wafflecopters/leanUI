/**
 * Tactic Interface and Core Tactics
 *
 * A tactic is a proof state transformation: it takes a TacticEngine and a goal,
 * and returns a new TacticEngine with the goal solved or refined into subgoals.
 */

import { TTKTerm, TTKContext } from '../compiler/kernel';
import { MetaVar, TCEnv } from '../compiler/term';
import { TacticEngine } from './tacticsEngine';
import { checkType, inferType } from '../compiler/checker';
import { whnf, areTypesDefEq } from '../compiler/whnf';
import { subst } from '../compiler/subst';
import { unifyTerms } from '../compiler/unify';

/**
 * TacticResult: Outcome of applying a tactic
 */
export type TacticResult =
  | { success: true; newEngine: TacticEngine }
  | { success: false; error: string; cause?: Error };

/**
 * Tactic: A proof state transformation
 */
export interface Tactic {
  /** Human-readable name */
  name: string;

  /** Apply this tactic to the given goal */
  apply(
    engine: TacticEngine,
    goal: MetaVar,
    goalId: string
  ): TacticResult;
}

/**
 * Helper: Generate fresh meta name
 */
let metaCounter = 0;
export function freshMetaName(): string {
  return `?tactic_meta_${metaCounter++}`;
}

/**
 * Helper: Reset meta counter (for tests)
 */
export function resetMetaCounter(): void {
  metaCounter = 0;
}

// =============================================================================
// Core Tactics
// =============================================================================

/**
 * exact: Solve the goal by providing the exact term
 *
 * Usage: exact <term>
 * Example: exact a
 *
 * The term must have the same type as the goal.
 */
export class ExactTactic implements Tactic {
  name = 'exact';

  constructor(public readonly term: TTKTerm) {}

  apply(engine: TacticEngine, goal: MetaVar, goalId: string): TacticResult {
    try {
      // Create TCEnv in goal's context
      const env = new TCEnv(
        goal.ctx,
        engine.definitions,
        engine.metaVars,
        engine.constraints,
        /* indexPath */ [],
        /* valueStack */ [],
        this.term,
        new Map(), // levelMetas
        { mode: 'check' }
      );

      // Check term has expected type
      const checkedEnv = checkType(env, goal.type);

      // Zonk the checked term (resolve any new metas)
      const solution = checkedEnv.zonkTerm(checkedEnv.elaboratedTerm ?? this.term);

      // Assign solution to goal
      const newMetaVars = new Map(engine.metaVars);
      newMetaVars.set(goalId, { ...goal, solution });

      // Remove goal from goal list
      const newGoals = engine.goals.filter(id => id !== goalId);

      // Adjust focus if we removed the focused goal
      let newFocusIndex = engine.focusIndex;
      if (newFocusIndex >= newGoals.length && newGoals.length > 0) {
        newFocusIndex = newGoals.length - 1;
      } else if (newGoals.length === 0) {
        newFocusIndex = 0;
      }

      return {
        success: true,
        newEngine: engine.withUpdates({
          metaVars: newMetaVars,
          constraints: checkedEnv.constraints,
          goals: newGoals,
          focusIndex: newFocusIndex
        }).solveConstraints()
      };
    } catch (e) {
      return {
        success: false,
        error: `exact: ${e instanceof Error ? e.message : String(e)}`,
        cause: e instanceof Error ? e : undefined
      };
    }
  }
}

/**
 * assumption: Search local context for a term of the goal type
 *
 * Usage: assumption
 *
 * Searches the local context for a hypothesis whose type matches the goal type.
 */
export class AssumptionTactic implements Tactic {
  name = 'assumption';

  apply(engine: TacticEngine, goal: MetaVar, goalId: string): TacticResult {
    const goalType = goal.type;

    // Search context backwards (most recent first)
    for (let i = goal.ctx.length - 1; i >= 0; i--) {
      const hyp = goal.ctx[i];

      // Check if hypothesis type matches goal type (definitionally equal)
      if (areTypesDefEq(hyp.type, goalType, engine.definitions)) {
        // Use variable at de Bruijn index (goal.ctx.length - 1 - i)
        const varIndex = goal.ctx.length - 1 - i;
        const solution: TTKTerm = { tag: 'Var', index: varIndex };

        // Apply exact with the variable
        return new ExactTactic(solution).apply(engine, goal, goalId);
      }
    }

    return {
      success: false,
      error: 'assumption: no matching hypothesis found in context'
    };
  }
}

/**
 * intro: Introduce a Pi binder into the context
 *
 * Usage: intro [name]
 * Example: intro x
 *
 * If the goal type is (x : A) -> B, introduces x : A into the context
 * and creates a new goal of type B.
 */
export class IntroTactic implements Tactic {
  name = 'intro';

  constructor(public readonly userName?: string) {}

  apply(engine: TacticEngine, goal: MetaVar, goalId: string): TacticResult {
    const goalType = goal.type;

    // Reduce goal type to WHNF
    const goalTypeWhnf = whnf(goalType, {
      definitions: engine.definitions
    });

    // Check if goal type is a Pi (Binder with BPi kind)
    if (goalTypeWhnf.tag !== 'Binder' || goalTypeWhnf.binderKind.tag !== 'BPi') {
      return {
        success: false,
        error: `intro: goal type is not a function type (got ${goalTypeWhnf.tag})`
      };
    }

    const { name, domain, body } = goalTypeWhnf;

    // Determine param name (user-provided or from binder)
    const paramName = this.userName ?? name ?? 'x';

    // Extend context with new parameter
    const newCtx = [...goal.ctx, { name: paramName, type: domain }];

    // Create fresh meta for body
    const newGoalId = freshMetaName();
    const newGoal: MetaVar = {
      ctx: newCtx,
      type: body, // Note: body already has correct de Bruijn indices
      solution: undefined
    };

    // Build lambda term: λ(paramName : domain) => ?newGoal
    const lambdaTerm: TTKTerm = {
      tag: 'Binder',
      name: paramName,
      binderKind: { tag: 'BLam' },
      domain,
      body: { tag: 'Meta', id: newGoalId }
    };

    // Assign lambda to current goal
    const newMetaVars = new Map(engine.metaVars);
    newMetaVars.set(goalId, { ...goal, solution: lambdaTerm });
    newMetaVars.set(newGoalId, newGoal);

    // Replace current goal with new goal
    const newGoals = engine.goals.map(id => id === goalId ? newGoalId : id);

    return {
      success: true,
      newEngine: engine.withUpdates({
        metaVars: newMetaVars,
        goals: newGoals
      })
    };
  }
}

/**
 * intros: Apply intro repeatedly until goal is not a Pi
 *
 * Usage: intros [names...]
 * Example: intros A B a b
 *
 * Optionally provide names for the introduced variables.
 * If no names given, uses names from binders or generates fresh names.
 */
export class IntrosTactic implements Tactic {
  name = 'intros';

  constructor(public readonly names?: string[]) {}

  apply(engine: TacticEngine, _goal: MetaVar, _goalId: string): TacticResult {
    let current = engine;
    let nameIndex = 0;

    // Keep applying intro while goal is a Pi type (Binder with BPi)
    while (true) {
      const currentGoal = current.getFocusedGoal();
      if (!currentGoal) break;

      const goalTypeWhnf = whnf(currentGoal.type, {
        definitions: current.definitions
      });

      // Check if it's a Pi type (Binder with BPi kind)
      if (goalTypeWhnf.tag !== 'Binder' || goalTypeWhnf.binderKind.tag !== 'BPi') {
        break;
      }

      // Determine name
      const name = this.names && nameIndex < this.names.length
        ? this.names[nameIndex]
        : undefined;
      nameIndex++;

      // Apply intro
      const currentGoalId = current.getFocusedGoalId();
      if (!currentGoalId) break;

      const introResult = new IntroTactic(name).apply(
        current,
        currentGoal,
        currentGoalId
      );

      if (!introResult.success) {
        // If intro fails for any reason, return what we have so far
        return { success: true, newEngine: current };
      }

      current = introResult.newEngine;
    }

    return { success: true, newEngine: current };
  }
}

/**
 * apply: Apply a function to solve the goal, creating subgoals for arguments
 *
 * Usage: apply <function>
 * Example: apply f
 *
 * If the goal is B and f has type A -> B, creates a subgoal of type A.
 */
export class ApplyTactic implements Tactic {
  name = 'apply';

  constructor(public readonly fn: TTKTerm) {}

  apply(engine: TacticEngine, goal: MetaVar, goalId: string): TacticResult {
    try {
      // Infer type of function in goal's context
      const env = new TCEnv(
        goal.ctx,
        engine.definitions,
        engine.metaVars,
        engine.constraints,
        [],
        [],
        this.fn,
        new Map(),
        { mode: 'check' }
      );

      const inferredEnv = inferType(env);
      const fnType = inferredEnv.value; // The inferred type

      // Collect arguments from Pi type
      const argMetas: { id: string; meta: MetaVar }[] = [];
      let currentType = whnf(fnType, {
        definitions: engine.definitions
      });

      // Unwrap Pi types (Binder with BPi kind) and create metas for each argument
      while (currentType.tag === 'Binder' && currentType.binderKind.tag === 'BPi') {
        // Create meta for this argument
        const argMetaId = freshMetaName();
        const argMeta: MetaVar = {
          ctx: goal.ctx,
          type: currentType.domain,
          solution: undefined
        };
        argMetas.push({ id: argMetaId, meta: argMeta });

        // Substitute meta into body to get next type
        currentType = subst(0, { tag: 'Meta', id: argMetaId }, currentType.body);
        currentType = whnf(currentType, {
          definitions: engine.definitions
        });
      }

      // Unify return type with goal type
      const unifyResult = unifyTerms(currentType, goal.type, {
        mode: 'check',
        definitions: engine.definitions,
        flexibleVars: false
      });

      if (!unifyResult.success) {
        return {
          success: false,
          error: `apply: return type mismatch (${unifyResult.reason})`
        };
      }

      // Build application term: fn ?arg1 ?arg2 ...
      let appTerm: TTKTerm = this.fn;
      for (const { id } of argMetas) {
        appTerm = {
          tag: 'App',
          fn: appTerm,
          arg: { tag: 'Meta', id }
        };
      }

      // Assign application to goal
      const newMetaVars = new Map(engine.metaVars);
      newMetaVars.set(goalId, { ...goal, solution: appTerm });

      // Add arg metas to metaVars
      for (const { id, meta } of argMetas) {
        newMetaVars.set(id, meta);
      }

      // Add meta constraints from unification
      const newConstraints = [
        ...engine.constraints,
        ...unifyResult.metaConstraints.map(mc => ({
          ctx: goal.ctx,
          meta: mc.meta,
          rhs: mc.rhs
        }))
      ];

      // Replace current goal with arg metas (subgoals)
      const newGoalIds = argMetas
        .filter(({ meta }) => meta.solution === undefined)
        .map(({ id }) => id);

      const newGoals = [
        ...engine.goals.slice(0, engine.focusIndex),
        ...newGoalIds,
        ...engine.goals.slice(engine.focusIndex + 1)
      ];

      // Adjust focus to first new subgoal (if any)
      const newFocusIndex = newGoalIds.length > 0
        ? engine.focusIndex
        : Math.min(engine.focusIndex, Math.max(0, newGoals.length - 1));

      return {
        success: true,
        newEngine: engine.withUpdates({
          metaVars: newMetaVars,
          constraints: newConstraints,
          goals: newGoals,
          focusIndex: newFocusIndex
        }).solveConstraints()
      };
    } catch (e) {
      return {
        success: false,
        error: `apply: ${e instanceof Error ? e.message : String(e)}`,
        cause: e instanceof Error ? e : undefined
      };
    }
  }
}

/**
 * TacticSequence: Compose tactics sequentially
 *
 * Usage: TacticSequence('name', [tac1, tac2, tac3])
 *
 * Applies each tactic in sequence. If any fails, the entire sequence fails.
 */
export class TacticSequence implements Tactic {
  constructor(
    public readonly name: string,
    public readonly tactics: Tactic[]
  ) {}

  apply(engine: TacticEngine, _goal: MetaVar, _goalId: string): TacticResult {
    let current = engine;

    for (const tactic of this.tactics) {
      const currentGoal = current.getFocusedGoal();
      const currentGoalId = current.getFocusedGoalId();

      if (!currentGoal || !currentGoalId) {
        return {
          success: false,
          error: `${this.name}: no focused goal during sequence`
        };
      }

      const result = tactic.apply(current, currentGoal, currentGoalId);
      if (!result.success) {
        return {
          success: false,
          error: `${this.name}: tactic '${tactic.name}' failed: ${result.error}`,
          cause: result.cause
        };
      }

      current = result.newEngine;
    }

    return { success: true, newEngine: current };
  }
}
