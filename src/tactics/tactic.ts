/**
 * Tactic Interface and Core Tactics
 *
 * A tactic is a proof state transformation: it takes a TacticEngine and a goal,
 * and returns a new TacticEngine with the goal solved or refined into subgoals.
 */

import { TTKTerm, TTKContext } from '../compiler/kernel';
import { MetaVar, TCEnv, createNamedArgLookup } from '../compiler/term';
import { TacticEngine } from './tacticsEngine';
import { checkType, inferType } from '../compiler/checker';
import { whnf } from '../compiler/whnf';
import { subst } from '../compiler/subst';
import { unifyTerms } from '../compiler/unify';

/**
 * TacticResult: Outcome of applying a tactic
 */
export type TacticResult =
  | { success: true; newEngine: TacticEngine; unifiedEquation?: UnifiedEquation; solvedArgs?: SolvedArg[] }
  | { success: false; error: string; cause?: Error };

/** Info about the equation used by a rewrite tactic (with all implicit args unified). */
export interface UnifiedEquation {
  readonly lhs: TTKTerm;
  readonly rhs: TTKTerm;
}

/** An argument that was solved by unification in an apply tactic. */
export interface SolvedArg {
  readonly term: TTKTerm;
  readonly type: TTKTerm;
  readonly implicit: boolean;
}

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

      // Zonk goal type to resolve any solved metas before type checking.
      // Without this, App(Meta(?P), Meta(?x)) stays as-is and hits the
      // flex-rigid solver, generating a constant-function heuristic that
      // conflicts with the already-solved pattern. After zonking (and WHNF),
      // it becomes the concrete type (e.g., Nat) and checks trivially.
      const zonkedGoalType = whnf(engine.zonkTerm(goal.type, goal.ctx.length), { definitions: engine.definitions, typingContext: goal.ctx });

      // Check term has expected type
      const checkedEnv = checkType(env, zonkedGoalType);

      // Zonk the checked term (resolve any new metas)
      const solution = checkedEnv.zonkTerm(checkedEnv.elaboratedTerm ?? this.term);

      // Assign solution to goal
      // Merge checkedEnv.metaVars to capture any new metas created during type checking
      // (e.g., implicit argument metas for constructors like Nil : {A : Type} -> List A)
      const newMetaVars = new Map(checkedEnv.metaVars);
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
      // Handle TCEnvError (which is not an Error instance)
      const errorMsg = e instanceof Error
        ? e.message
        : (e && typeof e === 'object' && 'message' in e)
          ? String((e as any).message)
          : String(e);

      return {
        success: false,
        error: `exact: ${errorMsg}`,
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
    // Search context backwards (most recent first)
    // Try exact with each variable - the checker handles de Bruijn adjustments
    for (let i = goal.ctx.length - 1; i >= 0; i--) {
      const varIndex = goal.ctx.length - 1 - i;
      const solution: TTKTerm = { tag: 'Var', index: varIndex };
      const result = new ExactTactic(solution).apply(engine, goal, goalId);
      if (result.success) {
        return result;
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
    // Zonk goal type to resolve solved metas, then WHNF
    const goalType = engine.zonkTerm(goal.type, goal.ctx.length);
    const goalTypeWhnf = whnf(goalType, {
      definitions: engine.definitions,
      typingContext: goal.ctx
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

    if (this.names && this.names.length > 0) {
      // Named mode: introduce exactly these names, fail if any can't be introduced
      for (let i = 0; i < this.names.length; i++) {
        const currentGoal = current.getFocusedGoal();
        if (!currentGoal) {
          return { success: false, error: `intros: no goal remaining for '${this.names[i]}'` };
        }
        const currentGoalId = current.getFocusedGoalId();
        if (!currentGoalId) {
          return { success: false, error: `intros: no goal remaining for '${this.names[i]}'` };
        }
        const introResult = new IntroTactic(this.names[i]).apply(current, currentGoal, currentGoalId);
        if (!introResult.success) {
          return { success: false, error: `intros: cannot introduce '${this.names[i]}' — ${introResult.error}` };
        }
        current = introResult.newEngine;
      }
    } else {
      // No names: introduce all Pi binders automatically
      while (true) {
        const currentGoal = current.getFocusedGoal();
        if (!currentGoal) break;
        const zonkedGoalType = current.zonkTerm(currentGoal.type, currentGoal.ctx.length);
        const goalTypeWhnf = whnf(zonkedGoalType, {
          definitions: current.definitions,
          typingContext: currentGoal.ctx
        });
        if (goalTypeWhnf.tag !== 'Binder' || goalTypeWhnf.binderKind.tag !== 'BPi') break;
        const currentGoalId = current.getFocusedGoalId();
        if (!currentGoalId) break;
        const introResult = new IntroTactic().apply(current, currentGoal, currentGoalId);
        if (!introResult.success) break;
        current = introResult.newEngine;
      }
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
      const argMetas: { id: string; meta: MetaVar; implicit: boolean }[] = [];
      let currentType = whnf(fnType, {
        definitions: engine.definitions,
        typingContext: goal.ctx
      });

      // Look up which args are implicit
      let fnName: string | undefined;
      if (this.fn.tag === 'Const') {
        fnName = this.fn.name;
      }
      const namedArgLookup = createNamedArgLookup(engine.definitions);
      const namedArgMap = fnName ? namedArgLookup(fnName) : undefined;
      const numImplicit = namedArgMap?.size ?? 0;
      let argIndex = 0;

      // Unwrap Pi types (Binder with BPi kind) and create metas for each argument
      while (currentType.tag === 'Binder' && currentType.binderKind.tag === 'BPi') {
        const isImplicit = argIndex < numImplicit;
        // Create meta for this argument
        const argMetaId = freshMetaName();
        const argMeta: MetaVar = {
          ctx: goal.ctx,
          type: currentType.domain,
          solution: undefined
        };
        argMetas.push({ id: argMetaId, meta: argMeta, implicit: isImplicit });

        // Substitute meta into body to get next type
        currentType = subst(0, { tag: 'Meta', id: argMetaId }, currentType.body);
        currentType = whnf(currentType, {
          definitions: engine.definitions,
          typingContext: goal.ctx
        });
        argIndex++;
      }

      // Unify return type with goal type.
      // Do NOT zonk the goal type first — zonking substitutes meta solutions which
      // may already be in reduced form (e.g., `Succ(plus n' X)` instead of
      // `plus (Succ n') X`), making structural matching with the function's return
      // type impossible. Instead, keep metas in the goal and let unification
      // produce meta constraints that the solver resolves.
      const unifyResult = unifyTerms(currentType, goal.type, {
        mode: 'check',
        definitions: engine.definitions,
        flexibleVars: false
      });

      if (!unifyResult.success) {
        return {
          success: false,
          error: `apply ${fnName ?? '?'}: return type mismatch (${unifyResult.reason})`
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
      // Merge inferredEnv.metaVars to capture any new metas created during type inference
      const newMetaVars = new Map(inferredEnv.metaVars);
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

      // Solve constraints FIRST so that explicit args solvable by unification
      // (e.g., congPlusRight's `p : Nat` determined by goal structure) get resolved
      // before we decide which args become subgoals.
      const solvedEngine = engine.withUpdates({
        metaVars: newMetaVars,
        constraints: newConstraints,
        goals: engine.goals,
        focusIndex: engine.focusIndex
      }).solveConstraints();

      // Replace current goal with arg metas that are STILL unsolved after constraint solving
      const newGoalIds = argMetas
        .filter(({ id, implicit }) => {
          const meta = solvedEngine.metaVars.get(id);
          return meta && meta.solution === undefined && !implicit;
        })
        .map(({ id }) => id);

      const newGoals = [
        ...solvedEngine.goals.slice(0, solvedEngine.focusIndex),
        ...newGoalIds,
        ...solvedEngine.goals.slice(solvedEngine.focusIndex + 1)
      ];

      // Adjust focus to first new subgoal (if any)
      const newFocusIndex = newGoalIds.length > 0
        ? solvedEngine.focusIndex
        : Math.min(solvedEngine.focusIndex, Math.max(0, newGoals.length - 1));

      // Collect solved args for prose rendering (e.g., "f" in "cong f")
      const solvedArgs: SolvedArg[] = argMetas.map(({ id, meta: origMeta, implicit }) => {
        const solved = solvedEngine.metaVars.get(id);
        return {
          term: solved?.solution ?? { tag: 'Hole' as const, id: '_' },
          type: origMeta.type,
          implicit,
        };
      });

      return {
        success: true,
        newEngine: solvedEngine.withUpdates({
          goals: newGoals,
          focusIndex: newFocusIndex
        }),
        solvedArgs,
      };
    } catch (e) {
      // Handle TCEnvError (which is not an Error instance)
      const errorMsg = e instanceof Error
        ? e.message
        : (e && typeof e === 'object' && 'message' in e)
          ? String((e as any).message)
          : String(e);

      return {
        success: false,
        error: `apply: ${errorMsg}`,
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
