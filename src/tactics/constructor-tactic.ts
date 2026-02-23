/**
 * Constructor Tactic: Apply the unique constructor of the goal's inductive type
 *
 * Usage: constructor
 * Example goal: Pair Nat Bool
 * Applies: MkPair, creating subgoals for each explicit argument
 *
 * Works for any inductive type with exactly one constructor (records, Pair, DPair, etc.)
 */

import { TTKTerm } from '../compiler/kernel';
import { MetaVar } from '../compiler/term';
import { TacticEngine } from './tacticsEngine';
import { Tactic, TacticResult, ApplyTactic } from './tactic';
import { whnf } from '../compiler/whnf';

/**
 * ConstructorTactic: Find the unique constructor and apply it
 *
 * 1. WHNF the goal type to find the inductive type head
 * 2. Look up the inductive definition
 * 3. Verify exactly one constructor exists
 * 4. Delegate to ApplyTactic with the constructor
 */
export class ConstructorTactic implements Tactic {
  name = 'constructor';

  apply(engine: TacticEngine, goal: MetaVar, goalId: string): TacticResult {
    try {
      // Zonk goal type to resolve any solved metas, then normalize to WHNF
      const zonkedGoalType = engine.zonkTerm(goal.type, goal.ctx.length);
      const goalTypeWhnf = whnf(zonkedGoalType, { definitions: engine.definitions, typingContext: goal.ctx });

      // Walk the App spine to find the inductive type head
      let current: TTKTerm = goalTypeWhnf;
      while (current.tag === 'App') {
        current = current.fn;
      }

      if (current.tag !== 'Const') {
        return {
          success: false,
          error: `constructor: goal type head is not a constant (got ${current.tag})`
        };
      }

      const typeName = current.name;

      // Look up the inductive definition
      const inductiveDef = engine.definitions.inductiveTypes.get(typeName);
      if (!inductiveDef) {
        return {
          success: false,
          error: `constructor: '${typeName}' is not an inductive type`
        };
      }

      // Verify exactly one constructor
      if (inductiveDef.constructors.length === 0) {
        return {
          success: false,
          error: `constructor: '${typeName}' has no constructors`
        };
      }

      if (inductiveDef.constructors.length > 1) {
        const ctorNames = inductiveDef.constructors.map(c => c.name).join(', ');
        return {
          success: false,
          error: `constructor: '${typeName}' has ${inductiveDef.constructors.length} constructors (${ctorNames}), use 'apply' instead`
        };
      }

      // Build the constructor term
      const ctor = inductiveDef.constructors[0];
      const ctorTerm: TTKTerm = { tag: 'Const', name: ctor.name };

      // Delegate to ApplyTactic with zonked goal type so that unification
      // sees the concrete type (e.g., Pair Nat Nat) instead of unresolved
      // metas from earlier constructor steps (e.g., App(Meta(?P), Meta(?fst)))
      const zonkedGoal = { ...goal, type: goalTypeWhnf };
      const applyResult = new ApplyTactic(ctorTerm).apply(engine, zonkedGoal, goalId);

      if (!applyResult.success) {
        return {
          success: false,
          error: `constructor: failed to apply '${ctor.name}': ${applyResult.error}`
        };
      }

      return applyResult;
    } catch (e) {
      const errorMsg = e instanceof Error
        ? e.message
        : (e && typeof e === 'object' && 'message' in e)
          ? String((e as any).message)
          : String(e);

      return {
        success: false,
        error: `constructor: ${errorMsg}`,
        cause: e instanceof Error ? e : undefined
      };
    }
  }
}
