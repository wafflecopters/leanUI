/**
 * Transitivity Tactic: Chain two equality proofs
 *
 * Given a goal Equal a c and a middle term b, creates two subgoals:
 * - Equal a b
 * - Equal b c
 *
 * Usage: transitivity b
 * Example:
 *   goal : Equal a c
 *   After transitivity b: two goals: Equal a b, Equal b c
 */

import { TTKTerm } from '../compiler/kernel';
import { MetaVar } from '../compiler/term';
import { TacticEngine } from './tacticsEngine';
import { Tactic, TacticResult, freshMetaName } from './tactic';
import { whnf } from '../compiler/whnf';

/**
 * TransitivityTactic: Split an equality goal using transitivity
 *
 * Given Equal a c, the user provides a middle term b, and we create two goals:
 * - Equal a b
 * - Equal b c
 * These are combined using trans to prove the original goal.
 */
export class TransitivityTactic implements Tactic {
  name = 'transitivity';

  constructor(public readonly middleTerm: TTKTerm) {}

  apply(engine: TacticEngine, goal: MetaVar, goalId: string): TacticResult {
    try {
      // Normalize the goal type to WHNF
      const goalTypeWhnf = whnf(goal.type, { definitions: engine.definitions });

      // Check if goal is an equality type: Equal A a c
      if (goalTypeWhnf.tag !== 'App') {
        return {
          success: false,
          error: `transitivity: goal is not an equality type, got ${goalTypeWhnf.tag}`
        };
      }

      // Walk backwards through the application spine to get all arguments
      const args: TTKTerm[] = [];
      let current: TTKTerm = goalTypeWhnf;
      while (current.tag === 'App') {
        args.unshift(current.arg);
        current = current.fn;
      }

      // Verify head is Equal
      if (current.tag !== 'Const' || current.name !== 'Equal') {
        return {
          success: false,
          error: `transitivity: goal is not an equality (head is ${current.tag === 'Const' ? current.name : current.tag})`
        };
      }

      if (args.length < 2) {
        return {
          success: false,
          error: `transitivity: equality needs at least 2 arguments (lhs and rhs), got ${args.length}`
        };
      }

      // Extract LHS (a) and RHS (c)
      const c = args[args.length - 1];
      const a = args[args.length - 2];

      // Build first goal: Equal a b
      let firstGoalType: TTKTerm = current; // Start with Equal
      for (let i = 0; i < args.length - 2; i++) {
        firstGoalType = { tag: 'App', fn: firstGoalType, arg: args[i] };
      }
      firstGoalType = { tag: 'App', fn: firstGoalType, arg: a };
      firstGoalType = { tag: 'App', fn: firstGoalType, arg: this.middleTerm };

      // Build second goal: Equal b c
      let secondGoalType: TTKTerm = current; // Start with Equal
      for (let i = 0; i < args.length - 2; i++) {
        secondGoalType = { tag: 'App', fn: secondGoalType, arg: args[i] };
      }
      secondGoalType = { tag: 'App', fn: secondGoalType, arg: this.middleTerm };
      secondGoalType = { tag: 'App', fn: secondGoalType, arg: c };

      // Create two new metas for the subgoals
      const firstMetaId = freshMetaName();
      const secondMetaId = freshMetaName();

      const firstMeta: MetaVar = {
        ctx: goal.ctx,
        type: firstGoalType,
        solution: undefined
      };

      const secondMeta: MetaVar = {
        ctx: goal.ctx,
        type: secondGoalType,
        solution: undefined
      };

      // Build the proof term: trans <?firstMeta> <?secondMeta>
      const transApp: TTKTerm = {
        tag: 'App',
        fn: {
          tag: 'App',
          fn: { tag: 'Const', name: 'trans' },
          arg: { tag: 'Meta', id: firstMetaId }
        },
        arg: { tag: 'Meta', id: secondMetaId }
      };

      // Update engine state
      const newMetaVars = new Map(engine.metaVars);
      newMetaVars.set(goalId, { ...goal, solution: transApp });
      newMetaVars.set(firstMetaId, firstMeta);
      newMetaVars.set(secondMetaId, secondMeta);

      // Replace current goal with two new goals
      const newGoals = [
        ...engine.goals.slice(0, engine.focusIndex),
        firstMetaId,
        secondMetaId,
        ...engine.goals.slice(engine.focusIndex + 1)
      ];

      return {
        success: true,
        newEngine: engine.withUpdates({
          metaVars: newMetaVars,
          goals: newGoals,
          focusIndex: engine.focusIndex // Focus on first new goal
        })
      };
    } catch (e) {
      const errorMsg = e instanceof Error ? e.message : String(e);
      return {
        success: false,
        error: `transitivity: ${errorMsg}`,
        cause: e instanceof Error ? e : undefined
      };
    }
  }
}
