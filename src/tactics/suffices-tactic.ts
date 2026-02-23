/**
 * Suffices Tactic: Introduce an intermediate claim, prove the goal using it,
 * then prove the claim.
 *
 * Usage: suffices h : T by closingTactic
 *
 * This is a "backward have": you state what you need (T), show how it
 * closes the current goal (closingTactic), then prove T.
 *
 * Proof term: let h : T = ?claim in <closingResult>
 */

import { TTKTerm } from '../compiler/kernel';
import { MetaVar } from '../compiler/term';
import { TacticEngine } from './tacticsEngine';
import { Tactic, TacticResult, freshMetaName } from './tactic';
import { shiftTerm } from '../compiler/subst';

export class SufficesTactic implements Tactic {
  name = 'suffices';

  constructor(
    public readonly hypName: string,
    public readonly hypType: TTKTerm,
    public readonly closingTactics: Tactic[]
  ) {}

  apply(engine: TacticEngine, goal: MetaVar, goalId: string): TacticResult {
    try {
      // 1. Create meta for the claim proof (to be solved later)
      const claimMetaId = freshMetaName();
      const claimMeta: MetaVar = {
        ctx: goal.ctx,
        type: this.hypType,
        solution: undefined
      };

      // 3. Create a temporary goal with h : T in context
      //    to run the closing tactic on
      const extendedCtx = [...goal.ctx, { name: this.hypName, type: this.hypType }];
      const shiftedGoalType = shiftTerm(goal.type, 1, 0);

      const closingGoalId = freshMetaName();
      const closingGoal: MetaVar = {
        ctx: extendedCtx,
        type: shiftedGoalType,
        solution: undefined
      };

      // 3. Run closing tactics on the extended goal
      const newMetaVars = new Map(engine.metaVars);
      newMetaVars.set(claimMetaId, claimMeta);
      newMetaVars.set(closingGoalId, closingGoal);

      let closingEngine = engine.withUpdates({
        metaVars: newMetaVars,
        constraints: engine.constraints,
        goals: [closingGoalId],
        focusIndex: 0
      });

      // Apply each closing tactic in sequence
      for (const tactic of this.closingTactics) {
        const currentGoal = closingEngine.getFocusedGoal();
        const currentGoalId = closingEngine.getFocusedGoalId();
        if (!currentGoal || !currentGoalId) {
          return {
            success: false,
            error: `suffices: closing tactic '${tactic.name}' has no goal to work on`
          };
        }

        const result = tactic.apply(closingEngine, currentGoal, currentGoalId);
        if (!result.success) {
          return {
            success: false,
            error: `suffices: closing tactic '${tactic.name}' failed: ${result.error}`,
            cause: result.cause
          };
        }
        closingEngine = result.newEngine;
      }

      // The closing tactics should have solved the closingGoal
      const solvedClosingGoal = closingEngine.metaVars.get(closingGoalId);
      if (!solvedClosingGoal?.solution) {
        return {
          success: false,
          error: 'suffices: closing tactic did not solve the goal'
        };
      }

      // 5. Build proof term: let h : T = ?claim in <closingResult>
      const letTerm: TTKTerm = {
        tag: 'Binder',
        binderKind: { tag: 'BLet', defVal: { tag: 'Meta', id: claimMetaId } },
        name: this.hypName,
        domain: this.hypType,
        body: solvedClosingGoal.solution
      };

      // 6. Update engine: solve original goal, add claim as new goal
      const finalMetaVars = new Map(closingEngine.metaVars);
      finalMetaVars.set(goalId, { ...goal, solution: letTerm });

      // The new goals: replace original goal with claim meta + any leftover closing goals
      const remainingClosingGoals = closingEngine.goals.filter(id => {
        const meta = closingEngine.metaVars.get(id);
        return meta && meta.solution === undefined;
      });

      const newGoals = [
        ...engine.goals.slice(0, engine.focusIndex),
        claimMetaId,
        ...remainingClosingGoals,
        ...engine.goals.slice(engine.focusIndex + 1)
      ];

      return {
        success: true,
        newEngine: engine.withUpdates({
          metaVars: finalMetaVars,
          constraints: closingEngine.constraints,
          goals: newGoals,
          focusIndex: engine.focusIndex
        })
      };
    } catch (e) {
      const errorMsg = e instanceof Error
        ? e.message
        : (e && typeof e === 'object' && 'message' in e)
          ? String((e as any).message)
          : String(e);
      return {
        success: false,
        error: `suffices: ${errorMsg}`,
        cause: e instanceof Error ? e : undefined
      };
    }
  }
}
