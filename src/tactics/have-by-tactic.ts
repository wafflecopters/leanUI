/**
 * Have-by Tactic: Introduce a local hypothesis by proving it with tactics.
 *
 * Given `have h : T by tactics`, runs the nested tactic block to prove `T`,
 * then extends the main goal context with `h : T` for the remaining proof.
 *
 * Usage: have h : T by
 *   exact proof
 *
 * Proof term: let h : T = <proved term> in ?newGoal
 */

import { TTKTerm } from '../compiler/kernel';
import { MetaVar } from '../compiler/term';
import { TacticEngine } from './tacticsEngine';
import { Tactic, TacticResult, freshMetaName } from './tactic';
import { shiftTerm } from '../compiler/subst';

export class HaveByTactic implements Tactic {
  name = 'have';

  constructor(
    public readonly hypName: string,
    public readonly hypType: TTKTerm,
    public readonly proofTactics: Tactic[],
  ) {}

  apply(engine: TacticEngine, goal: MetaVar, goalId: string): TacticResult {
    try {
      const proofGoalId = freshMetaName();
      const proofGoal: MetaVar = {
        ctx: goal.ctx,
        type: this.hypType,
        solution: undefined,
      };

      const proofMetaVars = new Map(engine.metaVars);
      proofMetaVars.set(proofGoalId, proofGoal);

      let proofEngine = engine.withUpdates({
        metaVars: proofMetaVars,
        constraints: engine.constraints,
        goals: [proofGoalId],
        focusIndex: 0,
      });

      for (const tactic of this.proofTactics) {
        const currentGoal = proofEngine.getFocusedGoal();
        const currentGoalId = proofEngine.getFocusedGoalId();
        if (!currentGoal || !currentGoalId) {
          return {
            success: false,
            error: `have: proof tactic '${tactic.name}' has no goal to work on`,
          };
        }

        const result = tactic.apply(proofEngine, currentGoal, currentGoalId);
        if (!result.success) {
          return {
            success: false,
            error: `have: proof tactic '${tactic.name}' failed: ${result.error}`,
            cause: result.cause,
          };
        }
        proofEngine = result.newEngine;
      }

      const solvedProofGoal = proofEngine.metaVars.get(proofGoalId);
      if (!solvedProofGoal?.solution) {
        return {
          success: false,
          error: 'have: proof tactics did not solve the intermediate claim',
        };
      }

      const checkedProof = solvedProofGoal.solution;
      const newCtx = [...goal.ctx, { name: this.hypName, type: this.hypType, value: checkedProof }];
      const newGoalType = shiftTerm(goal.type, 1, 0);

      const newMetaId = freshMetaName();
      const newMeta: MetaVar = {
        ctx: newCtx,
        type: newGoalType,
        solution: undefined,
      };

      const letTerm: TTKTerm = {
        tag: 'Binder',
        binderKind: { tag: 'BLet', defVal: checkedProof },
        name: this.hypName,
        domain: this.hypType,
        body: { tag: 'Meta', id: newMetaId },
      };

      const finalMetaVars = new Map(proofEngine.metaVars);
      finalMetaVars.set(goalId, { ...goal, solution: letTerm });
      finalMetaVars.set(newMetaId, newMeta);

      const remainingProofGoals = proofEngine.goals.filter(id => {
        const meta = proofEngine.metaVars.get(id);
        return meta && meta.solution === undefined;
      });

      const newGoals = [
        ...engine.goals.slice(0, engine.focusIndex),
        newMetaId,
        ...remainingProofGoals,
        ...engine.goals.slice(engine.focusIndex + 1),
      ];

      return {
        success: true,
        newEngine: engine.withUpdates({
          metaVars: finalMetaVars,
          constraints: proofEngine.constraints,
          goals: newGoals,
          focusIndex: engine.focusIndex,
        }),
      };
    } catch (e) {
      const errorMsg = e instanceof Error
        ? e.message
        : (e && typeof e === 'object' && 'message' in e)
          ? String((e as any).message)
          : String(e);
      return {
        success: false,
        error: `have: ${errorMsg}`,
        cause: e instanceof Error ? e : undefined,
      };
    }
  }
}
