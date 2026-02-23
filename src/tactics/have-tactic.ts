/**
 * Have Tactic: Introduce a local hypothesis with a proof
 *
 * Given `have h : T := proof`, type-checks proof against T,
 * then extends the context with h : T for subsequent tactics.
 *
 * Usage: have h : T := proof
 * Example:
 *   goal : Equal (Succ n) (Succ m)
 *   have h : Equal n m := someProof
 *   -- now h : Equal n m is in context
 *
 * Proof term: let h : T = proof in ?newGoal
 */

import { TTKTerm } from '../compiler/kernel';
import { MetaVar } from '../compiler/term';
import { TacticEngine } from './tacticsEngine';
import { Tactic, TacticResult, freshMetaName } from './tactic';
import { checkType, inferType } from '../compiler/checker';
import { shiftTerm } from '../compiler/subst';
import { TCEnv } from '../compiler/term';

/**
 * HaveTactic: Introduce a local hypothesis
 *
 * have h : T := proof
 * - Checks proof : T
 * - Adds h : T to context
 * - Shifts goal type by 1 (new binding)
 * - Builds let-binding in proof term
 */
export class HaveTactic implements Tactic {
  name = 'have';

  constructor(
    public readonly hypName: string,
    public readonly hypType: TTKTerm,
    public readonly hypProof: TTKTerm
  ) {}

  apply(engine: TacticEngine, goal: MetaVar, goalId: string): TacticResult {
    try {
      // 1. Type-check the proof against the declared type
      const env = new TCEnv(
        goal.ctx,
        engine.definitions,
        engine.metaVars,
        engine.constraints,
        [],
        [],
        this.hypProof,
        new Map(),
        { mode: 'check' }
      );

      // When no explicit type is given, hypType is a Hole. We need the actual inferred type.
      let resolvedType: TTKTerm;
      let checkedEnv: TCEnv<TTKTerm>;

      if (this.hypType.tag === 'Hole') {
        // Type inferred: infer the proof's type, then check against it
        const inferredEnv = inferType(env);
        resolvedType = inferredEnv.zonkTerm(inferredEnv.value);
        checkedEnv = inferredEnv as any;
      } else {
        // Explicit type given: check proof against it
        checkedEnv = checkType(env, this.hypType);
        resolvedType = this.hypType;
      }

      const checkedProof = checkedEnv.zonkTerm(checkedEnv.elaboratedTerm ?? this.hypProof);

      // 2. Create new goal with extended context (store value for ζ-reduction)
      const newCtx = [...goal.ctx, { name: this.hypName, type: resolvedType, value: checkedProof }];
      const newGoalType = shiftTerm(goal.type, 1, 0);

      const newMetaId = freshMetaName();
      const newMeta: MetaVar = {
        ctx: newCtx,
        type: newGoalType,
        solution: undefined
      };

      // 3. Build proof term: let h : T = proof in ?newGoal
      const letTerm: TTKTerm = {
        tag: 'Binder',
        binderKind: { tag: 'BLet', defVal: checkedProof },
        name: this.hypName,
        domain: resolvedType,
        body: { tag: 'Meta', id: newMetaId }
      };

      // 4. Update engine state
      // Merge metaVars from type-checking (may contain solved metas from implicit args)
      const newMetaVars = new Map(checkedEnv.metaVars);
      newMetaVars.set(goalId, { ...goal, solution: letTerm });
      newMetaVars.set(newMetaId, newMeta);

      const newGoals = engine.goals.map(g => g === goalId ? newMetaId : g);

      return {
        success: true,
        newEngine: engine.withUpdates({
          metaVars: newMetaVars,
          constraints: checkedEnv.constraints,
          goals: newGoals
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
        error: `have: ${errorMsg}`,
        cause: e instanceof Error ? e : undefined
      };
    }
  }
}
