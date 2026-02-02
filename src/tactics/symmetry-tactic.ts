/**
 * Symmetry Tactic: Transform Equal a b to Equal b a
 *
 * Given a goal Equal a b, applies the sym function to transform it to Equal b a.
 *
 * Usage: symmetry
 * Example:
 *   goal : Equal n m
 *   After symmetry: new goal Equal m n
 */

import { TTKTerm } from '../compiler/kernel';
import { MetaVar } from '../compiler/term';
import { TacticEngine } from './tacticsEngine';
import { Tactic, TacticResult, freshMetaName } from './tactic';
import { whnf } from '../compiler/whnf';

/**
 * SymmetryTactic: Flip an equality goal from Equal a b to Equal b a
 *
 * This tactic applies the symmetry rule: if we can prove Equal b a, then we get Equal a b.
 * It creates a new goal Equal b a and uses sym to derive the original goal.
 */
export class SymmetryTactic implements Tactic {
  name = 'symmetry';

  apply(engine: TacticEngine, goal: MetaVar, goalId: string): TacticResult {
    try {
      // Normalize the goal type to WHNF
      const goalTypeWhnf = whnf(goal.type, { definitions: engine.definitions });

      // Check if goal is an equality type: Equal A a b
      if (goalTypeWhnf.tag !== 'App') {
        return {
          success: false,
          error: `symmetry: goal is not an equality type, got ${goalTypeWhnf.tag}`
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
          error: `symmetry: goal is not an equality (head is ${current.tag === 'Const' ? current.name : current.tag})`
        };
      }

      if (args.length < 2) {
        return {
          success: false,
          error: `symmetry: equality needs at least 2 arguments (lhs and rhs), got ${args.length}`
        };
      }

      // Extract LHS and RHS
      const rhs = args[args.length - 1];
      const lhs = args[args.length - 2];

      // Build the flipped equality type: Equal rhs lhs
      // We need to rebuild the full application with swapped arguments
      let flippedType: TTKTerm = current; // Start with Equal
      for (let i = 0; i < args.length - 2; i++) {
        flippedType = { tag: 'App', fn: flippedType, arg: args[i] };
      }
      // Add RHS then LHS (flipped)
      flippedType = { tag: 'App', fn: flippedType, arg: rhs };
      flippedType = { tag: 'App', fn: flippedType, arg: lhs };

      // Create a new meta for the flipped goal
      const newMetaId = freshMetaName();
      const newMeta: MetaVar = {
        ctx: goal.ctx,
        type: flippedType,
        solution: undefined
      };

      // Build the proof term: sym <?newMeta>
      // This says "prove Equal b a (in newMeta), then apply sym to get Equal a b"
      const symApp: TTKTerm = {
        tag: 'App',
        fn: { tag: 'Const', name: 'sym' },
        arg: { tag: 'Meta', id: newMetaId }
      };

      // Update engine state
      const newMetaVars = new Map(engine.metaVars);
      newMetaVars.set(goalId, { ...goal, solution: symApp });
      newMetaVars.set(newMetaId, newMeta);

      // Replace current goal with new goal
      const newGoals = engine.goals.map(g => g === goalId ? newMetaId : g);

      return {
        success: true,
        newEngine: engine.withUpdates({
          metaVars: newMetaVars,
          goals: newGoals
        })
      };
    } catch (e) {
      const errorMsg = e instanceof Error ? e.message : String(e);
      return {
        success: false,
        error: `symmetry: ${errorMsg}`,
        cause: e instanceof Error ? e : undefined
      };
    }
  }
}
