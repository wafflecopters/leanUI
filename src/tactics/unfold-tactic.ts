/**
 * Unfold Tactic: Expand named definitions in the goal type
 *
 * Given `unfold f`, replaces all occurrences of Const("f") in the goal type
 * with f's definition body. Multiple names: `unfold f, g` unfolds both.
 *
 * Proof term: Meta(newGoalId) where newGoalId has the unfolded type.
 * This works because the unfolded type is definitionally equal to the original,
 * so the type checker accepts Meta(newGoalId) : originalGoalType.
 */

import { TTKTerm } from '../compiler/kernel';
import { MetaVar, getTermDefinition, createDefinitionsMap } from '../compiler/term';
import { fullNormalize } from '../compiler/whnf';
import { TacticEngine } from './tacticsEngine';
import { Tactic, TacticResult, freshMetaName } from './tactic';

export class UnfoldTactic implements Tactic {
  name = 'unfold';

  constructor(public readonly names: string[]) {}

  apply(engine: TacticEngine, goal: MetaVar, goalId: string): TacticResult {
    try {
      let currentType = goal.type;
      let changed = false;

      for (const name of this.names) {
        // Look up definition
        const def = getTermDefinition(engine.definitions, name);
        if (!def || !def.value) {
          return {
            success: false,
            error: `unfold: '${name}' has no definition to unfold`
          };
        }

        // Replace all Const(name) with def.value in current type
        const newType = this.replaceConst(currentType, name, def.value);
        if (newType !== currentType) {
          changed = true;
          currentType = newType;
        }
      }

      if (!changed) {
        return {
          success: false,
          error: `unfold: no occurrences of ${this.names.map(n => `'${n}'`).join(', ')} found in goal`
        };
      }

      // Deep beta/iota-normalize the unfolded type to reduce redexes
      // (e.g., (\x => body)(arg) from definition substitution, Match on known args).
      // Uses empty definitions so we only do beta/iota, not delta-reduction.
      currentType = fullNormalize(currentType, createDefinitionsMap());

      // Create new goal with unfolded type
      const newMetaId = freshMetaName();
      const newMeta: MetaVar = {
        ctx: goal.ctx,
        type: currentType,
        solution: undefined
      };

      // Proof term: just Meta(newMetaId)
      // Since unfolded type is definitionally equal to original,
      // the type checker accepts this.
      const newMetaVars = new Map(engine.metaVars);
      newMetaVars.set(goalId, { ...goal, solution: { tag: 'Meta', id: newMetaId } });
      newMetaVars.set(newMetaId, newMeta);

      const newGoals = engine.goals.map(g => g === goalId ? newMetaId : g);

      return {
        success: true,
        newEngine: engine.withUpdates({
          metaVars: newMetaVars,
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
        error: `unfold: ${errorMsg}`,
        cause: e instanceof Error ? e : undefined
      };
    }
  }

  /**
   * Replace all occurrences of Const(name) with replacement in term.
   * Returns the same reference if nothing changed (for fast equality check).
   * The App spine naturally handles argument application after replacement.
   */
  private replaceConst(term: TTKTerm, name: string, replacement: TTKTerm): TTKTerm {
    switch (term.tag) {
      case 'Const':
        return term.name === name ? replacement : term;

      case 'App': {
        const fn = this.replaceConst(term.fn, name, replacement);
        const arg = this.replaceConst(term.arg, name, replacement);
        if (fn === term.fn && arg === term.arg) return term;
        return { tag: 'App', fn, arg };
      }

      case 'Binder': {
        const domain = this.replaceConst(term.domain, name, replacement);
        const body = this.replaceConst(term.body, name, replacement);
        if (domain === term.domain && body === term.body) return term;
        return {
          tag: 'Binder',
          binderKind: term.binderKind,
          name: term.name,
          domain,
          body
        };
      }

      case 'Match': {
        const scrutinee = this.replaceConst(term.scrutinee, name, replacement);
        let clausesChanged = false;
        const clauses = term.clauses.map(c => {
          const rhs = this.replaceConst(c.rhs, name, replacement);
          if (rhs !== c.rhs) clausesChanged = true;
          return rhs === c.rhs ? c : { ...c, rhs };
        });
        if (scrutinee === term.scrutinee && !clausesChanged) return term;
        return { tag: 'Match', scrutinee, clauses };
      }

      // Leaf nodes — no Const inside
      case 'Var':
      case 'Hole':
      case 'Meta':
      case 'Sort':
      case 'ULevel':
      case 'ULit':
      case 'UOmega':
        return term;

      default:
        return term;
    }
  }
}
