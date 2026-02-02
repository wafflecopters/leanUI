/**
 * Reflexivity Tactic: Prove equality goals of the form a = a
 *
 * Usage: reflexivity
 * Example goal: Equal n n
 * Applies: refl
 */

import { TTKTerm } from '../compiler/kernel';
import { MetaVar } from '../compiler/term';
import { TacticEngine } from './tacticsEngine';
import { Tactic, TacticResult } from './tactic';
import { whnf } from '../compiler/whnf';

/**
 * ReflexivityTactic: Solve goals where both sides of equality are definitionally equal
 *
 * Checks if the goal is `Equal a a` (or `Equal a b` where `a ≡ b` definitionally),
 * and if so, solves it with `refl`.
 */
export class ReflexivityTactic implements Tactic {
  name = 'reflexivity';

  apply(engine: TacticEngine, goal: MetaVar, goalId: string): TacticResult {
    try {
      // Normalize the goal type to WHNF
      const goalTypeWhnf = whnf(goal.type, { definitions: engine.definitions });

      // Check if goal is an equality type
      // Equal is typically: Equal A a b (or Equal {A} a b with implicit A)
      // In application form: (Equal A) a b or ((Equal A) a) b

      // Extract the equality application
      if (goalTypeWhnf.tag !== 'App') {
        return {
          success: false,
          error: `reflexivity: goal is not an equality type, got ${goalTypeWhnf.tag}`
        };
      }

      // Walk backwards through the application spine to get all arguments
      const args: TTKTerm[] = [];
      let current: TTKTerm = goalTypeWhnf;
      while (current.tag === 'App') {
        args.unshift(current.arg);
        current = current.fn;
      }

      // Now 'current' should be the head (Equal or a const resolving to Equal)
      // args should be [A, lhs, rhs] or [lhs, rhs] if A is implicit

      if (args.length < 2) {
        return {
          success: false,
          error: `reflexivity: equality needs at least 2 arguments (lhs and rhs), got ${args.length}`
        };
      }

      // Get lhs and rhs (last two arguments)
      const rhs = args[args.length - 1];
      const lhs = args[args.length - 2];

      // Normalize both sides
      const lhsWhnf = whnf(lhs, { definitions: engine.definitions });
      const rhsWhnf = whnf(rhs, { definitions: engine.definitions });

      // Check if they're definitionally equal (structurally identical after normalization)
      if (!this.defEqual(lhsWhnf, rhsWhnf)) {
        return {
          success: false,
          error: `reflexivity: sides are not definitionally equal\n  LHS: ${this.termToString(lhsWhnf)}\n  RHS: ${this.termToString(rhsWhnf)}`
        };
      }

      // Sides are equal! Apply refl
      // refl has type: {A : Type} -> {a : A} -> Equal a a
      // We need to provide: refl {A := type_of_lhs} {a := lhs}

      // For now, let's use a simple refl constant application
      // The type checker should be able to infer the implicit arguments
      const reflTerm: TTKTerm = { tag: 'Const', name: 'refl' };

      // Solve the goal with refl
      const newMetaVars = new Map(engine.metaVars);
      newMetaVars.set(goalId, { ...goal, solution: reflTerm });

      // Remove this goal from the goal list
      const newGoals = engine.goals.filter(g => g !== goalId);

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
        error: `reflexivity: ${errorMsg}`,
        cause: e instanceof Error ? e : undefined
      };
    }
  }

  /**
   * Check if two terms are definitionally equal (structurally identical)
   */
  private defEqual(a: TTKTerm, b: TTKTerm): boolean {
    if (a.tag !== b.tag) return false;

    switch (a.tag) {
      case 'Var':
        return b.tag === 'Var' && a.index === b.index;

      case 'Const':
        return b.tag === 'Const' && a.name === b.name;

      case 'App':
        return b.tag === 'App' &&
               this.defEqual(a.fn, b.fn) &&
               this.defEqual(a.arg, b.arg);

      case 'Binder':
        return b.tag === 'Binder' &&
               a.binderKind.tag === b.binderKind.tag &&
               this.defEqual(a.domain, b.domain) &&
               this.defEqual(a.body, b.body);

      case 'Sort':
        return b.tag === 'Sort' && this.defEqual(a.level, b.level);

      case 'ULevel':
        return b.tag === 'ULevel';

      case 'ULit':
        return b.tag === 'ULit' && a.n === b.n;

      case 'UOmega':
        return b.tag === 'UOmega';

      case 'Meta':
        // Metas are equal if they have the same ID
        return b.tag === 'Meta' && a.id === b.id;

      case 'Hole':
        return b.tag === 'Hole' && a.id === b.id;

      default:
        return false;
    }
  }

  /**
   * Helper: Convert term to string for error messages
   */
  private termToString(term: TTKTerm): string {
    switch (term.tag) {
      case 'Const':
        return term.name;
      case 'Var':
        return `#${term.index}`;
      case 'App':
        return `(${this.termToString(term.fn)} ${this.termToString(term.arg)})`;
      case 'Binder':
        return `(${term.name} : ${this.termToString(term.domain)}) -> ${this.termToString(term.body)}`;
      default:
        return `<${term.tag}>`;
    }
  }
}
