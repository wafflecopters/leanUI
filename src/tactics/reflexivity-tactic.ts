/**
 * Reflexivity Tactic: Prove equality goals of the form a = a
 *
 * Usage: reflexivity
 * Example goal: Equal n n
 * Applies: refl
 */

import { TTKTerm, TTKPattern } from '../compiler/kernel';
import { MetaVar, DefinitionsMap } from '../compiler/term';
import { TacticEngine } from './tacticsEngine';
import { Tactic, TacticResult } from './tactic';
import { whnf } from '../compiler/whnf';
import { ExactTactic } from './tactic';

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

      // Check if they're definitionally equal (recursive WHNF + structural comparison)
      if (!this.defEqual(lhs, rhs, engine.definitions)) {
        const lhsWhnf = whnf(lhs, { definitions: engine.definitions });
        const rhsWhnf = whnf(rhs, { definitions: engine.definitions });
        return {
          success: false,
          error: `reflexivity: sides are not definitionally equal\n  LHS: ${this.termToString(lhsWhnf)}\n  RHS: ${this.termToString(rhsWhnf)}`
        };
      }

      // Delegate actual proof construction to ExactTactic so reflexivity
      // relies on the kernel checker/inference path instead of installing
      // a bare `refl` term by hand.
      return new ExactTactic({ tag: 'Const', name: 'refl' }).apply(engine, goal, goalId);
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
   * Check if two terms are definitionally equal (structurally identical after WHNF)
   */
  private defEqual(a: TTKTerm, b: TTKTerm, definitions?: DefinitionsMap, depth: number = 0): boolean {
    if (depth > 50) return false;
    if (a === b) return true;

    // Normalize both sides to WHNF
    const aN = definitions ? whnf(a, { definitions }) : a;
    const bN = definitions ? whnf(b, { definitions }) : b;

    if (aN === bN) return true;
    if (aN.tag !== bN.tag) return false;

    // Structural comparison of WHNF forms
    // Recursive calls use defEqual (which will WHNF subterms)
    switch (aN.tag) {
      case 'Var':
        return bN.tag === 'Var' && aN.index === bN.index;

      case 'Const':
        return bN.tag === 'Const' && aN.name === bN.name;

      case 'App':
        return bN.tag === 'App' &&
               this.defEqual(aN.fn, (bN as any).fn, definitions, depth + 1) &&
               this.defEqual(aN.arg, (bN as any).arg, definitions, depth + 1);

      case 'Binder':
        return bN.tag === 'Binder' &&
               aN.binderKind.tag === (bN as any).binderKind.tag &&
               this.defEqual(aN.domain, (bN as any).domain, definitions, depth + 1) &&
               this.defEqual(aN.body, (bN as any).body, definitions, depth + 1);

      case 'Sort':
        return bN.tag === 'Sort' && this.defEqual(aN.level, (bN as any).level, definitions, depth + 1);

      case 'Match':
        if (bN.tag !== 'Match') return false;
        if (aN.clauses.length !== bN.clauses.length) return false;
        // For stuck Match terms (after WHNF), compare scrutinee and clauses structurally
        // Don't re-WHNF scrutinee (it's already stuck), use undefined definitions
        if (!this.defEqual(aN.scrutinee, bN.scrutinee, definitions, depth + 1)) return false;
        return aN.clauses.every((c, i) =>
          this.patternsEqual(c.patterns, bN.clauses[i].patterns) &&
          this.defEqual(c.rhs, bN.clauses[i].rhs, undefined, depth + 1)
        );

      case 'Annot':
        return bN.tag === 'Annot' &&
               this.defEqual(aN.term, (bN as any).term, definitions, depth + 1);

      case 'ULit':
        return bN.tag === 'ULit' && aN.n === bN.n;

      case 'ULevel':
        return bN.tag === 'ULevel';

      case 'UOmega':
        return bN.tag === 'UOmega';

      case 'Meta':
        return bN.tag === 'Meta' && aN.id === bN.id;

      case 'Hole':
        return bN.tag === 'Hole' && aN.id === bN.id;

      default:
        return false;
    }
  }

  /**
   * Check if two pattern lists are structurally equal
   */
  private patternsEqual(a: TTKPattern[], b: TTKPattern[]): boolean {
    if (a.length !== b.length) return false;
    return a.every((p, i) => this.patternEqual(p, b[i]));
  }

  private patternEqual(a: TTKPattern, b: TTKPattern): boolean {
    if (a.tag !== b.tag) return false;
    switch (a.tag) {
      case 'PVar':
      case 'PWild':
        return true;
      case 'PCtor':
        return b.tag === 'PCtor' && a.name === b.name && this.patternsEqual(a.args, b.args);
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
