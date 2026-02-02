/**
 * Rewrite Tactic: Replace terms using equality proofs
 *
 * Given an equality proof `h : Equal a b`, rewrite `h` in the goal
 * replaces occurrences of `a` with `b`.
 *
 * Usage: rewrite h
 * Example:
 *   h : Equal (plus n Zero) n
 *   goal : Equal (plus (plus n Zero) m) (plus n m)
 *   After rewrite h: goal becomes Equal (plus n m) (plus n m)
 */

import { TTKTerm, TTKContext } from '../compiler/kernel';
import { MetaVar, DefinitionsMap } from '../compiler/term';
import { TacticEngine } from './tacticsEngine';
import { Tactic, TacticResult } from './tactic';
import { inferType } from '../compiler/checker';
import { whnf } from '../compiler/whnf';

/**
 * RewriteTactic: Use an equality proof to substitute in the goal
 *
 * Basic implementation: syntactic replacement of LHS with RHS
 */
export class RewriteTactic implements Tactic {
  name = 'rewrite';

  constructor(public readonly equalityProof: TTKTerm) {}

  apply(engine: TacticEngine, goal: MetaVar, goalId: string): TacticResult {
    try {
      // 1. Infer type of the equality proof
      const env = engine.toTCEnv(goal, this.equalityProof);
      const inferredEnv = inferType(env);
      const proofType = inferredEnv.value;

      // 2. Normalize to find equality type
      const proofTypeWhnf = whnf(proofType, { definitions: engine.definitions });

      // 3. Check that it's an equality type and extract LHS and RHS
      const { lhs, rhs } = this.extractEqualityArgs(proofTypeWhnf);
      if (!lhs || !rhs) {
        return {
          success: false,
          error: `rewrite: argument must be an equality proof, got ${this.termToString(proofTypeWhnf)}`
        };
      }

      // 4. Replace LHS with RHS in the goal type
      const newGoalType = this.substitute(goal.type, lhs, rhs);

      // 5. Check if anything changed
      if (this.defEqual(goal.type, newGoalType)) {
        return {
          success: false,
          error: `rewrite: no occurrences of ${this.termToString(lhs)} found in goal`
        };
      }

      // 6. Create a new meta for the transformed goal
      const newMeta: MetaVar = {
        ctx: goal.ctx,
        type: newGoalType,
        solution: undefined
      };

      // 7. Build the proof term using transport/subst
      // For now, we use a placeholder that will need to be elaborated
      // In a full implementation, this would construct:
      //   subst equalityProof newMetaProof
      const proofTerm: TTKTerm = {
        tag: 'Meta',
        id: goalId + '_rewrite'
      };

      // 8. Update engine state
      const newMetaVars = new Map(engine.metaVars);
      newMetaVars.set(goalId, { ...goal, solution: proofTerm });
      newMetaVars.set(goalId + '_rewrite', newMeta);

      // Replace current goal with new goal
      const newGoals = engine.goals.map(g => g === goalId ? goalId + '_rewrite' : g);

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
        error: `rewrite: ${errorMsg}`,
        cause: e instanceof Error ? e : undefined
      };
    }
  }

  /**
   * Extract LHS and RHS from an equality type
   * Equal is typically: (Equal A) lhs rhs or ((Equal A) lhs) rhs
   */
  private extractEqualityArgs(type: TTKTerm): { lhs: TTKTerm | null; rhs: TTKTerm | null } {
    if (type.tag !== 'App') {
      return { lhs: null, rhs: null };
    }

    // Walk backwards through application spine
    const args: TTKTerm[] = [];
    let current: TTKTerm = type;
    while (current.tag === 'App') {
      args.unshift(current.arg);
      current = current.fn;
    }

    // Check that head is Equal (or const resolving to Equal)
    if (current.tag !== 'Const' || current.name !== 'Equal') {
      return { lhs: null, rhs: null };
    }

    // Need at least 2 args (lhs and rhs); may have type arg
    if (args.length < 2) {
      return { lhs: null, rhs: null };
    }

    const rhs = args[args.length - 1];
    const lhs = args[args.length - 2];

    return { lhs, rhs };
  }

  /**
   * Substitute all occurrences of `from` with `to` in `term`
   */
  private substitute(term: TTKTerm, from: TTKTerm, to: TTKTerm): TTKTerm {
    // If term matches from, replace with to
    if (this.defEqual(term, from)) {
      return to;
    }

    // Recursively substitute in subterms
    switch (term.tag) {
      case 'Var':
      case 'Const':
      case 'Meta':
      case 'Hole':
      case 'Sort':
      case 'ULevel':
      case 'ULit':
      case 'UOmega':
        return term;

      case 'App':
        return {
          tag: 'App',
          fn: this.substitute(term.fn, from, to),
          arg: this.substitute(term.arg, from, to)
        };

      case 'Binder':
        return {
          tag: 'Binder',
          binderKind: term.binderKind,
          name: term.name,
          domain: this.substitute(term.domain, from, to),
          body: this.substitute(term.body, from, to)
        };

      default:
        return term;
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
