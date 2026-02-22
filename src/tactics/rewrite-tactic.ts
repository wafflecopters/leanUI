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
 *
 * Proof term: replace (\z => goal[lhs := z]) (sym h) ?newGoal
 * where ?newGoal has type goal[lhs := rhs]
 */

import { TTKTerm } from '../compiler/kernel';
import { MetaVar } from '../compiler/term';
import { TacticEngine } from './tacticsEngine';
import { Tactic, TacticResult, freshMetaName } from './tactic';
import { inferType } from '../compiler/checker';
import { whnf } from '../compiler/whnf';
import { shiftTerm } from '../compiler/subst';

/**
 * RewriteTactic: Use an equality proof to substitute in the goal
 *
 * Given h : Equal lhs rhs, transforms goal G[lhs] into G[rhs].
 * Builds proof term: replace P (sym h) ?newGoal
 * where P = \z => G[lhs := z] (the motive).
 */
export class RewriteTactic implements Tactic {
  name = 'rewrite';

  constructor(public readonly equalityProof: TTKTerm) {}

  apply(engine: TacticEngine, goal: MetaVar, goalId: string): TacticResult {
    try {
      // 1. Infer type of the equality proof
      const env = engine.toTCEnv(goal, this.equalityProof);
      const inferredEnv = inferType(env);
      // Solve constraints to resolve implicit argument metas (e.g., for `sym h`)
      let solvedEnv = inferredEnv;
      try {
        solvedEnv = inferredEnv.solveMetasAndConstraints({ liftMetasToFullContext: false });
      } catch {
        // Best effort — proceed with what we have
      }
      // Zonk to substitute solved metas into the type
      const proofType = solvedEnv.zonkTerm(solvedEnv.value);

      // 2. Normalize to find equality type
      const proofTypeWhnf = whnf(proofType, { definitions: engine.definitions });

      // 3. Check that it's an equality type and extract type param, LHS, and RHS
      const eqArgs = this.extractEqualityArgs(proofTypeWhnf);
      if (!eqArgs) {
        return {
          success: false,
          error: `rewrite: argument must be an equality proof, got ${this.termToString(proofTypeWhnf)}`
        };
      }

      const { typeA, lhs, rhs } = eqArgs;

      // 4. Replace LHS with RHS in the goal type
      const newGoalType = this.substitute(goal.type, lhs, rhs);

      // 5. Check if anything changed
      if (this.termEqual(goal.type, newGoalType)) {
        return {
          success: false,
          error: `rewrite: no occurrences of ${this.termToString(lhs)} found in goal`
        };
      }

      // 6. Build the motive: \z => goal.type[lhs := z]
      //    Shift goal type and lhs into the lambda body scope (depth +1),
      //    then replace shifted lhs with Var(0).
      const shiftedGoal = shiftTerm(goal.type, 1, 0);
      const shiftedLhs = shiftTerm(lhs, 1, 0);
      const motiveBody = this.substitute(shiftedGoal, shiftedLhs, { tag: 'Var', index: 0 });
      const motive: TTKTerm = {
        tag: 'Binder',
        binderKind: { tag: 'BLam' },
        name: '_z',
        domain: typeA,
        body: motiveBody
      };

      // 7. Create a new meta for the transformed goal
      const newMetaId = freshMetaName();
      const newMeta: MetaVar = {
        ctx: goal.ctx,
        type: newGoalType,
        solution: undefined
      };

      // 8. Build the proof term: replace motive (sym h) ?newGoal
      //    replace : {A} -> {x y : A} -> (P : A -> Type) -> Equal x y -> P x -> P y
      //    We need: P lhs (original goal) from P rhs (new goal)
      //    sym h : Equal rhs lhs, so replace P (sym h) : P rhs -> P lhs
      const symProof: TTKTerm = {
        tag: 'App',
        fn: { tag: 'Const', name: 'sym' },
        arg: this.equalityProof
      };

      // replace motive (sym h) ?newGoal
      const proofTerm: TTKTerm = {
        tag: 'App',
        fn: {
          tag: 'App',
          fn: {
            tag: 'App',
            fn: { tag: 'Const', name: 'replace' },
            arg: motive
          },
          arg: symProof
        },
        arg: { tag: 'Meta', id: newMetaId }
      };

      // 9. Update engine state
      const newMetaVars = new Map(engine.metaVars);
      newMetaVars.set(goalId, { ...goal, solution: proofTerm });
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
      const errorMsg = e instanceof Error
        ? e.message
        : (e && typeof e === 'object' && 'message' in e)
          ? String((e as any).message)
          : String(e);
      return {
        success: false,
        error: `rewrite: ${errorMsg}`,
        cause: e instanceof Error ? e : undefined
      };
    }
  }

  /**
   * Extract type param, LHS and RHS from an equality type
   * Equal is typically: (Equal A) lhs rhs or ((Equal A) lhs) rhs
   */
  private extractEqualityArgs(type: TTKTerm): { typeA: TTKTerm; lhs: TTKTerm; rhs: TTKTerm } | null {
    if (type.tag !== 'App') {
      return null;
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
      return null;
    }

    // Need at least 2 args (lhs and rhs); may have type arg
    if (args.length < 2) {
      return null;
    }

    const rhs = args[args.length - 1];
    const lhs = args[args.length - 2];
    // Type arg is the first arg (if present), otherwise use a Hole
    const typeA = args.length >= 3
      ? args[args.length - 3]
      : { tag: 'Hole' as const, id: '_rewrite_type' };

    return { typeA, lhs, rhs };
  }

  /**
   * Substitute all occurrences of `from` with `to` in `term`
   */
  private substitute(term: TTKTerm, from: TTKTerm, to: TTKTerm): TTKTerm {
    // If term matches from, replace with to
    if (this.termEqual(term, from)) {
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
   * Check if two terms are structurally equal
   */
  private termEqual(a: TTKTerm, b: TTKTerm): boolean {
    if (a.tag !== b.tag) return false;

    switch (a.tag) {
      case 'Var':
        return b.tag === 'Var' && a.index === b.index;

      case 'Const':
        return b.tag === 'Const' && a.name === b.name;

      case 'App':
        return b.tag === 'App' &&
               this.termEqual(a.fn, b.fn) &&
               this.termEqual(a.arg, b.arg);

      case 'Binder':
        return b.tag === 'Binder' &&
               a.binderKind.tag === b.binderKind.tag &&
               this.termEqual(a.domain, b.domain) &&
               this.termEqual(a.body, b.body);

      case 'Sort':
        return b.tag === 'Sort' && this.termEqual(a.level, b.level);

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
