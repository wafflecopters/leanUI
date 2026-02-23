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
import { DefinitionsMap } from '../compiler/term';
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

  constructor(
    public readonly equalityProof: TTKTerm,
    public readonly options: { enhanced?: boolean } = {}
  ) {}

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
      const proofTypeWhnf = whnf(proofType, { definitions: engine.definitions, typingContext: goal.ctx });

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
      //    Uses WHNF-based matching to handle definition aliases
      //    (e.g., `radd R` matching `CompleteOrderedField.add (field R)`)
      const newGoalType = this.substitute(goal.type, lhs, rhs, engine.definitions);

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
      const motiveBody = this.substitute(shiftedGoal, shiftedLhs, { tag: 'Var', index: 0 }, engine.definitions);
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
   * Substitute all occurrences of `from` with `to` in `term`.
   * Uses WHNF-based matching when definitions are provided, so that
   * definition aliases (like `radd R` vs `CompleteOrderedField.add (field R)`)
   * are treated as equal.
   */
  private substitute(term: TTKTerm, from: TTKTerm, to: TTKTerm, definitions?: DefinitionsMap): TTKTerm {
    // If term matches from, replace with to
    // In enhanced mode (erw), use recursive deep definitional equality
    const isMatch = this.options.enhanced && definitions
      ? this.termEqualDeep(term, from, definitions)
      : this.termEqualModDefs(term, from, definitions);
    if (isMatch) {
      return to;
    }

    // In enhanced mode, WHNF the term to expose hidden subterms.
    // E.g., `rsub R a (rzero R)` WHNF's to `radd R a (rneg R (rzero R))`,
    // exposing `rneg R (rzero R)` which can then be matched and replaced.
    // Only attempt when the App head is a defined constant (δ-reduction target),
    // and only recurse if WHNF actually changes the head (prevents infinite loop
    // since whnf always creates new App objects even when nothing reduces).
    if (this.options.enhanced && definitions && term.tag === 'App') {
      let head: TTKTerm = term;
      while (head.tag === 'App') head = head.fn;
      if (head.tag === 'Const') {
        const termN = whnf(term, { definitions });
        let headN: TTKTerm = termN;
        while (headN.tag === 'App') headN = headN.fn;
        if (headN.tag !== 'Const' || headN.name !== head.name) {
          return this.substitute(termN, from, to, definitions);
        }
      }
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
          fn: this.substitute(term.fn, from, to, definitions),
          arg: this.substitute(term.arg, from, to, definitions)
        };

      case 'Binder':
        return {
          tag: 'Binder',
          binderKind: term.binderKind,
          name: term.name,
          domain: this.substitute(term.domain, from, to, definitions),
          body: this.substitute(term.body, from, to, definitions)
        };

      default:
        return term;
    }
  }

  /**
   * Check if two terms are definitionally equal (modulo definition unfolding).
   * First tries structural equality (fast path), then falls back to
   * WHNF comparison when definitions are available.
   */
  private termEqualModDefs(a: TTKTerm, b: TTKTerm, definitions?: DefinitionsMap): boolean {
    // Fast path: structural equality
    if (this.termEqual(a, b)) return true;

    // Slow path: WHNF both sides and compare structurally
    if (definitions) {
      const aN = whnf(a, { definitions });
      const bN = whnf(b, { definitions });
      // Only retry if WHNF actually changed something
      if (aN !== a || bN !== b) {
        return this.termEqual(aN, bN);
      }
    }
    return false;
  }

  /**
   * Deep definitional equality: WHNF at every level, then recursively compare.
   * Used by `erw` to handle nested aliases like `rzero R` vs
   * `CompleteOrderedField.zero (Carrier R) (field R)`.
   */
  private termEqualDeep(a: TTKTerm, b: TTKTerm, definitions: DefinitionsMap, depth: number = 0): boolean {
    // Prevent infinite recursion
    if (depth > 100) return false;

    // Fast path: structural equality
    if (this.termEqual(a, b)) return true;

    // WHNF both sides
    const aN = whnf(a, { definitions });
    const bN = whnf(b, { definitions });

    // Check structural equality after WHNF
    if (this.termEqual(aN, bN)) return true;

    // Recursive comparison on WHNF'd terms
    if (aN.tag !== bN.tag) return false;

    switch (aN.tag) {
      case 'Var':
        return bN.tag === 'Var' && aN.index === bN.index;
      case 'Const':
        return bN.tag === 'Const' && aN.name === bN.name;
      case 'App':
        return bN.tag === 'App' &&
               this.termEqualDeep(aN.fn, (bN as any).fn, definitions, depth + 1) &&
               this.termEqualDeep(aN.arg, (bN as any).arg, definitions, depth + 1);
      case 'Binder':
        return bN.tag === 'Binder' &&
               aN.binderKind.tag === (bN as any).binderKind.tag &&
               this.termEqualDeep(aN.domain, (bN as any).domain, definitions, depth + 1) &&
               this.termEqualDeep(aN.body, (bN as any).body, definitions, depth + 1);
      case 'Sort':
        return bN.tag === 'Sort' && this.termEqualDeep(aN.level, (bN as any).level, definitions, depth + 1);
      case 'Meta':
        return bN.tag === 'Meta' && aN.id === (bN as any).id;
      case 'Hole':
        return bN.tag === 'Hole' && aN.id === (bN as any).id;
      case 'ULit':
        return bN.tag === 'ULit' && aN.n === (bN as any).n;
      case 'ULevel':
        return bN.tag === 'ULevel';
      case 'UOmega':
        return bN.tag === 'UOmega';
      case 'Match':
        if (bN.tag !== 'Match') return false;
        if (!this.termEqualDeep(aN.scrutinee, (bN as any).scrutinee, definitions, depth + 1)) return false;
        if (aN.clauses.length !== (bN as any).clauses.length) return false;
        return aN.clauses.every((clause, i) => {
          const other = (bN as any).clauses[i];
          return this.termEqualDeep(clause.rhs, other.rhs, definitions, depth + 1);
        });
      default:
        return false;
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

      case 'Match':
        if (b.tag !== 'Match') return false;
        if (!this.termEqual(a.scrutinee, b.scrutinee)) return false;
        if (a.clauses.length !== b.clauses.length) return false;
        return a.clauses.every((clause, i) => {
          const other = b.tag === 'Match' ? b.clauses[i] : undefined;
          if (!other) return false;
          if (clause.patterns.length !== other.patterns.length) return false;
          return this.termEqual(clause.rhs, other.rhs);
        });

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
