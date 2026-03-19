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

import { TTKTerm, TTKPattern, TTKContext } from '../compiler/kernel';
import { DefinitionsMap, createDefinitionsMap } from '../compiler/term';
import { MetaVar } from '../compiler/term';
import { TacticEngine } from './tacticsEngine';
import { Tactic, TacticResult, UnifiedEquation, freshMetaName } from './tactic';
import { inferType } from '../compiler/checker';
import { whnf, fullNormalize } from '../compiler/whnf';
import { shiftTerm, subst } from '../compiler/subst';

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
    public readonly options: { enhanced?: boolean; reverse?: boolean; occurrences?: number[]; targetHead?: string } = {}
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
      // Zonk to substitute solved metas into the type.
      // Use depth-aware zonking because ensurePi's normalize may beta-reduce
      // App(\z => f({?m}, z), ?a) → f({?m}, ?a), moving meta ?m from depth D+1
      // (inside the lambda) to depth D (outside). zonkTermAtDepth adjusts the
      // meta solution's de Bruijn indices for the depth change.
      const proofType = solvedEnv.zonkTermAtDepth(solvedEnv.value, goal.ctx.length);

      // 2. Normalize to find equality type
      const proofTypeWhnf = whnf(proofType, { definitions: engine.definitions, typingContext: goal.ctx });

      // 3. Check that it's an equality type and extract type param, LHS, and RHS.
      //    If the proof type is a Pi (function type like minusSucc : {i n} -> Leq i n -> Equal ...),
      //    instantiate all binders with Meta placeholders to reach the equality at the end.
      let proofTypeForExtraction = proofTypeWhnf;
      let instantiated: { body: TTKTerm; metaIds: string[]; premiseTypes: Map<string, TTKTerm> } | null = null;
      if (proofTypeWhnf.tag === 'Binder' && proofTypeWhnf.binderKind.tag === 'BPi') {
        instantiated = this.instantiatePis(proofTypeWhnf);
        if (instantiated) {
          proofTypeForExtraction = instantiated.body;
        }
      }

      let eqArgs = this.extractEqualityArgs(proofTypeForExtraction);
      if (!eqArgs) {
        return {
          success: false,
          error: `rewrite: argument must be an equality proof, got ${this.termToString(proofTypeWhnf)}`
        };
      }

      let { typeA, lhs: rawLhs, rhs: rawRhs } = eqArgs;

      // 3b. Premise-driven rewrite: when the conclusion equality has bare metas as
      //     both LHS and RHS (e.g., plusCancelLeft : {a b c} -> Equal(plus a b)(plus a c) -> Equal b c
      //     produces conclusion Equal Meta(?b) Meta(?c)), the pattern is too general to match
      //     anything useful. Instead, find the premise equality and use IT as the rewrite source.
      //     Match the premise equality against the goal equality to solve metas, then the
      //     new goal becomes the conclusion equality with metas substituted.
      let premiseDrivenRewrite: {
        premiseEq: { typeA: TTKTerm; lhs: TTKTerm; rhs: TTKTerm };
        conclusionLhs: TTKTerm;
        conclusionRhs: TTKTerm;
      } | null = null;
      if (instantiated && rawLhs.tag === 'Meta' && rawRhs.tag === 'Meta') {
        for (const [_metaId, premiseType] of instantiated.premiseTypes) {
          const premiseEq = this.extractEqualityArgs(premiseType);
          if (premiseEq) {
            premiseDrivenRewrite = {
              premiseEq,
              conclusionLhs: rawLhs,
              conclusionRhs: rawRhs,
            };
            break;
          }
        }
      }

      // For reverse rewrite (rewrite←), swap LHS and RHS so we replace RHS with LHS.
      if (this.options.reverse) {
        [rawLhs, rawRhs] = [rawRhs, rawLhs];
      }

      // 4. Beta-reduce LHS and RHS without delta-reducing definitions.
      //    cong (\z => radd z z) h produces Equal ((\z => radd z z) a) ((\z => radd z z) b)
      //    where the LHS/RHS are un-beta-reduced. We need radd(a,a) / radd(b,b) to match the goal,
      //    but NOT the delta-reduced CompleteOrderedField.add(field(R), a, a).
      let lhs = this.betaReduce(rawLhs);
      let rhs = this.betaReduce(rawRhs);

      // 4b. Deep-normalize the goal type using beta+iota only (no delta).
      //     This reduces motive applications (App(λx.body, arg) → body[x:=arg])
      //     and match expressions on known constructors, but does NOT unfold
      //     definitions like `plus` or `sum`. This is critical because:
      //     - After induction, goals are App(motive, ctor_pattern) which need beta-reducing
      //     - After unfold, goals have match redexes that need iota-reducing
      //     - Delta-reducing would expose internal match structures, making subterm
      //       matching impossible (e.g., plus(Succ(x), y) → match x with ...)
      const emptyDefs = createDefinitionsMap();
      const goalType = fullNormalize(goal.type, emptyDefs);

      // 4c. If LHS/RHS contain Meta placeholders (from Pi instantiation), try to
      //     match the LHS pattern against subterms of the goal to solve the Metas.
      //     We collect ALL matches and try each, because the first match may produce
      //     a no-op rewrite (e.g., mulComm on mul(x,x) → mul(x,x)).
      let allBindings: Map<string, TTKTerm> | null = null;
      const occurrences = this.options.occurrences;
      let newGoalType: TTKTerm = goalType;
      let foundNonTrivialRewrite = false;

      if (premiseDrivenRewrite && instantiated) {
        // Premise-driven rewrite: match premise equality against goal equality.
        // For plusCancelLeft: premise = Equal(plus ?a ?b)(plus ?a ?c), conclusion = Equal ?b ?c
        // Match premise LHS against goal's equality LHS, premise RHS against goal's equality RHS.
        // The new goal becomes the conclusion with metas solved.
        const goalEq = this.extractEqualityArgs(goalType);
        if (goalEq) {
          const bindings = new Map<string, TTKTerm>();
          const premLhs = this.betaReduce(premiseDrivenRewrite.premiseEq.lhs);
          const premRhs = this.betaReduce(premiseDrivenRewrite.premiseEq.rhs);
          const goalLhsBeta = this.betaReduce(goalEq.lhs);
          const goalRhsBeta = this.betaReduce(goalEq.rhs);

          // Try matching premise LHS against goal LHS, then premise RHS against goal RHS
          if (this.tryMatchPattern(premLhs, goalLhsBeta, bindings, engine.definitions) &&
              this.tryMatchPattern(premRhs, goalRhsBeta, bindings, engine.definitions)) {

            // Build the new goal: conclusion equality with metas solved
            const concLhs = this.applyMetaBindings(premiseDrivenRewrite.conclusionLhs, bindings);
            const concRhs = this.applyMetaBindings(premiseDrivenRewrite.conclusionRhs, bindings);
            const concTypeA = this.applyMetaBindings(premiseDrivenRewrite.premiseEq.typeA, bindings);

            newGoalType = {
              tag: 'App',
              fn: { tag: 'App', fn: { tag: 'App', fn: { tag: 'Const', name: 'Equal' }, arg: concTypeA }, arg: concLhs },
              arg: concRhs
            };

            // For the motive and proof term, use the premise equality sides
            lhs = this.applyMetaBindings(premLhs, bindings);
            rhs = this.applyMetaBindings(premRhs, bindings);
            typeA = concTypeA;
            allBindings = bindings;
            foundNonTrivialRewrite = !this.termEqual(goalType, newGoalType);
          }
        }
      } else if (instantiated) {
        let allMatches = this.findAllPatternMatches(goalType, lhs, engine.definitions);

        for (const bindings of allMatches) {
          if (bindings.size === 0) continue;

          // 4d. Search context for unsolved premise metas (like Lean's `assumption`)
          this.searchContextForPremises(
            instantiated.metaIds, bindings, instantiated.premiseTypes,
            goal.ctx, engine.definitions
          );

          const candidateLhs = this.applyMetaBindings(lhs, bindings);
          const candidateRhs = this.applyMetaBindings(rhs, bindings);

          // 4d-sanity. Reject matches with unsolved Metas in LHS or RHS.
          //   After Pi instantiation and pattern matching, unsolved Metas mean
          //   some Pi arguments couldn't be resolved (e.g., absOfNonneg needs
          //   {R : Real} which can't be found). Such rewrites are type-incorrect.
          if (this.containsMeta(candidateLhs) || this.containsMeta(candidateRhs)) {
            continue;
          }

          // 4e. When targetHead is specified (from clicking a specific subterm in the UI),
          //     only accept matches whose resolved LHS has the matching head constant.
          //     This prevents bare-Meta LHS (from reverse rewrites) from resolving to
          //     wrong subterms like Const("Nat") instead of the clicked Const("two").
          if (this.options.targetHead && occurrences && occurrences.length > 0) {
            const resolvedHead = this.getTermHeadName(candidateLhs);
            if (resolvedHead !== this.options.targetHead) continue;
          }

          // 5. Replace LHS with RHS in the goal type
          let candidateGoal = this.substitute(goalType, candidateLhs, candidateRhs, engine.definitions, occurrences);

          // 5-sanity. Reject pathological rewrites that change the goal's head.
          //   When LHS is a bare Meta (from reverse rewrite), pattern matching can
          //   resolve ?n to the entire goal, producing mul(Equal(...), one) instead
          //   of replacing a specific subterm. Reject rewrites that change the goal's
          //   outermost head constant (e.g., Equal → mul is nonsensical).
          if (!this.termEqual(goalType, candidateGoal)) {
            const goalHead = this.getTermHeadName(goalType);
            const newHead = this.getTermHeadName(candidateGoal);
            if (goalHead && newHead !== goalHead) {
              continue; // Skip this pathological match, try the next one
            }
          }

          // 5a. If no match, try delta-normalizing the LHS for simple aliases
          if (this.termEqual(goalType, candidateGoal)) {
            const normalizedLhs = this.shallowDeltaNormalize(candidateLhs, engine.definitions);
            if (!this.termEqual(candidateLhs, normalizedLhs)) {
              candidateGoal = this.substitute(goalType, normalizedLhs, candidateRhs, engine.definitions, occurrences);
              if (!this.termEqual(goalType, candidateGoal)) {
                lhs = normalizedLhs;
                rhs = candidateRhs;
                typeA = this.applyMetaBindings(typeA, bindings);
                allBindings = bindings;
                newGoalType = candidateGoal;
                foundNonTrivialRewrite = true;
                break;
              }
            }
          }

          if (!this.termEqual(goalType, candidateGoal)) {
            lhs = candidateLhs;
            rhs = candidateRhs;
            typeA = this.applyMetaBindings(typeA, bindings);
            allBindings = bindings;
            newGoalType = candidateGoal;
            foundNonTrivialRewrite = true;
            break;
          }
        }
      } else {
        // No Pi instantiation needed — direct substitute
        newGoalType = this.substitute(goalType, lhs, rhs, engine.definitions, occurrences);

        // 5a. Delta-normalize fallback
        if (this.termEqual(goalType, newGoalType)) {
          const normalizedLhs = this.shallowDeltaNormalize(lhs, engine.definitions);
          if (!this.termEqual(lhs, normalizedLhs)) {
            newGoalType = this.substitute(goalType, normalizedLhs, rhs, engine.definitions, occurrences);
            if (!this.termEqual(goalType, newGoalType)) {
              lhs = normalizedLhs;
            }
          }
        }

        if (!this.termEqual(goalType, newGoalType)) {
          foundNonTrivialRewrite = true;
        }
      }

      // 5b. Check if anything changed
      if (!foundNonTrivialRewrite) {
        return {
          success: false,
          error: `rewrite: no occurrences of ${this.termToString(lhs)} found in goal`
        };
      }

      // 6-8. Build the proof term
      const newMetaId = freshMetaName();
      const newMeta: MetaVar = {
        ctx: goal.ctx,
        type: newGoalType,
        solution: undefined
      };

      let proofTerm: TTKTerm;

      if (premiseDrivenRewrite && instantiated && allBindings) {
        // Premise-driven rewrite: the lemma takes the original goal as a premise
        // and produces the new goal as its conclusion.
        // Proof term: lemma {implicit_args...} ?premiseMeta
        // where ?premiseMeta : originalGoalType is solved by the original goal,
        // and the result has type newGoalType = Equal b c.
        //
        // Since the lemma goes original→new (not new→original), we can't use
        // replace. Instead, we record that the original goal is "consumed" by
        // the lemma application, and the new goal is what the user must prove
        // to complete the overall proof.
        //
        // We create a "premise meta" for the original goal type, and the lemma
        // applied to all args (including the premise meta) produces the new goal.
        const premiseMetaId = freshMetaName();
        const premiseMeta: MetaVar = {
          ctx: goal.ctx,
          type: goalType,  // The original goal type becomes the premise
          solution: undefined
        };

        // Build: lemma {a} {b} {c} ?premiseMeta
        let appliedProof: TTKTerm = this.equalityProof;
        for (const metaId of instantiated.metaIds) {
          const arg = allBindings.get(metaId) ?? { tag: 'Meta' as const, id: metaId };
          appliedProof = { tag: 'App', fn: appliedProof, arg };
        }

        // The proof term is the fully-applied lemma — its type is the new goal.
        // The old goal's solution references the premise meta which the user must prove.
        proofTerm = appliedProof;

        // The old goal is solved by the premise meta (the user proves the original goal
        // indirectly through the new goal). We swap: the user proves ?newGoal : newGoalType,
        // and the engine tracks that the lemma connects old→new.
        // For the engine, we set the old goal's solution to a Hole placeholder that
        // records the premise-driven connection.
        proofTerm = { tag: 'Hole', id: `_premise_driven_${this.termToString(this.equalityProof)}` };
      } else {
        // Standard rewrite: build replace-based proof term.
        //
        // 6. Build the motive: \z => goal.type[lhs := z]
        const shiftedGoal = shiftTerm(goalType, 1, 0);
        const shiftedLhs = shiftTerm(lhs, 1, 0);
        const motiveBody = this.substitute(shiftedGoal, shiftedLhs, { tag: 'Var', index: 0 }, engine.definitions, occurrences);
        const motive: TTKTerm = {
          tag: 'Binder',
          binderKind: { tag: 'BLam' },
          name: '_z',
          domain: typeA,
          body: motiveBody
        };

        // 8. Build the proof term: replace motive eqProof ?newGoal
        //    replace : {A} -> {x y : A} -> (P : A -> Type) -> Equal x y -> P x -> P y
        let appliedProof: TTKTerm = this.equalityProof;
        if (instantiated && allBindings) {
          for (const metaId of instantiated.metaIds) {
            const arg = allBindings.get(metaId) ?? { tag: 'Meta' as const, id: metaId };
            appliedProof = { tag: 'App', fn: appliedProof, arg };
          }
        }
        const eqProof: TTKTerm = this.options.reverse
          ? appliedProof
          : { tag: 'App', fn: { tag: 'Const', name: 'sym' }, arg: appliedProof };

        proofTerm = {
          tag: 'App',
          fn: {
            tag: 'App',
            fn: {
              tag: 'App',
              fn: { tag: 'Const', name: 'replace' },
              arg: motive
            },
            arg: eqProof
          },
          arg: { tag: 'Meta', id: newMetaId }
        };
      }

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
        }),
        unifiedEquation: { lhs, rhs } as UnifiedEquation,
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
   * Beta-reduce a term (repeatedly at the top level) without delta-reducing definitions.
   * Reduces App(Binder(BLam, ..., body), arg) → body[0 := arg].
   * This is needed because cong/sym produce un-beta-reduced terms like
   * App(\z => radd z z, h) which should match radd(h, h) in the goal.
   */
  private betaReduce(term: TTKTerm): TTKTerm {
    let current = term;
    // Repeat to handle nested beta-redexes
    for (let i = 0; i < 100; i++) {
      if (current.tag === 'App') {
        // Collect the application spine
        const args: TTKTerm[] = [];
        let head: TTKTerm = current;
        while (head.tag === 'App') {
          args.unshift(head.arg);
          head = head.fn;
        }
        // If head is a lambda, beta-reduce one step
        if (head.tag === 'Binder' && head.binderKind.tag === 'BLam' && args.length > 0) {
          const arg = args[0];
          let result = subst(0, arg, head.body);
          // Re-apply remaining args
          for (let j = 1; j < args.length; j++) {
            result = { tag: 'App', fn: result, arg: args[j] };
          }
          current = result;
          continue;
        }
      }
      break;
    }
    return current;
  }

  /**
   * Peel all Pi binders from a type, substituting Meta placeholders for each bound var.
   * Returns the instantiated body, the list of meta IDs created, and the domain types
   * for each meta (with prior metas already substituted in).
   * Used when the rewrite proof is a function (e.g., minusSucc : {i n} -> Leq i n -> Equal ...).
   */
  private instantiatePis(type: TTKTerm): { body: TTKTerm; metaIds: string[]; premiseTypes: Map<string, TTKTerm> } | null {
    const metaIds: string[] = [];
    const premiseTypes = new Map<string, TTKTerm>();
    let current = type;
    while (current.tag === 'Binder' && current.binderKind.tag === 'BPi') {
      const metaId = `_rewrite_arg_${metaIds.length}`;
      metaIds.push(metaId);
      // Record the domain type BEFORE substituting (it already has prior metas substituted
      // because we processed earlier binders)
      premiseTypes.set(metaId, current.domain);
      current = subst(0, { tag: 'Meta', id: metaId }, current.body);
    }
    if (metaIds.length === 0) return null;
    return { body: current, metaIds, premiseTypes };
  }

  /**
   * Find a subterm of `term` that matches the `pattern` (which may contain Metas).
   * Returns the Meta bindings if a match is found, null otherwise.
   */
  private findPatternMatch(
    term: TTKTerm,
    pattern: TTKTerm,
    definitions?: DefinitionsMap,
  ): Map<string, TTKTerm> | null {
    const all = this.findAllPatternMatches(term, pattern, definitions);
    return all.length > 0 ? all[0] : null;
  }

  /**
   * Find ALL pattern matches of `pattern` in `term`, returned in tree-traversal order.
   * Used to retry when the first match produces a no-op rewrite (e.g., mulComm on mul(x,x)).
   */
  private findAllPatternMatches(
    term: TTKTerm,
    pattern: TTKTerm,
    definitions?: DefinitionsMap,
  ): Map<string, TTKTerm>[] {
    const results: Map<string, TTKTerm>[] = [];

    // Try matching at this node
    const bindings = new Map<string, TTKTerm>();
    if (this.tryMatchPattern(pattern, term, bindings, definitions)) {
      results.push(bindings);
    }

    // Recurse into subterms
    switch (term.tag) {
      case 'App': {
        results.push(...this.findAllPatternMatches(term.fn, pattern, definitions));
        results.push(...this.findAllPatternMatches(term.arg, pattern, definitions));
        break;
      }
      case 'Binder': {
        results.push(...this.findAllPatternMatches(term.domain, pattern, definitions));
        // Don't recurse into binder body — pattern vars would have wrong indices
        break;
      }
      case 'Match': {
        results.push(...this.findAllPatternMatches(term.scrutinee, pattern, definitions));
        for (const clause of term.clauses) {
          results.push(...this.findAllPatternMatches(clause.rhs, pattern, definitions));
        }
        break;
      }
    }

    return results;
  }

  /**
   * Try to match a pattern (with Metas as wildcards) against a concrete term.
   * Records meta bindings in the `bindings` map.
   * Returns true if the match succeeds.
   */
  private tryMatchPattern(
    pattern: TTKTerm,
    term: TTKTerm,
    bindings: Map<string, TTKTerm>,
    definitions?: DefinitionsMap,
  ): boolean {
    // Meta in pattern matches anything
    if (pattern.tag === 'Meta') {
      const existing = bindings.get(pattern.id);
      if (existing) return this.termEqual(existing, term);
      bindings.set(pattern.id, term);
      return true;
    }

    // Try structural match first
    if (pattern.tag !== term.tag) {
      // If definitions available, try WHNF on both sides
      if (definitions) {
        const patN = whnf(pattern, { definitions });
        const termN = whnf(term, { definitions });
        if ((patN !== pattern || termN !== term) && patN.tag === termN.tag) {
          return this.tryMatchPattern(patN, termN, bindings, definitions);
        }
      }
      return false;
    }

    switch (pattern.tag) {
      case 'Var':
        return term.tag === 'Var' && pattern.index === term.index;
      case 'Const':
        return term.tag === 'Const' && pattern.name === term.name;
      case 'App':
        return term.tag === 'App' &&
          this.tryMatchPattern(pattern.fn, term.fn, bindings, definitions) &&
          this.tryMatchPattern(pattern.arg, term.arg, bindings, definitions);
      case 'Binder':
        return term.tag === 'Binder' &&
          pattern.binderKind.tag === term.binderKind.tag &&
          this.tryMatchPattern(pattern.domain, term.domain, bindings, definitions) &&
          this.tryMatchPattern(pattern.body, term.body, bindings, definitions);
      case 'Sort':
        return term.tag === 'Sort' && this.tryMatchPattern(pattern.level, term.level, bindings, definitions);
      case 'ULit':
        return term.tag === 'ULit' && pattern.n === term.n;
      case 'Hole':
        // Holes also act as wildcards
        bindings.set(pattern.id, term);
        return true;
      default:
        return this.termEqual(pattern, term);
    }
  }

  /**
   * Replace Meta placeholders in a term with their bound values.
   */
  private applyMetaBindings(term: TTKTerm, bindings: Map<string, TTKTerm>): TTKTerm {
    switch (term.tag) {
      case 'Meta': {
        const bound = bindings.get(term.id);
        return bound ?? term;
      }
      case 'App': {
        const fn = this.applyMetaBindings(term.fn, bindings);
        const arg = this.applyMetaBindings(term.arg, bindings);
        if (fn === term.fn && arg === term.arg) return term;
        return { tag: 'App', fn, arg };
      }
      case 'Binder': {
        const domain = this.applyMetaBindings(term.domain, bindings);
        const body = this.applyMetaBindings(term.body, bindings);
        if (domain === term.domain && body === term.body) return term;
        return { ...term, domain, body };
      }
      case 'Sort': {
        const level = this.applyMetaBindings(term.level, bindings);
        if (level === term.level) return term;
        return { tag: 'Sort', level };
      }
      default:
        return term;
    }
  }

  /**
   * Search the goal context for hypotheses matching unsolved premise types.
   * After pattern matching solves equality-pattern metas (like {i}, {n}),
   * premise metas (like Leq i n) may remain unsolved. This method searches
   * the context for matching hypotheses, similar to Lean's `assumption` tactic.
   */
  private searchContextForPremises(
    metaIds: string[],
    bindings: Map<string, TTKTerm>,
    premiseTypes: Map<string, TTKTerm>,
    goalCtx: TTKContext,
    definitions?: DefinitionsMap,
  ): void {
    for (const metaId of metaIds) {
      if (bindings.has(metaId)) continue; // already solved by pattern match

      const rawPremiseType = premiseTypes.get(metaId);
      if (!rawPremiseType) continue;

      // Apply current bindings to get concrete type (e.g., Leq Meta(?_0) Meta(?_1) → Leq i n)
      const concreteType = this.applyMetaBindings(rawPremiseType, bindings);

      // Search context backwards (most recent first)
      for (let i = goalCtx.length - 1; i >= 0; i--) {
        const entryType = goalCtx[i].type;
        if (this.termEqualModDefs(concreteType, entryType, definitions)) {
          const debruijnIdx = goalCtx.length - 1 - i;
          bindings.set(metaId, { tag: 'Var', index: debruijnIdx });
          break;
        }
      }
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

  /** Collect an App chain into head + args array. */
  private collectAppSpine(term: TTKTerm): { head: TTKTerm; args: TTKTerm[] } {
    const args: TTKTerm[] = [];
    let head = term;
    while (head.tag === 'App') {
      args.unshift(head.arg);
      head = head.fn;
    }
    return { head, args };
  }

  /** Look up implicit arg positions for a constant (from namedArgMap). */
  private getImplicitPositions(headName: string, definitions?: DefinitionsMap): Set<number> | null {
    if (!definitions) return null;
    const termDef = definitions.terms.get(headName);
    if (termDef?.namedArgMap && termDef.namedArgMap.size > 0) {
      return new Set(termDef.namedArgMap.values());
    }
    const indDef = definitions.inductiveTypes.get(headName);
    if (indDef?.namedArgMap && indDef.namedArgMap.size > 0) {
      return new Set(indDef.namedArgMap.values());
    }
    const indName = definitions.inductiveNameOfConstructor.get(headName);
    if (indName) {
      const parentInd = definitions.inductiveTypes.get(indName);
      if (parentInd) {
        const ctor = parentInd.constructors.find(c => c.name === headName);
        if (ctor?.namedArgMap && ctor.namedArgMap.size > 0) {
          return new Set(ctor.namedArgMap.values());
        }
      }
    }
    return null;
  }

  /** Get the head constant name of a term's App chain, or null. */
  private getTermHeadName(term: TTKTerm): string | null {
    let current = term;
    while (current.tag === 'App') current = current.fn;
    return current.tag === 'Const' ? current.name : null;
  }

  /** Check if a term contains any Meta nodes (unsolved Pi instantiation args). */
  private containsMeta(term: TTKTerm): boolean {
    switch (term.tag) {
      case 'Meta': return true;
      case 'App': return this.containsMeta(term.fn) || this.containsMeta(term.arg);
      case 'Binder': return this.containsMeta(term.domain) || this.containsMeta(term.body);
      case 'Match': return this.containsMeta(term.scrutinee) ||
        term.clauses.some(c => this.containsMeta(c.rhs));
      default: return false;
    }
  }

  /**
   * Substitute occurrences of `from` with `to` in `term`.
   * When `occurrences` is provided (1-based indices), only replaces at those positions.
   *
   * IMPORTANT: When occurrence-targeted, counting is by HEAD CONSTANT NAME
   * (matching the surface annotator's counting), not by full LHS match.
   * This ensures that surface occurrence N maps to the same subterm in the kernel.
   * For example, if the goal has mul(2,a) and mul(1,b) and the LHS is mul(1,?x),
   * both count as `mul` occurrences (1 and 2), even though only mul(1,b) matches.
   */
  private substitute(
    term: TTKTerm, from: TTKTerm, to: TTKTerm,
    definitions?: DefinitionsMap, occurrences?: number[],
  ): TTKTerm {
    const counter = { value: 0 };
    // Only use head-based counting when `from` is an App — bare Consts/Vars
    // don't form App spines, so head-based counting would skip them entirely
    const lhsHead = (occurrences && occurrences.length > 0 && from.tag === 'App')
      ? this.getTermHeadName(from)
      : null;
    return this.substituteImpl(term, from, to, definitions, occurrences, counter, lhsHead);
  }

  private substituteImpl(
    term: TTKTerm, from: TTKTerm, to: TTKTerm,
    definitions: DefinitionsMap | undefined, occurrences: number[] | undefined,
    counter: { value: number },
    lhsHead: string | null,
  ): TTKTerm {
    // When occurrence-targeted with a head constant, use head-based counting.
    // This counts ALL Apps with the same head as the LHS (matching the surface
    // annotator), not just full LHS matches.
    //
    // IMPORTANT: Uses POST-ORDER counting (children before parent) to match the
    // surface annotator, which assigns occurrence indices bottom-up during rendering
    // (children are rendered/annotated before parents in ttermToMathNodes).
    if (lhsHead && occurrences && term.tag === 'App') {
      const termHead = this.getTermHeadName(term);
      if (termHead === lhsHead) {
        // Post-order: first recurse into children
        const recursedTerm = this.substituteIntoAppArgs(term, from, to, definitions, occurrences, counter, lhsHead);
        // Then count this node
        counter.value++;
        if (occurrences.includes(counter.value)) {
          // This is the targeted occurrence — try the full match on ORIGINAL term
          const isMatch = this.options.enhanced && definitions
            ? this.termEqualDeep(term, from, definitions)
            : this.termEqual(term, from);
          if (isMatch) {
            return to;
          }
          // Head matches but LHS doesn't fully match — return recursed version
          return recursedTerm;
        }
        // Not a targeted occurrence — return recursed version
        return recursedTerm;
      }
    }

    // If term matches from, replace with to (respecting occurrence filter)
    // In enhanced mode (erw), use recursive deep definitional equality.
    // In normal mode, use structural equality only — WHNF comparison is too aggressive
    // because unrelated subterms may be definitionally equal to the LHS
    // (e.g., mul(2, sumStartCount(0,1,id)) WHNF≡ sumStartCount(0,1,id) ≡ Zero)
    if (!lhsHead) {
      const isMatch = this.options.enhanced && definitions
        ? this.termEqualDeep(term, from, definitions)
        : this.termEqual(term, from);
      if (isMatch) {
        counter.value++;
        if (!occurrences || occurrences.includes(counter.value)) {
          return to;
        }
        return term;  // Skip this occurrence
      }
    }

    // In enhanced mode, WHNF the term to expose hidden subterms.
    // E.g., `rsub R a (rzero R)` WHNF's to `radd R a (rneg R (rzero R))`,
    // exposing `rneg R (rzero R)` which can then be matched and replaced.
    // Only attempt when the App head is a defined constant (δ-reduction target),
    // and only recurse if WHNF actually changes the head (prevents infinite loop
    // since whnf always creates new App objects even when nothing reduces).
    // IMPORTANT: Only keep the WHNF'd result if a substitution actually occurred
    // within it (detected via reference identity). Otherwise, fall through to the
    // normal recursive descent on the original term to preserve its structural form
    // for subsequent rewrite steps.
    if (this.options.enhanced && definitions && term.tag === 'App') {
      let head: TTKTerm = term;
      while (head.tag === 'App') head = head.fn;
      if (head.tag === 'Const') {
        const termN = whnf(term, { definitions });
        let headN: TTKTerm = termN;
        while (headN.tag === 'App') headN = headN.fn;
        if (headN.tag !== 'Const' || headN.name !== head.name) {
          const result = this.substituteImpl(termN, from, to, definitions, occurrences, counter, lhsHead);
          if (result !== termN) {
            // A substitution occurred in the WHNF'd form — use it
            return result;
          }
          // No substitution in WHNF'd form — fall through to preserve original structure
        }
      }
    }

    // Recursively substitute in subterms, preserving reference identity when nothing changes
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
        return this.substituteIntoAppArgs(term, from, to, definitions, occurrences, counter, lhsHead);

      case 'Binder': {
        const newDomain = this.substituteImpl(term.domain, from, to, definitions, occurrences, counter, lhsHead);
        const newBody = this.substituteImpl(term.body, from, to, definitions, occurrences, counter, lhsHead);
        if (newDomain === term.domain && newBody === term.body) return term;
        return {
          tag: 'Binder',
          binderKind: term.binderKind,
          name: term.name,
          domain: newDomain,
          body: newBody
        };
      }

      default:
        return term;
    }
  }

  /**
   * Recurse into an App's arguments for substitution.
   * When occurrence-targeted, skips implicit arg subtrees to match surface counting.
   */
  private substituteIntoAppArgs(
    term: TTKTerm, from: TTKTerm, to: TTKTerm,
    definitions: DefinitionsMap | undefined, occurrences: number[] | undefined,
    counter: { value: number }, lhsHead: string | null,
  ): TTKTerm {
    // When lhsHead is set (occurrence-targeted with head-based counting),
    // we MUST collect the App spine and recurse only into args, NOT the fn chain.
    // Otherwise, App(App(Const("mul"), a), b) would recurse into fn=App(Const("mul"), a),
    // which is also a mul-headed App, causing double-counting.
    if (lhsHead && occurrences && occurrences.length > 0) {
      const { head, args } = this.collectAppSpine(term);
      const implicitPositions = (head.tag === 'Const' && definitions)
        ? this.getImplicitPositions(head.name, definitions)
        : null;
      let changed = false;
      const newArgs = args.map((arg, i) => {
        if (implicitPositions && implicitPositions.has(i)) return arg; // skip implicit subtrees
        const newArg = this.substituteImpl(arg, from, to, definitions, occurrences, counter, lhsHead);
        if (newArg !== arg) changed = true;
        return newArg;
      });
      if (!changed) return term;
      let result: TTKTerm = head;
      for (const arg of newArgs) {
        result = { tag: 'App', fn: result, arg };
      }
      return result;
    }
    // Untargeted — use original recursive descent
    if (term.tag !== 'App') return term;
    const newFn = this.substituteImpl(term.fn, from, to, definitions, occurrences, counter, lhsHead);
    const newArg = this.substituteImpl(term.arg, from, to, definitions, occurrences, counter, lhsHead);
    if (newFn === term.fn && newArg === term.arg) return term;
    return { tag: 'App', fn: newFn, arg: newArg };
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
          if (clause.patterns.length !== other.patterns.length) return false;
          if (!this.patternsEqual(clause.patterns, other.patterns)) return false;
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
          if (!this.patternsEqual(clause.patterns, other.patterns)) return false;
          return this.termEqual(clause.rhs, other.rhs);
        });

      default:
        return false;
    }
  }

  /**
   * Shallow delta-normalize: expand simple (non-recursive) definitions throughout a term
   * so that aliases like `one` → `Succ(Zero)` are resolved. Does NOT expand functions
   * defined by pattern matching (whose values contain Match), preserving structure.
   */
  private shallowDeltaNormalize(term: TTKTerm, definitions: DefinitionsMap): TTKTerm {
    switch (term.tag) {
      case 'Const': {
        const def = definitions.terms.get(term.name);
        if (def?.value && !this.containsMatch(def.value)) {
          return this.shallowDeltaNormalize(def.value, definitions);
        }
        return term;
      }
      case 'App': {
        const newFn = this.shallowDeltaNormalize(term.fn, definitions);
        const newArg = this.shallowDeltaNormalize(term.arg, definitions);
        if (newFn === term.fn && newArg === term.arg) return term;
        return { tag: 'App', fn: newFn, arg: newArg };
      }
      case 'Binder': {
        const newDomain = this.shallowDeltaNormalize(term.domain, definitions);
        const newBody = this.shallowDeltaNormalize(term.body, definitions);
        if (newDomain === term.domain && newBody === term.body) return term;
        return { ...term, domain: newDomain, body: newBody };
      }
      default:
        return term;
    }
  }

  /** Check if a term contains a Match node (indicating a pattern-matching definition). */
  private containsMatch(term: TTKTerm): boolean {
    switch (term.tag) {
      case 'Match': return true;
      case 'App': return this.containsMatch(term.fn) || this.containsMatch(term.arg);
      case 'Binder': return this.containsMatch(term.domain) || this.containsMatch(term.body);
      default: return false;
    }
  }

  /**
   * Check if two pattern lists are structurally equal.
   * Compares tag, name (for PCtor), and recursively for PCtor args.
   */
  private patternsEqual(ps1: TTKPattern[], ps2: TTKPattern[]): boolean {
    if (ps1.length !== ps2.length) return false;
    return ps1.every((p, i) => this.patternEqual(p, ps2[i]));
  }

  private patternEqual(p1: TTKPattern, p2: TTKPattern): boolean {
    if (p1.tag !== p2.tag) return false;
    if (p1.tag === 'PCtor' && p2.tag === 'PCtor') {
      return p1.name === p2.name && this.patternsEqual(p1.args, p2.args);
    }
    // PVar and PWild: just tag match is enough
    return true;
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
        if (term.binderKind.tag === 'BLam') {
          return `(\\${term.name} => ${this.termToString(term.body)})`;
        }
        return `(${term.name} : ${this.termToString(term.domain)}) -> ${this.termToString(term.body)}`;
      default:
        return `<${term.tag}>`;
    }
  }
}
