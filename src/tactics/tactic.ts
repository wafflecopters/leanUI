/**
 * Tactic Interface and Core Tactics
 *
 * A tactic is a proof state transformation: it takes a TacticEngine and a goal,
 * and returns a new TacticEngine with the goal solved or refined into subgoals.
 */

import { TTKTerm } from '../compiler/kernel';
import { MetaVar, createNamedArgLookup, extractAppSpine } from '../compiler/term';
import { TacticEngine } from './tacticsEngine';
import { whnf, areTypesDefEq } from '../compiler/whnf';
import type { DefinitionsMap } from '../compiler/term';

// Memoize the "definitions minus record projections" map per definitions
// instance. Used by ApplyTactic's spine-shape fallback to whnf with
// projection unfolding disabled. Recomputing per-candidate (called 100×
// during suggestion iteration) was a major slowdown.
const __reducedDefsCache = new WeakMap<DefinitionsMap, DefinitionsMap>();
function getReducedDefs(definitions: DefinitionsMap): DefinitionsMap {
  const cached = __reducedDefsCache.get(definitions);
  if (cached) return cached;
  const projections = new Set<string>();
  for (const [, ind] of definitions.inductiveTypes) {
    if (ind.recordInfo) for (const p of ind.recordInfo.projections) projections.add(p);
  }
  const reducedTerms = new Map(definitions.terms);
  for (const p of projections) reducedTerms.delete(p);
  const reduced = { ...definitions, terms: reducedTerms };
  __reducedDefsCache.set(definitions, reduced);
  return reduced;
}
import { subst } from '../compiler/subst';
import { unifyTerms } from '../compiler/unify';

/**
 * TacticResult: Outcome of applying a tactic
 */
export type TacticResult =
  | { success: true; newEngine: TacticEngine; unifiedEquation?: UnifiedEquation; solvedArgs?: SolvedArg[] }
  | { success: false; error: string; cause?: Error };

/** Info about the equation used by a rewrite tactic (with all implicit args unified). */
export interface UnifiedEquation {
  readonly lhs: TTKTerm;
  readonly rhs: TTKTerm;
}

/** An argument that was solved by unification in an apply tactic. */
export interface SolvedArg {
  readonly term: TTKTerm;
  readonly type: TTKTerm;
  readonly implicit: boolean;
}

/**
 * Tactic: A proof state transformation
 */
export interface Tactic {
  /** Human-readable name */
  name: string;

  /** Apply this tactic to the given goal */
  apply(
    engine: TacticEngine,
    goal: MetaVar,
    goalId: string
  ): TacticResult;
}

/**
 * Helper: Generate fresh meta name
 */
let metaCounter = 0;
export function freshMetaName(): string {
  return `?tactic_meta_${metaCounter++}`;
}

/**
 * Helper: Reset meta counter (for tests)
 */
export function resetMetaCounter(): void {
  metaCounter = 0;
}

// =============================================================================
// Core Tactics
// =============================================================================

/**
 * exact: Solve the goal by providing the exact term
 *
 * Usage: exact <term>
 * Example: exact a
 *
 * The term must have the same type as the goal.
 */
export class ExactTactic implements Tactic {
  name = 'exact';

  constructor(public readonly term: TTKTerm) {}

  apply(engine: TacticEngine, goal: MetaVar, goalId: string): TacticResult {
    try {
      // Zonk goal type to resolve any solved metas before type checking.
      // Without zonking, App(Meta(?P), Meta(?x)) stays as-is and hits the
      // flex-rigid solver, generating a constant-function heuristic that
      // conflicts with the already-solved pattern. Zonk replaces solved
      // metas with their solutions; checkType internally normalizes via
      // unifyTerms when needed.
      //
      // We deliberately do NOT WHNF here: that would unfold definitions like
      // `Carrier R` past their Const head, breaking checkType's @ofNat
      // coercion lookup (which keys on the head's Const name). The user-
      // facing impact: tactic-mode `exact 1` against goal `Carrier R` could
      // not coerce the literal via @ofNat. Term mode worked because the
      // expected type came from a Pi binder (un-unfolded) — tactic mode now
      // matches that behavior.
      const zonkedGoalType = engine.zonkTerm(goal.type, goal.ctx.length);

      // Check term has expected type
      const checkedEnv = engine.checkInGoal(goal, this.term, zonkedGoalType);

      // Solve constraints to detect meta conflicts (e.g., ?a := f(x) and ?a := f(y)
      // from `exact refl` on goal `f(x) = f(y)` where x ≠ y).
      // Without this, conflicting constraints are deferred and never validated,
      // allowing unsound proofs like `refl` for non-definitionally-equal sides.
      const solvedEnv = checkedEnv.solveMetasAndConstraints({ liftMetasToFullContext: false });

      // Zonk the checked term (resolve any new metas)
      const solution = solvedEnv.zonkTerm(solvedEnv.elaboratedTerm ?? checkedEnv.elaboratedTerm ?? this.term);

      // Assign solution to goal
      // Merge solvedEnv.metaVars to capture any new metas created during type checking
      // (e.g., implicit argument metas for constructors like Nil : {A : Type} -> List A)
      const newMetaVars = new Map(solvedEnv.metaVars);
      newMetaVars.set(goalId, { ...goal, solution });

      // Remove goal from goal list
      const newGoals = engine.goals.filter(id => id !== goalId);

      // Adjust focus if we removed the focused goal
      let newFocusIndex = engine.focusIndex;
      if (newFocusIndex >= newGoals.length && newGoals.length > 0) {
        newFocusIndex = newGoals.length - 1;
      } else if (newGoals.length === 0) {
        newFocusIndex = 0;
      }

      return {
        success: true,
        newEngine: engine.withUpdates({
          metaVars: newMetaVars,
          constraints: solvedEnv.constraints,
          goals: newGoals,
          focusIndex: newFocusIndex
        }).solveConstraints()
      };
    } catch (e) {
      // Handle TCEnvError (which is not an Error instance)
      const errorMsg = e instanceof Error
        ? e.message
        : (e && typeof e === 'object' && 'message' in e)
          ? String((e as any).message)
          : String(e);

      return {
        success: false,
        error: `exact: ${errorMsg}`,
        cause: e instanceof Error ? e : undefined
      };
    }
  }
}

/**
 * assumption: Search local context for a term of the goal type
 *
 * Usage: assumption
 *
 * Searches the local context for a hypothesis whose type matches the goal type.
 */
export class AssumptionTactic implements Tactic {
  name = 'assumption';

  apply(engine: TacticEngine, goal: MetaVar, goalId: string): TacticResult {
    // Search context backwards (most recent first)
    // Try exact with each variable - the checker handles de Bruijn adjustments
    for (let i = goal.ctx.length - 1; i >= 0; i--) {
      const varIndex = goal.ctx.length - 1 - i;
      const solution: TTKTerm = { tag: 'Var', index: varIndex };
      const result = new ExactTactic(solution).apply(engine, goal, goalId);
      if (result.success) {
        return result;
      }
    }

    return {
      success: false,
      error: 'assumption: no matching hypothesis found in context'
    };
  }
}

/**
 * intro: Introduce a Pi binder into the context
 *
 * Usage: intro [name]
 * Example: intro x
 *
 * If the goal type is (x : A) -> B, introduces x : A into the context
 * and creates a new goal of type B.
 */
export class IntroTactic implements Tactic {
  name = 'intro';

  constructor(public readonly userName?: string) {}

  apply(engine: TacticEngine, goal: MetaVar, goalId: string): TacticResult {
    // Zonk goal type to resolve solved metas, then WHNF
    const goalType = engine.zonkTerm(goal.type, goal.ctx.length);
    const goalTypeWhnf = whnf(goalType, {
      definitions: engine.definitions,
      typingContext: goal.ctx
    });

    // Check if goal type is a Pi (Binder with BPi kind)
    if (goalTypeWhnf.tag !== 'Binder' || goalTypeWhnf.binderKind.tag !== 'BPi') {
      return {
        success: false,
        error: `intro: goal type is not a function type (got ${goalTypeWhnf.tag})`
      };
    }

    const { name, domain, body } = goalTypeWhnf;

    // Determine param name (user-provided or from binder)
    const paramName = this.userName ?? name ?? 'x';

    // Extend context with new parameter
    const newCtx = [...goal.ctx, { name: paramName, type: domain }];

    // Create fresh meta for body
    const newGoalId = freshMetaName();
    const newGoal: MetaVar = {
      ctx: newCtx,
      type: body, // Note: body already has correct de Bruijn indices
      solution: undefined
    };

    // Build lambda term: λ(paramName : domain) => ?newGoal
    const lambdaTerm: TTKTerm = {
      tag: 'Binder',
      name: paramName,
      binderKind: { tag: 'BLam' },
      domain,
      body: { tag: 'Meta', id: newGoalId }
    };

    // Assign lambda to current goal
    const newMetaVars = new Map(engine.metaVars);
    newMetaVars.set(goalId, { ...goal, solution: lambdaTerm });
    newMetaVars.set(newGoalId, newGoal);

    // Replace current goal with new goal
    const newGoals = engine.goals.map(id => id === goalId ? newGoalId : id);

    return {
      success: true,
      newEngine: engine.withUpdates({
        metaVars: newMetaVars,
        goals: newGoals
      })
    };
  }
}

/**
 * intros: Apply intro repeatedly until goal is not a Pi
 *
 * Usage: intros [names...]
 * Example: intros A B a b
 *
 * Optionally provide names for the introduced variables.
 * If no names given, uses names from binders or generates fresh names.
 */
export class IntrosTactic implements Tactic {
  name = 'intros';

  constructor(public readonly names?: string[]) {}

  apply(engine: TacticEngine, _goal: MetaVar, _goalId: string): TacticResult {
    let current = engine;

    if (this.names && this.names.length > 0) {
      // Named mode: introduce exactly these names, fail if any can't be introduced
      for (let i = 0; i < this.names.length; i++) {
        const currentGoal = current.getFocusedGoal();
        if (!currentGoal) {
          return { success: false, error: `intros: no goal remaining for '${this.names[i]}'` };
        }
        const currentGoalId = current.getFocusedGoalId();
        if (!currentGoalId) {
          return { success: false, error: `intros: no goal remaining for '${this.names[i]}'` };
        }
        const introResult = new IntroTactic(this.names[i]).apply(current, currentGoal, currentGoalId);
        if (!introResult.success) {
          return { success: false, error: `intros: cannot introduce '${this.names[i]}' — ${introResult.error}` };
        }
        current = introResult.newEngine;
      }
    } else {
      // No names: introduce all Pi binders automatically
      while (true) {
        const currentGoal = current.getFocusedGoal();
        if (!currentGoal) break;
        const zonkedGoalType = current.zonkTerm(currentGoal.type, currentGoal.ctx.length);
        const goalTypeWhnf = whnf(zonkedGoalType, {
          definitions: current.definitions,
          typingContext: currentGoal.ctx
        });
        if (goalTypeWhnf.tag !== 'Binder' || goalTypeWhnf.binderKind.tag !== 'BPi') break;
        const currentGoalId = current.getFocusedGoalId();
        if (!currentGoalId) break;
        const introResult = new IntroTactic().apply(current, currentGoal, currentGoalId);
        if (!introResult.success) break;
        current = introResult.newEngine;
      }
    }

    return { success: true, newEngine: current };
  }
}

/**
 * apply: Apply a function to solve the goal, creating subgoals for arguments
 *
 * Usage: apply <function>
 * Example: apply f
 *
 * If the goal is B and f has type A -> B, creates a subgoal of type A.
 */
export class ApplyTactic implements Tactic {
  name = 'apply';

  constructor(public readonly fn: TTKTerm) {}

  apply(engine: TacticEngine, goal: MetaVar, goalId: string): TacticResult {
    try {
      // Infer type of function in goal's context
      const inferredEnv = engine.inferInGoal(goal, this.fn);
      const fnType = inferredEnv.value; // The inferred type

      // Collect arguments from Pi type
      const argMetas: { id: string; meta: MetaVar; implicit: boolean }[] = [];
      let currentType = whnf(fnType, {
        definitions: engine.definitions,
        typingContext: goal.ctx
      });

      // Look up which args are implicit
      let fnName: string | undefined;
      if (this.fn.tag === 'Const') {
        fnName = this.fn.name;
      }
      const namedArgLookup = createNamedArgLookup(engine.definitions);
      const namedArgMap = fnName ? namedArgLookup(fnName) : undefined;
      const numImplicit = namedArgMap?.size ?? 0;
      let argIndex = 0;

      // Track the RAW (un-whnf'd) return type — same meta substitutions
      // but without δ-reducing the head. Needed for post-hoc positional
      // matching when the candidate's head is a record projection that
      // whnf would otherwise unfold into a Match.
      let rawReturnType = fnType;

      // Unwrap Pi types (Binder with BPi kind) and create metas for each argument
      while (currentType.tag === 'Binder' && currentType.binderKind.tag === 'BPi') {
        const isImplicit = argIndex < numImplicit;
        // Create meta for this argument
        const argMetaId = freshMetaName();
        const argMeta: MetaVar = {
          ctx: goal.ctx,
          type: currentType.domain,
          solution: undefined
        };
        argMetas.push({ id: argMetaId, meta: argMeta, implicit: isImplicit });

        // Substitute meta into body to get next type
        currentType = subst(0, { tag: 'Meta', id: argMetaId }, currentType.body);
        currentType = whnf(currentType, {
          definitions: engine.definitions,
          typingContext: goal.ctx
        });
        if (rawReturnType.tag === 'Binder' && rawReturnType.binderKind.tag === 'BPi') {
          rawReturnType = subst(0, { tag: 'Meta', id: argMetaId }, rawReturnType.body);
        }
        argIndex++;
      }

      // Unify return type with goal type.
      // Do NOT zonk the goal type first — zonking substitutes meta solutions which
      // may already be in reduced form (e.g., `Succ(plus n' X)` instead of
      // `plus (Succ n') X`), making structural matching with the function's return
      // type impossible. Instead, keep metas in the goal and let unification
      // produce meta constraints that the solver resolves.
      let unifyResult = unifyTerms(currentType, goal.type, {
        mode: 'check',
        definitions: engine.definitions,
        flexibleVars: false
      });

      // Retry via definitional-equality check when the structural unify
      // fails. Catches cases where the lemma's return type and the goal
      // are definitionally equal but syntactically distinct — e.g. the
      // lemma returns \`rle (rzero R) (rone R)\` while the goal is
      // \`rle (realOfRat R 0) (realOfRat R 1)\` (literal coercions
      // unfold to rzero/rone but the structural unifier doesn't δ-reduce).
      // areTypesDefEq does whnf with full definitions on both sides
      // recursively, so it sees through aliases/coercions. We can't
      // recover meta solutions from a defEq pass — but for the apply
      // path we just need to know whether the goal IS the candidate
      // up to reduction; if so, the candidate's metas can be left
      // unsolved (no fresh constraints needed) and the engine fills
      // them via unification on the application term later.
      if (!unifyResult.success) {
        if (areTypesDefEq(currentType, goal.type, engine.definitions, goal.ctx)) {
          unifyResult = { success: true, metaConstraints: [] } as any;
        }
      }

      // Additional fallback: when unify AND defEq both fail, try a positional
      // spine match between the candidate's raw return type and the goal type
      // (whnf'd with record projections stripped so aliases unfold but
      // projections stay opaque). Only accept when:
      //   (1) heads + arities align,
      //   (2) the candidate has unsolved IMPLICIT metas at positions where the
      //       goal has concrete terms (i.e. positional matching can actually
      //       contribute solutions), AND
      //   (3) at every position where BOTH candidate and goal are concrete
      //       (i.e. neither is a meta), the heads match — so we don't accept
      //       obviously-wrong applies like \`zeroLtOne\` on \`0 < ε/2\` where
      //       the candidate's RHS \`rone R\` vs goal's \`ε/2\` (different
      //       concrete heads) signals a real type mismatch.
      // Without (3) the fallback would silently swallow type errors and surface
      // bogus apply suggestions. The post-hoc positional matcher below fills
      // in the remaining implicits.
      // Only attempt this fallback for record-projection candidates — that's
      // the case it was added to handle (e.g. \`CompleteOrderedField.zeroLeOne\`
      // applied to a goal headed by the alias \`rle\`). For top-level aliases,
      // structural unify already handles them — skip the expensive whnf to
      // keep candidate iteration fast.
      const isProjectionCandidate = (() => {
        if (this.fn.tag !== 'Const') return false;
        for (const [, ind] of engine.definitions.inductiveTypes) {
          if (ind.recordInfo?.projections?.includes(this.fn.name)) return true;
        }
        return false;
      })();
      if (!unifyResult.success && isProjectionCandidate) {
        try {
          const reducedDefs = getReducedDefs(engine.definitions);
          const candWhnf = whnf(rawReturnType, { definitions: reducedDefs, typingContext: goal.ctx });
          const goalWhnf = whnf(goal.type, { definitions: reducedDefs, typingContext: goal.ctx });
          const cs = extractAppSpine(candWhnf);
          const gs = extractAppSpine(goalWhnf);
          const allArgMetaIds = new Set(argMetas.map(m => m.id));
          if (cs.fn.tag === 'Const' && gs.fn.tag === 'Const'
              && cs.fn.name === gs.fn.name
              && cs.args.length === gs.args.length) {
            const stringify = (t: TTKTerm) => JSON.stringify(t, (_, v) => typeof v === 'bigint' ? `bi:${v}` : v);
            // (a) Group meta proposals by id (unique-proposal => solvable).
            const proposals = new Map<string, Set<string>>();
            for (let i = 0; i < cs.args.length; i++) {
              const ca = cs.args[i];
              const ga = gs.args[i];
              if (ca.tag === 'Meta' && allArgMetaIds.has(ca.id) && ga.tag !== 'Meta' && ga.tag !== 'Hole') {
                if (!proposals.has(ca.id)) proposals.set(ca.id, new Set());
                proposals.get(ca.id)!.add(stringify(ga));
              }
            }
            let contributes = false;
            for (const [, s] of proposals) {
              if (s.size === 1) { contributes = true; break; }
            }
            // (b) Non-meta positions on the candidate side MUST be def-equal
            // to the corresponding goal position. Without this check the
            // fallback would falsely accept e.g. \`zeroLeOne\` on \`rle 1 2\`:
            // the head/arity align and \`?A\`/\`?inst\` get unique proposals,
            // but positions 2/3 (\`zero ?A ?inst\` vs \`realOfRat R 1\`,
            // \`one ?A ?inst\` vs \`realOfRat R 2\`) are NOT def-eq once
            // \`?A\`/\`?inst\` are solved. We approximate the post-solve
            // check by substituting the unique proposals into the candidate
            // args inline, then calling \`areTypesDefEq\`.
            const inlineSubst = (t: TTKTerm): TTKTerm => {
              if (t.tag === 'Meta') {
                const ps = proposals.get(t.id);
                if (ps && ps.size === 1) return [...proposals.get(t.id)!.values() as any as IterableIterator<TTKTerm>][0] ?? t;
                return t;
              }
              if (t.tag === 'App') return { tag: 'App', fn: inlineSubst(t.fn), arg: inlineSubst(t.arg) };
              return t;
            };
            // Need to materialize the proposal terms (not just JSON keys).
            const proposalTerms = new Map<string, TTKTerm>();
            for (let i = 0; i < cs.args.length; i++) {
              const ca = cs.args[i];
              const ga = gs.args[i];
              if (ca.tag === 'Meta' && allArgMetaIds.has(ca.id) && ga.tag !== 'Meta' && ga.tag !== 'Hole') {
                if (proposals.get(ca.id)!.size === 1) {
                  proposalTerms.set(ca.id, ga);
                }
              }
            }
            const subst = (t: TTKTerm): TTKTerm => {
              if (t.tag === 'Meta') {
                const sol = proposalTerms.get(t.id);
                return sol !== undefined ? sol : t;
              }
              if (t.tag === 'App') return { tag: 'App', fn: subst(t.fn), arg: subst(t.arg) };
              return t;
            };
            let allPositionsAlign = true;
            for (let i = 0; i < cs.args.length; i++) {
              const ca = cs.args[i];
              const ga = gs.args[i];
              if (ca.tag === 'Meta' || ga.tag === 'Meta' || ca.tag === 'Hole' || ga.tag === 'Hole') continue;
              const caSubst = subst(ca);
              if (!areTypesDefEq(caSubst, ga, engine.definitions, goal.ctx)) {
                allPositionsAlign = false;
                break;
              }
            }
            if (contributes && allPositionsAlign) {
              unifyResult = { success: true, metaConstraints: [] } as any;
            }
            // Silence unused-var lint (inlineSubst is kept for readability/contrast).
            void inlineSubst;
          }
        } catch { /* fall through to failure */ }
      }

      if (!unifyResult.success) {
        return {
          success: false,
          error: `apply ${fnName ?? '?'}: return type mismatch (${unifyResult.reason})`
        };
      }

      // Build application term: fn ?arg1 ?arg2 ...
      let appTerm: TTKTerm = this.fn;
      for (const { id } of argMetas) {
        appTerm = {
          tag: 'App',
          fn: appTerm,
          arg: { tag: 'Meta', id }
        };
      }

      // Assign application to goal
      // Merge inferredEnv.metaVars to capture any new metas created during type inference
      const newMetaVars = new Map(inferredEnv.metaVars);
      newMetaVars.set(goalId, { ...goal, solution: appTerm });

      // Add arg metas to metaVars
      for (const { id, meta } of argMetas) {
        newMetaVars.set(id, meta);
      }

      // Add meta constraints from unification
      const newConstraints = [
        ...engine.constraints,
        ...unifyResult.metaConstraints.map(mc => ({
          ctx: goal.ctx,
          meta: mc.meta,
          rhs: mc.rhs
        }))
      ];

      // Solve constraints FIRST so that explicit args solvable by unification
      // (e.g., congPlusRight's `p : Nat` determined by goal structure) get resolved
      // before we decide which args become subgoals.
      const solvedEngine = engine.withUpdates({
        metaVars: newMetaVars,
        constraints: newConstraints,
        goals: engine.goals,
        focusIndex: engine.focusIndex
      }).solveConstraints();

      let zonkedEngine = solvedEngine;

      // POST-HOC POSITIONAL MATCH: when argMetas remain unsolved after
      // constraint solving, the structural unifier missed them (typically
      // because whnf descended into \`match\`/projection forms before
      // reaching the meta position — e.g. for record-projection applies
      // like \`CompleteOrderedField.zeroLeOne\` on a goal whose head is
      // the alias \`rle\`). Walk the App spine of \`rawReturnType\`
      // (un-whnf'd, projections preserved) against the goal type whnf'd
      // with projections REMOVED from defs (so aliases unfold but
      // projections stay opaque). For positions where the candidate has
      // an unsolved meta and the goal has a concrete term, propose
      // \`?meta := goal_arg\`. CONFLICT DETECTION: when a single meta has
      // multiple proposals (e.g. \`leRefl: a ≤ a\` on \`0 ≤ 1\` would
      // propose \`?a := 0\` AND \`?a := 1\` from positions 2 and 3),
      // group by JSON key and reject the meta if it has multiple distinct
      // proposals. This handles BOTH implicit type/instance args (which
      // appear at multiple positions but always agree, like \`?A\` in
      // \`zeroLeOne\`) AND explicit args (which we conservatively only
      // solve when all positions agree).
      const unsolvedArgMetas = argMetas.filter(({ id }) => {
        const m = zonkedEngine.metaVars.get(id);
        return m && m.solution === undefined;
      });
      if (unsolvedArgMetas.length > 0 && isProjectionCandidate) {
        try {
          const reducedDefs = getReducedDefs(engine.definitions);

          let candSpine = extractAppSpine(rawReturnType);
          let goalSpine = extractAppSpine(goal.type);
          const headsMatch = (cs: ReturnType<typeof extractAppSpine>, gs: ReturnType<typeof extractAppSpine>) =>
            cs.fn.tag === 'Const' && gs.fn.tag === 'Const' && cs.fn.name === gs.fn.name && cs.args.length === gs.args.length;
          if (!headsMatch(candSpine, goalSpine)) {
            const candWhnf = whnf(rawReturnType, { definitions: reducedDefs, typingContext: goal.ctx });
            const goalWhnf = whnf(goal.type, { definitions: reducedDefs, typingContext: goal.ctx });
            candSpine = extractAppSpine(candWhnf);
            goalSpine = extractAppSpine(goalWhnf);
          }
          if (headsMatch(candSpine, goalSpine)) {
            const unsolvedIds = new Set(unsolvedArgMetas.map(({ id }) => id));
            // Group proposals by meta id, dedup'd by JSON serialization.
            const proposalsByMeta = new Map<string, Map<string, TTKTerm>>();
            const stringify = (t: TTKTerm) => JSON.stringify(t, (_, v) => typeof v === 'bigint' ? `bi:${v}` : v);
            for (let i = 0; i < candSpine.args.length; i++) {
              const cArg = candSpine.args[i];
              const gArg = goalSpine.args[i];
              if (cArg.tag === 'Meta' && unsolvedIds.has(cArg.id)) {
                if (!proposalsByMeta.has(cArg.id)) proposalsByMeta.set(cArg.id, new Map());
                proposalsByMeta.get(cArg.id)!.set(stringify(gArg), gArg);
              }
            }
            const extraConstraints: { ctx: any; meta: string; rhs: TTKTerm }[] = [];
            for (const [metaId, proposals] of proposalsByMeta) {
              // Only add a constraint when ALL positional proposals agree.
              // Multiple distinct proposals = position conflict → reject
              // (let the meta stay unsolved / become a subgoal).
              if (proposals.size === 1) {
                const rhs = [...proposals.values()][0];
                extraConstraints.push({ ctx: goal.ctx, meta: metaId, rhs });
              }
            }
            if (extraConstraints.length > 0) {
              zonkedEngine = zonkedEngine.withUpdates({
                constraints: [...zonkedEngine.constraints, ...extraConstraints],
              }).solveConstraints();
            }
          }
        } catch { /* fallthrough: leave unsolved */ }
      }

      // SOUNDNESS CHECK (closed-goal case only): after constraint solving,
      // verify the substituted candidate return type is definitionally equal
      // to the goal type. Catches the constraint-solver-first-wins behavior
      // where conflicting solutions for the same meta (e.g. `leRefl: a ≤ a`
      // on `0 ≤ 1` gets `?a := 0` from pos 2 then `?a := 1` from pos 3 — the
      // second silently dropped, producing a ground proof of `0 ≤ 0` which
      // doesn't match the goal). Only check when ALL argMetas are solved
      // (zero new subgoals); otherwise the proof still has subgoal-holes
      // that defEq can't relate.
      const allArgsSolved = argMetas.every(({ id }) => {
        const m = zonkedEngine.metaVars.get(id);
        return m && m.solution !== undefined;
      });
      // Soundness check: when an EXPLICIT arg meta appears at ≥2 positions
      // of the candidate's spine, the constraint solver's first-wins
      // behavior may silently accept conflicting positional solutions
      // (e.g. \`leRefl: a ≤ a\` on \`0 ≤ 1\`). First do a CHEAP structural
      // scan of currentType (no whnf): does any explicit meta appear at
      // ≥2 positions? If not, the conflict pattern can't arise — skip the
      // expensive cross-spine check. Most apply candidates don't have
      // repeated metas (\`leTrans\`, \`addLeRightCancel\` etc.), so this
      // short-circuits quickly.
      if (allArgsSolved && argMetas.length > 0) {
        const explicitMetaIds = new Set(argMetas.filter(m => !m.implicit).map(m => m.id));
        if (explicitMetaIds.size > 0) {
          const explicitOccurrences = new Map<string, number>();
          const candSpineCheap = extractAppSpine(currentType);
          for (const arg of candSpineCheap.args) {
            if (arg.tag === 'Meta' && explicitMetaIds.has(arg.id)) {
              explicitOccurrences.set(arg.id, (explicitOccurrences.get(arg.id) ?? 0) + 1);
            }
          }
          const hasRepeated = [...explicitOccurrences.values()].some(n => n >= 2);
          if (hasRepeated) {
            try {
              const goalSpine = extractAppSpine(whnf(goal.type, {
                definitions: engine.definitions, typingContext: goal.ctx,
              }));
              if (candSpineCheap.args.length === goalSpine.args.length) {
                const stringify = (t: TTKTerm) => JSON.stringify(t, (_, v) => typeof v === 'bigint' ? `bi:${v}` : v);
                const positions = new Map<string, Set<string>>();
                for (let i = 0; i < candSpineCheap.args.length; i++) {
                  const ca = candSpineCheap.args[i];
                  if (ca.tag === 'Meta' && explicitMetaIds.has(ca.id)) {
                    if (!positions.has(ca.id)) positions.set(ca.id, new Set());
                    positions.get(ca.id)!.add(stringify(goalSpine.args[i]));
                  }
                }
                for (const [, vals] of positions) {
                  if (vals.size > 1) {
                    return {
                      success: false,
                      error: `apply ${fnName ?? '?'}: explicit argument has conflicting positional constraints`,
                    };
                  }
                }
              }
            } catch { /* fall through */ }
          }
        }
      }

      // Replace current goal with arg metas that are STILL unsolved after constraint solving
      const newGoalIds = argMetas
        .filter(({ id, implicit }) => {
          const meta = zonkedEngine.metaVars.get(id);
          return meta && meta.solution === undefined && !implicit;
        })
        .map(({ id }) => id);

      const newGoals = [
        ...zonkedEngine.goals.slice(0, zonkedEngine.focusIndex),
        ...newGoalIds,
        ...zonkedEngine.goals.slice(zonkedEngine.focusIndex + 1)
      ];

      // Adjust focus to first new subgoal (if any)
      const newFocusIndex = newGoalIds.length > 0
        ? zonkedEngine.focusIndex
        : Math.min(zonkedEngine.focusIndex, Math.max(0, newGoals.length - 1));

      // Collect solved args for prose rendering (e.g., "f" in "cong f")
      const solvedArgs: SolvedArg[] = argMetas.map(({ id, meta: origMeta, implicit }) => {
        const solved = zonkedEngine.metaVars.get(id);
        return {
          term: solved?.solution ?? { tag: 'Hole' as const, id: '_' },
          type: origMeta.type,
          implicit,
        };
      });

      return {
        success: true,
        newEngine: zonkedEngine.withUpdates({
          goals: newGoals,
          focusIndex: newFocusIndex
        }),
        solvedArgs,
      };
    } catch (e) {
      // Handle TCEnvError (which is not an Error instance)
      const errorMsg = e instanceof Error
        ? e.message
        : (e && typeof e === 'object' && 'message' in e)
          ? String((e as any).message)
          : String(e);

      return {
        success: false,
        error: `apply: ${errorMsg}`,
        cause: e instanceof Error ? e : undefined
      };
    }
  }
}

/**
 * TacticSequence: Compose tactics sequentially
 *
 * Usage: TacticSequence('name', [tac1, tac2, tac3])
 *
 * Applies each tactic in sequence. If any fails, the entire sequence fails.
 */
export class TacticSequence implements Tactic {
  constructor(
    public readonly name: string,
    public readonly tactics: Tactic[]
  ) {}

  apply(engine: TacticEngine, _goal: MetaVar, _goalId: string): TacticResult {
    let current = engine;

    for (const tactic of this.tactics) {
      const currentGoal = current.getFocusedGoal();
      const currentGoalId = current.getFocusedGoalId();

      if (!currentGoal || !currentGoalId) {
        return {
          success: false,
          error: `${this.name}: no focused goal during sequence`
        };
      }

      const result = tactic.apply(current, currentGoal, currentGoalId);
      if (!result.success) {
        return {
          success: false,
          error: `${this.name}: tactic '${tactic.name}' failed: ${result.error}`,
          cause: result.cause
        };
      }

      current = result.newEngine;
    }

    return { success: true, newEngine: current };
  }
}
