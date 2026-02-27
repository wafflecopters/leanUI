import { TTKTerm, TTKPattern, levelsEqual, prettyPrint, mkLSucc, isDefinitionallyEqual } from "./kernel";
import { shiftTerm, minFreeVarIndex, subst } from "./subst";
import { Constraint, DefinitionsMap, MetaVar, TTKContext } from "./term";
import { unifyTerms } from "./unify";
import { whnf } from "./whnf";

/**
 * Substitute solved metas in a term using the given metaVars map.
 * Standalone version of TCEnv.zonkTerm for use in solveConstraints.
 */
function zonkWithMetas(term: TTKTerm, metaVars: Map<string, MetaVar>): TTKTerm {
  switch (term.tag) {
    case 'Meta': {
      const metaVar = metaVars.get(term.id);
      if (metaVar?.solution) return zonkWithMetas(metaVar.solution, metaVars);
      return term;
    }
    case 'Hole': {
      const metaVar = metaVars.get(term.id);
      if (metaVar?.solution) return zonkWithMetas(metaVar.solution, metaVars);
      return term;
    }
    case 'Var':
    case 'Const':
    case 'ULevel':
    case 'ULit':
    case 'UOmega':
      return term;
    case 'Sort': {
      const level = zonkWithMetas(term.level, metaVars);
      return level === term.level ? term : { tag: 'Sort', level };
    }
    case 'App': {
      const fn = zonkWithMetas(term.fn, metaVars);
      const arg = zonkWithMetas(term.arg, metaVars);
      return fn === term.fn && arg === term.arg ? term : { tag: 'App', fn, arg };
    }
    case 'Binder': {
      const bk = term.binderKind.tag === 'BLet'
        ? { tag: 'BLet' as const, defVal: zonkWithMetas(term.binderKind.defVal, metaVars) }
        : term.binderKind;
      const domain = zonkWithMetas(term.domain, metaVars);
      const body = zonkWithMetas(term.body, metaVars);
      return domain === term.domain && body === term.body && bk === term.binderKind
        ? term
        : { tag: 'Binder', name: term.name, binderKind: bk, domain, body };
    }
    case 'Annot': {
      const t = zonkWithMetas(term.term, metaVars);
      const ty = zonkWithMetas(term.type, metaVars);
      return t === term.term && ty === term.type ? term : { tag: 'Annot', term: t, type: ty };
    }
    case 'Match': {
      const scrutinee = zonkWithMetas(term.scrutinee, metaVars);
      const clauses = term.clauses.map(c => ({
        ...c,
        rhs: zonkWithMetas(c.rhs, metaVars)
      }));
      return { tag: 'Match', scrutinee, clauses };
    }
    default:
      return term;
  }
}

/**
 * Check if a term contains any unsolved meta variables.
 * Used to avoid false "implicit argument conflict" errors when unification
 * fails because a term is stuck on unsolved metas (e.g., `plus ?m ?n` can't
 * reduce to WHNF, making it incomparable with `Succ(...)`).
 */
function containsUnsolvedMeta(term: TTKTerm, metaVars: Map<string, MetaVar>): boolean {
  switch (term.tag) {
    case 'Meta': {
      const meta = metaVars.get(term.id);
      if (!meta?.solution) return true;
      return containsUnsolvedMeta(meta.solution, metaVars);
    }
    case 'App':
      return containsUnsolvedMeta(term.fn, metaVars) || containsUnsolvedMeta(term.arg, metaVars);
    case 'Binder':
      return containsUnsolvedMeta(term.domain, metaVars) || containsUnsolvedMeta(term.body, metaVars);
    case 'Annot':
      return containsUnsolvedMeta(term.term, metaVars) || containsUnsolvedMeta(term.type, metaVars);
    default:
      return false;
  }
}

/**
 * Extract the head constructor name from a term in WHNF.
 * E.g., App(App(Const("Equal"), Nat), Succ(x)) → head is "Equal" if fully applied,
 * but App(Const("Succ"), x) → head is "Succ".
 */
function getHeadConst(term: TTKTerm): string | null {
  let t = term;
  while (t.tag === 'App') t = t.fn;
  return t.tag === 'Const' ? t.name : null;
}

/**
 * Case inversion: when we need `solution = rhs` but unification fails because
 * rhs is a stuck function application (e.g., `plus ?m ?n`) while solution is
 * a constructor (e.g., `Succ X`), try to WHNF the rhs and match the stuck
 * Match's clauses against the solution's constructor.
 *
 * E.g., `Succ(?43) = plus(?47, ?45)`:
 *   1. WHNF `plus(?47, ?45)` → `match ?47 { Zero → ?45; Succ n' → Succ(plus n' ?45) }`
 *   2. Solution head is "Succ" → find clause with PCtor("Succ", ...)
 *   3. Clause RHS is `Succ(plus Var(0) ?45)` (Var(0) is pattern-bound n')
 *   4. Create fresh meta ?k for Var(0), substitute: `Succ(plus ?k ?45)`
 *   5. Unify `Succ(?43)` with `Succ(plus ?k ?45)` → `?43 := plus ?k ?45`
 *   6. Assign scrutinee: `?47 := Succ(?k)`
 *
 * Returns sub-constraints if successful, null if inversion is not applicable.
 */
function tryCaseInversion(
  solution: TTKTerm,
  rhs: TTKTerm,
  definitions: DefinitionsMap | undefined,
  metaVars: Map<string, MetaVar>,
  context: TTKContext
): { constraints: Array<{ meta: string; rhs: TTKTerm }> } | null {
  if (!definitions) return null;

  // Get the head constructor of the solution
  const solutionHead = getHeadConst(solution);
  if (!solutionHead) return null;

  // WHNF the rhs to see if it becomes a stuck Match (possibly under App spine)
  const rhsWhnf = whnf(rhs, { definitions });

  // Extract the Match node and any extra args applied to it.
  // WHNF of `plus ?m ?n` may be `App(App(Match(scrutinee, clauses), arg1), arg2)`
  // because `plus` is defined by matching on its first arg, and the second arg
  // is passed through as an extra argument to the match result.
  let matchNode: TTKTerm = rhsWhnf;
  const extraArgs: TTKTerm[] = [];
  while (matchNode.tag === 'App') {
    extraArgs.push(matchNode.arg);
    matchNode = matchNode.fn;
  }
  extraArgs.reverse(); // collected in reverse order

  if (matchNode.tag !== 'Match') return null;

  // Determine the actual scrutinee.
  // When the Match comes from a function definition, the scrutinee is a Hole placeholder
  // and the real scrutinee is the first extra arg (e.g., `App(Match(Hole, clauses), arg1)`).
  let actualScrutinee: TTKTerm;
  let matchArgs: TTKTerm[]; // extra args to apply to clause RHS after matching
  if (matchNode.scrutinee.tag === 'Hole' && extraArgs.length > 0) {
    actualScrutinee = extraArgs[0];
    matchArgs = extraArgs.slice(1);
  } else {
    actualScrutinee = matchNode.scrutinee;
    matchArgs = extraArgs;
  }

  // Check if the actual scrutinee is a Meta (stuck)
  if (actualScrutinee.tag !== 'Meta') return null;
  const scrutineeMeta = actualScrutinee.id;

  // Check that this meta is unsolved
  const scrutineeMetaVar = metaVars.get(scrutineeMeta);
  if (scrutineeMetaVar?.solution) return null;

  // Find the clause whose pattern head matches the solution's constructor.
  // Clauses may have multiple patterns (e.g., `plus Zero m = m` has patterns
  // [PCtor("Zero"), PVar("m")]). The first pattern matches the scrutinee; the
  // remaining patterns match subsequent args from matchArgs.
  for (const clause of matchNode.clauses) {
    if (clause.patterns.length < 1) continue;
    const pat = clause.patterns[0];
    if (pat.tag !== 'PCtor' || pat.name !== solutionHead) continue;

    // Count ALL pattern-bound variables across all patterns in this clause.
    const countPatVars = (p: TTKPattern): number => {
      if (p.tag === 'PVar') return 1;
      if (p.tag === 'PCtor') return p.args.reduce((sum, a) => sum + countPatVars(a), 0);
      return 0; // PWild
    };
    const totalPatVars = clause.patterns.reduce((sum, p) => sum + countPatVars(p), 0);
    const scrutineePatVars = countPatVars(pat);

    // Create fresh metas for ALL pattern-bound variables.
    const freshMetas: string[] = [];
    const newConstraints: Array<{ meta: string; rhs: TTKTerm }> = [];

    for (let i = 0; i < totalPatVars; i++) {
      const freshId = `?case_inv_${scrutineeMeta}_${i}`;
      freshMetas.push(freshId);
      if (!metaVars.has(freshId)) {
        metaVars.set(freshId, {
          ctx: context,
          type: { tag: 'Hole', id: `${freshId}_type` },
          solution: undefined
        });
      }
    }

    // Substitute fresh metas for ALL pattern-bound variables in the clause RHS.
    // Pattern vars are bound at indices 0..totalPatVars-1 (innermost first).
    let clauseRhs = clause.rhs;
    for (let i = totalPatVars - 1; i >= 0; i--) {
      clauseRhs = subst(i, { tag: 'Meta', id: freshMetas[i] }, clauseRhs);
    }

    // Apply remaining matchArgs (those not consumed by clause patterns) to the RHS.
    // For multi-pattern clauses, some matchArgs are consumed by patterns 1..N,
    // and their bindings were already substituted. The remaining are extra args.
    const consumedByPatterns = clause.patterns.length - 1; // patterns[0] is the scrutinee
    for (let ai = consumedByPatterns; ai < matchArgs.length; ai++) {
      let substArg = matchArgs[ai];
      for (let i = totalPatVars - 1; i >= 0; i--) {
        substArg = subst(i, { tag: 'Meta', id: freshMetas[i] }, substArg);
      }
      clauseRhs = { tag: 'App', fn: clauseRhs, arg: substArg };
    }

    // For patterns after the first (patterns[1..N]), we need to constrain the
    // corresponding matchArgs to match those patterns. For PVar patterns, add
    // a constraint equating the fresh meta with the matchArg.
    let patVarIdx = scrutineePatVars; // start after scrutinee pattern vars
    for (let pi = 1; pi < clause.patterns.length && (pi - 1) < matchArgs.length; pi++) {
      const argPat = clause.patterns[pi];
      if (argPat.tag === 'PVar') {
        // This pattern binds a variable — constrain the fresh meta to equal the arg
        newConstraints.push({ meta: freshMetas[patVarIdx], rhs: matchArgs[pi - 1] });
        patVarIdx++;
      } else if (argPat.tag === 'PWild') {
        // No binding, skip
      } else {
        // PCtor in non-scrutinee position — too complex for now
        return null;
      }
    }

    // Unify the substituted clause RHS with the solution
    const unifyResult = unifyTerms(solution, clauseRhs, {
      mode: 'pattern',
      flexibleVars: true,
      definitions: undefined, // structural first
    });

    if (!unifyResult.success) {
      // Try with definitions
      const unifyResult2 = unifyTerms(solution, clauseRhs, {
        mode: 'pattern',
        flexibleVars: true,
        definitions,
      });
      if (!unifyResult2.success) return null;
      for (const mc of unifyResult2.metaConstraints) {
        newConstraints.push(mc);
      }
    } else {
      for (const mc of unifyResult.metaConstraints) {
        newConstraints.push(mc);
      }
    }

    // Build the constructor term for the scrutinee: Succ(?k) etc.
    // Only use the fresh metas for the scrutinee pattern's args (not other patterns' vars).
    let scrutineeSolution: TTKTerm = { tag: 'Const', name: solutionHead };
    for (let i = 0; i < scrutineePatVars; i++) {
      scrutineeSolution = { tag: 'App', fn: scrutineeSolution, arg: { tag: 'Meta', id: freshMetas[i] } };
    }

    // Add constraint to assign the scrutinee meta
    newConstraints.push({ meta: scrutineeMeta, rhs: scrutineeSolution });

    return { constraints: newConstraints };
  }

  return null;
}

/**
 * Checks if two terms are DEFINITELY incompatible (cannot possibly be unified).
 * Returns true only when the terms definitely cannot be equal, false otherwise.
 *
 * This is conservative: returns false (not definitely different) for cases like:
 * - Different Var indices at the top level (might be the same variable at
 *   different de Bruijn indices due to context depth changes)
 * - Metas/Holes (might be solved to the same value)
 * - Defined function applications (might reduce to the same value)
 *
 * Returns true when:
 * - Both terms have different constructor heads (disjointness)
 * - Same constructor head but some argument is definitely different (injectivity)
 *
 * Constructor injectivity enables deeper Var comparison: when two terms share
 * the same constructor head (e.g., both are `Succ _`), their arguments must be
 * equal. Inside these arguments, Var-Var differences are checked using context
 * binding name lookup when contexts are available. This catches cases like
 * `Succ x` vs `Succ y` where x and y are genuinely different variables.
 *
 * The Var name check is restricted to constructor argument positions because
 * at the top level, Var index differences commonly arise from context depth
 * shifts (e.g., let-bindings), not genuine variable differences. Inside
 * constructor arguments, the terms were produced by the same unification
 * decomposition, making Var index differences more reliable indicators of
 * genuine variable differences.
 */
function areTermsDefinitelyDifferent(
  a: TTKTerm, b: TTKTerm,
  definitions?: DefinitionsMap,
  ctxA?: TTKContext, ctxB?: TTKContext,
  _insideConstructorArg = false
): boolean {
  // If definitions are available, reduce to WHNF first.
  // This handles cases like `plus Zero Zero` reducing to `Zero`.
  let wa = a, wb = b;
  if (definitions) {
    wa = whnf(a, { definitions });
    wb = whnf(b, { definitions });
  }

  // Compare heads (unwrap applications)
  const headA = getHead(wa);
  const headB = getHead(wb);

  if (headA.tag === 'Const' && headB.tag === 'Const') {
    const isConstructorOrType = (name: string): boolean => {
      if (!definitions) return false;
      return definitions.inductiveNameOfConstructor.has(name)
        || definitions.inductiveTypes.has(name);
    };

    if (headA.name !== headB.name) {
      if (definitions) {
        // Only report conflict if BOTH heads are constructors (not defined functions).
        // A defined function might reduce further with different arguments,
        // but constructors are injective and distinct — different constructor heads
        // means definitely different terms.
        return isConstructorOrType(headA.name) && isConstructorOrType(headB.name);
      }
      // Without definitions, we can only detect conflicts between bare Const terms
      // (no App wrapping) since we can't distinguish constructors from functions.
      return wa.tag === 'Const' && wb.tag === 'Const';
    }

    // Same constructor head — constructors are injective, so if any corresponding
    // argument is definitely different, the whole terms are definitely different.
    // e.g., Succ Zero ≠ Succ (Succ x) because Zero ≠ Succ x
    if (definitions && isConstructorOrType(headA.name)) {
      const argsA = getSpine(wa);
      const argsB = getSpine(wb);
      if (argsA.length === argsB.length) {
        for (let i = 0; i < argsA.length; i++) {
          if (areTermsDefinitelyDifferent(argsA[i], argsB[i], definitions, ctxA, ctxB, true)) {
            return true;
          }
        }
      }
    }

    return false;
  }

  // Var vs constructor conflict: a named (non-wildcard) rigid variable cannot
  // equal a constructor application. E.g., if a meta is solved to `y` (a named
  // function parameter) and the constraint says `Succ x`, that's a definite
  // conflict. However, pattern wildcards (`?0`, `?1`, `_`) CAN match constructors
  // since they're flexible binding positions.
  if (definitions) {
    const isConstructorHead = (head: TTKTerm): boolean =>
      head.tag === 'Const' && definitions.inductiveNameOfConstructor.has(head.name);
    const isNamedVar = (head: TTKTerm, ctx?: TTKContext): boolean => {
      if (head.tag !== 'Var' || !ctx) return false;
      const binding = ctx[ctx.length - 1 - head.index];
      if (!binding) return false;
      // Pattern wildcards start with '?' or '_' — they're flexible and can match anything
      return !binding.name.startsWith('?') && !binding.name.startsWith('_');
    };
    if ((isNamedVar(headA, ctxA) && isConstructorHead(headB))
      || (isNamedVar(headB, ctxB) && isConstructorHead(headA))) {
      return true;
    }
  }

  // After WHNF, a rigid application (head is Const/Match/Sort — not Meta/Hole/Var)
  // is definitely different from a Binder (Pi/Lambda). An App in WHNF means the head
  // couldn't be reduced further, so it can never become a Pi or Lambda.
  // This catches under-application errors where a partially-applied function returns
  // a Pi but is expected to return a data type (e.g., Carrier R vs Limit -> Carrier R).
  {
    const isRigidHead = (h: TTKTerm): boolean =>
      h.tag === 'Match' || h.tag === 'Const' || h.tag === 'Sort';
    const isRigidApp = (t: TTKTerm): boolean =>
      t.tag === 'App' && isRigidHead(getHead(t));
    // Only check BPi (function types), not BLam (lambdas). A lambda can legitimately
    // appear alongside a rigid App when a type family parameter (e.g., \n => Pair Nat T)
    // is compared to a partially-applied type (e.g., Pair ?_implicit0) — they unify after
    // beta-reduction. But a Pi (function type) vs rigid App is a definite conflict.
    const isBPi = (t: TTKTerm): boolean =>
      t.tag === 'Binder' && t.binderKind.tag === 'BPi';
    if ((isRigidApp(wa) && isBPi(wb)) ||
        (isRigidApp(wb) && isBPi(wa))) {
      return true;
    }
    // Also: bare rigid Const vs Pi (type alias would have been unfolded by WHNF)
    if ((wa.tag === 'Const' && isBPi(wb)) ||
        (wb.tag === 'Const' && isBPi(wa))) {
      return true;
    }
    // Sort vs App/Binder
    if ((wa.tag === 'Sort' && (wb.tag === 'App' || wb.tag === 'Binder')) ||
        (wb.tag === 'Sort' && (wa.tag === 'App' || wa.tag === 'Binder'))) {
      return true;
    }
  }

  // Var-Var comparison with context-based name lookup — ONLY inside constructor
  // arguments. At the top level, different Var indices commonly arise from
  // context depth shifts (e.g., a let-binding for a recursive call shifts all
  // indices by 1), so Var-Var differences are not reliable. But inside
  // constructor arguments (reached via injectivity), both terms were decomposed
  // from the same constructor application, so Var differences are meaningful.
  //
  // We look up binding names in the provided contexts. Different names indicate
  // genuinely different variables (e.g., x vs y). Same names are treated
  // conservatively (might be the same variable at shifted indices).
  if (_insideConstructorArg && headA.tag === 'Var' && headB.tag === 'Var' && ctxA && ctxB) {
    if (headA.index !== headB.index) {
      const bindingA = ctxA[ctxA.length - 1 - headA.index];
      const bindingB = ctxB[ctxB.length - 1 - headB.index];
      if (bindingA && bindingB && bindingA.name !== bindingB.name) {
        return true;
      }
    }
  }

  // For all other cases, be conservative and say they might be equal
  return false;
}

/**
 * Check if two terms are compatible as constant functions — i.e., both WHNF
 * to function-like terms (lambda or Match with Hole scrutinee) that produce
 * the same result when applied to any argument.
 *
 * This handles the case where the constant-function heuristic produces a lambda
 * with a dummy domain (Type) but correct body, while the actual solution is a
 * named function (delta-unfolding to Match(Hole, ...)) with the proper domain.
 * E.g.: P (defined as match _ | n => Nat) vs \(_:Type) => Nat
 */
function areConstantFunctionsCompatible(a: TTKTerm, b: TTKTerm, definitions?: DefinitionsMap): boolean {
  const wa = definitions ? whnf(a, { definitions }) : a;
  const wb = definitions ? whnf(b, { definitions }) : b;
  // Check if both are function-like (lambda or Match with Hole scrutinee).
  // Pattern-matching definitions use Match(Hole, clauses) instead of lambdas.
  const isFnLike = (t: TTKTerm): boolean =>
    (t.tag === 'Binder' && t.binderKind.tag === 'BLam') ||
    (t.tag === 'Match' && t.scrutinee.tag === 'Hole');
  if (isFnLike(wa) && isFnLike(wb)) {
    // Apply both to a dummy argument and compare results.
    // This handles both lambdas (beta-reduction) and Match(Hole) (scrutinee substitution).
    const dummy: TTKTerm = { tag: 'Const', name: '_areConstFnCompat_dummy' };
    const mkApp = (fn: TTKTerm, arg: TTKTerm): TTKTerm => ({ tag: 'App', fn, arg });
    const ctx = definitions ? { definitions } : {};
    const resultA = whnf(mkApp(wa, dummy), ctx);
    const resultB = whnf(mkApp(wb, dummy), ctx);
    return isDefinitionallyEqual(resultA, resultB);
  }
  return false;
}

/**
 * Get the head of a term (unwrap applications).
 */
function getHead(term: TTKTerm): TTKTerm {
  while (term.tag === 'App') {
    term = term.fn;
  }
  return term;
}

/**
 * Get the argument spine of a term (collect App arguments left to right).
 * e.g., App(App(f, a), b) → [a, b]
 */
function getSpine(term: TTKTerm): TTKTerm[] {
  const args: TTKTerm[] = [];
  while (term.tag === 'App') {
    args.push(term.arg);
    term = term.fn;
  }
  args.reverse();
  return args;
}

/**
 * Check if a level contains a bound level variable (de Bruijn Var).
 * Returns true if the level contains any Var (bound level variable).
 */
function levelContainsBoundVar(level: TTKTerm): boolean {
  switch (level.tag) {
    case 'ULit':
    case 'UOmega':
    case 'ULevel':
    case 'Const':
    case 'Meta':
    case 'Hole':
      return false;
    case 'Var':
      return true;
    case 'App':
      return levelContainsBoundVar(level.fn) || levelContainsBoundVar(level.arg);
    default:
      return false;
  }
}

/**
 * Check if a level contains a solvable meta or hole.
 * Returns true if the level contains any Meta or Hole (which can be solved).
 */
function levelContainsMeta(level: TTKTerm): boolean {
  switch (level.tag) {
    case 'ULit':
    case 'UOmega':
    case 'ULevel':
    case 'Const':
    case 'Var':
      return false;
    case 'Meta':
    case 'Hole':
      return true;
    case 'App':
      return levelContainsMeta(level.fn) || levelContainsMeta(level.arg);
    default:
      return false;
  }
}

/**
 * Check type compatibility when solving a constraint ?m = t.
 *
 * When the meta has type Sort(l1) and the rhs has type Sort(l2),
 * we need to ensure the levels are compatible:
 * - If meta's level is concrete (no metas) and rhs's level has a bound Var, REJECT
 * - If meta's level has a solvable meta, it can be unified with any level
 *
 * This catches the case where an inductive has {A : Type} but a constructor
 * has {A : Type u} with u being a bound level variable - these are incompatible.
 *
 * Returns null if types are compatible, or an error message if not.
 */
function checkTypeCompatibility(
  metaType: TTKTerm,
  rhsType: TTKTerm
): string | null {
  // Both must be Sorts for this check to apply
  if (metaType.tag !== 'Sort' || rhsType.tag !== 'Sort') {
    return null;  // Not a Sort type mismatch - let other checks handle it
  }

  const metaLevel = metaType.level;
  const rhsLevel = rhsType.level;

  // If levels are equal, types are compatible
  if (levelsEqual(metaLevel, rhsLevel)) {
    return null;
  }

  // If meta's level contains a solvable meta/hole, it can be unified with anything
  // The level unification will handle ensuring consistency
  if (levelContainsMeta(metaLevel)) {
    return null;
  }

  // If meta's level contains a bound var, be permissive
  // The bound vars might refer to the same binding with different de Bruijn indices
  // due to context depth differences
  if (levelContainsBoundVar(metaLevel)) {
    return null;
  }

  // Meta's level is concrete (no metas, no bound vars)
  // If rhs's level has a bound Var, they're incompatible:
  // the concrete level cannot be unified with a bound level variable
  if (levelContainsBoundVar(rhsLevel)) {
    return `type level mismatch: expected concrete level but got bound level variable`;
  }

  // Both levels are fully concrete but different - this is OK
  // Different concrete levels can arise from context depth differences or
  // zonking that resolved levels at different points. Let the constraint be solved.
  return null;
}

/**
 * Get the type of a variable from the context.
 * Returns undefined if the index is out of bounds.
 */
function getVarTypeFromContext(ctx: TTKContext, varIndex: number): TTKTerm | undefined {
  const binding = ctx[ctx.length - 1 - varIndex];
  return binding?.type;
}

/**
 * Normalize a constraint's RHS to a target context depth by shifting de Bruijn
 * indices. This ensures constraints for the same meta use a consistent index
 * scheme, making Var-vs-Var conflict detection a simple index comparison.
 *
 * Returns null if the constraint references inner-scope variables that cannot
 * be shifted away (the constraint is "stuck" at its current depth).
 */
export function normalizeConstraintDepth(
  constraint: Constraint,
  targetContext: TTKContext
): { normalized: Constraint; shifted: boolean } | null {
  const depthDiff = constraint.ctx.length - targetContext.length;
  if (depthDiff === 0) {
    return { normalized: constraint, shifted: false };
  }
  if (depthDiff > 0) {
    // Constraint from deeper context: shift down to target depth.
    // Only safe if no free variables would go negative after shifting.
    const minIdx = minFreeVarIndex(constraint.rhs);
    if (minIdx < depthDiff) return null; // stuck: references inner-scope variables
    const rhs = shiftTerm(constraint.rhs, -depthDiff, 0);
    const rhsType = constraint.rhsType ? shiftTerm(constraint.rhsType, -depthDiff, 0) : undefined;
    return { normalized: { ...constraint, rhs, rhsType, ctx: targetContext }, shifted: true };
  }
  // Constraint from shallower context: shift up to target depth.
  const rhs = shiftTerm(constraint.rhs, -depthDiff, 0);
  const rhsType = constraint.rhsType ? shiftTerm(constraint.rhsType, -depthDiff, 0) : undefined;
  return { normalized: { ...constraint, rhs, rhsType, ctx: targetContext }, shifted: true };
}

/** Priority for constraint solving: lower = solved first.
 * Pattern solutions are most precise, constant-function heuristic least precise. */
function constraintPriority(c: Constraint): number {
  if (c.isPatternSolution === true) return 0;          // Non-constant pattern — best
  if (c.isPatternSolution === 'constant') return 1;    // Constant-function pattern
  if (c.isPatternSolution === undefined) return 2;     // Bare meta or non-flex-rigid
  return 3;                                             // Constant-function heuristic — worst
}

export function solveConstraints(
  metaVars: Map<string, MetaVar>,
  constraints: Constraint[],
  liftContext?: TTKContext,
  definitions?: DefinitionsMap
): { constraints: Constraint[], metaVars: Map<string, MetaVar> } {
  const stillStuck: Constraint[] = [];
  // Collect constraints that are deferred because the RHS contains unsolved metas.
  // After the main loop, we re-check these with updated meta solutions — metas that
  // were unsolved during the main pass may now be solved, enabling conflict detection.
  const deferredConflicts: { constraint: Constraint, effectiveContext: TTKContext }[] = [];

  const newMetaVars = new Map(metaVars);

  // Sort constraints by solution quality: pattern unification (precise) first,
  // then bare metas / non-flex-rigid, then constant-function heuristic (lossy) last.
  // This ensures that when multiple constraints target the same meta, the most
  // precise solution wins (e.g., pattern motive inference before constant-function).
  const queue = [...constraints].sort((a, b) => constraintPriority(a) - constraintPriority(b));
  // Fuel prevents infinite loops from cyclic meta chains.
  // Use a generous multiplier because structural unification decomposition
  // can generate sub-constraints that need processing in the same pass.
  let fuel = Math.max(queue.length * 10, 50);
  while (queue.length > 0 && fuel-- > 0) {
    const constraint = queue.shift()!;
    const meta = newMetaVars.get(constraint.meta);

    // Skip constraints for metas that don't exist in the map.
    // This happens when unification creates constraints for unelaborated Holes
    // (with names like 'hole:f_type') which haven't been converted to Metas yet.
    if (!meta) continue;

    // Determine the effective context for this meta. When liftContext is provided,
    // it overrides the meta's creation context for scope checking.
    const effectiveContext = liftContext ?? meta.ctx;

    // Normalize the constraint's RHS to the effective context depth.
    // This ensures all subsequent code can assume consistent de Bruijn indices.
    const normResult = normalizeConstraintDepth(constraint, effectiveContext);
    if (normResult === null) {
      // Constraint references inner-scope variables that can't be shifted away.
      // However, if the meta already has a solution, we can still detect structural
      // conflicts (constructor head mismatches) using the original non-normalized terms,
      // since constructor heads are depth-independent.
      if (meta.solution !== undefined && meta.solution.tag !== 'Meta') {
        // Resolve the constraint RHS through meta chains
        let resolvedRhs = constraint.rhs;
        while (resolvedRhs.tag === 'Meta') {
          const rhsMeta = newMetaVars.get(resolvedRhs.id);
          if (rhsMeta?.solution) {
            resolvedRhs = rhsMeta.solution;
          } else {
            break;
          }
        }
        // Check structural conflicts using original contexts (safe for constructor heads)
        if (areTermsDefinitelyDifferent(meta.solution, resolvedRhs, definitions, effectiveContext, constraint.ctx)) {
          const names = effectiveContext.map(c => c.name).reverse();
          const metaTypeStr = prettyPrint(meta.type, names);
          throw new Error(`Implicit argument conflict for ${constraint.meta} : ${metaTypeStr}: inferred ${prettyPrint(meta.solution, names)} but required to be ${prettyPrint(resolvedRhs, constraint.ctx.map(c => c.name).reverse())}`);
        }
        // Try unification — may detect conflicts even when normalization can't shift.
        // Try structural first (no definitions), fall back to full unification.
        let unifyResult = unifyTerms(meta.solution, resolvedRhs, {
          mode: 'pattern',
          flexibleVars: true,
          definitions: undefined,
        });
        if (!unifyResult.success) {
          unifyResult = unifyTerms(meta.solution, resolvedRhs, {
            mode: 'pattern',
            flexibleVars: true,
            definitions,
          });
        }
        if (!unifyResult.success) {
          // Don't throw if the RHS contains unsolved metas — the term may be stuck
          // (e.g., `plus ?m ?n` can't reduce to WHNF, making it incomparable with
          // `Succ(...)` even though `?m = Succ(k)` would make them equal).
          // Defer the constraint instead.
          //
          // Also tolerate conflicts when:
          // 1. The meta was solved by pattern unification and this constraint is non-pattern.
          //    Pattern solutions are the unique correct answer; non-pattern constraints
          //    (from APP decomposition) are less precise.
          // 2. The constraint is a constant-function heuristic (isPatternSolution: false).
          //    These use dummy lambda domains (Type instead of actual domain).
          // 3. The two solutions are compatible as constant functions (same result when applied).
          const tolerateConflict =
            (meta.isPatternSolved && constraint.isPatternSolution !== true) ||
            constraint.isPatternSolution === false ||
            areConstantFunctionsCompatible(meta.solution, resolvedRhs, definitions);
          if (!containsUnsolvedMeta(resolvedRhs, newMetaVars) && !tolerateConflict) {
            const names = effectiveContext.map(c => c.name).reverse();
            const metaTypeStr = prettyPrint(meta.type, names);
            throw new Error(`Implicit argument conflict for ${constraint.meta} : ${metaTypeStr}: inferred ${prettyPrint(meta.solution, names)} but required to be ${prettyPrint(resolvedRhs, constraint.ctx.map(c => c.name).reverse())}`);
          }
        } else {
          // Do NOT queue sub-constraints from non-normalized unification.
          // The meta.solution is at effectiveContext depth, but resolvedRhs is at
          // constraint.ctx depth (which is deeper). Sub-constraints from unifying
          // terms at different depths would have wrong de Bruijn indices.
          // This unification is only for conflict detection, not constraint propagation.
        }
      }
      stillStuck.push(constraint);
      continue;
    }
    const normConstraint = normResult.normalized;

    // If meta already has a solution, propagate the constraint through the solution.
    // This handles meta chains (e.g., _10 := Meta(_14), then _10 := Succ x → forward to _14)
    // and structural decomposition (e.g., _14 := Succ _12, then _14 := Succ x → _12 := x).
    if (meta.solution !== undefined) {
      // Resolve the constraint RHS through meta solutions so we compare concrete
      // terms, not Meta wrappers. E.g., if rhs is Meta(_7) and _7 is solved to Succ y,
      // we need to compare against Succ y, not Meta(_7).
      let resolvedRhs = normConstraint.rhs;
      while (resolvedRhs.tag === 'Meta') {
        const rhsMeta = newMetaVars.get(resolvedRhs.id);
        if (rhsMeta?.solution) {
          resolvedRhs = rhsMeta.solution;
        } else {
          break;
        }
      }

      if (meta.solution.tag === 'Meta') {
        // Forward constraint to the meta in the solution
        queue.push({ ...normConstraint, meta: meta.solution.id, rhs: resolvedRhs });
      } else {
        // Check for definite structural conflicts (constructor head mismatches
        // or context-verified Var differences).
        // After normalization, both solution and resolvedRhs are at effectiveContext depth.
        // Skip this check if the RHS contains unsolved metas — stuck terms can't be
        // reduced to WHNF, so head comparisons may give false positives.
        if (areTermsDefinitelyDifferent(meta.solution, resolvedRhs, definitions, effectiveContext, effectiveContext)) {
          // Tolerate when pattern-solved meta conflicts with non-pattern constraint,
          // or when the conflict comes from a constant-function heuristic (dummy domains),
          // or when both solutions are compatible constant functions.
          const tolerateConflict =
            (meta.isPatternSolved && normConstraint.isPatternSolution !== true) ||
            normConstraint.isPatternSolution === false ||
            areConstantFunctionsCompatible(meta.solution, resolvedRhs, definitions);
          if (!tolerateConflict) {
            const names = effectiveContext.map(c => c.name).reverse();
            const metaTypeStr = prettyPrint(meta.type, names);
            throw new Error(`Implicit argument conflict for ${normConstraint.meta} : ${metaTypeStr}: inferred ${prettyPrint(meta.solution, names)} but required to be ${prettyPrint(resolvedRhs, names)}`);
          }
        }
        // Var-vs-Var conflict detection.
        // After normalization, both solution and resolvedRhs are at effectiveContext
        // depth, so different indices mean genuinely different variables — with guards:
        //
        // 1. Both indices must be in-scope (< effectiveContext.length). A free variable
        //    (index >= context length) references the outer scope and may alias a
        //    captured variable at a different index.
        //
        // 2. The meta's type must not be Sort. In with-clause contexts, Type-valued
        //    metas often get constraints from pattern wildcards that capture the same
        //    type variable at different indices. Since these wildcards refer to the same
        //    type, the index difference is a false positive.
        //
        // 3. The meta's type must not be an unsolved Meta (too early to check).
        //    Resolve through solved metas first — the type might be Meta(?m0) where
        //    ?m0 has been solved to Nat in this same pass.
        let resolvedMetaType = meta.type;
        while (resolvedMetaType.tag === 'Meta') {
          const typeMeta = newMetaVars.get(resolvedMetaType.id);
          if (typeMeta?.solution) {
            resolvedMetaType = typeMeta.solution;
          } else {
            break;
          }
        }
        if (meta.solution.tag === 'Var' && resolvedRhs.tag === 'Var'
          && meta.solution.index !== resolvedRhs.index
          && resolvedMetaType.tag !== 'Meta'
          && resolvedMetaType.tag !== 'Sort'
          && meta.solution.index < effectiveContext.length
          && resolvedRhs.index < effectiveContext.length) {
          // Both variables must be named (non-wildcard) to be a real conflict.
          // Pattern wildcards (?0, _x, etc.) are flexible — they represent pattern
          // variables that may be unified, not rigid program variables.
          const solBinding = effectiveContext[effectiveContext.length - 1 - meta.solution.index];
          const rhsBinding = effectiveContext[effectiveContext.length - 1 - resolvedRhs.index];
          const isWildcard = (name: string) => name.startsWith('?') || name.startsWith('_');
          const solIsRigid = solBinding && !isWildcard(solBinding.name);
          const rhsIsRigid = rhsBinding && !isWildcard(rhsBinding.name);
          if (solIsRigid && rhsIsRigid) {
            // Type compatibility guard: only flag as a conflict if both Vars have
            // types that match the meta's type. This prevents false positives from
            // imprecise constraint propagation where a Var with a mismatched type
            // (e.g., a Type-valued wildcard) gets propagated as a solution for a
            // Nat-valued meta.
            const solType = getVarTypeFromContext(effectiveContext, meta.solution.index);
            const rhsType = getVarTypeFromContext(effectiveContext, resolvedRhs.index);
            const metaIsConst = resolvedMetaType.tag === 'Const';
            const solTypeMatches = !metaIsConst || !solType || (solType.tag === 'Const' && solType.name === (resolvedMetaType as any).name);
            const rhsTypeMatches = !metaIsConst || !rhsType || (rhsType.tag === 'Const' && rhsType.name === (resolvedMetaType as any).name);
            if (solTypeMatches && rhsTypeMatches) {
              const names = effectiveContext.map(c => c.name).reverse();
              const metaTypeStr = prettyPrint(resolvedMetaType, names);
              throw new Error(`Implicit argument conflict for ${normConstraint.meta} : ${metaTypeStr}: inferred ${prettyPrint(meta.solution, names)} but required to be ${prettyPrint(resolvedRhs, names)}`);
            }
          }
        }
        // Use pattern mode unification for meta decomposition and propagation.
        // E.g., if solution is Succ(?m) and rhs is Succ(x), this creates ?m := x.
        // Both sides are at effectiveContext depth after normalization.
        //
        // Try structural unification FIRST (no definitions/WHNF) to handle cases
        // where both sides have function applications that would become stuck
        // Match expressions after delta reduction (e.g., `plus X Y` vs `plus ?m ?n`).
        // Structural matching can decompose these directly.
        let unifyResult = unifyTerms(meta.solution, resolvedRhs, {
          mode: 'pattern',
          flexibleVars: true,
          definitions: undefined,
        });
        if (!unifyResult.success) {
          // Fall back to full unification with definitions
          unifyResult = unifyTerms(meta.solution, resolvedRhs, {
            mode: 'pattern',
            flexibleVars: true,
            definitions,
          });
        }
        if (!unifyResult.success) {
          // Try case inversion: if the solution is a constructor application and
          // the RHS is a stuck function application (e.g., `Succ(X) vs plus(?m, ?n)`),
          // WHNF the RHS to get a stuck Match and invert through the matching clause.
          const hasUnsolved = containsUnsolvedMeta(resolvedRhs, newMetaVars);
          const invResult = hasUnsolved
            ? tryCaseInversion(meta.solution, resolvedRhs, definitions, newMetaVars, effectiveContext)
            : null;

          if (invResult) {
            // Case inversion succeeded — queue the sub-constraints
            for (const mc of invResult.constraints) {
                queue.push({ ctx: effectiveContext, meta: mc.meta, rhs: mc.rhs });
            }
          } else if (!containsUnsolvedMeta(resolvedRhs, newMetaVars)) {
            // No unsolved metas and no inversion possible.
            // Tolerate conflicts when the meta was solved by pattern unification
            // and this constraint is non-pattern, or when the constraint is a
            // constant-function heuristic (uses dummy lambda domains).
            const tolerateConflict =
              (meta.isPatternSolved && normConstraint.isPatternSolution !== true) ||
              normConstraint.isPatternSolution === false;
            if (tolerateConflict) {
              // Existing solution takes precedence over less-trusted constraint.
              // However, if the pattern solution contains Holes (incomplete from
              // constant-function pattern unification where the body wasn't known)
              // and the new RHS is complete, upgrade to the complete solution.
              // The constant-function heuristic (isPatternSolution: false) often has
              // the correct body while the constant-pattern (isPatternSolution: 'constant')
              // has Holes for unknown positions.
              if (termContainsHole(meta.solution) && !termContainsHole(resolvedRhs)
                && canSolveMetaInContext(resolvedRhs, effectiveContext.length)) {
                newMetaVars.set(normConstraint.meta, { ...meta, solution: resolvedRhs, ctx: effectiveContext });
              }
            } else if (!areConstantFunctionsCompatible(meta.solution, resolvedRhs, definitions)) {
              // Real conflict — terms are not even compatible as constant functions
              const names = effectiveContext.map(c => c.name).reverse();
              const metaTypeStr = prettyPrint(meta.type, names);
              throw new Error(`Implicit argument conflict for ${normConstraint.meta} : ${metaTypeStr}: inferred ${prettyPrint(meta.solution, names)} but required to be ${prettyPrint(resolvedRhs, names)}`);
            }
          } else {
            // RHS has unsolved metas AND inversion failed.
            // Defer for post-pass: after the main loop, metas that were unsolved
            // during this pass may now be solved, allowing conflict detection.
            const tolerateConflict =
              (meta.isPatternSolved && normConstraint.isPatternSolution !== true) ||
              normConstraint.isPatternSolution === false;
            if (!tolerateConflict) {
              deferredConflicts.push({ constraint: { ...normConstraint, rhs: resolvedRhs }, effectiveContext });
            }
          }
        } else {
          // Queue any new meta constraints from the unification.
          // These inherit effectiveContext as their ctx — when dequeued, they'll
          // be re-normalized to the TARGET meta's effective context.
          for (const mc of unifyResult.metaConstraints) {
            queue.push({ ctx: effectiveContext, meta: mc.meta, rhs: mc.rhs });
          }
          // If the existing solution contains Holes (incomplete from constant-function
          // pattern unification) and the new RHS doesn't, upgrade to the complete solution.
          // The successful unification above confirms structural compatibility.
          if (termContainsHole(meta.solution) && !termContainsHole(resolvedRhs)
            && canSolveMetaInContext(resolvedRhs, effectiveContext.length)) {
            newMetaVars.set(normConstraint.meta, { ...meta, solution: resolvedRhs, ctx: effectiveContext });
          }
        }
      }
      continue;
    }

    // No solution yet: try to solve
    if (canSolveMetaInContext(normConstraint.rhs, effectiveContext.length)) {
      // Type compatibility check: if rhs is a Var, check that its type is compatible
      // with the meta's type. This catches cases where an inductive has {A : Type}
      // but a constructor has {A : Type u} with a bound level variable.
      if (normConstraint.rhs.tag === 'Var') {
        const rhsType = getVarTypeFromContext(effectiveContext, normConstraint.rhs.index);
        if (rhsType) {
          const typeError = checkTypeCompatibility(meta.type, rhsType);
          if (typeError) {
            throw new Error(`Type mismatch for meta ${normConstraint.meta}: ${typeError}`);
          }
        }
      }
      // Type check for Sort: if rhs is a Sort, its type is Sort(level+1).
      // Check that Sort(level+1) matches the meta's type exactly.
      // This catches cases where we try to solve ?A : Type with Type (which has type Type 1, not Type).
      // Skip this check if the meta's type contains unsolved metas - we can't determine the correct
      // universe level until those metas are solved.
      if (normConstraint.rhs.tag === 'Sort' && !termContainsMeta(meta.type)) {
        const rhsType: TTKTerm = { tag: 'Sort', level: mkLSucc(normConstraint.rhs.level) };
        if (!isDefinitionallyEqual(meta.type, rhsType)) {
          const names = effectiveContext.map(c => c.name).reverse();
          throw new Error(`Universe level mismatch for meta ${normConstraint.meta} : ${prettyPrint(meta.type, names)}: cannot solve with ${prettyPrint(normConstraint.rhs, names)} which has type ${prettyPrint(rhsType, names)}`);
        }
      }
      const isPatternSolved = (normConstraint.isPatternSolution === true || normConstraint.isPatternSolution === 'constant') ? true : meta.isPatternSolved;
      newMetaVars.set(normConstraint.meta, { ...meta, solution: normConstraint.rhs, ctx: effectiveContext, isPatternSolved });

      // If this is a "hole:" prefixed constraint, also copy the solution to the plain ID
      // This is needed because registerHolesInTermAsMetas creates two meta entries:
      // one with the plain ID (used by zonking) and one with "hole:" prefix (used by unification)
      if (normConstraint.meta.startsWith('hole:')) {
        const plainId = normConstraint.meta.slice(5); // Remove "hole:" prefix
        const plainMeta = newMetaVars.get(plainId);
        if (plainMeta && !plainMeta.solution) {
          newMetaVars.set(plainId, { ...plainMeta, solution: normConstraint.rhs, ctx: effectiveContext, isPatternSolved });
        }
      }
    } else {
      stillStuck.push(constraint); // original constraint, retains original ctx for future attempts
    }
  }

  // Post-pass: re-check deferred constraints with updated meta solutions.
  // Metas that were unsolved during the main pass may now have solutions,
  // enabling us to detect conflicts that were previously hidden.
  if (definitions) {
    for (const { constraint: dc, effectiveContext: dcCtx } of deferredConflicts) {
      const meta = newMetaVars.get(dc.meta);
      if (!meta?.solution) continue;

      // Zonk both sides to substitute any metas solved during the main pass
      const zonkedSol = zonkWithMetas(meta.solution, newMetaVars);
      const zonkedRhs = zonkWithMetas(dc.rhs, newMetaVars);

      // If both sides still contain unsolved metas after zonking,
      // skip — we can't make a definitive judgment yet
      if (containsUnsolvedMeta(zonkedSol, newMetaVars) && containsUnsolvedMeta(zonkedRhs, newMetaVars)) {
        continue;
      }

      // Check for Pi vs non-Pi conflict caused by under-application.
      // The key signal is: one side is fully resolved and NOT a Pi (its WHNF is final),
      // while the other side IS a Pi AND still contains unsolved metas.
      //
      // The unsolved metas in the Pi side are a strong signal of under-application:
      // the user forgot to provide some argument, leaving a function type (Pi) where
      // a value type was expected. The missing argument's meta remains unsolved.
      //
      // When both sides are fully resolved but disagree, we do NOT throw — this can
      // happen from spurious APP decomposition constraints where a meta gets a wrong
      // solution (e.g., DPair.fst projection vs function type from overflow args).
      // These spurious conflicts don't cause type errors because the "wrong" solution
      // is never used in a way that matters.
      const solHasUnsolved = containsUnsolvedMeta(zonkedSol, newMetaVars);
      const rhsHasUnsolved = containsUnsolvedMeta(zonkedRhs, newMetaVars);
      const wSol = whnf(zonkedSol, { definitions });
      const wRhs = whnf(zonkedRhs, { definitions });

      const isPi = (t: TTKTerm) => t.tag === 'Binder' && t.binderKind.tag === 'BPi';
      if ((!solHasUnsolved && !isPi(wSol) && isPi(wRhs) && rhsHasUnsolved) ||
          (!rhsHasUnsolved && !isPi(wRhs) && isPi(wSol) && solHasUnsolved)) {
        const names = dcCtx.map(c => c.name).reverse();
        const metaTypeStr = prettyPrint(meta.type, names);
        throw new Error(`Implicit argument conflict for ${dc.meta} : ${metaTypeStr}: inferred ${prettyPrint(zonkedSol, names)} but required to be ${prettyPrint(zonkedRhs, names)}`);
      }
    }
  }

  return { constraints: stillStuck, metaVars: newMetaVars };
}

/** Check if a term contains any Hole nodes (incomplete solutions from pattern unification) */
function termContainsHole(term: TTKTerm): boolean {
  switch (term.tag) {
    case 'Hole': return true;
    case 'Var': case 'Const': case 'Meta': return false;
    case 'Sort': return termContainsHole(term.level);
    case 'App': return termContainsHole(term.fn) || termContainsHole(term.arg);
    case 'Binder':
      return termContainsHole(term.domain) || termContainsHole(term.body) ||
        (term.binderKind.tag === 'BLet' && termContainsHole(term.binderKind.defVal));
    case 'Match':
      return termContainsHole(term.scrutinee) || term.clauses.some(c => termContainsHole(c.rhs));
    default: return false;
  }
}

function termContainsMeta(term: TTKTerm): boolean {
  switch (term.tag) {
    case 'Meta':
      return true;
    case 'Var':
    case 'Const':
    case 'Hole':
      return false;
    case 'Sort':
      return termContainsMeta(term.level);
    case 'App':
      return termContainsMeta(term.fn) || termContainsMeta(term.arg);
    case 'Binder':
      return termContainsMeta(term.domain) || termContainsMeta(term.body) ||
        (term.binderKind.tag === 'BLet' && termContainsMeta(term.binderKind.defVal));
    case 'Annot':
      return termContainsMeta(term.term) || termContainsMeta(term.type);
    case 'Match':
      return termContainsMeta(term.scrutinee) ||
        term.clauses.some(c => c.patterns.some(p => patternContainsMeta(p)) || termContainsMeta(c.rhs));
    default:
      return false;
  }
}

function patternContainsMeta(pattern: TTKPattern): boolean {
  switch (pattern.tag) {
    case 'PVar':
    case 'PWild':
      return false;
    case 'PCtor':
      return pattern.args.some(a => patternContainsMeta(a));
    default:
      return false;
  }
}

export function canSolveMeta(meta: MetaVar, rhs: TTKTerm): boolean {
  return canSolveMetaInContext(rhs, meta.ctx.length);
}

/** Count the total number of variables bound by patterns in a clause */
function countPatternVarsInClause(patterns: TTKPattern[]): number {
  let count = 0;
  for (const p of patterns) count += countPatternVarsInPattern(p);
  return count;
}

function countPatternVarsInPattern(pattern: TTKPattern): number {
  switch (pattern.tag) {
    case 'PVar':
    case 'PWild':
      return 1;
    case 'PCtor':
      return pattern.args.reduce((sum, p) => sum + countPatternVarsInPattern(p), 0);
  }
}

function canSolveMetaInContext(rhs: TTKTerm, contextLength: number): boolean {
  return maxFreeVarIndex(rhs) < contextLength;
}

function maxFreeVarIndex(term: TTKTerm): number {
  return maxFreeVarIndexAt(term, 0)
}

function maxFreeVarIndexAt(term: TTKTerm, depth: number): number {
  switch (term.tag) {
    case 'Var':
      return term.index >= depth ? term.index - depth : -1;
    case 'Sort':
    case 'Const':
      return -1;
    case 'Binder':
      if (term.binderKind.tag === 'BLet') {
        // In Let, defVal is at depth, body is at depth+1
        return Math.max(
          maxFreeVarIndexAt(term.domain, depth),
          maxFreeVarIndexAt(term.binderKind.defVal, depth),
          maxFreeVarIndexAt(term.body, depth + 1)
        );
      } else {
        // Pi, Lam, etc.
        return Math.max(
          maxFreeVarIndexAt(term.domain, depth),
          maxFreeVarIndexAt(term.body, depth + 1)
        );
      }
    case 'App':
      return Math.max(
        maxFreeVarIndexAt(term.fn, depth),
        maxFreeVarIndexAt(term.arg, depth),
      );
    case 'Hole':
    case 'Meta':
      return -Infinity; // No free variables
    case 'Annot':
      return Math.max(maxFreeVarIndexAt(term.term, depth), maxFreeVarIndexAt(term.type, depth));
    case 'Match':
      return Math.max(maxFreeVarIndexAt(term.scrutinee, depth), ...term.clauses.map(c => {
        const patVars = countPatternVarsInClause(c.patterns);
        return maxFreeVarIndexAt(c.rhs, depth + patVars);
      }));

    case 'ULevel':
    case 'ULit':
    case 'UOmega':
      return -1;
  }
}
