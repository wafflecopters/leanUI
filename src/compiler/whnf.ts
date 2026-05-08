import { TTKTerm, TTKPattern, TTKContext, isDefinitionallyEqual, levelsEqual, prettyPrint } from "./kernel";
import { subst, substPatternBindings, shiftTerm, minFreeVarIndex } from "./subst";
import { DefinitionsMap, getTermDefinition, RecordInfo, extractAppSpine } from "./term";

/**
 * Context for weak head normal form reduction.
 */
export type WhnfContext = {
  definitions?: DefinitionsMap;
  typingContext?: TTKContext;  // For ζ-reduction of Var nodes (let-binding values)
  fuel?: number;  // Prevent infinite reduction, default 1000
  deltaDepth?: number;  // Limit depth of δ-reduction (definition unfolding)
}

const DEFAULT_FUEL = 1000;
const DEFAULT_DELTA_DEPTH = 100;  // Limit definition unfolding depth

/**
 * Check if a variable index is free in a term.
 */
function isFreeIn(index: number, term: TTKTerm): boolean {
  switch (term.tag) {
    case 'Var':
      return term.index === index;
    case 'Sort':
    case 'Const':
    case 'Hole':
    case 'Meta':
      return false;
    case 'App':
      return isFreeIn(index, term.fn) || isFreeIn(index, term.arg);
    case 'Binder':
      if (isFreeIn(index, term.domain)) return true;
      if (isFreeIn(index + 1, term.body)) return true;
      if (term.binderKind.tag === 'BLet') {
        return isFreeIn(index, term.binderKind.defVal);
      }
      return false;
    case 'Annot':
      return isFreeIn(index, term.term) || isFreeIn(index, term.type);

    case 'Match':
      if (isFreeIn(index, term.scrutinee)) return true;
      for (const clause of term.clauses) {
        if (isFreeIn(index, clause.rhs)) return true;
      }
      return false;

    case 'ULevel':
    case 'ULit':
    case 'UOmega':
    case 'NatLit':
      return false;
  }
}

// ============================================================================
// Pattern Matching Helpers (for ι-reduction)
// ============================================================================

/**
 * Collect an application spine: `f a1 a2 a3` -> { head: f, args: [a1, a2, a3] }
 */
function collectAppSpine(term: TTKTerm): { head: TTKTerm; args: TTKTerm[] } {
  const args: TTKTerm[] = [];
  let current = term;
  while (current.tag === 'App') {
    args.unshift(current.arg);
    current = current.fn;
  }
  return { head: current, args };
}

/**
 * Try to match a pattern against a term.
 * Returns bindings array (in pattern order) if successful, null otherwise.
 * Bindings are returned in left-to-right pattern variable order.
 */
function matchPattern(pattern: TTKPattern, term: TTKTerm, ctx?: WhnfContext): TTKTerm[] | null {
  switch (pattern.tag) {
    case 'PVar':
      // Variable always matches, binds the term
      return [term];
    case 'PWild':
      // Wildcard matches but does NOT produce a binding.
      // Pattern-matching functions (compiled via checkTermValue) use RHS de Bruijn indices
      // relative to PVar bindings ONLY. Record projections must also follow this convention
      // (see buildProjectionValue in record.ts which uses Var(0) for the single PVar).
      return [];

    case 'PCtor': {
      // Reduce term to whnf and collect spine
      const reduced = whnf(term, ctx);
      const { head, args } = collectAppSpine(reduced);

      // Constructor pattern matches if head is same constructor
      if (head.tag !== 'Const' || head.name !== pattern.name) {
        return null;
      }

      // Match each pattern argument against the corresponding term argument
      return matchPatterns(pattern.args, args, ctx);
    }
  }
}

/**
 * Match multiple patterns against multiple terms.
 * Returns concatenated bindings if all match, null otherwise.
 */
function matchPatterns(patterns: TTKPattern[], terms: TTKTerm[], ctx?: WhnfContext): TTKTerm[] | null {
  if (patterns.length !== terms.length) {
    return null;
  }

  const allBindings: TTKTerm[] = [];
  for (let i = 0; i < patterns.length; i++) {
    const bindings = matchPattern(patterns[i], terms[i], ctx);
    if (bindings === null) {
      return null;
    }
    allBindings.push(...bindings);
  }
  return allBindings;
}

// ============================================================================
// Record Eta Helpers
// ============================================================================

/**
 * Get record info for a constructor name.
 * Returns the inductive definition with recordInfo if the constructor belongs to a record.
 */
function getRecordInfoForConstructor(ctorName: string, definitions?: DefinitionsMap): {
  inductiveName: string;
  recordInfo: RecordInfo;
  ctorName: string;
} | null {
  if (!definitions) return null;

  const inductiveName = definitions.inductiveNameOfConstructor.get(ctorName);
  if (!inductiveName) return null;

  const inductive = definitions.inductiveTypes.get(inductiveName);
  if (!inductive?.recordInfo) return null;

  return {
    inductiveName,
    recordInfo: inductive.recordInfo,
    ctorName,
  };
}

/**
 * Try to extract the eta target from a record constructor application.
 *
 * For a term like `MkPoint (Point.x p) (Point.y p)`, extracts `p`.
 *
 * The record eta rule: MkR (R.f1 r) (R.f2 r) ... (R.fN r) ≃ r
 *
 * Returns the common eta target term if the pattern matches, null otherwise.
 */
function tryRecordEtaContract(term: TTKTerm, definitions?: DefinitionsMap): TTKTerm | null {
  if (!definitions) return null;

  // Collect application spine
  const { fn: head, args } = extractAppSpine(term);

  // Head must be a constructor constant
  if (head.tag !== 'Const') return null;

  // Look up if this constructor belongs to a record
  const recordData = getRecordInfoForConstructor(head.name, definitions);
  if (!recordData) return null;

  const { recordInfo } = recordData;
  const { projections, paramCount } = recordInfo;

  // The constructor takes paramCount type arguments + numFields field arguments
  const numFields = projections.length;
  const expectedArgCount = paramCount + numFields;

  if (args.length !== expectedArgCount) return null;

  // Skip type arguments, check field arguments
  const fieldArgs = args.slice(paramCount);

  // Each field arg should be a projection applied to the same common term
  let commonTarget: TTKTerm | null = null;

  for (let i = 0; i < numFields; i++) {
    const fieldArg = fieldArgs[i];
    const expectedProjName = projections[i];

    // Extract the target from projection application
    const target = extractProjectionTarget(fieldArg, expectedProjName, paramCount, definitions);
    if (target === null) return null;

    if (commonTarget === null) {
      commonTarget = target;
    } else {
      // All fields must project from the same target
      if (!isDefinitionallyEqual(commonTarget, target)) return null;
    }
  }

  return commonTarget;
}

/**
 * Check if a term is a projection application and extract the target.
 *
 * For `Point.x p`, returns `p`.
 * For `Pair.fst A B p`, returns `p`.
 *
 * @param term - The term to check
 * @param projName - Expected projection name (e.g., "Point.x")
 * @param numTypeArgs - Number of type arguments the projection takes before the record arg
 * @param definitions - Definitions map to look up projection arity
 */
function extractProjectionTarget(
  term: TTKTerm,
  projName: string,
  numTypeArgs: number,
  _definitions: DefinitionsMap
): TTKTerm | null {
  // Collect application spine
  const { fn: head, args } = extractAppSpine(term);

  // Head must be the expected projection constant
  if (head.tag !== 'Const' || head.name !== projName) return null;

  // Projection has signature: (type args...) -> R ... -> field_type
  // So it takes numTypeArgs type arguments plus 1 record argument
  const expectedArgCount = numTypeArgs + 1;

  if (args.length !== expectedArgCount) return null;

  // The last argument is the record target
  return args[args.length - 1];
}

// ============================================================================
// Definitional Equality
// ============================================================================

/**
 * Check if two types are definitionally equal.
 *
 * Implements:
 * - β-reduction: (λx. e) a ≃ e[a/x]
 * - ζ-reduction: let x := t; u ≃ u[t/x]
 * - η-conversion: λx. f x ≃ f (when x not free in f)
 * - record η: MkR (R.f1 r) ... (R.fN r) ≃ r
 * - δ-reduction: unfold definitions
 * - ι-reduction: pattern matching on constructors
 */
export function areTypesDefEq(t1: TTKTerm, t2: TTKTerm, definitions?: DefinitionsMap, typingContext?: TTKContext): boolean {
  // Check record eta BEFORE normalization (projections get unfolded by whnf)
  // Record eta: MkR (R.f1 r) ... (R.fN r) ≃ r
  const eta1 = tryRecordEtaContract(t1, definitions);
  if (eta1 !== null) {
    if (areTypesDefEq(eta1, t2, definitions, typingContext)) {
      return true;
    }
  }

  const eta2 = tryRecordEtaContract(t2, definitions);
  if (eta2 !== null) {
    if (areTypesDefEq(t1, eta2, definitions, typingContext)) {
      return true;
    }
  }

  const ctx: WhnfContext = { definitions, typingContext };
  // Normalize both terms
  const n1 = whnf(t1, ctx);
  const n2 = whnf(t2, ctx);
  return areWhnfTypesDefEq(n1, n2, definitions, typingContext);
}

export function areWhnfTypesDefEq(n1: TTKTerm, n2: TTKTerm, definitions?: DefinitionsMap, typingContext?: TTKContext): boolean {
  // Record eta can become visible only after δ/β/ι reduction.
  // Example: `id2 p` WHNFs to `MkPoint (Point.x p) (Point.y p)`, which should
  // contract to `p` even though the original term was not constructor-headed.
  const eta1 = tryRecordEtaContract(n1, definitions);
  if (eta1 !== null) {
    if (areTypesDefEq(eta1, n2, definitions, typingContext)) {
      return true;
    }
  }

  const eta2 = tryRecordEtaContract(n2, definitions);
  if (eta2 !== null) {
    if (areTypesDefEq(n1, eta2, definitions, typingContext)) {
      return true;
    }
  }

  // Quick structural check first
  if (isDefinitionallyEqual(n1, n2)) {
    return true;
  }

  // Eta conversion for lambdas
  //
  // Two rules:
  // 1. Eta contraction (fast path): lam x. f x = f (when x not free in f)
  // 2. Eta expansion (general): lam x. body = f  iff  body = App(shift(f,1,0), Var(0))
  //    (when one side is a lambda and the other is not, eta-expand the non-lambda)
  //
  // Rule 2 subsumes rule 1, but we keep rule 1 as a fast path.

  if (n1.tag === 'Binder' && n1.binderKind.tag === 'BLam') {
    // Fast path: eta contraction (lam x. f x = f when x not in FV(f))
    if (n1.body.tag === 'App' && n1.body.arg.tag === 'Var' && n1.body.arg.index === 0) {
      if (!isFreeIn(0, n1.body.fn)) {
        const contracted = subst(0, { tag: 'Var', index: 0 }, n1.body.fn);
        return areTypesDefEq(contracted, n2, definitions, typingContext);
      }
    }
    // General eta expansion: if n2 is NOT a lambda, eta-expand n2
    // lam x. body = f  iff  body = App(shift(f,1,0), Var(0))
    if (!(n2.tag === 'Binder' && n2.binderKind.tag === 'BLam')) {
      const expandedN2Body: TTKTerm = {
        tag: 'App',
        fn: shiftTerm(n2, 1, 0),
        arg: { tag: 'Var', index: 0 },
      };
      const bodyCtx = typingContext
        ? [...typingContext, { name: n1.name, type: n1.domain }]
        : undefined;
      return areTypesDefEq(n1.body, expandedN2Body, definitions, bodyCtx);
    }
  }

  // Symmetric case: n2 is lambda, n1 is not
  if (n2.tag === 'Binder' && n2.binderKind.tag === 'BLam') {
    // Fast path: eta contraction
    if (n2.body.tag === 'App' && n2.body.arg.tag === 'Var' && n2.body.arg.index === 0) {
      if (!isFreeIn(0, n2.body.fn)) {
        const contracted = subst(0, { tag: 'Var', index: 0 }, n2.body.fn);
        return areTypesDefEq(n1, contracted, definitions, typingContext);
      }
    }
    // General eta expansion: eta-expand n1
    if (!(n1.tag === 'Binder' && n1.binderKind.tag === 'BLam')) {
      const expandedN1Body: TTKTerm = {
        tag: 'App',
        fn: shiftTerm(n1, 1, 0),
        arg: { tag: 'Var', index: 0 },
      };
      const bodyCtx = typingContext
        ? [...typingContext, { name: n2.name, type: n2.domain }]
        : undefined;
      return areTypesDefEq(expandedN1Body, n2.body, definitions, bodyCtx);
    }
  }

  // Deep structural comparison after normalization
  switch (n1.tag) {
    case 'Var':
      return n2.tag === 'Var' && n1.index === n2.index;

    case 'Sort':
      return n2.tag === 'Sort' && levelsEqual(n1.level, n2.level);

    case 'Const':
      return n2.tag === 'Const' && n1.name === n2.name;

    case 'Binder': {
      if (n2.tag !== 'Binder' || n1.binderKind.tag !== n2.binderKind.tag) {
        return false;
      }
      if (!areTypesDefEq(n1.domain, n2.domain, definitions, typingContext)) return false;
      // Extend typing context when comparing under binders so that Var indices
      // in the body are correctly mapped to context entries
      const letValue = n1.binderKind.tag === 'BLet' ? (n1.binderKind as { tag: 'BLet'; defVal: TTKTerm }).defVal : undefined;
      const bodyCtx = typingContext
        ? [...typingContext, { name: n1.name, type: n1.domain, value: letValue }]
        : undefined;
      if (!areTypesDefEq(n1.body, n2.body, definitions, bodyCtx)) return false;
      if (n1.binderKind.tag === 'BLet' && n2.binderKind.tag === 'BLet') {
        return areTypesDefEq(n1.binderKind.defVal, n2.binderKind.defVal, definitions, typingContext);
      }
      return true;
    }

    case 'App':
      return n2.tag === 'App' &&
        areTypesDefEq(n1.fn, n2.fn, definitions, typingContext) &&
        areTypesDefEq(n1.arg, n2.arg, definitions, typingContext);

    case 'Hole':
      return n2.tag === 'Hole' && n1.id === n2.id;

    case 'Meta':
      return n2.tag === 'Meta' && n1.id === n2.id;

    case 'Annot':
      return areTypesDefEq(n1.term, n2, definitions, typingContext);

    case 'Match':
      if (n2.tag !== 'Match') return false;
      if (!areTypesDefEq(n1.scrutinee, n2.scrutinee, definitions, typingContext)) return false;
      if (n1.clauses.length !== n2.clauses.length) return false;
      for (let i = 0; i < n1.clauses.length; i++) {
        if (!areTypesDefEq(n1.clauses[i].rhs, n2.clauses[i].rhs, definitions, typingContext)) return false;
      }
      return true;

    case 'ULevel':
      return n2.tag === 'ULevel';

    case 'ULit':
      return n2.tag === 'ULit' && n1.n === n2.n;

    case 'UOmega':
      return n2.tag === 'UOmega';

    case 'NatLit':
      return n2.tag === 'NatLit' && n1.value === n2.value;
  }
}

// ============================================================================
// Weak Head Normal Form
// ============================================================================

/**
 * Reduce a term to weak head normal form.
 *
 * Implements:
 * - β-reduction: (λx. t) s → t[x := s]
 * - ζ-reduction: let x := v in t → t[x := v]
 * - δ-reduction: unfold named constants to their definitions
 * - ι-reduction: reduce pattern matching when scrutinee is a constructor
 */
export function whnf(term: TTKTerm, ctx?: WhnfContext): TTKTerm {
  // Check fuel to prevent infinite reduction
  const fuel = ctx?.fuel ?? DEFAULT_FUEL;
  if (fuel <= 0) {
    return term;
  }
  const deltaDepth = ctx?.deltaDepth ?? DEFAULT_DELTA_DEPTH;
  const nextCtx: WhnfContext = { ...ctx, fuel: fuel - 1, deltaDepth };

  switch (term.tag) {
    case 'Var': {
      // ζ-reduction for variables: if the variable refers to a let-binding
      // in the typing context, reduce to its value
      if (ctx?.typingContext) {
        const D = ctx.typingContext.length;
        const entryIndex = D - 1 - term.index;
        if (entryIndex >= 0 && entryIndex < D) {
          const entry = ctx.typingContext[entryIndex];
          if (entry?.value) {
            // Shift value to current context depth: the value was stored at
            // context depth entryIndex, so shift by (term.index + 1)
            const shifted = shiftTerm(entry.value, term.index + 1, 0);
            return whnf(shifted, nextCtx);
          }
        }
      }
      return term;
    }

    case 'App': {
      const fn = whnf(term.fn, nextCtx);
      if (fn.tag === 'Binder' && fn.binderKind.tag === 'BLam') {
        // β-reduction: (λx. t) s → t[x := s]
        return whnf(subst(0, term.arg, fn.body), nextCtx);
      }
      // δ-reduction: If fn is a Const with a Match definition, try ι-reduction
      // Check deltaDepth to limit unfolding
      if (fn.tag === 'Const' && ctx?.definitions && deltaDepth > 0) {
        const def = getTermDefinition(ctx.definitions, fn.name);
        if (def?.value?.tag === 'Match') {
          // We have `f a` where f is defined by pattern matching
          // Try to reduce Match by applying the argument
          const matchTerm = def.value;
          return whnf({
            tag: 'App',
            fn: matchTerm,
            arg: term.arg
          }, { ...nextCtx, deltaDepth: deltaDepth - 1 });
        }
      }
      // Build the full application and check if head is a Match term
      // This handles nested applications like App(App(Match, arg1), arg2)
      const fullApp: TTKTerm = { tag: 'App', fn, arg: term.arg };
      const { head, args } = collectAppSpine(fullApp);

      if (head.tag === 'Match') {
        // Try to match against clauses with all accumulated arguments
        for (const clause of head.clauses) {
          if (clause.patterns.length <= args.length) {
            // When ALL patterns are PVar/PWild (a trivial catch-all clause, as
            // generated for type alias definitions like EpsDeltaWitness),
            // skip WHNF-reducing the args before binding. Reducing them is
            // unnecessary (PVar matches anything) and destructive: it
            // aggressively delta-reduces user-level names like `rdiv`, `rtwo`
            // into internal forms the rendering pipeline can't fold back.
            // For clauses with any PCtor, we still reduce all args — some
            // downstream type operations depend on the reduced forms.
            const allPVar = clause.patterns.every(p => p.tag === 'PVar' || p.tag === 'PWild');
            const reducedArgs = allPVar
              ? args.slice(0, clause.patterns.length)
              : args.slice(0, clause.patterns.length).map(
                  arg => whnf(arg, nextCtx)
                );
            const bindings = matchPatterns(clause.patterns, reducedArgs, nextCtx);
            if (bindings !== null) {
              // Found a match! Substitute bindings into rhs
              let result = substPatternBindings(bindings, clause.rhs);
              // Apply remaining arguments
              for (let i = clause.patterns.length; i < args.length; i++) {
                result = { tag: 'App', fn: result, arg: args[i] };
              }
              return whnf(result, nextCtx);
            }
          }
        }
        // No clause matched - return with reduced fn
        return fullApp;
      }
      return fullApp;
    }

    case 'Binder': {
      if (term.binderKind.tag === 'BLet') {
        // ζ-reduction: let x := v in t → t[x := v]
        return whnf(subst(0, term.binderKind.defVal, term.body), nextCtx);
      }
      return term;
    }

    case 'Const': {
      // δ-reduction: unfold named constants
      // Check deltaDepth to limit unfolding and prevent exponential expansion
      if (ctx?.definitions && deltaDepth > 0) {
        const def = getTermDefinition(ctx.definitions, term.name);
        if (def?.value) {
          return whnf(def.value, { ...nextCtx, deltaDepth: deltaDepth - 1 });
        }
      }
      return term;
    }

    case 'Match': {
      // ι-reduction: reduce pattern matching when scrutinee is a constructor
      const scrut = whnf(term.scrutinee, nextCtx);

      // NatLit iota-view: when scrutinee is a NatLit and the Match's clauses
      // use constructor patterns from a registered @impl=nat type, expand the
      // literal so iota can fire normally.
      //   NatLit 0       → Const(zeroCtor)
      //   NatLit (n+1)   → App(Const(succCtor), NatLit n)
      // This is the only "domain-aware" rule in the kernel — but it's
      // user-driven via @impl=nat annotation, never hardcoded ctor names.
      if (scrut.tag === 'NatLit' && ctx?.definitions?.natImplByCtor) {
        const reg = ctx.definitions.natImplByCtor;
        let impl = null;
        for (const clause of term.clauses) {
          const pat = clause.patterns[0];
          if (pat?.tag === 'PCtor') {
            const found = reg.get(pat.name);
            if (found) { impl = found; break; }
          }
        }
        if (impl) {
          let expanded: TTKTerm;
          if (scrut.value === 0n) {
            expanded = { tag: 'Const', name: impl.zeroCtor };
          } else {
            expanded = {
              tag: 'App',
              fn: { tag: 'Const', name: impl.succCtor },
              arg: { tag: 'NatLit', value: scrut.value - 1n },
            };
          }
          return whnf({ tag: 'Match', scrutinee: expanded, clauses: term.clauses }, nextCtx);
        }
      }

      // Pattern matching should only reduce when the scrutinee is a known value.
      // When the scrutinee is unknown (Hole, Var, Meta), the match is "stuck" and
      // should not reduce. This is a fundamental rule in type theory: we can't
      // perform pattern matching until we know what value we're matching against.
      //
      // Note: In our encoding, Match terms with Hole scrutinees represent pattern
      // parameters in function definitions. These should only reduce when applied
      // to arguments (handled by the App case above).
      if (scrut.tag === 'Hole' || scrut.tag === 'Meta' || scrut.tag === 'Var') {
        return { tag: 'Match', scrutinee: scrut, clauses: term.clauses };
      }

      // Try to find a matching clause
      for (const clause of term.clauses) {
        if (clause.patterns.length === 0) {
          // No patterns - this clause always matches (shouldn't happen in well-formed terms)
          continue;
        }

        const bindings = matchPattern(clause.patterns[0], scrut, nextCtx);
        if (bindings !== null) {
          // Found a match! Substitute bindings into rhs
          const result = substPatternBindings(bindings, clause.rhs);
          return whnf(result, nextCtx);
        }
      }

      // No clause matched - return Match with reduced scrutinee
      return { tag: 'Match', scrutinee: scrut, clauses: term.clauses };
    }

    case 'Annot':
      // Strip annotations
      return whnf(term.term, nextCtx);

    default:
      return term;
  }
}

/**
 * Count Pi binders in a term, using WHNF to unfold type aliases.
 * Unlike `countPiBinders` in term.ts which only counts syntactic Pis,
 * this version delta-reduces definitions like `Not A = A -> Void` to
 * expose hidden Pi binders.
 */
export function countPiBindersWhnf(term: TTKTerm, definitions: DefinitionsMap): number {
  let count = 0;
  let current = whnf(term, { definitions });
  while (current.tag === 'Binder' && current.binderKind.tag === 'BPi') {
    count++;
    current = whnf(current.body, { definitions });
  }
  return count;
}

/**
 * WHNF-reduce a term and assert it's a Pi type.
 * Used in pattern matching where the check type may be a type alias
 * that needs unfolding to expose the Pi structure.
 */
export function whnfToPi(term: TTKTerm, definitions: DefinitionsMap): TTKTerm & { tag: 'Binder'; binderKind: { tag: 'BPi' } } {
  const reduced = whnf(term, { definitions });
  if (reduced.tag !== 'Binder' || reduced.binderKind.tag !== 'BPi') {
    throw new Error(`Expected Pi type after WHNF, got: ${prettyPrint(reduced)}`);
  }
  return reduced as TTKTerm & { tag: 'Binder'; binderKind: { tag: 'BPi' } };
}

/**
 * Deep normalization: recursively applies WHNF to all subterms.
 * Reduces beta (lambda application), delta (definition unfolding),
 * and iota (match/pattern reduction) at every position.
 *
 * Use with full definitions to normalize terms like `plus(Succ(x0), Zero)`
 * into `Succ(plus(x0, Zero))`. Use with empty definitions for beta+iota only.
 */
export function fullNormalize(term: TTKTerm, definitions: DefinitionsMap, fuel = 50): TTKTerm {
  if (fuel <= 0) return term;

  const reduced = whnf(term, { definitions, fuel: 200 });

  switch (reduced.tag) {
    case 'Var':
    case 'Const':
    case 'Hole':
    case 'Meta':
    case 'ULevel':
    case 'ULit':
    case 'UOmega':
    case 'NatLit':
      return reduced;

    case 'Sort':
      return { tag: 'Sort', level: fullNormalize(reduced.level, definitions, fuel - 1) };

    case 'App': {
      const args: TTKTerm[] = [];
      let head = reduced as TTKTerm;
      while (head.tag === 'App') {
        args.unshift(head.arg);
        head = head.fn;
      }
      const normArgs = args.map(a => fullNormalize(a, definitions, fuel - 1));
      let result: TTKTerm = head;
      for (const a of normArgs) {
        result = { tag: 'App', fn: result, arg: a };
      }
      const re = whnf(result, { definitions, fuel: 200 });
      if (re !== result && re.tag !== 'App') {
        return fullNormalize(re, definitions, fuel - 1);
      }
      return re !== result ? re : result;
    }

    case 'Binder': {
      const domain = fullNormalize(reduced.domain, definitions, fuel - 1);
      const body = fullNormalize(reduced.body, definitions, fuel - 1);
      if (reduced.binderKind.tag === 'BLet') {
        const defVal = fullNormalize(reduced.binderKind.defVal, definitions, fuel - 1);
        return { ...reduced, domain, body, binderKind: { tag: 'BLet', defVal } };
      }
      return { ...reduced, domain, body };
    }

    case 'Annot':
      return fullNormalize(reduced.term, definitions, fuel - 1);

    case 'Match': {
      const scrutinee = fullNormalize(reduced.scrutinee, definitions, fuel - 1);
      const match: TTKTerm = { tag: 'Match', scrutinee, clauses: reduced.clauses };
      const re = whnf(match, { definitions, fuel: 200 });
      if (re.tag !== 'Match') {
        return fullNormalize(re, definitions, fuel - 1);
      }
      return match;
    }
  }
}
