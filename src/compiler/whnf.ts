import { TTKTerm, TTKPattern, isDefinitionallyEqual, levelsEqual } from "./kernel";
import { subst, substPatternBindings } from "./subst";
import { DefinitionsMap, getTermDefinition } from "./term";

/**
 * Context for weak head normal form reduction.
 */
export type WhnfContext = {
  definitions?: DefinitionsMap;
  fuel?: number;  // Prevent infinite reduction, default 1000
}

const DEFAULT_FUEL = 1000;

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
    case 'PWild':
      // Variable/wildcard always matches, binds the term
      return [term];

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
// Definitional Equality
// ============================================================================

/**
 * Check if two types are definitionally equal.
 *
 * Implements:
 * - β-reduction: (λx. e) a ≃ e[a/x]
 * - ζ-reduction: let x := t; u ≃ u[t/x]
 * - η-conversion: λx. f x ≃ f (when x not free in f)
 * - δ-reduction: unfold definitions
 * - ι-reduction: pattern matching on constructors
 */
export function areTypesDefEq(t1: TTKTerm, t2: TTKTerm, definitions?: DefinitionsMap): boolean {
  const ctx: WhnfContext = { definitions };
  // Normalize both terms
  const n1 = whnf(t1, ctx);
  const n2 = whnf(t2, ctx);
  return areWhnfTypesDefEq(n1, n2, definitions);
}

export function areWhnfTypesDefEq(n1: TTKTerm, n2: TTKTerm, definitions?: DefinitionsMap): boolean {
  // Quick structural check first
  if (isDefinitionallyEqual(n1, n2)) {
    return true;
  }

  // Eta conversion for lambdas
  // λx. f x ≃ f (when x not free in f)
  if (n1.tag === 'Binder' && n1.binderKind.tag === 'BLam') {
    // Check if n1 is of the form λx. f x where x is not free in f
    if (n1.body.tag === 'App' && n1.body.arg.tag === 'Var' && n1.body.arg.index === 0) {
      if (!isFreeIn(0, n1.body.fn)) {
        // Eta contract: compare f with n2 (f needs index shift down)
        const contracted = subst(0, { tag: 'Var', index: 0 }, n1.body.fn);
        return areTypesDefEq(contracted, n2, definitions);
      }
    }
  }

  // Symmetric case
  if (n2.tag === 'Binder' && n2.binderKind.tag === 'BLam') {
    if (n2.body.tag === 'App' && n2.body.arg.tag === 'Var' && n2.body.arg.index === 0) {
      if (!isFreeIn(0, n2.body.fn)) {
        const contracted = subst(0, { tag: 'Var', index: 0 }, n2.body.fn);
        return areTypesDefEq(n1, contracted, definitions);
      }
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

    case 'Binder':
      if (n2.tag !== 'Binder' || n1.binderKind.tag !== n2.binderKind.tag) {
        return false;
      }
      if (!areTypesDefEq(n1.domain, n2.domain, definitions)) return false;
      if (!areTypesDefEq(n1.body, n2.body, definitions)) return false;
      if (n1.binderKind.tag === 'BLet' && n2.binderKind.tag === 'BLet') {
        return areTypesDefEq(n1.binderKind.defVal, n2.binderKind.defVal, definitions);
      }
      return true;

    case 'App':
      return n2.tag === 'App' &&
        areTypesDefEq(n1.fn, n2.fn, definitions) &&
        areTypesDefEq(n1.arg, n2.arg, definitions);

    case 'Hole':
      return n2.tag === 'Hole' && n1.id === n2.id;

    case 'Meta':
      return n2.tag === 'Meta' && n1.id === n2.id;

    case 'Annot':
      return areTypesDefEq(n1.term, n2, definitions);

    case 'Match':
      if (n2.tag !== 'Match') return false;
      if (!areTypesDefEq(n1.scrutinee, n2.scrutinee, definitions)) return false;
      if (n1.clauses.length !== n2.clauses.length) return false;
      for (let i = 0; i < n1.clauses.length; i++) {
        if (!areTypesDefEq(n1.clauses[i].rhs, n2.clauses[i].rhs, definitions)) return false;
      }
      return true;

    case 'ULevel':
      return n2.tag === 'ULevel';

    case 'ULit':
      return n2.tag === 'ULit' && n1.n === n2.n;

    case 'UOmega':
      return n2.tag === 'UOmega';
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
  const nextCtx: WhnfContext = { ...ctx, fuel: fuel - 1 };

  switch (term.tag) {
    case 'App': {
      const fn = whnf(term.fn, nextCtx);
      if (fn.tag === 'Binder' && fn.binderKind.tag === 'BLam') {
        // β-reduction: (λx. t) s → t[x := s]
        return whnf(subst(0, term.arg, fn.body), nextCtx);
      }
      // δ-reduction: If fn is a Const with a Match definition, try ι-reduction
      if (fn.tag === 'Const' && ctx?.definitions) {
        const def = getTermDefinition(ctx.definitions, fn.name);
        if (def?.value?.tag === 'Match') {
          // We have `f a` where f is defined by pattern matching
          // Try to reduce Match by applying the argument
          const matchTerm = def.value;
          return whnf({
            tag: 'App',
            fn: matchTerm,
            arg: term.arg
          }, nextCtx);
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
            // Reduce all arguments that will be matched
            const reducedArgs = args.slice(0, clause.patterns.length).map(
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
      if (ctx?.definitions) {
        const def = getTermDefinition(ctx.definitions, term.name);
        if (def?.value) {
          return whnf(def.value, nextCtx);
        }
      }
      return term;
    }

    case 'Match': {
      // ι-reduction: reduce pattern matching when scrutinee is a constructor
      const scrut = whnf(term.scrutinee, nextCtx);

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