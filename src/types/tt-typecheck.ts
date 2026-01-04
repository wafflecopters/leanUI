/**
 * Type Checker for TTK (Typed Terms - Kernel) Layer
 *
 * This implements bidirectional type checking for our dependent type theory.
 * The type checker operates on KERNEL terms (TTK), not surface terms (TT).
 *
 * The type checker has two modes:
 *
 * 1. **Synthesis** (inferType): Given a term, compute its type
 *    - Used for checking if a term is well-formed
 *    - Example: infer that (λx:ℕ. x) has type ℕ → ℕ
 *
 * 2. **Checking** (checkType): Given a term and an expected type, verify they match
 *    - Used for filling in holes and checking proof terms
 *    - Example: check that (λx:ℕ. 0) has type ℕ → ℕ
 *
 * The type checker also handles:
 * - Universe checking (Prop : Type_1, Type_i : Type_(i+1))
 * - Conversion checking (are two types equal up to computation?)
 * - Context management (tracking bound variables and their types)
 *
 * NOTE: This operates on kernel terms. Surface terms (TT) must be elaborated
 * to kernel terms (TTK) before type-checking. See tt-elab.ts.
 */

import {
  TTKTerm,
  TTKContext,
  TTKBinderKind,
  subst,
  prettyPrint,
} from './tt-kernel';
import { IndexPath } from './source-position';

// ============================================================================
// Type Checking Errors
// ============================================================================

export class TypeCheckError extends Error {
  constructor(
    message: string,
    public term?: TTKTerm,
    public context?: TTKContext,
    public termPath?: IndexPath
  ) {
    super(message);
    this.name = 'TypeCheckError';
  }
}

// ============================================================================
// Context Operations
// ============================================================================

/**
 * Extend context with a new binding
 * This adds a binding at index 0 (most recent)
 *
 * IMPORTANT: The type is shifted by 1 because it was valid in the outer context,
 * but after extending, all De Bruijn indices need to be incremented to account
 * for the new binding at index 0.
 */
export function extendContext(ctx: TTKContext, name: string, type: TTKTerm): TTKContext {
  // Shift the type by 1 since we're adding a new binding at index 0
  const shiftedType = shiftTermBy(type, 1, 0);
  return [{ name, type: shiftedType }, ...ctx];
}

/**
 * Look up the type of a variable by its De Bruijn index
 */
export function lookupVar(ctx: TTKContext, index: number): TTKTerm | null {
  if (index < 0 || index >= ctx.length) {
    return null;
  }
  // Index 0 is the most recent binding
  return ctx[index].type;
}

/**
 * Extract variable names from a context for pretty printing.
 * Returns an array where index i contains the name of the variable at De Bruijn index i.
 */
export function contextToNames(ctx: TTKContext): string[] {
  return ctx.map(binding => binding.name);
}

/**
 * Look up the type of a constant by name in the context.
 * This is used when a Const has a Hole type (unresolved forward reference)
 * but the actual type is known from the context.
 */
export function lookupConstByName(ctx: TTKContext, name: string): TTKTerm | null {
  for (const binding of ctx) {
    if (binding.name === name) {
      return binding.type;
    }
  }
  return null;
}

// ============================================================================
// Normalization and Conversion
// ============================================================================

/**
 * Weak-head normal form (WHNF)
 * Reduce a term until it's a lambda, pi, or stuck application
 *
 * This is used for conversion checking.
 */
export function whnf(term: TTKTerm, ctx: TTKContext = []): TTKTerm {
  switch (term.tag) {
    case 'App': {
      const fn = whnf(term.fn, ctx);
      if (fn.tag === 'Binder' && fn.binderKind.tag === 'BLam') {
        // Beta reduction: (λx. t) s  -->  t[x := s]
        return whnf(subst(0, term.arg, fn.body), ctx);
      }
      return { tag: 'App', fn, arg: term.arg };
    }

    case 'Binder': {
      // Let expansion: let x := v in t  -->  t[x := v]
      if (term.binderKind.tag === 'BLet') {
        return whnf(subst(0, term.binderKind.defVal, term.body), ctx);
      }
      // Pi and Lambda are already in normal form
      return term;
    }

    default:
      return term;
  }
}

/**
 * Check if a variable index is free in a term.
 *
 * @param index - The De Bruijn index to check
 * @param term - The term to search in
 * @returns true if the variable appears free in the term
 */
function isFreeIn(index: number, term: TTKTerm): boolean {
  switch (term.tag) {
    case 'Var':
      return term.index === index;
    case 'Sort':
    case 'Const':
      return false;
    case 'Hole':
      return isFreeIn(index, term.type);
    case 'App':
      return isFreeIn(index, term.fn) || isFreeIn(index, term.arg);
    case 'Binder':
      // In the body, the index we're looking for is shifted by 1
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
  }
}

/**
 * Try to eta-expand a term to a lambda if possible.
 *
 * If `t` has a Pi type `(x : A) → B`, we can eta-expand it to `λx. t x`.
 * This is used when comparing a non-lambda with a lambda.
 *
 * @param term - The term to potentially eta-expand
 * @param ctx - The typing context
 * @returns The eta-expanded lambda, or null if not applicable
 */
function tryEtaExpand(term: TTKTerm, ctx: TTKContext): TTKTerm | null {
  // Get the type of the term
  try {
    const termType = whnf(inferType(term, ctx), ctx);
    if (termType.tag === 'Binder' && termType.binderKind.tag === 'BPi') {
      // Eta expand: t → λx. t x
      // We need to shift t by 1 since we're going under a binder
      const shiftedTerm = shiftTermBy(term, 1, 0);
      return {
        tag: 'Binder',
        name: termType.name,
        binderKind: { tag: 'BLam' },
        domain: termType.domain,
        body: { tag: 'App', fn: shiftedTerm, arg: { tag: 'Var', index: 0 } }
      };
    }
  } catch {
    // If type inference fails, can't eta expand
  }
  return null;
}

/**
 * Shift all free variables in a term by a given amount.
 *
 * @param term - The term to shift
 * @param amount - How much to shift by
 * @param cutoff - Only shift variables >= cutoff
 */
function shiftTermBy(term: TTKTerm, amount: number, cutoff: number): TTKTerm {
  switch (term.tag) {
    case 'Var':
      return term.index >= cutoff
        ? { tag: 'Var', index: term.index + amount }
        : term;
    case 'Sort':
    case 'Const':
      return term;
    case 'Hole':
      return { ...term, type: shiftTermBy(term.type, amount, cutoff) };
    case 'App':
      return {
        tag: 'App',
        fn: shiftTermBy(term.fn, amount, cutoff),
        arg: shiftTermBy(term.arg, amount, cutoff)
      };
    case 'Binder': {
      const newDomain = shiftTermBy(term.domain, amount, cutoff);
      const newBody = shiftTermBy(term.body, amount, cutoff + 1);
      let newBinderKind: TTKBinderKind = term.binderKind;
      if (term.binderKind.tag === 'BLet') {
        newBinderKind = {
          tag: 'BLet',
          defVal: shiftTermBy(term.binderKind.defVal, amount, cutoff)
        };
      }
      return { ...term, domain: newDomain, body: newBody, binderKind: newBinderKind };
    }
    case 'Annot':
      return {
        tag: 'Annot',
        term: shiftTermBy(term.term, amount, cutoff),
        type: shiftTermBy(term.type, amount, cutoff)
      };

    case 'Match':
      return {
        tag: 'Match',
        scrutinee: shiftTermBy(term.scrutinee, amount, cutoff),
        clauses: term.clauses.map(c => ({
          patterns: c.patterns,
          rhs: shiftTermBy(c.rhs, amount, cutoff)
        }))
      };
  }
}

/**
 * Conversion checking: Are two terms equal up to computation?
 *
 * This is the core of definitional equality in type theory.
 * Two terms are convertible if they reduce to the same normal form.
 *
 * Implements:
 * - Beta reduction: (λx. e) a ≃ e[a/x]
 * - Let expansion: let x := v in t ≃ t[v/x]
 * - Eta conversion: λx. f x ≃ f (when x not free in f)
 */
export function convertible(t1: TTKTerm, t2: TTKTerm, ctx: TTKContext = []): boolean {
  const n1 = whnf(t1, ctx);
  const n2 = whnf(t2, ctx);

  // Structural equality on normal forms
  switch (n1.tag) {
    case 'Var':
      return n2.tag === 'Var' && n1.index === n2.index;

    case 'Sort':
      return n2.tag === 'Sort' && n1.level === n2.level;

    case 'Const':
      return n2.tag === 'Const' && n1.name === n2.name;

    case 'Binder':
      // Eta rule for lambdas: λx. f x ≃ f (when x not free in f)
      if (n1.binderKind.tag === 'BLam') {
        // Check if n1 is of the form λx. f x where x is not free in f
        if (n1.body.tag === 'App' && n1.body.arg.tag === 'Var' && n1.body.arg.index === 0) {
          // Check if x (index 0) is not free in f
          if (!isFreeIn(0, n1.body.fn)) {
            // Eta contract: λx. f x → f (with index shift)
            const contracted = subst(0, { tag: 'Var', index: 0 }, n1.body.fn);
            return convertible(contracted, n2, ctx);
          }
        }

        // If n2 is not a lambda but has function type, try eta-expanding n2
        if (n2.tag !== 'Binder' || n2.binderKind.tag !== 'BLam') {
          const expanded = tryEtaExpand(n2, ctx);
          if (expanded) {
            return convertible(n1, expanded, ctx);
          }
        }
      }

      // Symmetric case: if n2 is a lambda and n1 is not
      if (n2.tag === 'Binder' && n2.binderKind.tag === 'BLam' &&
        (n1.tag !== 'Binder' || n1.binderKind.tag !== 'BLam')) {
        // Check eta contraction on n2
        if (n2.body.tag === 'App' && n2.body.arg.tag === 'Var' && n2.body.arg.index === 0) {
          if (!isFreeIn(0, n2.body.fn)) {
            const contracted = subst(0, { tag: 'Var', index: 0 }, n2.body.fn);
            return convertible(n1, contracted, ctx);
          }
        }

        // Try eta-expanding n1
        const expanded = tryEtaExpand(n1, ctx);
        if (expanded) {
          return convertible(expanded, n2, ctx);
        }
      }

      // Both must be binders of the same kind
      if (n2.tag !== 'Binder' || n1.binderKind.tag !== n2.binderKind.tag) {
        return false;
      }

      // Check domains are convertible
      if (!convertible(n1.domain, n2.domain, ctx)) {
        return false;
      }

      // Check bodies in extended context
      const extCtx = extendContext(ctx, n1.name, n1.domain);
      if (!convertible(n1.body, n2.body, extCtx)) {
        return false;
      }

      // For BLet, also check definition values
      if (n1.binderKind.tag === 'BLet' && n2.binderKind.tag === 'BLet') {
        return convertible(n1.binderKind.defVal, n2.binderKind.defVal, ctx);
      }

      return true;

    case 'App':
      // Eta expansion for n1: if n2 is a lambda, we might need to eta-expand n1
      if (n2.tag === 'Binder' && n2.binderKind.tag === 'BLam') {
        const expanded = tryEtaExpand(n1, ctx);
        if (expanded) {
          return convertible(expanded, n2, ctx);
        }
      }

      return n2.tag === 'App' &&
        convertible(n1.fn, n2.fn, ctx) &&
        convertible(n1.arg, n2.arg, ctx);

    case 'Hole':
      // Holes are only equal if they have the same id
      return n2.tag === 'Hole' && n1.id === n2.id;

    case 'Annot':
      // Compare the underlying terms
      return convertible(n1.term, n2, ctx);

    case 'Match':
      if (n2.tag !== 'Match') return false;
      if (!convertible(n1.scrutinee, n2.scrutinee, ctx)) return false;
      if (n1.clauses.length !== n2.clauses.length) return false;
      for (let i = 0; i < n1.clauses.length; i++) {
        if (!convertible(n1.clauses[i].rhs, n2.clauses[i].rhs, ctx)) return false;
      }
      return true;
  }
}

// ============================================================================
// Type Synthesis (Inference)
// ============================================================================

/**
 * Synthesize (infer) the type of a term
 *
 * Returns the type of the given term, or throws TypeCheckError if ill-typed.
 *
 * @param term - The term to infer the type of
 * @param ctx - The typing context
 * @param path - Optional index path for source tracking
 */
export function inferType(
  term: TTKTerm,
  ctx: TTKContext = [],
  path: IndexPath = []
): TTKTerm {
  // For now, we accept the path but don't thread it deeply
  // TODO: Thread path through all recursive calls for fine-grained error reporting
  void path;

  switch (term.tag) {
    case 'Var': {
      const type = lookupVar(ctx, term.index);
      if (!type) {
        throw new TypeCheckError(
          `Variable index ${term.index} not found in context of size ${ctx.length}`,
          term,
          ctx,
          path
        );
      }
      return type;
    }

    case 'Sort': {
      // Universe hierarchy: Prop : Type_1, Type_i : Type_(i+1)
      return { tag: 'Sort', level: term.level + 1 };
    }

    case 'Const': {
      // If the constant has a Hole type (unresolved forward reference),
      // try to look it up in the context
      if (term.type.tag === 'Hole') {
        const ctxType = lookupConstByName(ctx, term.name);
        if (ctxType) {
          return ctxType;
        }
      }
      // Otherwise use the built-in type
      return term.type;
    }

    case 'Binder': {
      switch (term.binderKind.tag) {
        case 'BPi': {
          // Check that domain is a type
          const domainType = inferType(term.domain, ctx);
          // Accept Sort or Hole (Hole represents forward references like inductive types)
          if (domainType.tag !== 'Sort' && domainType.tag !== 'Hole') {
            throw new TypeCheckError(
              `Pi domain must be a type, got: ${prettyPrint(domainType)}`,
              term,
              ctx
            );
          }

          // Check that body is a type (in extended context)
          const extCtx = extendContext(ctx, term.name, term.domain);
          const bodyType = inferType(term.body, extCtx);
          // Accept Sort or Hole (Hole represents forward references)
          if (bodyType.tag !== 'Sort' && bodyType.tag !== 'Hole') {
            throw new TypeCheckError(
              `Pi codomain must be a type, got: ${prettyPrint(bodyType)}`,
              term,
              ctx
            );
          }

          // The type of a Pi is the max of its universe levels
          // If either is a Hole, conservatively return universe 0
          const domainLevel = domainType.tag === 'Sort' ? domainType.level : 0;
          const bodyLevel = bodyType.tag === 'Sort' ? bodyType.level : 0;
          const level = Math.max(domainLevel, bodyLevel);
          return { tag: 'Sort', level };
        }

        case 'BLam': {
          // For lambda, we need to synthesize the type of the body
          // λ(x : A). t  has type  Π(x : A). T  where t : T

          // Check domain is a type
          const domainType = inferType(term.domain, ctx);
          if (domainType.tag !== 'Sort') {
            throw new TypeCheckError(
              `Lambda domain must be a type, got: ${prettyPrint(domainType)}`,
              term,
              ctx
            );
          }

          // Synthesize type of body
          const extCtx = extendContext(ctx, term.name, term.domain);
          const bodyType = inferType(term.body, extCtx);

          // Result type: Π(x : domain). bodyType
          return {
            tag: 'Binder',
            name: term.name,
            binderKind: { tag: 'BPi' },
            domain: term.domain,
            body: bodyType
          };
        }

        case 'BLet': {
          // Check definition type
          const defTypeType = inferType(term.domain, ctx);
          if (defTypeType.tag !== 'Sort') {
            throw new TypeCheckError(
              `Let definition type must be a type, got: ${prettyPrint(defTypeType)}`,
              term,
              ctx
            );
          }

          // Check definition value
          checkType(term.binderKind.defVal, term.domain, ctx);

          // Synthesize type of body in extended context
          const extCtx = extendContext(ctx, term.name, term.domain);
          return inferType(term.body, extCtx);
        }
      }
    }

    case 'App': {
      // Infer type of function
      const fnType = whnf(inferType(term.fn, ctx), ctx);

      if (fnType.tag !== 'Binder' || fnType.binderKind.tag !== 'BPi') {
        throw new TypeCheckError(
          `Application requires Pi type, got: ${prettyPrint(fnType)}`,
          term,
          ctx
        );
      }

      // Check that argument has the domain type
      checkType(term.arg, fnType.domain, ctx);

      // Result type: body[x := arg]
      return subst(0, term.arg, fnType.body);
    }

    case 'Hole': {
      // A hole has its type stored with it
      return term.type;
    }

    case 'Annot': {
      // Check that the term has the annotated type
      checkType(term.term, term.type, ctx);
      return term.type;
    }

    case 'Match': {
      // TODO: Implement proper pattern matching type checking
      // For now, just return a placeholder type
      // This would need to check that all clauses have the same return type
      // and that the patterns cover all constructors of the scrutinee's type
      throw new Error('Pattern matching type inference not yet implemented');
    }
  }
}

// ============================================================================
// Type Checking
// ============================================================================

/**
 * Check that a term has an expected type
 *
 * Throws TypeCheckError if the term doesn't have the expected type.
 *
 * @param term - The term to check
 * @param expectedType - The expected type
 * @param ctx - The typing context
 * @param path - Optional index path for source tracking
 */
export function checkType(
  term: TTKTerm,
  expectedType: TTKTerm,
  ctx: TTKContext = [],
  path: IndexPath = []
): void {
  // For now, we accept the path but don't thread it deeply
  // TODO: Thread path through all recursive calls for fine-grained error reporting
  void path;

  // Special case: Lambda can be checked against Pi type
  if (term.tag === 'Binder' && term.binderKind.tag === 'BLam' &&
    expectedType.tag === 'Binder' && expectedType.binderKind.tag === 'BPi') {
    // Check that domains match
    if (!convertible(term.domain, expectedType.domain, ctx)) {
      throw new TypeCheckError(
        `Lambda domain mismatch.\n  Expected: ${prettyPrint(expectedType.domain)}\n  Got: ${prettyPrint(term.domain)}`,
        term,
        ctx,
        path
      );
    }

    // Check body against Pi's body
    const extCtx = extendContext(ctx, term.name, term.domain);
    checkType(term.body, expectedType.body, extCtx, path);
    return;
  }

  // General case: Synthesize type and check convertibility
  const inferredType = inferType(term, ctx, path);

  if (!convertible(inferredType, expectedType, ctx)) {
    // Use context names for readable error messages
    const names = contextToNames(ctx);
    throw new TypeCheckError(
      `Type mismatch.\n  Expected: ${prettyPrint(expectedType, names)}\n  Inferred: ${prettyPrint(inferredType, names)}`,
      term,
      ctx,
      path
    );
  }
}

// ============================================================================
// Helper: Extract all holes from a term
// ============================================================================

/**
 * Extract all holes (metavariables) from a term
 * Returns a list of hole IDs and their types
 */
export function extractHoles(term: TTKTerm): { id: string; type: TTKTerm; context: TTKContext }[] {
  const holes: { id: string; type: TTKTerm; context: TTKContext }[] = [];

  function traverse(t: TTKTerm): void {
    switch (t.tag) {
      case 'Hole':
        holes.push({ id: t.id, type: t.type, context: t.context });
        break;

      case 'Binder':
        traverse(t.domain);
        traverse(t.body);
        if (t.binderKind.tag === 'BLet') {
          traverse(t.binderKind.defVal);
        }
        break;

      case 'App':
        traverse(t.fn);
        traverse(t.arg);
        break;

      case 'Annot':
        traverse(t.term);
        traverse(t.type);
        break;

      case 'Match':
        traverse(t.scrutinee);
        for (const clause of t.clauses) {
          traverse(clause.rhs);
        }
        break;

      case 'Const':
        traverse(t.type);
        break;

      case 'Var':
      case 'Sort':
        // No sub-terms
        break;
    }
  }

  traverse(term);
  return holes;
}

// ============================================================================
// Helper: Find a hole in a term
// ============================================================================

/**
 * Find a hole by ID in a term.
 * Returns the hole term if found, or null if not found.
 * 
 * @param term - The term to search
 * @param holeId - The ID of the hole to find
 * @returns The hole term or null
 */
export function findHole(term: TTKTerm, holeId: string): TTKTerm | null {
  switch (term.tag) {
    case 'Hole':
      return term.id === holeId ? term : null;

    case 'Var':
    case 'Sort':
    case 'Const':
      return null;

    case 'Binder': {
      // Check domain
      const inDomain = findHole(term.domain, holeId);
      if (inDomain) return inDomain;

      // Check body
      const inBody = findHole(term.body, holeId);
      if (inBody) return inBody;

      // Check defVal if it's a let
      if (term.binderKind.tag === 'BLet') {
        const inDefVal = findHole(term.binderKind.defVal, holeId);
        if (inDefVal) return inDefVal;
      }

      return null;
    }

    case 'App': {
      const inFn = findHole(term.fn, holeId);
      if (inFn) return inFn;

      const inArg = findHole(term.arg, holeId);
      if (inArg) return inArg;

      return null;
    }

    case 'Annot': {
      const inTerm = findHole(term.term, holeId);
      if (inTerm) return inTerm;

      const inType = findHole(term.type, holeId);
      if (inType) return inType;

      return null;
    }

    case 'Match': {
      const inScrutinee = findHole(term.scrutinee, holeId);
      if (inScrutinee) return inScrutinee;

      for (const clause of term.clauses) {
        const inRhs = findHole(clause.rhs, holeId);
        if (inRhs) return inRhs;
      }

      return null;
    }
  }
}

// ============================================================================
// Helper: Fill a hole in a term
// ============================================================================

/**
 * Fill a hole with a proof term
 * Returns a new term with the hole replaced
 */
export function fillHole(term: TTKTerm, holeId: string, proofTerm: TTKTerm): TTKTerm {
  switch (term.tag) {
    case 'Hole':
      return term.id === holeId ? proofTerm : term;

    case 'Var':
    case 'Sort':
    case 'Const':
      return term;

    case 'Binder': {
      const newDomain = fillHole(term.domain, holeId, proofTerm);
      const newBody = fillHole(term.body, holeId, proofTerm);

      let newBinderKind: TTKBinderKind;
      if (term.binderKind.tag === 'BLet') {
        const newDefVal = fillHole(term.binderKind.defVal, holeId, proofTerm);
        newBinderKind = { tag: 'BLet', defVal: newDefVal };
      } else {
        newBinderKind = term.binderKind;
      }

      return {
        tag: 'Binder',
        name: term.name,
        binderKind: newBinderKind,
        domain: newDomain,
        body: newBody
      };
    }

    case 'App':
      return {
        tag: 'App',
        fn: fillHole(term.fn, holeId, proofTerm),
        arg: fillHole(term.arg, holeId, proofTerm)
      };

    case 'Annot':
      return {
        tag: 'Annot',
        term: fillHole(term.term, holeId, proofTerm),
        type: fillHole(term.type, holeId, proofTerm)
      };

    case 'Match':
      return {
        tag: 'Match',
        scrutinee: fillHole(term.scrutinee, holeId, proofTerm),
        clauses: term.clauses.map(c => ({
          patterns: c.patterns,
          rhs: fillHole(c.rhs, holeId, proofTerm)
        }))
      };
  }
}

/**
 * Fill a hole with a term generated by a function.
 * The function receives the hole's type and context, allowing dynamic replacement.
 * 
 * This is useful when you need to create new holes or terms that depend on the
 * context where the hole appears.
 * 
 * @param term - The term containing the hole
 * @param holeId - The ID of the hole to fill
 * @param generator - Function that takes (holeType, holeContext) and returns the replacement term
 * @returns A new term with the hole replaced
 * 
 * Example:
 *   fillHoleWith(term, "proof", (type, ctx) => 
 *     mkLet("foo", fooType, fooVal, mkHole("after-foo", type, ctx))
 *   )
 */
export function fillHoleWith(
  term: TTKTerm,
  holeId: string,
  generator: (holeType: TTKTerm, holeContext: TTKContext) => TTKTerm
): TTKTerm {
  switch (term.tag) {
    case 'Hole':
      if (term.id === holeId) {
        return generator(term.type, term.context);
      }
      return term;

    case 'Var':
    case 'Sort':
    case 'Const':
      return term;

    case 'Binder': {
      const newDomain = fillHoleWith(term.domain, holeId, generator);
      const newBody = fillHoleWith(term.body, holeId, generator);

      let newBinderKind: TTKBinderKind;
      if (term.binderKind.tag === 'BLet') {
        const newDefVal = fillHoleWith(term.binderKind.defVal, holeId, generator);
        newBinderKind = { tag: 'BLet', defVal: newDefVal };
      } else {
        newBinderKind = term.binderKind;
      }

      return {
        tag: 'Binder',
        name: term.name,
        binderKind: newBinderKind,
        domain: newDomain,
        body: newBody
      };
    }

    case 'App':
      return {
        tag: 'App',
        fn: fillHoleWith(term.fn, holeId, generator),
        arg: fillHoleWith(term.arg, holeId, generator)
      };

    case 'Annot':
      return {
        tag: 'Annot',
        term: fillHoleWith(term.term, holeId, generator),
        type: fillHoleWith(term.type, holeId, generator)
      };

    case 'Match':
      return {
        tag: 'Match',
        scrutinee: fillHoleWith(term.scrutinee, holeId, generator),
        clauses: term.clauses.map(c => ({
          patterns: c.patterns,
          rhs: fillHoleWith(c.rhs, holeId, generator)
        }))
      };
  }
}
