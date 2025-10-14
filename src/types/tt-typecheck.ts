/**
 * Type Checker for TT (Typed Terms) Layer
 *
 * This implements bidirectional type checking for our dependent type theory.
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
 */

import {
  TTerm,
  TContext,
  subst,
  prettyPrint,
} from './tt-core';

// ============================================================================
// Type Checking Errors
// ============================================================================

export class TypeCheckError extends Error {
  constructor(message: string, public term?: TTerm, public context?: TContext) {
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
 */
export function extendContext(ctx: TContext, name: string, type: TTerm): TContext {
  return [{ name, type }, ...ctx];
}

/**
 * Look up the type of a variable by its De Bruijn index
 */
export function lookupVar(ctx: TContext, index: number): TTerm | null {
  if (index < 0 || index >= ctx.length) {
    return null;
  }
  // Index 0 is the most recent binding
  return ctx[index].type;
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
export function whnf(term: TTerm, ctx: TContext = []): TTerm {
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
 * Conversion checking: Are two terms equal up to computation?
 *
 * This is the core of definitional equality in type theory.
 * Two terms are convertible if they reduce to the same normal form.
 */
export function convertible(t1: TTerm, t2: TTerm, ctx: TContext = []): boolean {
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
      return n2.tag === 'App' &&
        convertible(n1.fn, n2.fn, ctx) &&
        convertible(n1.arg, n2.arg, ctx);

    case 'Hole':
      // Holes are only equal if they have the same id
      return n2.tag === 'Hole' && n1.id === n2.id;

    case 'Annot':
      // Compare the underlying terms
      return convertible(n1.term, n2, ctx);
  }
}

// ============================================================================
// Type Synthesis (Inference)
// ============================================================================

/**
 * Synthesize (infer) the type of a term
 *
 * Returns the type of the given term, or throws TypeCheckError if ill-typed.
 */
export function inferType(term: TTerm, ctx: TContext = []): TTerm {
  switch (term.tag) {
    case 'Var': {
      const type = lookupVar(ctx, term.index);
      if (!type) {
        throw new TypeCheckError(
          `Variable index ${term.index} not found in context of size ${ctx.length}`,
          term,
          ctx
        );
      }
      return type;
    }

    case 'Sort': {
      // Universe hierarchy: Prop : Type_1, Type_i : Type_(i+1)
      return { tag: 'Sort', level: term.level + 1 };
    }

    case 'Const': {
      // Constants have their types built-in
      return term.type;
    }

    case 'Binder': {
      switch (term.binderKind.tag) {
        case 'BPi': {
          // Check that domain is a type
          const domainType = inferType(term.domain, ctx);
          if (domainType.tag !== 'Sort') {
            throw new TypeCheckError(
              `Pi domain must be a type, got: ${prettyPrint(domainType)}`,
              term,
              ctx
            );
          }

          // Check that body is a type (in extended context)
          const extCtx = extendContext(ctx, term.name, term.domain);
          const bodyType = inferType(term.body, extCtx);
          if (bodyType.tag !== 'Sort') {
            throw new TypeCheckError(
              `Pi codomain must be a type, got: ${prettyPrint(bodyType)}`,
              term,
              ctx
            );
          }

          // The type of a Pi is the max of its universe levels
          const level = Math.max(domainType.level, bodyType.level);
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
  }
}

// ============================================================================
// Type Checking
// ============================================================================

/**
 * Check that a term has an expected type
 *
 * Throws TypeCheckError if the term doesn't have the expected type.
 */
export function checkType(term: TTerm, expectedType: TTerm, ctx: TContext = []): void {
  // Special case: Lambda can be checked against Pi type
  if (term.tag === 'Binder' && term.binderKind.tag === 'BLam' &&
      expectedType.tag === 'Binder' && expectedType.binderKind.tag === 'BPi') {
    // Check that domains match
    if (!convertible(term.domain, expectedType.domain, ctx)) {
      throw new TypeCheckError(
        `Lambda domain mismatch.\n  Expected: ${prettyPrint(expectedType.domain)}\n  Got: ${prettyPrint(term.domain)}`,
        term,
        ctx
      );
    }

    // Check body against Pi's body
    const extCtx = extendContext(ctx, term.name, term.domain);
    checkType(term.body, expectedType.body, extCtx);
    return;
  }

  // General case: Synthesize type and check convertibility
  const inferredType = inferType(term, ctx);

  if (!convertible(inferredType, expectedType, ctx)) {
    throw new TypeCheckError(
      `Type mismatch.\n  Expected: ${prettyPrint(expectedType)}\n  Inferred: ${prettyPrint(inferredType)}`,
      term,
      ctx
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
export function extractHoles(term: TTerm): { id: string; type: TTerm; context: TContext }[] {
  const holes: { id: string; type: TTerm; context: TContext }[] = [];

  function traverse(t: TTerm): void {
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
// Helper: Fill a hole in a term
// ============================================================================

/**
 * Fill a hole with a proof term
 * Returns a new term with the hole replaced
 */
export function fillHole(term: TTerm, holeId: string, proofTerm: TTerm): TTerm {
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

      let newBinderKind: import('./tt-core').BinderKind;
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
  }
}
