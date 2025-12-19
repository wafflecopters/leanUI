/**
 * Type Inference and Checking for TTK (Typed Terms - Kernel)
 * 
 * Implements bidirectional type checking for a dependent type system
 * based on Lean's type theory. This operates on kernel terms (TTK).
 * 
 * Key concepts:
 * - Inference (⇒): Given term t, compute its type T
 * - Checking (⇐): Given term t and expected type T, verify t has type T
 * - Definitional equality (≃): Terms are equal up to β/ζ/δ/ι/η reductions
 * 
 * Rules implemented:
 * - Structural: VAR, LET, CONV
 * - Sorts: PROP, TYPE, CUM
 * - Functions: PI, LAM, APP
 * - Equality: EQ, RFL
 * - Inductive: IND, MATCH (stubbed)
 * - Quotients: QUOT (stubbed)
 * 
 * NOTE: This operates on kernel terms. Surface terms (TT) must be elaborated
 * to kernel terms (TTK) before type-checking. See tt-elab.ts.
 */

import {
  TTKTerm,
  TTKContext,
  mkProp,
  mkType,
  prettyPrint,
  isDefinitionallyEqual,
  subst,
} from './tt-kernel';

// ============================================================================
// Type Inference Result
// ============================================================================

export type InferResult =
  | { ok: true; type: TTKTerm }
  | { ok: false; error: string };

export type CheckResult =
  | { ok: true }
  | { ok: false; error: string };

// ============================================================================
// Definitional Equality (≃)
// ============================================================================

/**
 * Check if a variable index is free in a term.
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
      if (isFreeIn(index, term.domain)) return true;
      if (isFreeIn(index + 1, term.body)) return true;
      if (term.binderKind.tag === 'BLet') {
        return isFreeIn(index, term.binderKind.defVal);
      }
      return false;
    case 'Annot':
      return isFreeIn(index, term.term) || isFreeIn(index, term.type);
  }
}

/**
 * Weak-head normal form reduction.
 * Reduces beta and let redexes at the head.
 */
function whnf(term: TTKTerm): TTKTerm {
  switch (term.tag) {
    case 'App': {
      const fn = whnf(term.fn);
      if (fn.tag === 'Binder' && fn.binderKind.tag === 'BLam') {
        // Beta reduction: (λx. t) s → t[x := s]
        return whnf(subst(0, term.arg, fn.body));
      }
      return { tag: 'App', fn, arg: term.arg };
    }
    case 'Binder': {
      if (term.binderKind.tag === 'BLet') {
        // Let expansion: let x := v in t → t[x := v]
        return whnf(subst(0, term.binderKind.defVal, term.body));
      }
      return term;
    }
    default:
      return term;
  }
}

/**
 * Check if two types are definitionally equal.
 * 
 * Implements:
 * - β-reduction: (λx. e) a ≃ e[a/x]
 * - ζ-reduction: let x := t; u ≃ u[t/x]
 * - η-conversion: λx. f x ≃ f (when x not free in f)
 * - δ-reduction: unfold definitions (todo)
 * - ι-reduction: recursor on constructor (todo)
 */
export function areTypesDefEq(t1: TTKTerm, t2: TTKTerm): boolean {
  // Normalize both terms
  const n1 = whnf(t1);
  const n2 = whnf(t2);

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
        return areTypesDefEq(contracted, n2);
      }
    }
  }

  // Symmetric case
  if (n2.tag === 'Binder' && n2.binderKind.tag === 'BLam') {
    if (n2.body.tag === 'App' && n2.body.arg.tag === 'Var' && n2.body.arg.index === 0) {
      if (!isFreeIn(0, n2.body.fn)) {
        const contracted = subst(0, { tag: 'Var', index: 0 }, n2.body.fn);
        return areTypesDefEq(n1, contracted);
      }
    }
  }

  // Deep structural comparison after normalization
  switch (n1.tag) {
    case 'Var':
      return n2.tag === 'Var' && n1.index === n2.index;

    case 'Sort':
      return n2.tag === 'Sort' && n1.level === n2.level;

    case 'Const':
      return n2.tag === 'Const' && n1.name === n2.name;

    case 'Binder':
      if (n2.tag !== 'Binder' || n1.binderKind.tag !== n2.binderKind.tag) {
        return false;
      }
      if (!areTypesDefEq(n1.domain, n2.domain)) return false;
      if (!areTypesDefEq(n1.body, n2.body)) return false;
      if (n1.binderKind.tag === 'BLet' && n2.binderKind.tag === 'BLet') {
        return areTypesDefEq(n1.binderKind.defVal, n2.binderKind.defVal);
      }
      return true;

    case 'App':
      return n2.tag === 'App' &&
        areTypesDefEq(n1.fn, n2.fn) &&
        areTypesDefEq(n1.arg, n2.arg);

    case 'Hole':
      return n2.tag === 'Hole' && n1.id === n2.id;

    case 'Annot':
      return areTypesDefEq(n1.term, n2);
  }
}

// ============================================================================
// Type Inference (⇒)
// ============================================================================

/**
 * Infer the type of a term.
 * 
 * Judgment: Γ ⊢ t ⇒ T
 * 
 * @param term - The term to infer
 * @param context - The typing context (Γ)
 * @returns The inferred type or an error
 */
export function inferType(term: TTKTerm, context: TTKContext = []): InferResult {
  switch (term.tag) {
    // ────────────────────────────────────────────────────────────────
    // (VAR) - Variable lookup
    // 
    //   x : A ∈ Γ
    //   ─────────────
    //   Γ ⊢ x ⇒ A
    // ────────────────────────────────────────────────────────────────
    case 'Var': {
      const idx = term.index;
      if (idx < 0 || idx >= context.length) {
        return { ok: false, error: `Variable index ${idx} out of bounds (context size: ${context.length})` };
      }
      return { ok: true, type: context[idx].type };
    }

    // ────────────────────────────────────────────────────────────────
    // (CONST) - Constant lookup
    // 
    // Constants have their types stored with them.
    // ────────────────────────────────────────────────────────────────
    case 'Const': {
      return { ok: true, type: term.type };
    }

    // ────────────────────────────────────────────────────────────────
    // (PROP) and (TYPE) - Universe hierarchy
    // 
    //   Prop : Type 0   (Sort 0 : Sort 1)
    //   Type u : Type (u+1)   (Sort u : Sort (u+1))
    // ────────────────────────────────────────────────────────────────
    case 'Sort': {
      // Type u : Type (u+1)
      // Note: Prop is Sort 0, and Sort 0 : Sort 1
      return { ok: true, type: mkType(term.level + 1) };
    }

    // ────────────────────────────────────────────────────────────────
    // (BINDER) - Pi, Lambda, or Let
    // ────────────────────────────────────────────────────────────────
    case 'Binder': {
      if (term.binderKind.tag === 'BPi') {
        // ────────────────────────────────────────────────────────────────
        // (PI) - Dependent function type
        // 
        //   Γ ⊢ A ⇒ s₁
        //   Γ, x : A ⊢ B ⇒ s₂
        //   ──────────────────────────────────────────────────────
        //   Γ ⊢ Π x : A, B ⇒ Sort (max s₁ s₂)
        // ────────────────────────────────────────────────────────────────
        const domainTypeResult = inferType(term.domain, context);
        if (!domainTypeResult.ok) {
          return { ok: false, error: `Pi domain error: ${domainTypeResult.error}` };
        }

        // Domain must be a sort
        const domainSort = extractSort(domainTypeResult.type);
        if (domainSort === null) {
          return { ok: false, error: `Pi domain type is not a sort: ${prettyPrint(domainTypeResult.type)}` };
        }

        // Check body in extended context
        const extendedContext: TTKContext = [{ name: term.name, type: term.domain }, ...context];
        const bodyTypeResult = inferType(term.body, extendedContext);
        if (!bodyTypeResult.ok) {
          return { ok: false, error: `Pi body error: ${bodyTypeResult.error}` };
        }

        // Body must be a sort
        const bodySort = extractSort(bodyTypeResult.type);
        if (bodySort === null) {
          return { ok: false, error: `Pi body type is not a sort: ${prettyPrint(bodyTypeResult.type)}` };
        }

        // Check if the body itself (codomain) is Prop for impredicativity
        const bodyIsSort = extractSort(term.body);

        // Result is Sort (max s₁ s₂), with special impredicative rule:
        // If the codomain itself is Prop (Sort 0), the result is Prop regardless of domain
        const resultLevel = (bodyIsSort !== null && bodyIsSort === 0) ? 0 : Math.max(domainSort, bodySort);
        return { ok: true, type: { tag: 'Sort', level: resultLevel } };
      } else if (term.binderKind.tag === 'BLam') {
        // ────────────────────────────────────────────────────────────────
        // (LAM) - Lambda abstraction (requires checking mode)
        // 
        // Lambda inference is difficult without a target type.
        // We return an error and suggest using checking mode.
        // ────────────────────────────────────────────────────────────────
        return { ok: false, error: 'Cannot infer type of lambda; use checking mode with expected Pi type' };
      } else if (term.binderKind.tag === 'BLet') {
        // ────────────────────────────────────────────────────────────────
        // (LET) - Local definition
        // 
        //   Γ ⊢ t ⇐ A
        //   Γ, x : A ⊢ u ⇒ B
        //   ───────────────────────────────
        //   Γ ⊢ let x := t; u ⇒ B[t/x]
        // ────────────────────────────────────────────────────────────────
        const defTypeResult = inferType(term.binderKind.defVal, context);
        if (!defTypeResult.ok) {
          return { ok: false, error: `Let definition error: ${defTypeResult.error}` };
        }

        // Check that the definition has the declared type
        const checkResult = checkType(term.binderKind.defVal, term.domain, context);
        if (!checkResult.ok) {
          return { ok: false, error: `Let definition type mismatch: ${checkResult.error}` };
        }

        // Infer body type in extended context
        const extendedContext: TTKContext = [{ name: term.name, type: term.domain }, ...context];
        const bodyResult = inferType(term.body, extendedContext);
        if (!bodyResult.ok) {
          return { ok: false, error: `Let body error: ${bodyResult.error}` };
        }

        // Result type is B[t/x] (body type with substitution)
        // For simplicity, we return the body type without substitution for now
        // TODO: Implement proper ζ-reduction
        return { ok: true, type: bodyResult.type };
      }
      return { ok: false, error: `Unknown binder kind: ${term.binderKind}` };
    }

    // ────────────────────────────────────────────────────────────────
    // (APP) - Function application
    // 
    //   Γ ⊢ f ⇒ Π x : A, B
    //   Γ ⊢ a ⇐ A
    //   ───────────────────────────────
    //   Γ ⊢ f a ⇒ B[a/x]
    // ────────────────────────────────────────────────────────────────
    case 'App': {
      const fnTypeResult = inferType(term.fn, context);
      if (!fnTypeResult.ok) {
        return { ok: false, error: `App function error: ${fnTypeResult.error}` };
      }

      // Function type must be a Pi
      if (fnTypeResult.type.tag !== 'Binder' || fnTypeResult.type.binderKind.tag !== 'BPi') {
        return { ok: false, error: `App function is not a Pi type: ${prettyPrint(fnTypeResult.type)}` };
      }

      const piType = fnTypeResult.type;

      // Verify piType has the expected structure
      if (!piType.domain || !piType.body) {
        return { ok: false, error: `Malformed Pi type: ${prettyPrint(piType)}` };
      }

      // Check argument against domain
      const checkResult = checkType(term.arg, piType.domain, context);
      if (!checkResult.ok) {
        return { ok: false, error: `App argument type mismatch: ${checkResult.error}` };
      }

      // Result type is B[a/x]
      // subst(0, replacement, term) substitutes for the most recent binder
      const resultType = subst(0, term.arg, piType.body);
      return { ok: true, type: resultType };
    }

    // ────────────────────────────────────────────────────────────────
    // (ANNOT) - Type annotation
    // ────────────────────────────────────────────────────────────────
    case 'Annot': {
      const checkResult = checkType(term.term, term.type, context);
      if (!checkResult.ok) {
        return { ok: false, error: `Annotation type mismatch: ${checkResult.error}` };
      }
      return { ok: true, type: term.type };
    }

    // ────────────────────────────────────────────────────────────────
    // (HOLE) - Metavariable
    // 
    // Holes have their expected types stored with them.
    // ────────────────────────────────────────────────────────────────
    case 'Hole': {
      return { ok: true, type: term.type };
    }
  }
}

// ============================================================================
// Type Checking (⇐)
// ============================================================================

/**
 * Check that a term has a given type.
 * 
 * Judgment: Γ ⊢ t ⇐ T
 * 
 * @param term - The term to check
 * @param expectedType - The expected type
 * @param context - The typing context (Γ)
 * @returns Success or error
 */
export function checkType(term: TTKTerm, expectedType: TTKTerm, context: TTKContext = []): CheckResult {
  // Special case: Lambda checking
  if (term.tag === 'Binder' && term.binderKind.tag === 'BLam') {
    // ────────────────────────────────────────────────────────────────
    // (LAM) - Lambda abstraction
    // 
    //   Γ ⊢ Π x : A, B
    //   Γ, x : A ⊢ t ⇐ B
    //   ───────────────────────────────
    //   Γ ⊢ λ x : A => t ⇐ Π x : A, B
    // ────────────────────────────────────────────────────────────────
    if (expectedType.tag !== 'Binder' || expectedType.binderKind.tag !== 'BPi') {
      return { ok: false, error: `Lambda expected Pi type, got: ${prettyPrint(expectedType)}` };
    }

    const piType = expectedType;

    // Check that domains match
    if (!areTypesDefEq(term.domain, piType.domain)) {
      return { ok: false, error: `Lambda domain mismatch: ${prettyPrint(term.domain)} vs ${prettyPrint(piType.domain)}` };
    }

    // Check body in extended context
    const extendedContext: TTKContext = [{ name: term.name, type: term.domain }, ...context];
    return checkType(term.body, piType.body, extendedContext);
  }

  // ────────────────────────────────────────────────────────────────
  // (CONV) - Type conversion
  // 
  //   Γ ⊢ t ⇒ T
  //   T ≃ T′
  //   ─────────────
  //   Γ ⊢ t ⇐ T′
  // ────────────────────────────────────────────────────────────────
  const inferResult = inferType(term, context);
  if (!inferResult.ok) {
    return { ok: false, error: inferResult.error };
  }

  if (!areTypesDefEq(inferResult.type, expectedType)) {
    return {
      ok: false,
      error: `Type mismatch:\n  Expected: ${prettyPrint(expectedType)}\n  Got:      ${prettyPrint(inferResult.type)}`
    };
  }

  return { ok: true };
}

// ============================================================================
// Helper Functions
// ============================================================================

/**
 * Extract the universe level from a Sort term.
 * Returns null if the term is not a Sort.
 */
function extractSort(term: TTKTerm): number | null {
  if (term.tag === 'Sort') {
    return term.level;
  }
  return null;
}

// ============================================================================
// Stub: Equality Types
// ============================================================================

/**
 * (EQ) - Equality type
 * 
 *   Γ ⊢ A : Type u
 *   Γ ⊢ a, b : A
 *   ─────────────────────────────
 *   Γ ⊢ Eq A a b : Prop
 * 
 * TODO: Implement Eq as a kernel primitive
 */
export function mkEq(type: TTKTerm, lhs: TTKTerm, rhs: TTKTerm): TTKTerm {
  // Stubbed: Eq is represented as a Const for now
  return {
    tag: 'App',
    fn: {
      tag: 'App',
      fn: {
        tag: 'App',
        fn: { tag: 'Const', name: 'Eq', type: mkProp() },
        arg: type
      },
      arg: lhs
    },
    arg: rhs
  };
}

/**
 * (RFL) - Reflexivity of equality
 * 
 *   Γ ⊢ a : A
 *   ───────────────
 *   Γ ⊢ rfl : Eq A a a
 * 
 * TODO: Implement rfl as a kernel primitive
 */
export function mkRfl(type: TTKTerm, term: TTKTerm): TTKTerm {
  return { tag: 'Const', name: 'rfl', type: mkEq(type, term, term) };
}

// ============================================================================
// Stub: Inductive Types
// ============================================================================

/**
 * (IND) - Inductive type declaration
 *
 *   (I, cᵢ defined strictly positive)
 *   Γ ⊢ I : Π Δ, Sort u
 *   Γ ⊢ cᵢ : Π Δᵢ, I paramsᵢ
 *
 * TODO: Implement inductive types with:
 * - Strict positivity checking
 * - Constructor generation
 * - Eliminator generation
 */

/**
 * (MATCH) - Pattern matching / eliminator
 *
 *   Γ ⊢ z ⇒ I args
 *   motive C : Π (x : I args), Sort w
 *   ∀i. Γ, Δᵢ ⊢ rhsᵢ ⇐ C (cᵢ Δᵢ)
 *   ─────────────────────────────────────
 *   Γ ⊢ match z with | cᵢ Δᵢ => rhsᵢ ⇒ C z
 *
 * TODO: Implement pattern matching with:
 * - Motive computation
 * - Branch checking
 * - ι-reduction (recursor on constructor)
 */

// ============================================================================
// Stub: Quotient Types
// ============================================================================

/**
 * (QUOT) - Quotient type
 *
 *   Γ ⊢ A : Type u
 *   Γ ⊢ R : A → A → Prop
 *   ─────────────────────────────
 *   Γ ⊢ Quot A R : Type u
 *
 * TODO: Implement quotients with:
 * - mk: A → Quot A R
 * - ind: (motive) (mk_case) → eliminates into Prop
 * - lift: for functions respecting R
 * - sound: R a b → mk a = mk b
 */

// ============================================================================
// Summary
// ============================================================================

/**
 * Type inference implements these rules:
 * 
 * Inference (⇒): VAR, CONST, PROP, TYPE, PI, APP, ANNOT, HOLE
 * Checking (⇐): LAM, CONV
 * 
 * Stubbed for future:
 * - IND, MATCH (inductive types)
 * - QUOT (quotient types)
 * - EQ, RFL (equality as primitive)
 * - CUM (cumulativity)
 * - Full definitional equality with normalization
 */

