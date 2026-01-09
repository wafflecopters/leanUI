/**
 * Unification Algorithm for TTK (Typed Terms - Kernel)
 *
 * This implements the unification algorithm from "Pattern Matching Without K"
 * by Jesper Cockx, Dominique Devriese, and Frank Piessens (ICFP 2014).
 *
 * The algorithm supports:
 * - Metavariable (hole) solving
 * - Injectivity of constructors
 * - Conflict detection (distinct constructors)
 * - Cycle detection (occurs check)
 * - Deletion of reflexive equations (optional, requires UIP/K)
 *
 * Key Features:
 * - By default, operates in "without K" mode (deletion disabled)
 * - With `useUIP: true`, enables deletion rule (UIP = Uniqueness of Identity Proofs)
 * - Returns three possible outcomes:
 *   1. Positive success: unification succeeds with a substitution
 *   2. Negative success: unification proves impossibility (conflict/cycle)
 *   3. Stuck: unification cannot proceed (needs more information)
 */

import {
  TTKTerm,
  TTKContext,
  occursIn,
  prettyPrint,
  isDefinitionallyEqual,
} from './tt-kernel';
import { whnf, convertible } from './tt-typecheck';

// ============================================================================
// Unification Problem Types
// ============================================================================

/**
 * A single unification constraint: two terms that should be equal.
 * The context is needed for type-directed operations.
 */
export interface UnifyEquation {
  lhs: TTKTerm;
  rhs: TTKTerm;
  type: TTKTerm;  // The type at which the terms are being unified
}

/**
 * A unification problem: a list of equations to solve.
 */
export interface UnifyProblem {
  equations: UnifyEquation[];
  context: TTKContext;
}

/**
 * A substitution maps hole IDs and variable indices to terms.
 *
 * The map uses string keys:
 * - For holes: the hole ID (e.g., "?x", "?_auto_1")
 * - For variables: "var:" + index (e.g., "var:0", "var:3")
 *
 * Variable substitutions arise from dependent pattern matching on indexed types.
 * For example, matching on `refl : Equal A x x` against `Equal Nat a b` produces
 * a substitution that `a = b` (represented as var:1 := Var(0) or vice versa).
 */
export type Substitution = Map<string, TTKTerm>;

/**
 * Key prefix for variable substitutions in the substitution map.
 */
const VAR_KEY_PREFIX = 'var:';

/**
 * Create a substitution key for a variable index.
 */
export function varKey(index: number): string {
  return `${VAR_KEY_PREFIX}${index}`;
}

/**
 * Check if a substitution key is for a variable (vs a hole).
 */
export function isVarKey(key: string): boolean {
  return key.startsWith(VAR_KEY_PREFIX);
}

/**
 * Extract the variable index from a var key.
 */
export function varIndexFromKey(key: string): number {
  return parseInt(key.substring(VAR_KEY_PREFIX.length), 10);
}

/**
 * Result of a unification attempt.
 */
export type UnifyResult =
  | { tag: 'success'; substitution: Substitution }
  | { tag: 'failure'; reason: string }
  | { tag: 'stuck'; reason: string };

/**
 * Configuration options for unification.
 */
export interface UnifyOptions {
  /**
   * If true, enables the deletion rule (UIP / Streicher's K).
   * This allows deleting equations of the form `x = x`.
   *
   * In HoTT, this is unsound as types can have higher structure.
   * In traditional type theory (like Lean without HoTT), this is sound.
   *
   * Default: false (--without-K mode)
   */
  useUIP?: boolean;

  /**
   * Map of function definitions for WHNF reduction.
   * This allows unification to reduce function applications like `plus Zero b` to `b`.
   */
  definitions?: Map<string, TTKTerm>;
}

// ============================================================================
// Substitution Operations
// ============================================================================

/**
 * Create an empty substitution.
 */
export function emptySubstitution(): Substitution {
  return new Map();
}

/**
 * Extend a substitution with a new mapping.
 * Throws if the hole is already mapped to a different term.
 */
export function extendSubstitution(
  subst: Substitution,
  holeId: string,
  term: TTKTerm
): Substitution {
  const existing = subst.get(holeId);
  if (existing !== undefined) {
    // Check if the existing mapping is compatible
    if (!isDefinitionallyEqual(existing, term)) {
      throw new Error(
        `Conflicting substitutions for hole ?${holeId}: ` +
        `${prettyPrint(existing)} vs ${prettyPrint(term)}`
      );
    }
    return subst; // Already mapped to the same term
  }

  const newSubst = new Map(subst);
  newSubst.set(holeId, term);
  return newSubst;
}

/**
 * Compose two substitutions.
 * The second substitution is applied first, then the first.
 */
export function composeSubstitutions(
  subst1: Substitution,
  subst2: Substitution
): Substitution {
  const result = new Map(subst1);

  for (const [holeId, term] of subst2) {
    const appliedTerm = applySubstitution(subst1, term);
    const existing = result.get(holeId);
    if (existing !== undefined && !isDefinitionallyEqual(existing, appliedTerm)) {
      throw new Error(
        `Conflicting substitutions for hole ?${holeId} during composition`
      );
    }
    result.set(holeId, appliedTerm);
  }

  return result;
}

/**
 * Apply a substitution to a term, replacing holes and variables with their assigned values.
 *
 * This handles both:
 * - Hole substitutions: ?x -> term (from meta-variable solving)
 * - Variable substitutions: Var(i) -> term (from dependent pattern matching)
 */
export function applySubstitution(subst: Substitution, term: TTKTerm): TTKTerm {
  switch (term.tag) {
    case 'Var': {
      // Check if this variable has a substitution
      const replacement = subst.get(varKey(term.index));
      if (replacement !== undefined) {
        // Recursively apply substitution in case the replacement has more substitutable terms
        return applySubstitution(subst, replacement);
      }
      return term;
    }

    case 'Sort':
    case 'Const':
      return term;

    case 'Hole': {
      const replacement = subst.get(term.id);
      if (replacement !== undefined) {
        // Recursively apply substitution in case the replacement has holes
        return applySubstitution(subst, replacement);
      }
      return term;
    }

    case 'App':
      return {
        tag: 'App',
        fn: applySubstitution(subst, term.fn),
        arg: applySubstitution(subst, term.arg),
      };

    case 'Binder': {
      const newDomain = applySubstitution(subst, term.domain);
      const newBody = applySubstitution(subst, term.body);

      if (term.binderKind.tag === 'BLet') {
        return {
          ...term,
          domain: newDomain,
          body: newBody,
          binderKind: {
            tag: 'BLet',
            defVal: applySubstitution(subst, term.binderKind.defVal),
          },
        };
      }

      return {
        ...term,
        domain: newDomain,
        body: newBody,
      };
    }

    case 'Annot':
      return {
        tag: 'Annot',
        term: applySubstitution(subst, term.term),
        type: applySubstitution(subst, term.type),
      };

    case 'Match':
      return {
        tag: 'Match',
        scrutinee: applySubstitution(subst, term.scrutinee),
        clauses: term.clauses.map(c => ({
          patterns: c.patterns,
          rhs: applySubstitution(subst, c.rhs)
        }))
      };
  }
}

/**
 * Apply a substitution to all equations in a problem.
 */
export function applySubstitutionToProblem(
  subst: Substitution,
  problem: UnifyProblem
): UnifyProblem {
  return {
    equations: problem.equations.map((eq) => ({
      lhs: applySubstitution(subst, eq.lhs),
      rhs: applySubstitution(subst, eq.rhs),
      type: applySubstitution(subst, eq.type),
    })),
    context: problem.context,
  };
}

// ============================================================================
// Occurs Check (Cycle Detection)
// ============================================================================

/**
 * Check if a hole occurs in a term (cycle detection).
 * Returns true if the hole with the given ID appears in the term.
 */
export function holeOccursIn(holeId: string, term: TTKTerm): boolean {
  switch (term.tag) {
    case 'Var':
    case 'Sort':
    case 'Const':
      return false;

    case 'Hole':
      return term.id === holeId;

    case 'App':
      return holeOccursIn(holeId, term.fn) || holeOccursIn(holeId, term.arg);

    case 'Binder': {
      if (holeOccursIn(holeId, term.domain)) return true;
      if (holeOccursIn(holeId, term.body)) return true;
      if (term.binderKind.tag === 'BLet') {
        return holeOccursIn(holeId, term.binderKind.defVal);
      }
      return false;
    }

    case 'Annot':
      return holeOccursIn(holeId, term.term) || holeOccursIn(holeId, term.type);

    case 'Match':
      if (holeOccursIn(holeId, term.scrutinee)) return true;
      for (const clause of term.clauses) {
        if (holeOccursIn(holeId, clause.rhs)) return true;
      }
      return false;
  }
}

// ============================================================================
// Constructor Detection
// ============================================================================

/**
 * A constructor application is a constant applied to arguments.
 * This represents `Constructor arg1 arg2 ...`
 */
export interface ConstructorApp {
  name: string;
  args: TTKTerm[];
}

/**
 * Try to decompose a term into a constructor application.
 * Returns null if the term is not a constructor application.
 *
 * A constructor application is identified as:
 * - A Const (potentially applied to arguments)
 * - The Const name starts with lowercase or is a known constructor
 *
 * For now, we use a simple heuristic: any Const applied to arguments.
 * In a full implementation, we'd check against a signature/environment.
 */
export function asConstructorApp(term: TTKTerm): ConstructorApp | null {
  const args: TTKTerm[] = [];
  let current = term;

  // Collect arguments from nested applications
  while (current.tag === 'App') {
    args.unshift(current.arg);
    current = current.fn;
  }

  // The head should be a constant (constructor)
  if (current.tag === 'Const') {
    return {
      name: current.name,
      args,
    };
  }

  return null;
}

/**
 * Check if a term is a rigid term (not a hole/metavariable).
 * Rigid terms are: Var, Sort, Const, App with rigid head, Binder.
 */
export function isRigid(term: TTKTerm): boolean {
  switch (term.tag) {
    case 'Var':
    case 'Sort':
    case 'Const':
    case 'Binder':
      return true;
    case 'App':
      return isRigid(term.fn);
    case 'Hole':
      return false;
    case 'Annot':
      return isRigid(term.term);

    case 'Match':
      return isRigid(term.scrutinee);
  }
}

/**
 * Check if a term is flexible (a hole or has a hole as head).
 */
export function isFlexible(term: TTKTerm): boolean {
  return !isRigid(term);
}

// ============================================================================
// Unification Rules
// ============================================================================

/**
 * Result of applying a single unification rule.
 */
type RuleResult =
  | { tag: 'progress'; newEquations: UnifyEquation[]; substitution: Substitution }
  | { tag: 'solved'; substitution: Substitution }
  | { tag: 'failure'; reason: string }
  | { tag: 'stuck' };

/**
 * DELETION RULE
 *
 * If lhs and rhs are definitionally equal, the equation can be deleted.
 *
 * IMPORTANT: This rule is only valid with UIP (Uniqueness of Identity Proofs).
 * Without UIP, we cannot assume that all proofs of `x = x` are equal.
 *
 * When useUIP is false, this only deletes reflexive equations where both
 * sides are the exact same term (syntactically), which is always safe.
 */
function tryDeletion(
  eq: UnifyEquation,
  ctx: TTKContext,
  options: UnifyOptions
): RuleResult {
  // First, check definitional equality (includes beta/eta conversion)
  if (convertible(eq.lhs, eq.rhs, ctx)) {
    // If UIP is enabled, we can delete any reflexive equation
    if (options.useUIP) {
      return { tag: 'solved', substitution: emptySubstitution() };
    }

    // Without UIP, we can only delete if both sides are syntactically identical
    // This is always safe because it doesn't rely on UIP
    if (isDefinitionallyEqual(eq.lhs, eq.rhs)) {
      return { tag: 'solved', substitution: emptySubstitution() };
    }

    // Without UIP: we're stuck on reflexive equations that need computation
    // The equation x = x cannot be deleted because there might be multiple
    // proofs of reflexivity in HoTT
    return { tag: 'stuck' };
  }

  return { tag: 'stuck' };
}

/**
 * SOLUTION RULE
 *
 * If one side is a hole (metavariable) and the other is a term,
 * assign the term to the hole.
 *
 * Preconditions:
 * - The hole must not occur in the term (occurs check / cycle detection)
 * - The term must be well-typed in the hole's context
 */
function trySolution(
  eq: UnifyEquation,
  _ctx: TTKContext,
  _options: UnifyOptions
): RuleResult {
  // Check if LHS is a hole
  if (eq.lhs.tag === 'Hole') {
    const holeId = eq.lhs.id;
    const term = eq.rhs;

    // Occurs check: fail if the hole appears in the term (cycle)
    if (holeOccursIn(holeId, term)) {
      return {
        tag: 'failure',
        reason: `Cycle detected: hole ?${holeId} occurs in ${prettyPrint(term)}`,
      };
    }

    // Success: assign the term to the hole
    const subst = extendSubstitution(emptySubstitution(), holeId, term);
    return { tag: 'solved', substitution: subst };
  }

  // Check if RHS is a hole
  if (eq.rhs.tag === 'Hole') {
    const holeId = eq.rhs.id;
    const term = eq.lhs;

    // Occurs check
    if (holeOccursIn(holeId, term)) {
      return {
        tag: 'failure',
        reason: `Cycle detected: hole ?${holeId} occurs in ${prettyPrint(term)}`,
      };
    }

    const subst = extendSubstitution(emptySubstitution(), holeId, term);
    return { tag: 'solved', substitution: subst };
  }

  return { tag: 'stuck' };
}

/**
 * INJECTIVITY RULE
 *
 * If both sides are applications of the same constructor,
 * decompose into equations between corresponding arguments.
 *
 * c u₁ ... uₙ = c v₁ ... vₙ  ⟹  u₁ = v₁, ..., uₙ = vₙ
 *
 * In --without-K mode, this additionally requires that the indices
 * of the datatype are self-unifiable. For simplicity, we currently
 * allow injectivity for any constructor application.
 *
 * TODO: Implement proper self-unifiability check for indexed types.
 */
function tryInjectivity(
  eq: UnifyEquation,
  ctx: TTKContext,
  options: UnifyOptions
): RuleResult {
  // Reduce to WHNF first (pass definitions for function reduction)
  const lhsWhnf = whnf(eq.lhs, ctx, options.definitions);
  const rhsWhnf = whnf(eq.rhs, ctx, options.definitions);

  // Try to decompose as constructor applications
  const lhsCtor = asConstructorApp(lhsWhnf);
  const rhsCtor = asConstructorApp(rhsWhnf);

  if (lhsCtor === null || rhsCtor === null) {
    return { tag: 'stuck' };
  }

  // If different constructors, it's a conflict
  if (lhsCtor.name !== rhsCtor.name) {
    return {
      tag: 'failure',
      reason: `Conflict: constructor ${lhsCtor.name} ≠ ${rhsCtor.name}`,
    };
  }

  // Same constructor: decompose (injectivity)
  if (lhsCtor.args.length !== rhsCtor.args.length) {
    return {
      tag: 'failure',
      reason: `Arity mismatch for constructor ${lhsCtor.name}: ` +
        `${lhsCtor.args.length} vs ${rhsCtor.args.length}`,
    };
  }

  // In --without-K mode, we need to check self-unifiability of indices.
  // For now, we implement a simplified version:
  // - If useUIP is false, we still allow injectivity but should be more careful
  // - A proper implementation would check if the datatype indices can be self-unified

  // Create new equations for each pair of arguments
  const newEquations: UnifyEquation[] = [];
  for (let i = 0; i < lhsCtor.args.length; i++) {
    // Note: We should infer the type of each argument here.
    // For now, we use a placeholder (the same type as the original equation).
    // In a full implementation, we'd compute the actual argument types.
    newEquations.push({
      lhs: lhsCtor.args[i],
      rhs: rhsCtor.args[i],
      type: eq.type, // Simplified: should be the actual argument type
    });
  }

  return {
    tag: 'progress',
    newEquations,
    substitution: emptySubstitution(),
  };
}

/**
 * CONFLICT RULE
 *
 * If both sides are applications of different constructors of the same type,
 * the equation is impossible.
 *
 * This is a "negative success": we've proven unification is impossible.
 */
function tryConflict(
  eq: UnifyEquation,
  ctx: TTKContext,
  options: UnifyOptions
): RuleResult {
  // Reduce to WHNF (pass definitions for function reduction)
  const lhsWhnf = whnf(eq.lhs, ctx, options.definitions);
  const rhsWhnf = whnf(eq.rhs, ctx, options.definitions);

  const lhsCtor = asConstructorApp(lhsWhnf);
  const rhsCtor = asConstructorApp(rhsWhnf);

  if (lhsCtor !== null && rhsCtor !== null && lhsCtor.name !== rhsCtor.name) {
    return {
      tag: 'failure',
      reason: `Conflict: constructor ${lhsCtor.name} ≠ ${rhsCtor.name}`,
    };
  }

  return { tag: 'stuck' };
}

/**
 * CYCLE RULE
 *
 * If we're trying to unify a variable with a term that contains it,
 * the equation is impossible (infinite regress).
 *
 * This is already handled by the occurs check in the solution rule,
 * but we include it here for completeness.
 */
function tryCycle(
  eq: UnifyEquation,
  _ctx: TTKContext,
  _options: UnifyOptions
): RuleResult {
  // For holes, cycle detection is in the solution rule
  // For variables, we check if one side is a variable that occurs in the other
  if (eq.lhs.tag === 'Var') {
    if (occursIn(eq.lhs.index, eq.rhs)) {
      return {
        tag: 'failure',
        reason: `Cycle: variable #${eq.lhs.index} occurs in ${prettyPrint(eq.rhs)}`,
      };
    }
  }

  if (eq.rhs.tag === 'Var') {
    if (occursIn(eq.rhs.index, eq.lhs)) {
      return {
        tag: 'failure',
        reason: `Cycle: variable #${eq.rhs.index} occurs in ${prettyPrint(eq.lhs)}`,
      };
    }
  }

  return { tag: 'stuck' };
}

/**
 * ETA RULE (for functions)
 *
 * If both sides are lambdas, unify their bodies under an extended context.
 * λ(x:A). u = λ(x:A). v  ⟹  u = v (in extended context with x:A)
 *
 * Also handles eta-expansion: f = λx. f x
 */
function tryEta(
  eq: UnifyEquation,
  ctx: TTKContext,
  options: UnifyOptions
): RuleResult {
  const lhsWhnf = whnf(eq.lhs, ctx, options.definitions);
  const rhsWhnf = whnf(eq.rhs, ctx, options.definitions);

  // Both are lambdas
  if (
    lhsWhnf.tag === 'Binder' &&
    lhsWhnf.binderKind.tag === 'BLam' &&
    rhsWhnf.tag === 'Binder' &&
    rhsWhnf.binderKind.tag === 'BLam'
  ) {
    // First unify the domains
    const domainEq: UnifyEquation = {
      lhs: lhsWhnf.domain,
      rhs: rhsWhnf.domain,
      type: { tag: 'Sort', level: 1 }, // Type
    };

    // Then unify bodies
    // TODO: Pass extended context through UnifyEquation for proper scoping under binders
    const bodyEq: UnifyEquation = {
      lhs: lhsWhnf.body,
      rhs: rhsWhnf.body,
      type: eq.type, // Simplified: should compute codomain type
    };

    return {
      tag: 'progress',
      newEquations: [domainEq, bodyEq],
      substitution: emptySubstitution(),
    };
  }

  // Both are Pi types
  if (
    lhsWhnf.tag === 'Binder' &&
    lhsWhnf.binderKind.tag === 'BPi' &&
    rhsWhnf.tag === 'Binder' &&
    rhsWhnf.binderKind.tag === 'BPi'
  ) {
    // Unify domains
    const domainEq: UnifyEquation = {
      lhs: lhsWhnf.domain,
      rhs: rhsWhnf.domain,
      type: { tag: 'Sort', level: 1 },
    };

    // Unify codomains
    // TODO: Pass extended context through UnifyEquation for proper scoping under binders
    const codomainEq: UnifyEquation = {
      lhs: lhsWhnf.body,
      rhs: rhsWhnf.body,
      type: { tag: 'Sort', level: 1 },
    };

    return {
      tag: 'progress',
      newEquations: [domainEq, codomainEq],
      substitution: emptySubstitution(),
    };
  }

  return { tag: 'stuck' };
}

// ============================================================================
// Main Unification Algorithm
// ============================================================================

/**
 * VARIABLE SOLUTION RULE
 *
 * If one side is a variable and the other is a different variable or term,
 * record this equality as a variable substitution.
 *
 * This handles dependent pattern matching on indexed types, where unification
 * determines that one pattern variable equals another.
 *
 * For example, matching `refl : Equal A x x` against `Equal Nat a b` produces
 * a substitution that maps one of `a` or `b` to the other.
 *
 * For Var = Var equations, we substitute the higher-indexed variable with
 * the lower-indexed one. This is a canonical choice that ensures transitivity.
 *
 * For Var = Term equations, we substitute the variable with the term
 * (after checking for cycles).
 */
function tryVarSolution(
  eq: UnifyEquation,
  ctx: TTKContext,
  _options: UnifyOptions
): RuleResult {
  const lhsWhnf = eq.lhs;
  const rhsWhnf = eq.rhs;

  // Case 1: Var = Var (different indices)
  if (lhsWhnf.tag === 'Var' && rhsWhnf.tag === 'Var') {
    if (lhsWhnf.index === rhsWhnf.index) {
      // Same variable - already handled by deletion rule
      return { tag: 'stuck' };
    }

    // The unification succeeds - these two variables are now known to be equal.
    // We substitute the higher-indexed variable with the lower-indexed one.
    // This is a canonical choice for consistency.
    const subst = new Map<string, TTKTerm>();

    const [higherIdx, lowerIdx] = lhsWhnf.index > rhsWhnf.index
      ? [lhsWhnf.index, rhsWhnf.index]
      : [rhsWhnf.index, lhsWhnf.index];

    // Create a substitution: var:higherIdx := Var(lowerIdx)
    subst.set(varKey(higherIdx), { tag: 'Var', index: lowerIdx });

    // Also record human-readable info for UI display
    if (higherIdx < ctx.length && lowerIdx < ctx.length) {
      const higherName = ctx[higherIdx].name;
      const lowerName = ctx[lowerIdx].name;
      subst.set(`name:${higherName}`, { tag: 'Const', name: lowerName, type: ctx[lowerIdx].type });
    }

    return { tag: 'solved', substitution: subst };
  }

  // Case 2: Var = Term (non-variable, non-hole term)
  // Substitute the variable with the term
  if (lhsWhnf.tag === 'Var' && rhsWhnf.tag !== 'Var' && rhsWhnf.tag !== 'Hole') {
    // Occurs check: fail if the variable appears in the term
    if (occursIn(lhsWhnf.index, rhsWhnf)) {
      return {
        tag: 'failure',
        reason: `Cycle: variable #${lhsWhnf.index} occurs in ${prettyPrint(rhsWhnf)}`,
      };
    }

    const subst = new Map<string, TTKTerm>();
    subst.set(varKey(lhsWhnf.index), rhsWhnf);
    return { tag: 'solved', substitution: subst };
  }

  // Case 3: Term = Var
  if (rhsWhnf.tag === 'Var' && lhsWhnf.tag !== 'Var' && lhsWhnf.tag !== 'Hole') {
    // Occurs check
    if (occursIn(rhsWhnf.index, lhsWhnf)) {
      return {
        tag: 'failure',
        reason: `Cycle: variable #${rhsWhnf.index} occurs in ${prettyPrint(lhsWhnf)}`,
      };
    }

    const subst = new Map<string, TTKTerm>();
    subst.set(varKey(rhsWhnf.index), lhsWhnf);
    return { tag: 'solved', substitution: subst };
  }

  return { tag: 'stuck' };
}

/**
 * Try all unification rules on a single equation.
 * Returns the result of the first rule that makes progress.
 */
function tryRulesOnEquation(
  eq: UnifyEquation,
  ctx: TTKContext,
  options: UnifyOptions
): RuleResult {
  // Order of rules matters for efficiency:
  // 1. Deletion - handles trivial reflexive equations
  // 2. Solution - handles holes/metavariables
  // 3. VarSolution - handles variable-to-variable unification (NEW!)
  // 4. Injectivity - decomposes constructor equations
  // 5. Conflict - detects impossible equations
  // 6. Cycle - detects infinite regress
  // 7. Eta - handles function/Pi type equations

  const rules = [
    tryDeletion,
    trySolution,
    tryVarSolution,  // NEW: handle Var = Var and Var = Term
    tryInjectivity,
    tryConflict,
    tryCycle,
    tryEta,
  ];

  for (const rule of rules) {
    const result = rule(eq, ctx, options);
    if (result.tag !== 'stuck') {
      return result;
    }
  }

  return { tag: 'stuck' };
}

/**
 * Unify a list of equations.
 *
 * This is the main entry point for unification. It takes a list of
 * equation pairs and a context, and returns either:
 * - A substitution that makes all equations hold
 * - A failure reason (negative success or actual failure)
 * - Stuck if no progress can be made
 *
 * @param equations - Array of [lhs, rhs] pairs to unify
 * @param context - The typing context
 * @param options - Unification options (useUIP, etc.)
 */
export function unify(
  equations: Array<{ lhs: TTKTerm; rhs: TTKTerm; type: TTKTerm }>,
  context: TTKContext = [],
  options: UnifyOptions = {}
): UnifyResult {
  const opts: UnifyOptions = {
    useUIP: false,
    ...options,
  };

  let problem: UnifyProblem = {
    equations: equations.map((eq) => ({ ...eq })),
    context,
  };

  let substitution = emptySubstitution();
  let madeProgress = true;

  // Keep iterating until we can't make progress
  while (madeProgress && problem.equations.length > 0) {
    madeProgress = false;

    // Try to solve each equation
    const remainingEquations: UnifyEquation[] = [];

    for (const eq of problem.equations) {
      const result = tryRulesOnEquation(eq, problem.context, opts);

      switch (result.tag) {
        case 'solved':
          // Equation is solved, add substitution
          madeProgress = true;
          try {
            substitution = composeSubstitutions(result.substitution, substitution);
          } catch (e) {
            return {
              tag: 'failure',
              reason: e instanceof Error ? e.message : String(e),
            };
          }
          // Apply new substitution to remaining equations
          remainingEquations.forEach((remEq, i) => {
            remainingEquations[i] = {
              lhs: applySubstitution(result.substitution, remEq.lhs),
              rhs: applySubstitution(result.substitution, remEq.rhs),
              type: applySubstitution(result.substitution, remEq.type),
            };
          });
          break;

        case 'progress':
          // Made progress, add new equations
          madeProgress = true;
          try {
            substitution = composeSubstitutions(result.substitution, substitution);
          } catch (e) {
            return {
              tag: 'failure',
              reason: e instanceof Error ? e.message : String(e),
            };
          }
          // Add new equations (with substitution applied)
          for (const newEq of result.newEquations) {
            remainingEquations.push({
              lhs: applySubstitution(substitution, newEq.lhs),
              rhs: applySubstitution(substitution, newEq.rhs),
              type: applySubstitution(substitution, newEq.type),
            });
          }
          break;

        case 'failure':
          // Unification failed (conflict, cycle, etc.)
          return { tag: 'failure', reason: result.reason };

        case 'stuck':
          // Keep this equation for next iteration
          remainingEquations.push(eq);
          break;
      }
    }

    problem = {
      equations: remainingEquations,
      context: problem.context,
    };
  }

  // Check if we solved all equations
  if (problem.equations.length === 0) {
    return { tag: 'success', substitution };
  }

  // We're stuck with unsolved equations
  const stuckEqs = problem.equations
    .map((eq) => `${prettyPrint(eq.lhs)} = ${prettyPrint(eq.rhs)}`)
    .join(', ');

  return {
    tag: 'stuck',
    reason: `Cannot solve: ${stuckEqs}`,
  };
}

// ============================================================================
// Convenience Functions
// ============================================================================

/**
 * Unify two terms, returning a substitution if successful.
 */
export function unifyTerms(
  lhs: TTKTerm,
  rhs: TTKTerm,
  type: TTKTerm,
  context: TTKContext = [],
  options: UnifyOptions = {}
): UnifyResult {
  return unify([{ lhs, rhs, type }], context, options);
}

/**
 * Check if two terms can be unified (ignoring the actual substitution).
 */
export function canUnify(
  lhs: TTKTerm,
  rhs: TTKTerm,
  type: TTKTerm,
  context: TTKContext = [],
  options: UnifyOptions = {}
): boolean {
  const result = unifyTerms(lhs, rhs, type, context, options);
  return result.tag === 'success';
}

/**
 * Unify and apply the resulting substitution to a term.
 * Returns the term with holes filled in by the unification.
 */
export function unifyAndApply(
  equations: Array<{ lhs: TTKTerm; rhs: TTKTerm; type: TTKTerm }>,
  term: TTKTerm,
  context: TTKContext = [],
  options: UnifyOptions = {}
): { result: TTKTerm; substitution: Substitution } | { error: string } {
  const unifyResult = unify(equations, context, options);

  switch (unifyResult.tag) {
    case 'success':
      return {
        result: applySubstitution(unifyResult.substitution, term),
        substitution: unifyResult.substitution,
      };
    case 'failure':
      return { error: unifyResult.reason };
    case 'stuck':
      return { error: `Unification stuck: ${unifyResult.reason}` };
  }
}
