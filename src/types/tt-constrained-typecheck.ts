/**
 * Constraint-Based Type Checking with Metavariables
 *
 * This module extends the type-checker from tt-typecheck.ts to support
 * type-checking in the presence of unsolved metavariables, based on:
 *
 * "Type checking in the presence of meta-variables"
 * by Ulf Norell and Catarina Coquand
 * https://www.cse.chalmers.se/~ulfn/papers/meta-variables.pdf
 *
 * KEY INNOVATION: Guarded Constants
 * ==================================
 * When we can't immediately verify that M : B (because types involve unsolved metas),
 * we replace M with a "guarded constant" p that:
 * - Has type B (so it's well-typed for further checking)
 * - Computes to M only when its guards (constraints) are solved
 * - Prevents ill-typed terms from being evaluated during type-checking
 *
 * Example from the paper:
 *   Checking: λg. g 0 : ((x : F ?) → F (¬ x)) → Nat
 *   Problem: F ? might not equal Nat, so (g 0) might be ill-typed
 *   Solution: Replace with guarded constant p where:
 *     p : Nat = (g 0) when F ? = Nat
 *
 * This ensures we never normalize ill-typed terms, maintaining soundness.
 */

import {
  TTKTerm,
  TTKContext,
  mkConst,
  mkType,
  mkPi,
  mkApp,
  mkLet,
  subst,
  prettyPrint,
} from './tt-kernel';

import {
  inferType as baseInferType,
  convertible as baseConvertible,
  whnf as baseWhnf,
  TypeCheckError,
  extendContext,
} from './tt-typecheck';

import {
  unifyTerms,
  applySubstitution,
  Substitution,
  UnifyResult,
} from './tt-unify';

// ============================================================================
// Constraint Types
// ============================================================================

/**
 * A type constraint that must be solved for well-typedness.
 *
 * These correspond to the constraints in Section 3 of the paper.
 */
export type Constraint =
  | { tag: 'TypeEq'; ctx: TTKContext; lhs: TTKTerm; rhs: TTKTerm; description?: string }
  | { tag: 'TermEq'; ctx: TTKContext; lhs: TTKTerm; rhs: TTKTerm; type: TTKTerm; description?: string }

/**
 * Pretty-print a constraint for debugging
 */
export function prettyPrintConstraint(c: Constraint): string {
  const desc = c.description ? ` (${c.description})` : '';
  switch (c.tag) {
    case 'TypeEq':
      return `${prettyPrint(c.lhs)} = ${prettyPrint(c.rhs)}${desc}`;
    case 'TermEq':
      return `${prettyPrint(c.lhs)} = ${prettyPrint(c.rhs)} : ${prettyPrint(c.type)}${desc}`;
  }
}

// ============================================================================
// Guarded Constants
// ============================================================================

/**
 * A guarded constant is a proxy for a potentially ill-typed term.
 *
 * From the paper:
 *   p : A = M when C
 *
 * The constant p:
 * - Has type A (well-typed)
 * - Computes to M when all constraints in C are solved
 * - Stays stuck (doesn't reduce) if any constraints are unsolved
 *
 * This ensures we never evaluate M unless we know it's well-typed.
 */
export interface GuardedConst {
  id: string;           // Unique identifier
  type: TTKTerm;        // Type A (guaranteed well-typed)
  value: TTKTerm;       // Value M (computes to this when guards solved)
  guards: Constraint[]; // Constraints that must hold for M to be well-typed
  ctx: TTKContext;      // Context where this was created
}

/**
 * State for constraint-based type-checking.
 * Threads through the algorithm to collect constraints and guarded constants.
 */
export interface CheckState {
  constraints: Constraint[];      // Collected constraints
  guardedConsts: GuardedConst[];  // Created guarded constants
  nextGuardId: number;             // Counter for generating unique IDs
}

/**
 * Create an empty check state
 */
export function emptyCheckState(): CheckState {
  return {
    constraints: [],
    guardedConsts: [],
    nextGuardId: 0,
  };
}

/**
 * Add a constraint to the state
 */
export function addConstraint(state: CheckState, constraint: Constraint): CheckState {
  return {
    ...state,
    constraints: [...state.constraints, constraint],
  };
}

/**
 * Create a guarded constant and add it to the state.
 *
 * Returns: [new state, term representing the guarded constant]
 */
export function createGuardedConst(
  state: CheckState,
  type: TTKTerm,
  value: TTKTerm,
  guards: Constraint[],
  ctx: TTKContext
): [CheckState, TTKTerm] {
  const id = `guard_${state.nextGuardId}`;
  const guarded: GuardedConst = {
    id,
    type,
    value,
    guards,
    ctx,
  };

  const newState: CheckState = {
    constraints: state.constraints,
    guardedConsts: [...state.guardedConsts, guarded],
    nextGuardId: state.nextGuardId + 1,
  };

  // Return a constant term representing this guarded constant
  const term = mkConst(id, type);

  return [newState, term];
}

// ============================================================================
// Result Types
// ============================================================================

/**
 * Result of constraint-based type synthesis.
 * Returns inferred type, elaborated term, and updated state.
 */
export interface InferResult {
  type: TTKTerm;           // Inferred type
  term: TTKTerm;           // Elaborated term (with guarded constants)
  state: CheckState;       // Updated state with constraints
}

/**
 * Result of constraint-based type checking.
 * Returns elaborated term and updated state.
 */
export interface CheckResult {
  term: TTKTerm;           // Elaborated term (with guarded constants)
  state: CheckState;       // Updated state with constraints
}

// ============================================================================
// Constraint-Based Type Inference
// ============================================================================

/**
 * Infer the type of a term, generating constraints when needed.
 *
 * This extends the standard type inference to handle metavariables:
 * - When checking App, if the function type is unknown, create constraints
 * - When checking Binder types, allow unsolved metas in domains/codomains
 * - Generate well-typed approximations using guarded constants
 */
export function inferTypeWithConstraints(
  term: TTKTerm,
  ctx: TTKContext,
  state: CheckState
): InferResult {
  // For most cases, we can use the base type inference
  // The key difference is in handling applications with metavariables

  switch (term.tag) {
    case 'Var':
    case 'Sort':
    case 'Const':
    case 'Hole':
      // These can be handled by base inference (no constraints needed)
      try {
        const type = baseInferType(term, ctx);
        return { type, term, state };
      } catch (e) {
        throw new TypeCheckError(
          `Type inference failed: ${e instanceof Error ? e.message : String(e)}`,
          term,
          ctx
        );
      }

    case 'App': {
      // Infer type of function
      const fnResult = inferTypeWithConstraints(term.fn, ctx, state);
      let currentState = fnResult.state;

      // Normalize function type to see if it's a Pi
      const fnTypeNorm = baseWhnf(fnResult.type, ctx);

      if (fnTypeNorm.tag === 'Binder' && fnTypeNorm.binderKind.tag === 'BPi') {
        // Check argument against domain
        const argResult = checkTypeWithConstraints(term.arg, fnTypeNorm.domain, ctx, currentState);
        currentState = argResult.state;

        // Result type: codomain with argument substituted
        const resultType = subst(0, argResult.term, fnTypeNorm.body);

        const elaboratedApp = mkApp(fnResult.term, argResult.term);
        return { type: resultType, term: elaboratedApp, state: currentState };
      }

      // Function type might be a metavariable - stuck
      // For now, throw error (full implementation would create fresh meta for result type)
      throw new TypeCheckError(
        `Cannot infer type of application: function has non-Pi type ${prettyPrint(fnTypeNorm)}`,
        term,
        ctx
      );
    }

    case 'Binder': {
      // Handle Pi, Lambda, Let types
      switch (term.binderKind.tag) {
        case 'BPi': {
          const domResult = inferTypeWithConstraints(term.domain, ctx, state);
          let currentState = domResult.state;

          const extCtx = extendContext(ctx, term.name, term.domain);
          const bodyResult = inferTypeWithConstraints(term.body, extCtx, currentState);
          currentState = bodyResult.state;

          // Pi type has type = max(dom level, body level)
          if (domResult.type.tag === 'Sort' && bodyResult.type.tag === 'Sort') {
            const level = Math.max(domResult.type.level, bodyResult.type.level);
            return {
              type: mkType(level),
              term: {
                tag: 'Binder',
                name: term.name,
                binderKind: { tag: 'BPi' },
                domain: domResult.term,
                body: bodyResult.term,
              },
              state: currentState,
            };
          }

          throw new TypeCheckError(
            `Pi domain and codomain must be types`,
            term,
            ctx
          );
        }

        case 'BLam': {
          const domResult = inferTypeWithConstraints(term.domain, ctx, state);
          let currentState = domResult.state;

          const extCtx = extendContext(ctx, term.name, term.domain);
          const bodyResult = inferTypeWithConstraints(term.body, extCtx, currentState);
          currentState = bodyResult.state;

          // Lambda has type: Pi(x : domain) -> bodyType
          const resultType = mkPi(domResult.term, bodyResult.type, term.name);
          const elaboratedLam = {
            tag: 'Binder' as const,
            name: term.name,
            binderKind: { tag: 'BLam' as const },
            domain: domResult.term,
            body: bodyResult.term,
          };

          return { type: resultType, term: elaboratedLam, state: currentState };
        }

        case 'BLet': {
          const typeResult = inferTypeWithConstraints(term.domain, ctx, state);
          let currentState = typeResult.state;

          const valResult = checkTypeWithConstraints(
            term.binderKind.defVal,
            typeResult.term,
            ctx,
            currentState
          );
          currentState = valResult.state;

          const extCtx = extendContext(ctx, term.name, term.domain);
          const bodyResult = inferTypeWithConstraints(term.body, extCtx, currentState);
          currentState = bodyResult.state;

          const elaboratedLet = mkLet(
            term.name,
            typeResult.term,
            valResult.term,
            bodyResult.term
          );

          return { type: bodyResult.type, term: elaboratedLet, state: currentState };
        }
      }
    }

    case 'Annot': {
      const typeResult = inferTypeWithConstraints(term.type, ctx, state);
      let currentState = typeResult.state;

      const termResult = checkTypeWithConstraints(term.term, typeResult.term, ctx, currentState);
      currentState = termResult.state;

      return {
        type: typeResult.term,
        term: termResult.term,
        state: currentState,
      };
    }
  }
}

// ============================================================================
// Constraint-Based Type Checking
// ============================================================================

/**
 * Check that a term has the expected type, generating constraints when needed.
 *
 * This is the KEY function from the paper (Section 3.2).
 *
 * When we can't immediately verify M : A (because A involves unsolved metas),
 * we create a guarded constant instead of failing:
 *
 * 1. Try to check M : A normally
 * 2. If it fails due to unsolved metas, generate constraints
 * 3. Create guarded constant p : A = M when {constraints}
 * 4. Return p instead of M (well-typed approximation)
 */
export function checkTypeWithConstraints(
  term: TTKTerm,
  expectedType: TTKTerm,
  ctx: TTKContext,
  state: CheckState
): CheckResult {
  // Special case: Lambda against Pi type
  if (
    term.tag === 'Binder' &&
    term.binderKind.tag === 'BLam' &&
    expectedType.tag === 'Binder' &&
    expectedType.binderKind.tag === 'BPi'
  ) {
    // Check domain convertibility
    const domConstraint: Constraint = {
      tag: 'TypeEq',
      ctx,
      lhs: term.domain,
      rhs: expectedType.domain,
      description: 'Lambda domain check',
    };

    let currentState = addConstraint(state, domConstraint);

    // Check body in extended context
    const extCtx = extendContext(ctx, term.name, term.domain);
    const bodyResult = checkTypeWithConstraints(
      term.body,
      expectedType.body,
      extCtx,
      currentState
    );

    const elaboratedLam = {
      tag: 'Binder' as const,
      name: term.name,
      binderKind: { tag: 'BLam' as const },
      domain: term.domain,
      body: bodyResult.term,
    };

    return { term: elaboratedLam, state: bodyResult.state };
  }

  // General case: Infer type and check convertibility
  const inferResult = inferTypeWithConstraints(term, ctx, state);
  let currentState = inferResult.state;

  // Try to check convertibility
  try {
    // First try without constraints (fast path)
    if (baseConvertible(inferResult.type, expectedType, ctx)) {
      return { term: inferResult.term, state: currentState };
    }
  } catch {
    // Convertibility check might fail - that's okay, we'll create constraints
  }

  // Convertibility unknown - create constraint and guarded constant
  const convConstraint: Constraint = {
    tag: 'TypeEq',
    ctx,
    lhs: inferResult.type,
    rhs: expectedType,
    description: `Type mismatch: expected ${prettyPrint(expectedType)}, got ${prettyPrint(inferResult.type)}`,
  };

  currentState = addConstraint(currentState, convConstraint);

  // Create guarded constant: p : expectedType = term when {convConstraint}
  const [newState, guardedTerm] = createGuardedConst(
    currentState,
    expectedType,
    inferResult.term,
    [convConstraint],
    ctx
  );

  return { term: guardedTerm, state: newState };
}

// ============================================================================
// Constraint Solving
// ============================================================================

/**
 * Attempt to solve collected constraints using unification.
 *
 * This implements the constraint solving from Section 3.2 of the paper.
 *
 * Process:
 * 1. Try to solve each constraint via unification
 * 2. Apply successful substitutions to remaining constraints
 * 3. Return: solved substitution, remaining unsolved constraints, failed constraints
 */
export function solveConstraints(
  constraints: Constraint[],
  ctx: TTKContext = []
): {
  substitution: Substitution;
  solved: Constraint[];
  unsolved: Constraint[];
  failed: Array<{ constraint: Constraint; reason: string }>;
} {
  let solved: Constraint[] = [];
  let unsolved: Constraint[] = [];
  let failed: Array<{ constraint: Constraint; reason: string }> = [];
  let substitution: Substitution = new Map();

  for (const constraint of constraints) {
    // First apply existing substitution to the constraint
    const appliedConstraint = applySubstitutionToConstraint(constraint, substitution);

    let unifyResult: UnifyResult | null = null;

    switch (appliedConstraint.tag) {
      case 'TypeEq':
        unifyResult = unifyTerms(
          appliedConstraint.lhs,
          appliedConstraint.rhs,
          mkType(0), // Types have type Type
          appliedConstraint.ctx
        );
        break;

      case 'TermEq':
        unifyResult = unifyTerms(
          appliedConstraint.lhs,
          appliedConstraint.rhs,
          appliedConstraint.type,
          appliedConstraint.ctx
        );
        break;
    }

    if (unifyResult) {
      switch (unifyResult.tag) {
        case 'success':
          // Constraint solved!
          solved.push(constraint);
          // Compose with existing substitution
          // Check for conflicts: if we already have a mapping for a hole, check compatibility
          for (const [holeId, term] of unifyResult.substitution) {
            const existing = substitution.get(holeId);
            if (existing !== undefined) {
              // We already have a substitution for this hole - check if they're compatible
              const compatCheck = unifyTerms(existing, term, mkType(0), ctx);
              if (compatCheck.tag === 'failure') {
                failed.push({
                  constraint,
                  reason: `Conflicting substitutions for ?${holeId}: ${prettyPrint(existing)} vs ${prettyPrint(term)}`,
                });
                continue; // Don't add this substitution
              }
            } else {
              substitution.set(holeId, term);
            }
          }
          // Apply new substitution to unsolved constraints
          unsolved = unsolved.map((c) => applySubstitutionToConstraint(c, unifyResult.substitution));
          break;

        case 'failure':
          // Constraint is unsatisfiable
          failed.push({ constraint, reason: unifyResult.reason });
          break;

        case 'stuck':
          // Cannot solve yet - needs more information
          unsolved.push(constraint);
          break;
      }
    } else {
      unsolved.push(constraint);
    }
  }

  return { substitution, solved, unsolved, failed };
}

/**
 * Apply a substitution to a constraint
 */
function applySubstitutionToConstraint(c: Constraint, subst: Substitution): Constraint {
  switch (c.tag) {
    case 'TypeEq':
      return {
        ...c,
        lhs: applySubstitution(subst, c.lhs),
        rhs: applySubstitution(subst, c.rhs),
      };
    case 'TermEq':
      return {
        ...c,
        lhs: applySubstitution(subst, c.lhs),
        rhs: applySubstitution(subst, c.rhs),
        type: applySubstitution(subst, c.type),
      };
  }
}

/**
 * Solve constraints of a guarded constant.
 * If all guards solve, the constant can reduce to its value.
 */
export function solveGuardedConst(
  guarded: GuardedConst
): { solved: boolean; substitution?: Substitution; failures?: string[] } {
  const result = solveConstraints(guarded.guards, guarded.ctx);

  if (result.failed.length > 0) {
    return {
      solved: false,
      failures: result.failed.map((f) => f.reason),
    };
  }

  if (result.unsolved.length > 0) {
    return {
      solved: false,
    };
  }

  return {
    solved: true,
    substitution: result.substitution,
  };
}

// ============================================================================
// Integration with Standard Type-Checker
// ============================================================================

/**
 * Check a term with constraint generation, then solve constraints.
 *
 * This is a convenience function that combines:
 * 1. Constraint-based type-checking
 * 2. Constraint solving
 * 3. Application of solved substitutions
 *
 * Returns the elaborated term and any remaining unsolved constraints.
 */
export function checkAndSolve(
  term: TTKTerm,
  expectedType: TTKTerm,
  ctx: TTKContext = []
): {
  term: TTKTerm;
  substitution: Substitution;
  unsolvedConstraints: Constraint[];
  failedConstraints: Array<{ constraint: Constraint; reason: string }>;
} {
  const initialState = emptyCheckState();
  const checkResult = checkTypeWithConstraints(term, expectedType, ctx, initialState);

  const solveResult = solveConstraints(checkResult.state.constraints, ctx);

  // Apply substitution to the elaborated term
  const finalTerm = applySubstitution(solveResult.substitution, checkResult.term);

  return {
    term: finalTerm,
    substitution: solveResult.substitution,
    unsolvedConstraints: solveResult.unsolved,
    failedConstraints: solveResult.failed,
  };
}

/**
 * Infer type with constraint generation and solving.
 */
export function inferAndSolve(
  term: TTKTerm,
  ctx: TTKContext = []
): {
  type: TTKTerm;
  term: TTKTerm;
  substitution: Substitution;
  unsolvedConstraints: Constraint[];
  failedConstraints: Array<{ constraint: Constraint; reason: string }>;
} {
  const initialState = emptyCheckState();
  const inferResult = inferTypeWithConstraints(term, ctx, initialState);

  const solveResult = solveConstraints(inferResult.state.constraints, ctx);

  const finalTerm = applySubstitution(solveResult.substitution, inferResult.term);
  const finalType = applySubstitution(solveResult.substitution, inferResult.type);

  return {
    type: finalType,
    term: finalTerm,
    substitution: solveResult.substitution,
    unsolvedConstraints: solveResult.unsolved,
    failedConstraints: solveResult.failed,
  };
}
