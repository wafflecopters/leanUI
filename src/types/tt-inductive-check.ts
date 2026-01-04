/**
 * Inductive Type Validity Checking
 *
 * This module implements the core validity checks for inductive type definitions:
 *
 * 1. **Constructor Return Type Check**: Each constructor must return the inductive type
 *    being defined (with appropriate parameters/indices applied).
 *
 * 2. **Strict Positivity**: The inductive type being defined must only occur in
 *    strictly positive positions in constructor arguments. This means:
 *    - NOT to the left of any function arrow
 *    - Only as direct arguments or nested under other strictly positive types
 *
 * 3. **Universe Constraints**: For an inductive type in Sort level `s`, constructor
 *    argument types (excluding parameters) must be in universes < s.
 *
 * References:
 * - Lean 4 Reference: https://lean-lang.org/doc/reference/latest/The-Type-System/Inductive-Types/
 * - Why Strict Positivity: https://vilhelms.github.io/posts/why-must-inductive-types-be-strictly-positive/
 * - Counterexamples: https://counterexamples.org/strict-positivity.html
 */

import { TTKTerm, TTKContext, prettyPrint } from './tt-kernel';
import { inferType, whnf } from './tt-typecheck';
import { CheckError } from './tt-typecheck-decl';
import { IndexPath } from './source-position';

// ============================================================================
// Path Helpers
// ============================================================================

/**
 * Create a path to a constructor's type: constructors[i].type
 */
function constructorTypePath(ctorIndex: number): IndexPath {
  return [
    { kind: 'field', name: 'constructors' },
    { kind: 'array', index: ctorIndex },
    { kind: 'field', name: 'type' }
  ];
}

// ============================================================================
// Types
// ============================================================================

export interface InductiveCheckResult {
  success: boolean;
  errors: CheckError[];
}

/**
 * Polarity of an occurrence of a type variable.
 * - 'positive': Can appear here (target of arrows or direct argument)
 * - 'negative': Cannot appear here (source of arrow)
 * - 'strictly_positive': Can appear here and is not under any arrow on the left
 */
export type Polarity = 'strictly_positive' | 'positive' | 'negative';

// ============================================================================
// Main Checking Function
// ============================================================================

/**
 * Check an inductive type definition for validity.
 *
 * @param inductiveName - Name of the inductive type being defined
 * @param inductiveType - The type/kind of the inductive (e.g., Type, Type → Type)
 * @param constructors - List of constructors with their types
 * @param ctx - Typing context
 * @param indexPositions - Positions that are indices (not parameters). Universe constraints
 *                         only apply to indices. If not provided, all positions are treated as indices.
 * @returns CheckResult with all errors found
 */
export function checkInductiveValidity(
  inductiveName: string,
  inductiveType: TTKTerm,
  constructors: Array<{ name: string; type: TTKTerm }>,
  ctx: TTKContext,
  indexPositions?: number[]
): InductiveCheckResult {
  const errors: CheckError[] = [];

  // Determine the universe level of the inductive type
  const inductiveLevel = getInductiveUniverseLevel(inductiveType, ctx);

  // If indexPositions is not provided, we treat ALL positions as indices (conservative).
  // This means all type-level arguments will be checked for universe constraints.
  // When indexPositions IS provided, only those positions are indices; others are parameters.
  const hasIndexInfo = indexPositions !== undefined;
  const indexSet = new Set(indexPositions ?? []);

  for (let i = 0; i < constructors.length; i++) {
    const ctor = constructors[i];
    const ctorPath = constructorTypePath(i);

    // Check 1: Constructor return type
    const returnTypeErrors = checkConstructorReturnType(
      inductiveName,
      inductiveType,
      ctor.name,
      ctor.type,
      ctx,
      ctorPath
    );
    errors.push(...returnTypeErrors);

    // Check 2: Strict positivity
    const positivityErrors = checkStrictPositivity(
      inductiveName,
      ctor.name,
      ctor.type,
      ctx,
      ctorPath
    );
    errors.push(...positivityErrors);

    // Check 3: Universe constraints (only for indices, not parameters)
    if (inductiveLevel !== null) {
      const universeErrors = checkUniverseConstraints(
        inductiveName,
        inductiveLevel,
        ctor.name,
        ctor.type,
        ctx,
        indexSet,
        inductiveType,
        hasIndexInfo,
        ctorPath
      );
      errors.push(...universeErrors);
    }
  }

  return {
    success: errors.length === 0,
    errors
  };
}

// ============================================================================
// Check 1: Constructor Return Type
// ============================================================================

/**
 * Check that a constructor returns the inductive type being defined.
 *
 * This only checks that the HEAD of the return type is the inductive type.
 * Arity and argument type checking is done by the main type-checker in
 * tt-typecheck-decl.ts, which adds the inductive type to the context before
 * checking constructor types.
 *
 * For a constructor of `Nat`, the return type must be `Nat`.
 * For a constructor of `List`, the return type must be `List A` (head is List).
 * For a constructor of `Vec`, the return type must be `Vec A n` (head is Vec).
 */
function checkConstructorReturnType(
  inductiveName: string,
  _inductiveType: TTKTerm,
  ctorName: string,
  ctorType: TTKTerm,
  ctx: TTKContext,
  ctorPath: IndexPath
): CheckError[] {
  // Unwrap all Pi binders to get to the return type
  const { returnType } = unwrapPis(ctorType);

  // The return type should be an application of the inductive type to some arguments,
  // or just the inductive type itself if it has no arguments
  const headConst = getHeadConstant(returnType);

  if (headConst === null) {
    return [{
      message: `Constructor '${ctorName}' must return the inductive type '${inductiveName}', but returns: ${prettyPrint(returnType)}`,
      path: ctorPath,
      term: ctorType,
      context: ctx
    }];
  }

  if (headConst !== inductiveName) {
    return [{
      message: `Constructor '${ctorName}' must return type '${inductiveName}', but returns '${headConst}'`,
      path: ctorPath,
      term: ctorType,
      context: ctx
    }];
  }

  return [];
}

/**
 * Get the head constant of a type (unwrapping applications).
 * For `List A`, returns "List".
 * For `Vec A n`, returns "Vec".
 * For `Nat`, returns "Nat".
 */
function getHeadConstant(term: TTKTerm): string | null {
  switch (term.tag) {
    case 'Const':
      return term.name;
    case 'App':
      return getHeadConstant(term.fn);
    case 'Hole':
      // Holes may represent the inductive type - check if we have a name
      // This is lenient to allow forward references
      return null;
    default:
      return null;
  }
}

/**
 * Unwrap all Pi binders from a type, returning the bindings and final return type.
 */
function unwrapPis(term: TTKTerm): { bindings: Array<{ name: string; domain: TTKTerm }>; returnType: TTKTerm } {
  const bindings: Array<{ name: string; domain: TTKTerm }> = [];
  let current = term;

  while (current.tag === 'Binder' && current.binderKind.tag === 'BPi') {
    bindings.push({ name: current.name, domain: current.domain });
    current = current.body;
  }

  return { bindings, returnType: current };
}

// ============================================================================
// Check 2: Strict Positivity
// ============================================================================

/**
 * Check that the inductive type occurs only in strictly positive positions.
 *
 * A strictly positive occurrence means the inductive type does NOT appear
 * in the domain (left side) of any function arrow, except as a direct argument.
 *
 * The key insight is:
 * - For `succ : Nat -> Nat`, the `Nat` argument is strictly positive ✓
 *   (It's a direct argument, not nested under any arrows in its type)
 * - For `bad : (Nat -> X) -> Bad`, the `Nat` is NEGATIVE ✗
 *   (It's in the domain of a function type that is itself an argument)
 *
 * We check the DOMAINS of the constructor's Pi binders. Within each domain,
 * any occurrence of the inductive type is problematic because it means
 * the inductive type appears in a negative position.
 *
 * Examples:
 * - `Nat → Nat` - Nat in argument position is strictly positive ✓
 * - `(Nat → A) → Nat` - Nat inside the argument type is NEGATIVE ✗
 * - `((Nat → A) → A) → Nat` - Nat is still negative (nested) ✗
 */
function checkStrictPositivity(
  inductiveName: string,
  ctorName: string,
  ctorType: TTKTerm,
  ctx: TTKContext,
  ctorPath: IndexPath
): CheckError[] {
  const errors: CheckError[] = [];

  // Walk through the Pi binders manually to track paths
  // For each Pi, we check the domain for positivity violations
  let current = ctorType;
  let currentPath = ctorPath;

  while (current.tag === 'Binder' && current.binderKind.tag === 'BPi') {
    // Check if the domain contains the inductive type in a negative position
    // An occurrence is negative if it appears:
    // 1. Directly in the domain (e.g., Nat in "Nat -> X")
    //    - Actually, this is STRICTLY POSITIVE - it's a direct argument
    // 2. In the domain of a nested function type (e.g., Nat in "(Nat -> X) -> Y")
    //    - This is NEGATIVE
    //
    // So we need to check recursively WITHIN the domain for nested function types
    const domainPath = [...currentPath, { kind: 'field' as const, name: 'domain' }];
    checkDomainPositivity(
      inductiveName,
      ctorName,
      current.domain,
      errors,
      ctx,
      domainPath
    );

    // Move to the body
    currentPath = [...currentPath, { kind: 'field' as const, name: 'body' }];
    current = current.body;
  }

  return errors;
}

/**
 * Check a constructor argument type for positivity violations.
 *
 * A direct occurrence of the inductive type is fine (strictly positive).
 * But if the inductive type appears in the domain of a nested function type,
 * that's a positivity violation.
 *
 * @param termPath - The path to the current term being checked (for error reporting)
 */
function checkDomainPositivity(
  inductiveName: string,
  ctorName: string,
  domain: TTKTerm,
  errors: CheckError[],
  ctx: TTKContext,
  termPath: IndexPath
): void {
  switch (domain.tag) {
    case 'Const':
    case 'Var':
    case 'Sort':
    case 'Hole':
      // Direct occurrences of constants/vars are fine
      // Even if it's the inductive type, this is strictly positive
      break;

    case 'App':
      // Application - check both function and argument
      // These are still in strictly positive position
      checkDomainPositivity(inductiveName, ctorName, domain.fn, errors, ctx,
        [...termPath, { kind: 'field', name: 'fn' }]);
      checkDomainPositivity(inductiveName, ctorName, domain.arg, errors, ctx,
        [...termPath, { kind: 'field', name: 'arg' }]);
      break;

    case 'Binder':
      if (domain.binderKind.tag === 'BPi') {
        // This is a nested function type: (A -> B)
        // If the inductive type appears in A, it's NEGATIVE
        // If the inductive type appears in B, we need to check recursively
        checkNestedPiForNegativeOccurrences(
          inductiveName,
          ctorName,
          domain,
          'strictly_positive',
          errors,
          ctx,
          termPath
        );
      } else if (domain.binderKind.tag === 'BLam') {
        // Lambda in a type - check recursively
        checkDomainPositivity(inductiveName, ctorName, domain.domain, errors, ctx,
          [...termPath, { kind: 'field', name: 'domain' }]);
        checkDomainPositivity(inductiveName, ctorName, domain.body, errors, ctx,
          [...termPath, { kind: 'field', name: 'body' }]);
      } else if (domain.binderKind.tag === 'BLet') {
        // Let in a type - check all parts
        checkDomainPositivity(inductiveName, ctorName, domain.domain, errors, ctx,
          [...termPath, { kind: 'field', name: 'domain' }]);
        checkDomainPositivity(inductiveName, ctorName, domain.binderKind.defVal, errors, ctx,
          [...termPath, { kind: 'field', name: 'defVal' }]);
        checkDomainPositivity(inductiveName, ctorName, domain.body, errors, ctx,
          [...termPath, { kind: 'field', name: 'body' }]);
      }
      break;

    case 'Annot':
      checkDomainPositivity(inductiveName, ctorName, domain.term, errors, ctx,
        [...termPath, { kind: 'field', name: 'term' }]);
      checkDomainPositivity(inductiveName, ctorName, domain.type, errors, ctx,
        [...termPath, { kind: 'field', name: 'type' }]);
      break;

    case 'Match':
      checkDomainPositivity(inductiveName, ctorName, domain.scrutinee, errors, ctx,
        [...termPath, { kind: 'field', name: 'scrutinee' }]);
      for (let i = 0; i < domain.clauses.length; i++) {
        checkDomainPositivity(inductiveName, ctorName, domain.clauses[i].rhs, errors, ctx,
          [...termPath, { kind: 'field', name: 'clauses' }, { kind: 'array', index: i }, { kind: 'field', name: 'rhs' }]);
      }
      break;
  }
}

/**
 * Check a nested Pi type for negative occurrences of the inductive type.
 *
 * For a Pi type (A -> B):
 * - In the domain A, polarity is FLIPPED
 * - In the body B, polarity stays the same
 *
 * When we find the inductive type at negative polarity, it's an error.
 *
 * @param termPath - The path to the current term being checked (for error reporting)
 */
function checkNestedPiForNegativeOccurrences(
  inductiveName: string,
  ctorName: string,
  term: TTKTerm,
  polarity: Polarity,
  errors: CheckError[],
  ctx: TTKContext,
  termPath: IndexPath
): void {
  switch (term.tag) {
    case 'Const':
      // Found a constant reference
      if (term.name === inductiveName) {
        if (polarity === 'negative') {
          errors.push({
            message: `Constructor '${ctorName}' has a negative occurrence of '${inductiveName}' (appears to the left of a function arrow)`,
            path: termPath,
            term,
            context: ctx
          });
        } else if (polarity === 'positive') {
          // Positive but not strictly positive
          errors.push({
            message: `Constructor '${ctorName}' has a non-strictly-positive occurrence of '${inductiveName}' (nested under function arrows)`,
            path: termPath,
            term,
            context: ctx
          });
        }
      }
      break;

    case 'Var':
    case 'Sort':
    case 'Hole':
      // No occurrences of the inductive type
      break;

    case 'App':
      // Check function and argument with same polarity
      checkNestedPiForNegativeOccurrences(inductiveName, ctorName, term.fn, polarity, errors, ctx,
        [...termPath, { kind: 'field', name: 'fn' }]);
      checkNestedPiForNegativeOccurrences(inductiveName, ctorName, term.arg, polarity, errors, ctx,
        [...termPath, { kind: 'field', name: 'arg' }]);
      break;

    case 'Binder':
      if (term.binderKind.tag === 'BPi') {
        // Pi type: flip polarity in domain, keep in body
        const domainPolarity = flipPolarity(polarity);
        checkNestedPiForNegativeOccurrences(inductiveName, ctorName, term.domain, domainPolarity, errors, ctx,
          [...termPath, { kind: 'field', name: 'domain' }]);
        checkNestedPiForNegativeOccurrences(inductiveName, ctorName, term.body, polarity, errors, ctx,
          [...termPath, { kind: 'field', name: 'body' }]);
      } else if (term.binderKind.tag === 'BLam') {
        checkNestedPiForNegativeOccurrences(inductiveName, ctorName, term.domain, polarity, errors, ctx,
          [...termPath, { kind: 'field', name: 'domain' }]);
        checkNestedPiForNegativeOccurrences(inductiveName, ctorName, term.body, polarity, errors, ctx,
          [...termPath, { kind: 'field', name: 'body' }]);
      } else if (term.binderKind.tag === 'BLet') {
        checkNestedPiForNegativeOccurrences(inductiveName, ctorName, term.domain, polarity, errors, ctx,
          [...termPath, { kind: 'field', name: 'domain' }]);
        checkNestedPiForNegativeOccurrences(inductiveName, ctorName, term.binderKind.defVal, polarity, errors, ctx,
          [...termPath, { kind: 'field', name: 'defVal' }]);
        checkNestedPiForNegativeOccurrences(inductiveName, ctorName, term.body, polarity, errors, ctx,
          [...termPath, { kind: 'field', name: 'body' }]);
      }
      break;

    case 'Annot':
      checkNestedPiForNegativeOccurrences(inductiveName, ctorName, term.term, polarity, errors, ctx,
        [...termPath, { kind: 'field', name: 'term' }]);
      checkNestedPiForNegativeOccurrences(inductiveName, ctorName, term.type, polarity, errors, ctx,
        [...termPath, { kind: 'field', name: 'type' }]);
      break;

    case 'Match':
      checkNestedPiForNegativeOccurrences(inductiveName, ctorName, term.scrutinee, polarity, errors, ctx,
        [...termPath, { kind: 'field', name: 'scrutinee' }]);
      for (let i = 0; i < term.clauses.length; i++) {
        checkNestedPiForNegativeOccurrences(inductiveName, ctorName, term.clauses[i].rhs, polarity, errors, ctx,
          [...termPath, { kind: 'field', name: 'clauses' }, { kind: 'array', index: i }, { kind: 'field', name: 'rhs' }]);
      }
      break;
  }
}

/**
 * Flip the polarity when entering the domain of a function type.
 */
function flipPolarity(p: Polarity): Polarity {
  switch (p) {
    case 'strictly_positive':
      return 'negative';
    case 'positive':
      return 'negative';
    case 'negative':
      return 'positive';
  }
}

// ============================================================================
// Check 3: Universe Constraints
// ============================================================================

/**
 * Check that constructor argument types respect universe constraints.
 *
 * For an inductive type in Sort level `s`, constructor arguments that are
 * themselves TYPE-level (i.e., their type is a Sort) must be in universes
 * strictly less than `s`.
 *
 * IMPORTANT: This constraint only applies to INDICES, not PARAMETERS.
 * Parameters are uniform across all constructors and are conceptually
 * "outside" the inductive definition, so they don't contribute to its size.
 *
 * This ensures predicativity: a type cannot be defined in terms of
 * quantification over types at the same level or higher.
 *
 * Example:
 * - `inductive T : Type where | mk : Type → T` is INVALID
 *   because Type (Sort 1) is not < Sort 1 (Type's universe)
 * - `inductive T : Type where | mk : Nat → T` is VALID
 *   because Nat is a data type, not a type-level argument
 * - `inductive Large : Type 1 where | mk : Type → Large` is VALID
 *   because Type (Sort 1) < Sort 2 (Type 1's universe)
 * - `inductive Vec : Type -> Nat -> Type` with `VNil : (A: Type) -> Vec A Zero` is VALID
 *   because `A : Type` is a PARAMETER, not an index
 *
 * The key distinction:
 * - Arguments like `(n : Nat)` are data-level - Nat has type Type, not Type_i
 * - Arguments like `(A : Type)` are type-level - Type has type Type 1
 * - Only type-level arguments that are INDICES contribute to universe constraints
 *
 * @param indexPositions - Set of positions in the inductive type that are indices.
 *                         Constructor arguments at non-index positions are parameters
 *                         and are exempt from universe constraints.
 */
function checkUniverseConstraints(
  inductiveName: string,
  inductiveLevel: number,
  ctorName: string,
  ctorType: TTKTerm,
  ctx: TTKContext,
  indexPositions: Set<number>,
  inductiveType: TTKTerm,
  hasIndexInfo: boolean,
  ctorPath: IndexPath
): CheckError[] {
  const errors: CheckError[] = [];

  // Count the number of positions in the inductive type (for determining parameter prefix)
  const numInductivePositions = countInductivePositions(inductiveType);

  // Walk through the Pi binders and check each argument type
  let current = ctorType;
  let argIndex = 0;

  while (current.tag === 'Binder' && current.binderKind.tag === 'BPi') {
    const argType = current.domain;

    // Check if this argument corresponds to a parameter position.
    // The first N arguments of a constructor typically correspond to the N
    // positions of the inductive type. If this position is a parameter
    // (not in indexPositions), skip the universe check.
    //
    // If we don't have index info (hasIndexInfo is false), treat all positions
    // as indices (conservative - check everything).
    const isParameterPosition = hasIndexInfo &&
      argIndex < numInductivePositions &&
      !indexPositions.has(argIndex);

    if (!isParameterPosition) {
      // Check if this argument is type-level.
      // An argument is type-level if its TYPE is a Sort.
      //
      // Examples:
      // - `(A : Type)` - Type is Sort 1, so A is type-level (quantifying over types)
      // - `(n : Nat)` - Nat is a Const (not a Sort), so n is value-level (quantifying over Nats)
      //
      // Only type-level arguments (where the domain IS a Sort) contribute to universe constraints
      const normalizedDomain = whnf(argType, ctx);

      if (normalizedDomain.tag === 'Sort') {
        const argLevel = normalizedDomain.level;

        // The argument quantifies over all types in this universe.
        // This universe must be < the inductive's universe.
        if (argLevel >= inductiveLevel) {
          errors.push({
            message: `Constructor '${ctorName}' argument ${argIndex + 1} quantifies over universe ${formatUniverseLevel(argLevel)}, but '${inductiveName}' is in ${formatUniverseLevel(inductiveLevel)}. Type arguments must be in smaller universes.`,
            path: ctorPath,
            term: argType,
            context: ctx
          });
        }
      }
    }
    // If the domain is not a Sort (e.g., it's Nat, List A, etc.),
    // we're quantifying over values of that type, not over types themselves.
    // This doesn't contribute to universe constraints.

    current = current.body;
    argIndex++;
  }

  return errors;
}

/**
 * Count the number of argument positions in an inductive type.
 * For `Vec : Type -> Nat -> Type`, this returns 2.
 * For `Nat : Type`, this returns 0.
 */
function countInductivePositions(inductiveType: TTKTerm): number {
  let count = 0;
  let current = inductiveType;

  while (current.tag === 'Binder' && current.binderKind.tag === 'BPi') {
    count++;
    current = current.body;
  }

  return count;
}

/**
 * Format a universe level for error messages.
 */
function formatUniverseLevel(level: number): string {
  if (level === 0) return 'Prop';
  if (level === 1) return 'Type';
  return `Type ${level - 1}`;
}

/**
 * Get the universe level of an inductive type from its kind.
 *
 * For `Nat : Type`, this returns 1 (Sort 1 = Type).
 * For `List : Type → Type`, this returns 1.
 * For `Higher : Type 1`, this returns 2 (Sort 2 = Type 1).
 */
function getInductiveUniverseLevel(inductiveType: TTKTerm, ctx: TTKContext): number | null {
  // Unwrap any Pis to get to the final Sort
  let current = inductiveType;

  while (current.tag === 'Binder' && current.binderKind.tag === 'BPi') {
    current = current.body;
  }

  if (current.tag === 'Sort') {
    return current.level;
  }

  // Try to infer the type
  try {
    const t = whnf(inferType(inductiveType, ctx), ctx);
    if (t.tag === 'Sort') {
      return t.level;
    }
  } catch {
    // Ignore inference errors
  }

  return null;
}

// ============================================================================
// Convenience: Check if a term contains the inductive type at all
// ============================================================================

/**
 * Check if a term contains any reference to the given constant name.
 */
export function containsConstant(term: TTKTerm, name: string): boolean {
  switch (term.tag) {
    case 'Const':
      return term.name === name;
    case 'Var':
    case 'Sort':
    case 'Hole':
      return false;
    case 'App':
      return containsConstant(term.fn, name) || containsConstant(term.arg, name);
    case 'Binder':
      if (containsConstant(term.domain, name)) return true;
      if (containsConstant(term.body, name)) return true;
      if (term.binderKind.tag === 'BLet' && containsConstant(term.binderKind.defVal, name)) return true;
      return false;
    case 'Annot':
      return containsConstant(term.term, name) || containsConstant(term.type, name);
    case 'Match':
      if (containsConstant(term.scrutinee, name)) return true;
      return term.clauses.some(c => containsConstant(c.rhs, name));
  }
}
