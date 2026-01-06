/**
 * Declaration-Level Type Checking with Parallel Error Collection
 *
 * This module provides type checking for top-level declarations with
 * comprehensive error reporting. Unlike the basic type checker which
 * throws on first error, this collects ALL errors from parallel checks.
 *
 * Key features:
 * - Check all inductive constructors in parallel
 * - Check term definitions (type-only, value-only, or both)
 * - Support forward references between declarations
 * - Return detailed error information with paths
 */

import { TTKTerm, TTKContext } from './tt-kernel';
import { inferType, checkType, TypeCheckError } from './tt-typecheck';
import { IndexPath } from './source-position';
import { checkInductiveValidity } from './tt-inductive-check';
import { analyzeRecursionTTK, termPathToIndexPath } from './ttk-recursion-check';
import { checkFunctionTotality } from './ttk-totality-check';

// ============================================================================
// Error Types
// ============================================================================

/**
 * A single type checking error with location information.
 */
export interface CheckError {
  message: string;
  path: IndexPath;  // Location in the AST where error occurred
  term?: TTKTerm;
  context?: TTKContext;
  expected?: TTKTerm;
  actual?: TTKTerm;
}

/**
 * Result of a type checking operation.
 *
 * For declarations with both type and value:
 * - success: true means both type and value checked
 * - success: false with validType means type checked but value failed
 * - success: false without validType means type itself failed
 *
 * This distinction matters because even when a value fails to type-check
 * (e.g., pattern matching not yet implemented), the TYPE signature may be
 * perfectly valid. Other declarations should be able to reference that type.
 */
export type CheckResult<T = void> =
  | { success: true; value: T }
  | { success: false; errors: CheckError[]; validType?: T };

// ============================================================================
// Inductive Type Checking
// ============================================================================

/**
 * Check an inductive type declaration with parallel constructor checking.
 *
 * This checks ALL constructors and collects ALL errors, rather than
 * failing on the first error.
 *
 * @param inductiveName - Name of the inductive type
 * @param inductiveType - Type of the inductive (usually Type or Prop)
 * @param constructors - List of constructors with their types
 * @param ctx - Typing context
 * @param indexPositions - Positions that are indices (not parameters). Universe constraints
 *                         only apply to indices. If not provided, all positions are treated as indices.
 * @returns CheckResult indicating success or all collected errors
 */
export function checkInductiveDeclaration(
  inductiveName: string,
  inductiveType: TTKTerm,
  constructors: Array<{ name: string; type: TTKTerm }>,
  ctx: TTKContext,
  indexPositions?: number[]
): CheckResult<void> {
  const errors: CheckError[] = [];

  // First, check that the inductive type itself is well-formed
  try {
    inferType(inductiveType, ctx);
  } catch (e) {
    if (e instanceof TypeCheckError) {
      errors.push({
        message: `Inductive type '${inductiveName}' is ill-formed: ${e.message}`,
        path: e.termPath || [],
        term: e.term,
        context: e.context
      });
    }
  }

  // Build a context that includes the inductive type being defined.
  // This allows constructor types like "Nat -> Nat" to reference Nat.
  const ctxWithInductive: TTKContext = [{ name: inductiveName, type: inductiveType }, ...ctx];

  // Check each constructor (collect all errors)
  for (let i = 0; i < constructors.length; i++) {
    const ctor = constructors[i];
    try {
      // Type-check the constructor type in the context that includes the inductive type.
      // This naturally catches:
      // - Wrong arity (e.g., Vec A n when Vec only takes 1 arg)
      // - Wrong argument types (e.g., Type where Nat expected)
      // - References to undefined symbols
      const ctorTypeOfType = inferType(ctor.type, ctxWithInductive);

      // Verify the constructor type is itself a type (not a value)
      if (ctorTypeOfType.tag !== 'Sort' && ctorTypeOfType.tag !== 'Hole') {
        errors.push({
          message: `Constructor '${ctor.name}' type must be a Type or Prop, got: ${ctorTypeOfType.tag}`,
          path: [],
          term: ctor.type,
          context: ctxWithInductive
        });
      }

    } catch (e) {
      if (e instanceof TypeCheckError) {
        errors.push({
          message: `Constructor '${ctor.name}' has invalid type: ${e.message}`,
          path: e.termPath || [],
          term: e.term,
          context: e.context
        });
      }
    }
  }

  // After basic type checking, run validity checks:
  // - Constructor return type must be the inductive type
  // - Strict positivity (no negative occurrences)
  // - Universe constraints (only for indices, not parameters)
  const validityResult = checkInductiveValidity(
    inductiveName,
    inductiveType,
    constructors,
    ctx,
    indexPositions
  );
  errors.push(...validityResult.errors);

  if (errors.length > 0) {
    return { success: false, errors };
  }

  return { success: true, value: undefined };
}

// ============================================================================
// Term Declaration Checking
// ============================================================================

/**
 * Check a term declaration.
 *
 * Handles three cases:
 * 1. Type signature only (name : type)
 * 2. Definition only (name = value)
 * 3. Both (name : type; name = value)
 *
 * @param name - Name of the declaration
 * @param declaredType - Declared type (if any)
 * @param value - Definition value (if any)
 * @param ctx - Typing context
 * @returns CheckResult with inferred type or errors
 */
export function checkTermDeclaration(
  name: string,
  declaredType: TTKTerm | undefined,
  value: TTKTerm | undefined,
  ctx: TTKContext
): CheckResult<TTKTerm> {
  const errors: CheckError[] = [];

  // Case 1: Type signature only
  if (declaredType && !value) {
    try {
      // Check that the type is well-formed
      inferType(declaredType, ctx);
      return { success: true, value: declaredType };
    } catch (e) {
      if (e instanceof TypeCheckError) {
        errors.push({
          message: `Type signature for '${name}' is invalid: ${e.message}`,
          path: e.termPath || [],
          term: e.term,
          context: e.context
        });
      } else if (e instanceof Error) {
        // Generic error (e.g., "Pattern matching not yet implemented")
        errors.push({
          message: `Type signature for '${name}' is invalid: ${e.message}`,
          path: []
        });
      }
      return { success: false, errors };
    }
  }

  // Case 2: Definition only (infer type from value)
  if (!declaredType && value) {
    try {
      const inferredType = inferType(value, ctx);
      return { success: true, value: inferredType };
    } catch (e) {
      if (e instanceof TypeCheckError) {
        errors.push({
          message: `Cannot infer type for '${name}': ${e.message}`,
          path: e.termPath || [],
          term: e.term,
          context: e.context
        });
      } else if (e instanceof Error) {
        // Generic error (e.g., "Pattern matching not yet implemented")
        errors.push({
          message: `Cannot infer type for '${name}': ${e.message}`,
          path: []
        });
      }
      return { success: false, errors };
    }
  }

  // Case 3: Both type and value
  if (declaredType && value) {
    // PHASE 1: Check that the declared type is well-formed
    let typeIsValid = false;
    try {
      inferType(declaredType, ctx);
      typeIsValid = true;
    } catch (e) {
      if (e instanceof TypeCheckError) {
        errors.push({
          message: `Type signature for '${name}' is invalid: ${e.message}`,
          path: e.termPath || [],
          term: e.term,
          context: e.context
        });
      } else if (e instanceof Error) {
        errors.push({
          message: `Type signature for '${name}' is invalid: ${e.message}`,
          path: []
        });
      }
    }

    // PHASE 2: Check that the value has the declared type
    // Only do this if the type itself is valid
    if (typeIsValid) {
      try {
        // For recursive functions, we need the function itself in scope when checking
        // the body. This allows recursive calls like `plus a b` in `plus (Succ a) b = Succ (plus a b)`.
        const ctxWithSelf: TTKContext = [{ name, type: declaredType }, ...ctx];
        // Pass the 'value' path so errors can be traced back to source positions
        const valuePath: IndexPath = [{ kind: 'field', name: 'value' }];
        checkType(value, declaredType, ctxWithSelf, valuePath);

        // PHASE 3: Check structural recursion
        // Analyze the value for safe/unsafe recursive calls
        const recursionAnalysis = analyzeRecursionTTK(name, value);
        if (recursionAnalysis.unsafeRecursion.length > 0) {
          // Report all unsafe recursion as errors
          for (const unsafe of recursionAnalysis.unsafeRecursion) {
            // Prepend 'value' to the path since the recursion checker paths are
            // relative to the term, but the elabMap keys start with 'value.'
            const fullPath: IndexPath = [
              { kind: 'field', name: 'value' },
              ...termPathToIndexPath(unsafe.termPath)
            ];
            errors.push({
              message: `${unsafe.error}`,
              path: fullPath,
              term: value,
              context: ctxWithSelf
            });
          }
          // Type is valid but recursion is unsafe
          return { success: false, errors, validType: declaredType };
        }

        // PHASE 4: Check exhaustiveness (totality) for pattern matching
        // Only check if the value is a Match expression with clauses
        if (value.tag === 'Match' && value.clauses.length > 0) {
          const totalityAnalysis = checkFunctionTotality(name, declaredType, value.clauses, ctxWithSelf);
          if (!totalityAnalysis.exhaustive) {
            for (const missingCase of totalityAnalysis.missingCases) {
              errors.push({
                message: `Non-exhaustive pattern match: missing case for ${missingCase.join(' ')}`,
                path: [{ kind: 'field', name: 'value' }],
                term: value,
                context: ctxWithSelf
              });
            }
            // Type is valid but pattern matching is non-exhaustive
            return { success: false, errors, validType: declaredType };
          }
        }

        // All checks passed!
        return { success: true, value: declaredType };
      } catch (e) {
        if (e instanceof TypeCheckError) {
          errors.push({
            message: `Value for '${name}' has wrong type: ${e.message}`,
            path: e.termPath || [{ kind: 'field', name: 'value' }],
            term: e.term,
            context: e.context
          });
        } else if (e instanceof Error) {
          // Generic error (e.g., "Pattern matching not yet implemented")
          errors.push({
            message: `Cannot check value for '${name}': ${e.message}`,
            path: []
          });
        }
        // Type is valid but value failed - return validType so it can be used by later decls
        return { success: false, errors, validType: declaredType };
      }
    }

    // Type itself failed - no validType to provide
    return { success: false, errors };
  }

  // Case 4: Neither (shouldn't happen in well-formed input)
  errors.push({
    message: `Declaration '${name}' has neither type nor value`,
    path: []
  });
  return { success: false, errors };
}

// ============================================================================
// Multi-Declaration Checking (Future: Forward References)
// ============================================================================

/**
 * Check multiple declarations together.
 *
 * This enables forward references: later declarations can reference
 * earlier ones in the same block.
 *
 * For now, this is a simple wrapper that checks each declaration
 * independently. In the future, we'll build a global environment
 * as we go to support mutual recursion.
 *
 * @param declarations - Array of {name, type, value} declarations
 * @returns Array of check results, one per declaration
 */
export function checkDeclarations(
  declarations: Array<{
    name?: string;
    type?: TTKTerm;
    value?: TTKTerm;
    kind: string;
  }>
): Array<{ declIndex: number; result: CheckResult<TTKTerm> }> {
  const results: Array<{ declIndex: number; result: CheckResult<TTKTerm> }> = [];
  const ctx: TTKContext = [];  // Global context for forward references

  for (let i = 0; i < declarations.length; i++) {
    const decl = declarations[i];

    // Skip non-term declarations for now
    if (decl.kind === 'inductive') {
      // TODO: Handle inductive declarations
      results.push({
        declIndex: i,
        result: { success: true, value: { tag: 'Sort', level: 0 } }
      });
      continue;
    }

    const result = checkTermDeclaration(
      decl.name || `decl_${i}`,
      decl.type,
      decl.value,
      ctx
    );

    results.push({ declIndex: i, result });

    // TODO: Add successfully checked declarations to ctx for forward references
  }

  return results;
}
