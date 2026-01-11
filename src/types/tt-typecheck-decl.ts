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
import { inferType, checkType, TypeCheckError, DefinitionsMap } from './tt-typecheck';
import { IndexPath } from './source-position';
import { checkInductiveValidity } from './tt-inductive-check';
import { analyzeRecursionTTK, termPathToIndexPath } from './ttk-recursion-check';
import { checkFunctionTotality, formatMissingCase, SplitTree } from './ttk-totality-check';
import { checkFunctionClausesWithResult, FunctionClausesResult, ClauseCheckResult, PatternElabData } from './tt-pattern-elab';
import { buildStepperEnvironment } from './stepper-utils';

// Re-export DefinitionsMap for use by callers
export type { DefinitionsMap } from './tt-typecheck';

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
  | { success: true; value: T; splitTree?: SplitTree; clauseResults?: ClauseCheckResult[]; patternData?: PatternElabData }
  | { success: false; errors: CheckError[]; validType?: T; splitTree?: SplitTree; clauseResults?: ClauseCheckResult[]; patternData?: PatternElabData };

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
 * @param typePath - Base path for the inductive type (for error location tracking)
 * @param constructorPaths - Base paths for each constructor type (for error location tracking)
 * @returns CheckResult indicating success or all collected errors
 */
export function checkInductiveDeclaration(
  inductiveName: string,
  inductiveType: TTKTerm,
  constructors: Array<{ name: string; type: TTKTerm }>,
  ctx: TTKContext,
  indexPositions?: number[],
  typePath: IndexPath = [],
  constructorPaths: IndexPath[] = []
): CheckResult<void> {
  const errors: CheckError[] = [];

  // First, check that the inductive type itself is well-formed
  try {
    inferType(inductiveType, ctx, typePath);
  } catch (e) {
    if (e instanceof TypeCheckError) {
      errors.push({
        message: `Inductive type '${inductiveName}' is ill-formed: ${e.message}`,
        path: e.termPath || typePath,
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
    const ctorPath = constructorPaths[i] || [];
    try {
      // Type-check the constructor type in the context that includes the inductive type.
      // This naturally catches:
      // - Wrong arity (e.g., Vec A n when Vec only takes 1 arg)
      // - Wrong argument types (e.g., Type where Nat expected)
      // - References to undefined symbols
      const ctorTypeOfType = inferType(ctor.type, ctxWithInductive, ctorPath);

      // Verify the constructor type is itself a type (not a value)
      if (ctorTypeOfType.tag !== 'Sort' && ctorTypeOfType.tag !== 'Hole') {
        errors.push({
          message: `Constructor '${ctor.name}' type must be a Type or Prop, got: ${ctorTypeOfType.tag}`,
          path: ctorPath,
          term: ctor.type,
          context: ctxWithInductive
        });
      }

    } catch (e) {
      if (e instanceof TypeCheckError) {
        errors.push({
          message: `Constructor '${ctor.name}' has invalid type: ${e.message}`,
          path: e.termPath || ctorPath,
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
 * Elaborate and check a single term (CORE function - operates on AST).
 *
 * This is the core single-term elaboration function that operates on already-elaborated
 * kernel terms (TTK). It performs type checking, recursion analysis, totality checking,
 * and builds complete pattern elaboration data for the stepper.
 *
 * Handles three cases:
 * 1. Type signature only (name : type)
 * 2. Definition only (name = value)
 * 3. Both (name : type; name = value)
 *
 * For pattern matching functions, this also:
 * - Checks all clauses in parallel
 * - Analyzes structural recursion
 * - Checks exhaustiveness (totality)
 * - Builds stepper environment (EAGER - not on-demand)
 *
 * @param name - Declaration name (for error messages and recursion analysis)
 * @param declaredType - Already-elaborated type (TTK)
 * @param value - Already-elaborated value (TTK)
 * @param ctx - Type checking context
 * @param typePath - Index path to type (for error locations)
 * @param valuePath - Index path to value (for error locations)
 * @param definitions - Function definitions map (for WHNF reduction)
 * @param constructorNames - Set of constructor names (for totality checking)
 * @returns CheckResult with all elaboration data including patternData
 */
export function elaborateTT(
  name: string,
  declaredType: TTKTerm | undefined,
  value: TTKTerm | undefined,
  ctx: TTKContext,
  typePath: IndexPath = [],
  valuePath: IndexPath = [],
  definitions?: DefinitionsMap,
  constructorNames?: Set<string>
): CheckResult<TTKTerm> {
  const errors: CheckError[] = [];

  // Case 1: Type signature only
  if (declaredType && !value) {
    try {
      // Check that the type is well-formed
      inferType(declaredType, ctx, typePath);
      return { success: true, value: declaredType };
    } catch (e) {
      if (e instanceof TypeCheckError) {
        errors.push({
          message: `Type signature for '${name}' is invalid: ${e.message}`,
          path: e.termPath || typePath,
          term: e.term,
          context: e.context
        });
      } else if (e instanceof Error) {
        // Generic error (e.g., "Pattern matching not yet implemented")
        errors.push({
          message: `Type signature for '${name}' is invalid: ${e.message}`,
          path: typePath
        });
      }
      return { success: false, errors };
    }
  }

  // Case 2: Definition only (infer type from value)
  if (!declaredType && value) {
    try {
      const inferredType = inferType(value, ctx, valuePath);
      return { success: true, value: inferredType };
    } catch (e) {
      if (e instanceof TypeCheckError) {
        errors.push({
          message: `Cannot infer type for '${name}': ${e.message}`,
          path: e.termPath || valuePath,
          term: e.term,
          context: e.context
        });
      } else if (e instanceof Error) {
        // Generic error (e.g., "Pattern matching not yet implemented")
        errors.push({
          message: `Cannot infer type for '${name}': ${e.message}`,
          path: valuePath
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
      inferType(declaredType, ctx, typePath);
      typeIsValid = true;
    } catch (e) {
      if (e instanceof TypeCheckError) {
        errors.push({
          message: `Type signature for '${name}' is invalid: ${e.message}`,
          path: e.termPath || typePath,
          term: e.term,
          context: e.context
        });
      } else if (e instanceof Error) {
        errors.push({
          message: `Type signature for '${name}' is invalid: ${e.message}`,
          path: typePath
        });
      }
    }

    // PHASE 2: Check that the value has the declared type
    // Only do this if the type itself is valid
    if (typeIsValid) {
      // For recursive functions, we need the function itself in scope when checking
      // the body. This allows recursive calls like `plus a b` in `plus (Succ a) b = Succ (plus a b)`.
      const ctxWithSelf: TTKContext = [{ name, type: declaredType }, ...ctx];

      // Check if this is a function definition (Match with _scrutinee placeholder)
      // If so, use checkFunctionClausesWithResult to capture elaboration results
      let clauseResults: ClauseCheckResult[] | undefined;

      try {

        if (value.tag === 'Match' &&
            value.scrutinee.tag === 'Hole' &&
            value.scrutinee.id === '_scrutinee') {
          // Function definition - use result-returning variant to capture elaboration
          const funcResult = checkFunctionClausesWithResult(
            declaredType,
            value.clauses,
            ctxWithSelf,
            valuePath,
            definitions
          );
          clauseResults = funcResult.clauses;

          // Add any clause errors to the errors array
          for (const clauseError of funcResult.errors) {
            errors.push({
              message: `Value for '${name}' has wrong type: ${clauseError.message}`,
              path: clauseError.path,
              term: clauseError.term,
              context: clauseError.context
            });
          }

          // If there were clause errors, return early with the errors
          if (funcResult.errors.length > 0) {
            return { success: false, errors, validType: declaredType, clauseResults, patternData: undefined };
          }
        } else {
          // Regular value - use standard checkType
          // Pass the value path so errors can be traced back to source positions
          checkType(value, declaredType, ctxWithSelf, valuePath);
        }

        // PHASE 3: Check structural recursion
        // Analyze the value for safe/unsafe recursive calls
        const recursionAnalysis = analyzeRecursionTTK(name, value);
        if (recursionAnalysis.unsafeRecursion.length > 0) {
          // Report all unsafe recursion as errors
          for (const unsafe of recursionAnalysis.unsafeRecursion) {
            // Prepend valuePath since the recursion checker paths are
            // relative to the term, but the elabMap keys start with the valuePath prefix
            const fullPath: IndexPath = [
              ...valuePath,
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
          return { success: false, errors, validType: declaredType, clauseResults, patternData: undefined };
        }

        // PHASE 4: Check exhaustiveness (totality) for pattern matching
        // Only check if the value is a Match expression with clauses
        let splitTree: SplitTree | undefined;
        let patternData: PatternElabData | undefined;
        if (value.tag === 'Match' && value.clauses.length > 0) {
          const totalityAnalysis = checkFunctionTotality(name, declaredType, value.clauses, ctxWithSelf, constructorNames);
          splitTree = totalityAnalysis.splitTree;

          // PHASE 5: Build complete pattern elaboration data for stepper
          // This is done eagerly so the stepper modal can just read it
          patternData = {
            clauseResults: clauseResults || [],
            splitTree: totalityAnalysis.splitTree,
            missingCases: totalityAnalysis.missingCases,
            inaccessibleClauses: totalityAnalysis.inaccessibleClauses,
            stepperEnv: buildStepperEnvironment(ctxWithSelf)
          };

          // Check for inaccessible clauses (excess patterns that can never match)
          for (const clauseIdx of totalityAnalysis.inaccessibleClauses) {
            // Path to the inaccessible clause
            const clausePath: IndexPath = [
              ...valuePath,
              { kind: 'field', name: 'clauses' },
              { kind: 'array', index: clauseIdx }
            ];
            errors.push({
              message: `Inaccessible clause: this pattern is already covered by earlier clauses`,
              path: clausePath,
              term: value.clauses[clauseIdx].rhs,
              context: ctxWithSelf
            });
          }

          if (!totalityAnalysis.exhaustive) {
            for (const missingCase of totalityAnalysis.missingCases) {
              const formattedCase = formatMissingCase(name, missingCase);
              errors.push({
                message: `Non-exhaustive pattern match: missing case \`${formattedCase}\``,
                path: valuePath,
                term: value,
                context: ctxWithSelf
              });
            }
          }

          // Return failure if there are inaccessible clauses or missing cases
          if (totalityAnalysis.inaccessibleClauses.length > 0 || !totalityAnalysis.exhaustive) {
            return { success: false, errors, validType: declaredType, splitTree, clauseResults, patternData };
          }
        }

        // All checks passed!
        return { success: true, value: declaredType, splitTree, clauseResults, patternData };
      } catch (e) {
        if (e instanceof TypeCheckError) {
          errors.push({
            message: `Value for '${name}' has wrong type: ${e.message}`,
            path: e.termPath || valuePath,
            term: e.term,
            context: e.context
          });
        } else if (e instanceof Error) {
          // Generic error (e.g., "Pattern matching not yet implemented")
          errors.push({
            message: `Cannot check value for '${name}': ${e.message}`,
            path: valuePath
          });
        }
        // Type is valid but value failed - return validType so it can be used by later decls
        return { success: false, errors, validType: declaredType, clauseResults, patternData: undefined };
      }
    }

    // Type itself failed - no validType to provide
    return { success: false, errors, patternData: undefined };
  }

  // Case 4: Neither (shouldn't happen in well-formed input)
  errors.push({
    message: `Declaration '${name}' has neither type nor value`,
    path: []
  });
  return { success: false, errors, patternData: undefined };
}

/**
 * Check a term declaration (BACKWARDS COMPATIBILITY ALIAS).
 *
 * This is an alias for `elaborateTT` kept for backwards compatibility.
 * New code should use `elaborateTT` directly.
 *
 * @deprecated Use elaborateTT instead
 */
export function checkTermDeclaration(
  name: string,
  declaredType: TTKTerm | undefined,
  value: TTKTerm | undefined,
  ctx: TTKContext,
  typePath: IndexPath = [],
  valuePath: IndexPath = [],
  definitions?: DefinitionsMap,
  constructorNames?: Set<string>
): CheckResult<TTKTerm> {
  return elaborateTT(name, declaredType, value, ctx, typePath, valuePath, definitions, constructorNames);
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
