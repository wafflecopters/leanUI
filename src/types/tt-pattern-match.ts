/**
 * Pattern Matching Type-Checking
 *
 * This module implements type-checking for dependent pattern matching.
 * The algorithm is based on:
 *
 * - "Pattern Matching Without K" by Cockx, Devriese & Piessens (ICFP 2014)
 * - "Elaborating Dependent (Co)pattern Matching" by Cockx & Abel (ICFP 2018)
 *
 * Key concepts:
 *
 * 1. **Pattern Variable Binding**: Patterns bind variables that are in scope
 *    for the right-hand side. Variables are bound left-to-right, depth-first.
 *
 * 2. **Unification**: When matching against indexed types (like Vec A n),
 *    pattern matching unifies the indices with constructor patterns.
 *
 * 3. **Forced Patterns**: For types like Equal A x y, matching on Refl
 *    *forces* y to equal x. These "inaccessible" patterns don't bind new
 *    variables but constrain the types.
 *
 * 4. **Context Extension**: Each pattern extends the typing context with
 *    the variables it binds. The RHS is type-checked in this extended context.
 *
 * ## Algorithm Overview
 *
 * To type-check `match scrutinee { p1 => e1 | p2 => e2 | ... }`:
 *
 * 1. Infer the type of the scrutinee
 * 2. For each clause (pi => ei):
 *    a. Check that pi is a valid pattern for the scrutinee's type
 *    b. Compute the bindings and refined context from pi
 *    c. Type-check ei in the refined context
 *    d. Verify ei's type is compatible with the overall return type
 * 3. Unify all clause return types to get the match's type
 */

import { TPattern } from './tt-core';
import {
  TTKTerm,
  TTKContext,
  TTKClause,
  mkVar,
  mkConst,
  mkApp,
  mkType,
  prettyPrint,
} from './tt-kernel';
import {
  TypeCheckError,
  inferType,
  checkType,
  extendContext,
  whnf,
  convertible,
  lookupConstByName,
  DefinitionsMap,
} from './tt-typecheck';
import {
  unifyTerms,
  applySubstitution,
  Substitution,
  emptySubstitution,
  composeSubstitutions,
} from './tt-unify';
import {
  IndexPath,
  appendPath,
  fieldSeg,
  arraySeg,
} from './source-position';

// ============================================================================
// Pattern Variable Counting
// ============================================================================

/**
 * Count the number of variables bound by a pattern.
 * Variables are bound by PVar nodes (but not PWild).
 */
export function countPatternVars(pattern: TPattern): number {
  switch (pattern.tag) {
    case 'PVar':
      return 1;
    case 'PWild':
      return 0;
    case 'PCtor':
      return pattern.args.reduce((sum, arg) => sum + countPatternVars(arg), 0);
  }
}

/**
 * Count total variables bound by a list of patterns.
 */
export function countPatternsVars(patterns: TPattern[]): number {
  return patterns.reduce((sum, p) => sum + countPatternVars(p), 0);
}

/**
 * Extract variable names from a pattern in binding order (left-to-right, depth-first).
 */
export function extractPatternVarNames(pattern: TPattern): string[] {
  switch (pattern.tag) {
    case 'PVar':
      return [pattern.name];
    case 'PWild':
      return [];
    case 'PCtor':
      return pattern.args.flatMap(extractPatternVarNames);
  }
}

/**
 * Extract variable names from patterns in binding order.
 */
export function extractPatternsVarNames(patterns: TPattern[]): string[] {
  return patterns.flatMap(extractPatternVarNames);
}

// ============================================================================
// Constructor Information
// ============================================================================

/**
 * Information about a constructor needed for pattern matching.
 */
export interface ConstructorInfo {
  name: string;
  /** The full type of the constructor, e.g., (A : Type) -> A -> List A -> List A */
  fullType: TTKTerm;
  /** The inductive type this constructor belongs to */
  inductiveTypeName: string;
  /** Number of parameters in the inductive type */
  numParams: number;
}

/**
 * Look up constructor information from the context.
 * Returns null if the constructor is not found.
 */
export function lookupConstructor(
  ctorName: string,
  ctx: TTKContext
): ConstructorInfo | null {
  // Look up the constructor in the context
  const ctorType = lookupConstByName(ctx, ctorName);
  if (!ctorType) {
    return null;
  }

  // Find the inductive type by looking at the return type of the constructor
  const returnType = getReturnType(ctorType);
  const inductiveName = getHeadConstName(returnType);
  if (!inductiveName) {
    return null;
  }

  // Count parameters by examining the constructor's return type
  const numParams = countInductiveParams(ctorType);

  return {
    name: ctorName,
    fullType: ctorType,
    inductiveTypeName: inductiveName,
    numParams,
  };
}

/**
 * Get the return type of a function type (unwrapping all Pi binders).
 */
function getReturnType(type: TTKTerm): TTKTerm {
  let current = type;
  while (current.tag === 'Binder' && current.binderKind.tag === 'BPi') {
    current = current.body;
  }
  return current;
}

/**
 * Get the head constant name from a type (unwrapping applications).
 */
function getHeadConstName(type: TTKTerm): string | null {
  let current = type;
  while (current.tag === 'App') {
    current = current.fn;
  }
  if (current.tag === 'Const') {
    return current.name;
  }
  return null;
}

/**
 * Count the number of Pi parameters in a type (the arity).
 */
function countPiParams(type: TTKTerm): number {
  let count = 0;
  let current = type;
  while (current.tag === 'Binder' && current.binderKind.tag === 'BPi') {
    count++;
    current = current.body;
  }
  return count;
}

/**
 * Count the number of parameters for an inductive type by examining
 * its constructor's return type.
 *
 * Parameters are indices that appear exactly once in the constructor's
 * return type at their corresponding telescope position. Indices are
 * positions that appear multiple times or are computed values.
 *
 * For example, for `Refl : (A : Type) -> (x : A) -> Equal A x x`:
 * - A appears once at position 0 in `Equal A x x` → parameter
 * - x appears twice at positions 1 and 2 → index
 * So numParams = 1.
 */
function countInductiveParams(ctorType: TTKTerm): number {
  const telescope = extractTelescope(ctorType);
  const returnType = getReturnType(ctorType);
  const indices = extractTypeIndices(returnType);

  let numParams = 0;
  for (let i = 0; i < telescope.length && i < indices.length; i++) {
    const idx = indices[i];
    // Check if this index is exactly Var(telescope.length - 1 - i)
    // which means it's the corresponding telescope variable passed through
    const expectedVarIndex = telescope.length - 1 - i;
    if (idx.tag === 'Var' && idx.index === expectedVarIndex) {
      // Check if this variable appears only once in the indices
      let count = 0;
      for (const otherIdx of indices) {
        if (otherIdx.tag === 'Var' && otherIdx.index === expectedVarIndex) {
          count++;
        }
      }
      if (count === 1) {
        numParams++;
      } else {
        // Once we hit a non-parameter, all subsequent are indices
        break;
      }
    } else {
      break;
    }
  }
  return numParams;
}

// ============================================================================
// Pattern Binding Computation
// ============================================================================

/**
 * Result of checking a pattern against a type.
 */
export interface PatternCheckResult {
  /** Bindings introduced by this pattern (name -> type) */
  bindings: Array<{ name: string; type: TTKTerm }>;
  /** Substitution from unification (for indexed types) */
  substitution: Substitution;
  /** The refined type after pattern matching (with indices substituted) */
  refinedType: TTKTerm;
}

/**
 * Result of checking a clause, including solved/elaborated information.
 * This is used to propagate unification results up for UI display.
 */
export interface ClauseCheckResult {
  /** The return type of the RHS (with substitutions applied) */
  returnType: TTKTerm;
  /** Bindings introduced by patterns, with SOLVED types (substitutions applied) */
  solvedBindings: Array<{ name: string; type: TTKTerm }>;
  /** The full substitution accumulated from pattern matching */
  substitution: Substitution;
}

/**
 * Result of checking all function clauses.
 */
export interface FunctionClausesResult {
  /** Per-clause elaboration results */
  clauses: ClauseCheckResult[];
  /** Combined substitution from all clauses */
  substitution: Substitution;
}

/**
 * Check a pattern against an expected type and compute the bindings.
 *
 * This is the core of pattern matching type-checking.
 *
 * @param pattern - The pattern to check
 * @param expectedType - The type the pattern should match
 * @param ctx - The typing context
 * @param patternPath - Path to this pattern in the source (for error reporting)
 * @returns The bindings introduced and any unification substitution
 */
export function checkPattern(
  pattern: TPattern,
  expectedType: TTKTerm,
  ctx: TTKContext,
  patternPath: IndexPath = []
): PatternCheckResult {
  // Normalize the expected type
  const normType = whnf(expectedType, ctx);

  switch (pattern.tag) {
    case 'PVar': {
      // Variable pattern: binds a variable of the expected type
      return {
        bindings: [{ name: pattern.name, type: expectedType }],
        substitution: new Map(),
        refinedType: expectedType,
      };
    }

    case 'PWild': {
      // Wildcard: matches anything, binds a fresh variable for dependent type purposes
      // Even though the variable can't be used in the RHS, its type is needed for
      // subsequent patterns and the return type in dependent function types.
      // For example, in `head : (A : Type) -> A -> List A -> A`, matching
      // `head _ default (Nil _) = default` needs the first wildcard to bind A
      // so that later types can reference it.
      return {
        bindings: [{ name: '_', type: expectedType }],
        substitution: new Map(),
        refinedType: expectedType,
      };
    }

    case 'PCtor': {
      // Constructor pattern: look up constructor and check arguments
      const ctorInfo = lookupConstructor(pattern.name, ctx);
      if (!ctorInfo) {
        // If it looks like a constructor but isn't known, and has no args,
        // treat it as a variable pattern. This handles cases like:
        //   map A B f (Nil _) = ...
        // where A and B are parsed as PCtor (uppercase) but are really type variables.
        if (pattern.args.length === 0) {
          return {
            bindings: [{ name: pattern.name, type: expectedType }],
            substitution: new Map(),
            refinedType: expectedType,
          };
        }
        throw new TypeCheckError(
          `Unknown constructor '${pattern.name}' in pattern`,
          undefined,
          ctx,
          patternPath
        );
      }

      // Check that the constructor belongs to the expected type
      const expectedHead = getHeadConstName(normType);
      if (expectedHead !== ctorInfo.inductiveTypeName) {
        throw new TypeCheckError(
          `Constructor '${pattern.name}' belongs to '${ctorInfo.inductiveTypeName}' ` +
          `but expected type is '${expectedHead || prettyPrint(normType)}'`,
          undefined,
          ctx,
          patternPath
        );
      }

      // Extract the indices from the expected type (e.g., for Vec A n, extract A and n)
      const expectedIndices = extractTypeIndices(normType);

      // Check constructor arguments against the constructor's parameter types
      return checkConstructorPattern(
        pattern,
        ctorInfo,
        expectedIndices,
        ctx,
        patternPath
      );
    }
  }
}

/**
 * Extract indices from an applied type.
 * For `Vec A n`, returns [A, n].
 * For `Nat`, returns [].
 */
function extractTypeIndices(type: TTKTerm): TTKTerm[] {
  const indices: TTKTerm[] = [];
  let current = type;
  while (current.tag === 'App') {
    indices.unshift(current.arg);
    current = current.fn;
  }
  return indices;
}

/**
 * Check a constructor pattern and compute bindings.
 *
 * This handles:
 * 1. Matching constructor arguments against the constructor's type telescope
 * 2. Unifying indices from the expected type with constructor's return type indices
 * 3. Computing forced patterns (inaccessible patterns)
 *
 * Note: Patterns include ALL constructor arguments (parameters AND non-parameters).
 * For example, for `Nil : (A : Type) -> List A`, the pattern is `(Nil _)` where
 * the `_` matches the type parameter `A`.
 */
function checkConstructorPattern(
  pattern: { tag: 'PCtor'; name: string; args: TPattern[] },
  ctorInfo: ConstructorInfo,
  expectedIndices: TTKTerm[],
  ctx: TTKContext,
  patternPath: IndexPath = []
): PatternCheckResult {
  const allBindings: Array<{ name: string; type: TTKTerm }> = [];
  let substitution: Substitution = new Map();

  // Get the constructor's argument types (the telescope)
  // This includes ALL arguments: parameters, indices, and data fields
  const telescope = extractTelescope(ctorInfo.fullType);

  // Check that we have the right number of pattern arguments
  // Patterns must match ALL constructor arguments (including parameters)
  if (pattern.args.length !== telescope.length) {
    throw new TypeCheckError(
      `Constructor '${pattern.name}' expects ${telescope.length} arguments, ` +
      `but pattern has ${pattern.args.length}`,
      undefined,
      ctx,
      patternPath
    );
  }

  // Build context with parameter substitutions from expected indices
  let currentCtx = ctx;
  let currentSubst = substitution;
  const numParams = ctorInfo.numParams;

  // Track bindings added so far to shift expectedIndices appropriately
  let bindingsAdded = 0;

  // Check each argument pattern against its expected type
  for (let i = 0; i < pattern.args.length; i++) {
    const argPattern = pattern.args[i];
    // Get the type for this argument position from the constructor's telescope
    let argType = telescope[i].type;

    // Apply current substitution to the argument type
    argType = applySubstitution(currentSubst, argType);

    // For non-parameter positions, substitute the expected indices into the type
    // to get the concrete type.
    // Note: Parameter positions keep their telescope type (e.g., Type for type params).
    // The expected indices tell us what VALUES are at those parameter positions,
    // but the type of those patterns is still the domain type from the telescope.
    if (i >= numParams) {
      // Substitute parameters into this type
      // telescope[i].type may reference Var(k) where k < i refers to earlier
      // telescope entries. For k < numParams, substitute expectedIndices[k].
      for (let j = 0; j < numParams && j < expectedIndices.length; j++) {
        // In telescope position i, Var(i-1-j) references telescope position j
        const varIndex = i - 1 - j;
        if (varIndex >= 0) {
          // Shift the expected index by the number of bindings we've added
          // since entering this constructor pattern. This accounts for the
          // fact that expectedIndices were valid at ctx, but we've extended
          // the context with constructor pattern bindings.
          const shiftedIndex = shiftTermBy(expectedIndices[j], bindingsAdded, 0);
          argType = substituteAt(argType, varIndex, shiftedIndex);
        }
      }
    }

    // Check the sub-pattern - path descends into args[i]
    const argPatternPath = appendPath(patternPath, fieldSeg('args'), arraySeg(i));
    const result = checkPattern(argPattern, argType, currentCtx, argPatternPath);

    // Extend context with new bindings
    for (const binding of result.bindings) {
      currentCtx = extendContext(currentCtx, binding.name, binding.type);
      allBindings.push(binding);
      bindingsAdded++;
    }

    // Compose substitutions
    for (const [key, value] of result.substitution) {
      currentSubst.set(key, value);
    }
  }

  // Now unify the constructor's return type indices with the expected indices
  // This handles dependent pattern matching where indices are refined
  const ctorReturnType = getReturnType(ctorInfo.fullType);
  const ctorIndices = extractTypeIndices(ctorReturnType);

  // Skip parameters in constructor indices - only unify the actual indices.
  // Parameters are type arguments that are passed through unchanged (like A in List A).
  // Indices are type arguments that can vary between constructors (like n in Vec A n).
  // We only need to unify indices since parameters are handled by the type system.
  const ctorNonParamIndices = ctorIndices.slice(numParams);
  const expectedNonParamIndices = expectedIndices.slice(numParams);

  // Record parameter bindings for display purposes (without running unification)
  // Parameter position i in the constructor corresponds to expectedIndices[i]
  // The pattern binding for that parameter is at De Bruijn index (telescopeLen - 1 - i)
  for (let i = 0; i < numParams && i < expectedIndices.length; i++) {
    const ctorIdx = ctorIndices[i];
    // Only record if the constructor index is a variable (pattern binding)
    if (ctorIdx.tag === 'Var' && ctorIdx.index < telescope.length) {
      // Shift expected value by bindings added
      const shiftedExpected = shiftTermBy(expectedIndices[i], bindingsAdded, 0);
      // Record this binding: the pattern variable at ctorIdx.index equals shiftedExpected
      currentSubst.set(`var:${ctorIdx.index}`, shiftedExpected);
    }
  }

  // Map constructor telescope indices to pattern bindings.
  // The constructor's return type uses De Bruijn indices relative to its telescope:
  // - Var(0) refers to the last telescope entry (most recently bound)
  // - Var(n-1) refers to the first telescope entry
  // We've added pattern bindings in the same order as the telescope, so:
  // - Pattern binding 0 (first added) corresponds to telescope entry 0 (first in telescope)
  // - Pattern binding n-1 (last added) corresponds to telescope entry n-1 (last in telescope)
  //
  // In De Bruijn notation after adding bindings:
  // - The last pattern binding (telescope entry n-1) is at Var(0)
  // - The first pattern binding (telescope entry 0) is at Var(n-1)
  //
  // So Var(k) in constructor return type (which refers to telescope entry (n-1-k))
  // should map to Var(k) in current context (which refers to pattern binding (n-1-k)).
  // The indices are the same! We just need to ensure they're within the telescope.
  const telescopeLen = telescope.length;
  function mapCtorIndex(term: TTKTerm): TTKTerm {
    switch (term.tag) {
      case 'Var':
        // Only map indices that refer to the constructor's telescope
        // Indices >= telescopeLen refer to bindings outside the constructor pattern
        // and should be shifted to account for the new bindings
        if (term.index < telescopeLen) {
          // Indices within telescope stay the same - they now refer to pattern bindings
          return term;
        }
        // Indices outside telescope need to be shifted by bindingsAdded
        // Actually, these shouldn't occur in constructor return type indices
        return term;
      case 'App':
        return { tag: 'App', fn: mapCtorIndex(term.fn), arg: mapCtorIndex(term.arg) };
      case 'Binder':
        // Note: We don't expect binders in type indices, but handle for completeness
        return {
          ...term,
          domain: mapCtorIndex(term.domain),
          body: mapCtorIndex(term.body),
        };
      default:
        return term;
    }
  }

  // Unify each non-parameter index
  for (let i = 0; i < Math.min(ctorNonParamIndices.length, expectedNonParamIndices.length); i++) {
    let ctorIdx = ctorNonParamIndices[i];
    let expIdx = expectedNonParamIndices[i];

    // Map constructor indices to pattern context
    ctorIdx = mapCtorIndex(ctorIdx);

    // Shift expected indices by the number of bindings added by this constructor pattern
    // Expected indices were valid at the original ctx, but we've extended with bindings
    expIdx = shiftTermBy(expIdx, bindingsAdded, 0);

    // Apply current substitution
    ctorIdx = applySubstitution(currentSubst, ctorIdx);
    expIdx = applySubstitution(currentSubst, expIdx);

    // Try to unify
    const unifyResult = unifyTerms(ctorIdx, expIdx, mkType(0), currentCtx);
    if (unifyResult.tag === 'success') {
      for (const [key, value] of unifyResult.substitution) {
        currentSubst.set(key, value);
      }
    } else if (unifyResult.tag === 'failure') {
      throw new TypeCheckError(
        `Index mismatch in pattern: cannot unify ${prettyPrint(ctorIdx)} with ${prettyPrint(expIdx)}`,
        undefined,
        ctx,
        patternPath
      );
    }
    // If stuck, we continue (the constraint may be resolved later)
  }

  // Apply final substitution to the expected type
  const refinedType = applySubstitution(currentSubst, whnf(buildAppliedType(ctorInfo.inductiveTypeName, expectedIndices, ctx), ctx));

  return {
    bindings: allBindings,
    substitution: currentSubst,
    refinedType,
  };
}

/**
 * Extract the telescope (argument types) from a function type.
 */
function extractTelescope(type: TTKTerm): Array<{ name: string; type: TTKTerm }> {
  const telescope: Array<{ name: string; type: TTKTerm }> = [];
  let current = type;
  while (current.tag === 'Binder' && current.binderKind.tag === 'BPi') {
    telescope.push({ name: current.name, type: current.domain });
    current = current.body;
  }
  return telescope;
}

/**
 * Substitute a term at a specific De Bruijn index.
 */
function substituteAt(term: TTKTerm, index: number, replacement: TTKTerm): TTKTerm {
  return substituteAtHelper(term, index, replacement, 0);
}

function substituteAtHelper(
  term: TTKTerm,
  targetIndex: number,
  replacement: TTKTerm,
  depth: number
): TTKTerm {
  switch (term.tag) {
    case 'Var':
      if (term.index === targetIndex + depth) {
        return shiftTermBy(replacement, depth, 0);
      }
      return term;

    case 'Sort':
    case 'Const':
      return term;

    case 'Hole':
      return {
        ...term,
        type: substituteAtHelper(term.type, targetIndex, replacement, depth),
      };

    case 'Binder': {
      const newDomain = substituteAtHelper(term.domain, targetIndex, replacement, depth);
      const newBody = substituteAtHelper(term.body, targetIndex, replacement, depth + 1);
      let newBinderKind = term.binderKind;
      if (term.binderKind.tag === 'BLet') {
        newBinderKind = {
          tag: 'BLet',
          defVal: substituteAtHelper(term.binderKind.defVal, targetIndex, replacement, depth),
        };
      }
      return { ...term, domain: newDomain, body: newBody, binderKind: newBinderKind };
    }

    case 'App':
      return {
        tag: 'App',
        fn: substituteAtHelper(term.fn, targetIndex, replacement, depth),
        arg: substituteAtHelper(term.arg, targetIndex, replacement, depth),
      };

    case 'Annot':
      return {
        tag: 'Annot',
        term: substituteAtHelper(term.term, targetIndex, replacement, depth),
        type: substituteAtHelper(term.type, targetIndex, replacement, depth),
      };

    case 'Match':
      return {
        tag: 'Match',
        scrutinee: substituteAtHelper(term.scrutinee, targetIndex, replacement, depth),
        clauses: term.clauses.map(c => ({
          patterns: c.patterns,
          rhs: substituteAtHelper(c.rhs, targetIndex, replacement, depth),
        })),
      };
  }
}

/**
 * Shift De Bruijn indices in a term.
 */
function shiftTermBy(term: TTKTerm, amount: number, cutoff: number): TTKTerm {
  if (amount === 0) return term;

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

    case 'Binder': {
      const newDomain = shiftTermBy(term.domain, amount, cutoff);
      const newBody = shiftTermBy(term.body, amount, cutoff + 1);
      let newBinderKind = term.binderKind;
      if (term.binderKind.tag === 'BLet') {
        newBinderKind = {
          tag: 'BLet',
          defVal: shiftTermBy(term.binderKind.defVal, amount, cutoff),
        };
      }
      return { ...term, domain: newDomain, body: newBody, binderKind: newBinderKind };
    }

    case 'App':
      return {
        tag: 'App',
        fn: shiftTermBy(term.fn, amount, cutoff),
        arg: shiftTermBy(term.arg, amount, cutoff),
      };

    case 'Annot':
      return {
        tag: 'Annot',
        term: shiftTermBy(term.term, amount, cutoff),
        type: shiftTermBy(term.type, amount, cutoff),
      };

    case 'Match':
      return {
        tag: 'Match',
        scrutinee: shiftTermBy(term.scrutinee, amount, cutoff),
        clauses: term.clauses.map(c => ({
          patterns: c.patterns,
          rhs: shiftTermBy(c.rhs, amount, cutoff),
        })),
      };
  }
}

/**
 * Build an applied type from a type name and indices.
 */
function buildAppliedType(
  typeName: string,
  indices: TTKTerm[],
  ctx: TTKContext
): TTKTerm {
  const typeConst = lookupConstByName(ctx, typeName);
  let result: TTKTerm = mkConst(typeName, typeConst || mkType(0));
  for (const idx of indices) {
    result = mkApp(result, idx);
  }
  return result;
}

// ============================================================================
// Clause Type-Checking
// ============================================================================

/**
 * Check a single pattern matching clause.
 *
 * This is more complex than simple pattern matching because of dependent types:
 * when we have `f : (A : Type) -> A -> List A -> A`, the type of the second
 * argument depends on the first argument. When pattern matching, we need to
 * substitute the matched value into subsequent types.
 *
 * @param clause - The clause to check
 * @param scrutineeTypes - Types of the scrutinees (one per pattern), as a telescope
 *                         where type[i] may reference Var(j) for j < i
 * @param expectedReturnType - Expected return type (may reference pattern positions)
 * @param ctx - The typing context
 * @param clausePath - Path to this clause in the source (for error reporting)
 * @param definitions - Map of function definitions for WHNF reduction
 * @returns The inferred return type of the RHS
 */
export function checkClause(
  clause: TTKClause,
  scrutineeTypes: TTKTerm[],
  expectedReturnType: TTKTerm | null,
  ctx: TTKContext,
  clausePath: IndexPath = [],
  definitions?: DefinitionsMap
): TTKTerm {
  const result = checkClauseWithResult(clause, scrutineeTypes, expectedReturnType, ctx, clausePath, definitions);
  return result.returnType;
}

/**
 * Check a single pattern matching clause, returning full elaboration result.
 *
 * This version returns the solved bindings and substitution in addition to the
 * return type. Use this when you need access to the elaborated context (e.g.,
 * for type queries that should show solved types).
 *
 * @param clause - The clause to check
 * @param scrutineeTypes - Types of the scrutinees (one per pattern), as a telescope
 *                         where type[i] may reference Var(j) for j < i
 * @param expectedReturnType - Expected return type (may reference pattern positions)
 * @param ctx - The typing context
 * @param clausePath - Path to this clause in the source (for error reporting)
 * @param definitions - Map of function definitions for WHNF reduction
 * @returns ClauseCheckResult with return type, solved bindings, and substitution
 */
export function checkClauseWithResult(
  clause: TTKClause,
  scrutineeTypes: TTKTerm[],
  expectedReturnType: TTKTerm | null,
  ctx: TTKContext,
  clausePath: IndexPath = [],
  definitions?: DefinitionsMap
): ClauseCheckResult {
  if (clause.patterns.length !== scrutineeTypes.length) {
    throw new TypeCheckError(
      `Clause has ${clause.patterns.length} patterns but expected ${scrutineeTypes.length}`,
      undefined,
      ctx,
      clausePath
    );
  }

  // Build up the context with pattern-bound variables
  // We need to track:
  // 1. The bindings introduced by each pattern (for the RHS context)
  // 2. For dependent types, substitute earlier pattern positions into later types
  let currentCtx = ctx;
  let currentSubst: Substitution = new Map();

  // Collect all bindings from all patterns
  const allBindings: Array<{ name: string; type: TTKTerm }> = [];

  // Track total bindings for shifting the return type at the end
  let totalBindings = 0;

  // Track extra bindings (beyond 1 per pattern) to shift telescope types
  let extraBindingsFromPreviousPatterns = 0;

  for (let i = 0; i < clause.patterns.length; i++) {
    const pattern = clause.patterns[i];
    const patternPath = appendPath(clausePath, fieldSeg('patterns'), arraySeg(i));

    // Get the type for this argument position.
    // The telescope type at position i uses De Bruijn indices relative to that position:
    // - Var(0) refers to position i-1
    // - Var(k) refers to position i-1-k
    //
    // If each pattern added exactly 1 binding, we wouldn't need to shift.
    // But constructor patterns can add multiple bindings (e.g., Refl adds 2).
    // So we track the "extra" bindings and shift the telescope type accordingly.
    let argType = scrutineeTypes[i];
    if (extraBindingsFromPreviousPatterns > 0) {
      argType = shiftTermBy(argType, extraBindingsFromPreviousPatterns, 0);
    }

    // Apply unification substitution
    argType = applySubstitution(currentSubst, argType);

    const result = checkPattern(pattern, argType, currentCtx, patternPath);

    // Track how many extra bindings this pattern added (beyond the expected 1)
    const bindingsAdded = result.bindings.length;
    extraBindingsFromPreviousPatterns += (bindingsAdded > 0 ? bindingsAdded - 1 : 0);

    // Extend context with pattern bindings
    const bindingsAddedThisPattern = result.bindings.length;
    for (const binding of result.bindings) {
      currentCtx = extendContext(currentCtx, binding.name, binding.type);
      allBindings.push(binding);
      totalBindings++;
    }

    // Before composing new substitutions, shift existing substitution entries
    // by the number of bindings we just added (because De Bruijn indices are relative).
    // Both the keys (var indices) and values need to be shifted.
    if (bindingsAddedThisPattern > 0) {
      const shiftedSubst = new Map<string, TTKTerm>();
      for (const [key, value] of currentSubst.entries()) {
        // Only shift var: keys (not name: keys which are informational)
        if (key.startsWith('var:')) {
          // Shift both the key index and the value
          const oldIndex = parseInt(key.substring(4), 10);
          const newKey = 'var:' + (oldIndex + bindingsAddedThisPattern);
          const newValue = shiftTermBy(value, bindingsAddedThisPattern, 0);
          shiftedSubst.set(newKey, newValue);
        } else {
          shiftedSubst.set(key, value);
        }
      }
      currentSubst = shiftedSubst;
    }

    // Compose substitutions from unification
    for (const [key, value] of result.substitution) {
      currentSubst.set(key, value);
    }
  }

  // Apply the final substitution to all bindings to get "solved" types
  const solvedBindings = allBindings.map(binding => ({
    name: binding.name,
    type: applySubstitution(currentSubst, binding.type),
  }));

  // Type-check the RHS in the extended context
  // The RHS path is clausePath.rhs for error reporting
  const rhsPath = appendPath(clausePath, fieldSeg('rhs'));

  let returnType: TTKTerm;
  if (expectedReturnType) {
    // The return type uses telescope-relative indices, where Var(k) refers to
    // telescope position (numPatterns - 1 - k). After binding all patterns,
    // we need to shift the return type if constructor patterns bound more
    // variables than their single telescope position.
    //
    // For example, with 3 telescope positions and 5 total bindings:
    // - Telescope position 0 (A) is now at context index 4
    // - Return type Var(2) refers to telescope position 0
    // - After shift by (5-3)=2: Var(2) -> Var(4), which correctly refers to A
    const numPatterns = clause.patterns.length;
    const extraBindings = totalBindings - numPatterns;

    let refinedReturnType = expectedReturnType;
    if (extraBindings > 0) {
      refinedReturnType = shiftTermBy(refinedReturnType, extraBindings, 0);
    }
    refinedReturnType = applySubstitution(currentSubst, refinedReturnType);

    // Use checkType for bidirectional type checking (important for lambdas).
    // If checkType fails, we try a fallback that applies substitution to
    // the inferred type, which handles dependent pattern matching where
    // the RHS uses original variables that are equal to pattern variables.
    try {
      checkType(clause.rhs, refinedReturnType, currentCtx, rhsPath);
    } catch (e) {
      if (!(e instanceof TypeCheckError)) throw e;

      // Fallback: try with substitution applied to inferred type
      const inferredType = inferType(clause.rhs, currentCtx, rhsPath);
      const normalizedInferred = applySubstitution(currentSubst, inferredType);

      if (!convertible(normalizedInferred, refinedReturnType, currentCtx, definitions)) {
        // Use context names for readable error messages
        const names: string[] = currentCtx.map((entry, i) => entry.name || `_${i}`);
        throw new TypeCheckError(
          `Type mismatch.\n  Expected: ${prettyPrint(refinedReturnType, names)}\n  Inferred: ${prettyPrint(normalizedInferred, names)}`,
          clause.rhs,
          currentCtx,
          rhsPath
        );
      }
    }
    returnType = refinedReturnType;
  } else {
    // Infer the return type
    returnType = inferType(clause.rhs, currentCtx, rhsPath);
  }

  return {
    returnType,
    solvedBindings,
    substitution: currentSubst,
  };
}

/**
 * Instantiate a type from a telescope position.
 *
 * In a telescope like (A : Type) -> (x : A) -> List A -> A,
 * the type `A` at position 1 is represented as Var(0), referencing position 0.
 *
 * With our pattern matching approach where every pattern (including wildcards)
 * binds exactly one variable per argument position, the telescope variables
 * map directly to the context variables.
 *
 * However, extendContext shifts all types, so we need to account for that.
 * After processing position i, we've added i+1 bindings to the context.
 * The type at position i was originally written with Var(0) referring to
 * position i-1, but after extending the context, we need to shift appropriately.
 *
 * Actually, the key insight is simpler: the telescope types are already in
 * "shifted" form where Var(k) refers to the k-th previously bound variable.
 * This matches exactly how extendContext works - it shifts existing types.
 *
 * For now, we return the type as-is since the shifting is handled by extendContext.
 */
function instantiateTelescopeType(
  type: TTKTerm,
  _currentPosition: number,
  _telescopeTypes: TTKTerm[],
  _patternBindings: Array<{ name: string; type: TTKTerm }>,
  _ctx: TTKContext
): TTKTerm {
  // The type is already in telescope form with proper De Bruijn indices.
  // extendContext handles shifting as we add bindings.
  return type;
}

// ============================================================================
// Match Expression Type-Checking
// ============================================================================

/**
 * Type-check a match expression and infer its type.
 *
 * @param scrutinee - The term being matched
 * @param clauses - The pattern matching clauses
 * @param ctx - The typing context
 * @param expectedType - Optional expected type for checking mode
 * @param matchPath - Path to the match expression in the source (for error reporting)
 * @returns The inferred type of the match expression
 */
export function inferMatchType(
  scrutinee: TTKTerm,
  clauses: TTKClause[],
  ctx: TTKContext,
  expectedType?: TTKTerm,
  matchPath: IndexPath = [],
  definitions?: DefinitionsMap
): TTKTerm {
  if (clauses.length === 0) {
    throw new TypeCheckError(
      'Match expression must have at least one clause',
      undefined,
      ctx,
      matchPath
    );
  }

  // Infer the type of the scrutinee
  const scrutineePath = appendPath(matchPath, fieldSeg('scrutinee'));
  const scrutineeType = inferType(scrutinee, ctx, scrutineePath);

  // Type-check each clause
  let inferredReturnType: TTKTerm | null = expectedType || null;

  for (let i = 0; i < clauses.length; i++) {
    const clause = clauses[i];
    const clausePath = appendPath(matchPath, fieldSeg('clauses'), arraySeg(i));

    try {
      const clauseReturnType = checkClause(
        clause,
        [scrutineeType],
        inferredReturnType,
        ctx,
        clausePath,
        definitions
      );

      if (inferredReturnType === null) {
        // First clause: use its return type
        inferredReturnType = clauseReturnType;
      } else if (!expectedType) {
        // Subsequent clauses: check compatibility
        if (!convertible(clauseReturnType, inferredReturnType, ctx, definitions)) {
          throw new TypeCheckError(
            `Clause ${i + 1} returns type ${prettyPrint(clauseReturnType)} ` +
            `but previous clauses return ${prettyPrint(inferredReturnType)}`,
            undefined,
            ctx,
            clausePath
          );
        }
      }
    } catch (e) {
      if (e instanceof TypeCheckError) {
        throw new TypeCheckError(
          `In clause ${i + 1}: ${e.message}`,
          e.term,
          e.context || ctx,
          e.termPath || clausePath
        );
      }
      throw e;
    }
  }

  if (inferredReturnType === null) {
    throw new TypeCheckError(
      'Could not infer return type of match expression',
      undefined,
      ctx,
      matchPath
    );
  }

  return inferredReturnType;
}

/**
 * Type-check a multi-clause function definition.
 *
 * This handles the common case where a function is defined by multiple clauses:
 * ```
 * plus : Nat -> Nat -> Nat
 * plus Zero b = b
 * plus (Succ a) b = Succ (plus a b)
 * ```
 *
 * The function type is given, and we check that all clauses are well-typed
 * and return the expected type.
 *
 * ## Currying and Partial Application
 *
 * Clauses may have fewer patterns than the function's total arity, enabling
 * curried definitions. All clauses must have the same number of patterns.
 *
 * For example, all of these are valid definitions of the same function:
 * ```
 * swap : (A : Type) -> (f : A -> A -> A) -> (A -> A -> A)
 * swap A = \f => \x y => f y x       -- 1 pattern
 * swap A f = \x y => f y x           -- 2 patterns
 * swap A f x = \y => f y x           -- 3 patterns
 * swap A f x y = f y x               -- 4 patterns (fully saturated)
 * ```
 *
 * When n patterns are given for a function with m arguments (n < m),
 * the expected return type for the RHS is the remaining (m - n) Pi binders.
 *
 * @param functionType - The declared type of the function
 * @param clauses - The pattern matching clauses
 * @param ctx - The typing context (should include the function itself for recursion)
 * @param valuePath - Path to the match expression in the source (for error reporting)
 */
export function checkFunctionClauses(
  functionType: TTKTerm,
  clauses: TTKClause[],
  ctx: TTKContext,
  valuePath: IndexPath = []
): void {
  // Delegate to the result-returning version, discarding the result
  checkFunctionClausesWithResult(functionType, clauses, ctx, valuePath);
}

/**
 * Type-check a multi-clause function definition, returning elaboration results.
 *
 * This version returns the per-clause elaboration results including solved bindings
 * and substitutions. Use this when you need access to the elaborated context for
 * type queries or IDE features.
 *
 * @param functionType - The declared type of the function
 * @param clauses - The pattern matching clauses
 * @param ctx - The typing context (should include the function itself for recursion)
 * @param valuePath - Path to the match expression in the source (for error reporting)
 * @param definitions - Map of function definitions for WHNF reduction
 * @returns FunctionClausesResult with per-clause results and combined substitution
 */
export function checkFunctionClausesWithResult(
  functionType: TTKTerm,
  clauses: TTKClause[],
  ctx: TTKContext,
  valuePath: IndexPath = [],
  definitions?: DefinitionsMap
): FunctionClausesResult {
  if (clauses.length === 0) {
    throw new TypeCheckError(
      'Function must have at least one clause',
      undefined,
      ctx,
      valuePath
    );
  }

  // Extract the full argument types and return type from the function type
  const { argTypes: fullArgTypes, returnType: baseReturnType } = extractFunctionSignature(functionType);

  // Determine the arity (number of patterns) from the first clause
  const arity = clauses[0].patterns.length;

  // Validate arity: must not exceed the function's total arguments
  if (arity > fullArgTypes.length) {
    throw new TypeCheckError(
      `Clause 1 has ${arity} patterns but function type only has ${fullArgTypes.length} arguments`,
      undefined,
      ctx,
      appendPath(valuePath, fieldSeg('clauses'), arraySeg(0))
    );
  }

  // All clauses must have the same arity
  for (let i = 1; i < clauses.length; i++) {
    if (clauses[i].patterns.length !== arity) {
      throw new TypeCheckError(
        `Clause ${i + 1} has ${clauses[i].patterns.length} patterns but other clauses have ${arity}`,
        undefined,
        ctx,
        appendPath(valuePath, fieldSeg('clauses'), arraySeg(i))
      );
    }
  }

  // The patterns match the first `arity` argument types
  const patternArgTypes = fullArgTypes.slice(0, arity);

  // The expected return type is either the base return type (if fully saturated)
  // or a function type for the remaining arguments (if curried)
  const expectedReturnType = buildReturnType(
    fullArgTypes.slice(arity),
    baseReturnType
  );

  // Check each clause and collect results
  const clauseResults: ClauseCheckResult[] = [];
  let combinedSubstitution: Substitution = emptySubstitution();

  for (let i = 0; i < clauses.length; i++) {
    const clause = clauses[i];
    const clausePath = appendPath(valuePath, fieldSeg('clauses'), arraySeg(i));

    try {
      const result = checkClauseWithResult(clause, patternArgTypes, expectedReturnType, ctx, clausePath, definitions);
      clauseResults.push(result);

      // Compose substitutions from all clauses
      // Note: In practice, each clause's substitution is independent (they're alternative branches),
      // but we track them for potential cross-clause analysis
      try {
        combinedSubstitution = composeSubstitutions(combinedSubstitution, result.substitution);
      } catch {
        // If substitutions conflict between clauses, that's fine - they're alternatives
        // Just keep the first one
      }
    } catch (e) {
      if (e instanceof TypeCheckError) {
        // Preserve the original path if the error already has one
        throw new TypeCheckError(
          `In clause ${i + 1}: ${e.message}`,
          e.term,
          e.context || ctx,
          e.termPath || clausePath
        );
      }
      throw e;
    }
  }

  return {
    clauses: clauseResults,
    substitution: combinedSubstitution,
  };
}

/**
 * Build a return type by wrapping remaining argument types as Pi binders.
 *
 * If remainingArgTypes is empty, returns the baseReturnType.
 * Otherwise, builds: (arg1 : T1) -> (arg2 : T2) -> ... -> baseReturnType
 *
 * Note: The remaining argument types are in telescope form, where each type
 * may reference earlier arguments via De Bruijn indices. When we peel off
 * the first `arity` arguments and use the rest as a return type, the indices
 * need adjustment because those arguments are no longer bound.
 */
function buildReturnType(
  remainingArgTypes: TTKTerm[],
  baseReturnType: TTKTerm
): TTKTerm {
  if (remainingArgTypes.length === 0) {
    return baseReturnType;
  }

  // Build the return type right-to-left, starting with the base
  let result = baseReturnType;

  for (let i = remainingArgTypes.length - 1; i >= 0; i--) {
    result = {
      tag: 'Binder',
      name: '_', // Anonymous binders for the curried part
      binderKind: { tag: 'BPi' },
      domain: remainingArgTypes[i],
      body: result,
    } as TTKTerm;
  }

  return result;
}

/**
 * Extract argument types and return type from a function type.
 */
function extractFunctionSignature(
  type: TTKTerm
): { argTypes: TTKTerm[]; returnType: TTKTerm } {
  const argTypes: TTKTerm[] = [];
  let current = type;

  while (current.tag === 'Binder' && current.binderKind.tag === 'BPi') {
    argTypes.push(current.domain);
    current = current.body;
  }

  return { argTypes, returnType: current };
}
