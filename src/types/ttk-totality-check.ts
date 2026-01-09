/**
 * Totality/Exhaustiveness Checking for Pattern Matching (TTK Layer)
 *
 * This module implements coverage checking for pattern matching in the kernel layer.
 * It detects when function definitions don't cover all possible constructor cases,
 * making them *partial* functions.
 *
 * ## Algorithm Overview
 *
 * Based on Maranget (2008) "Compiling Pattern Matching to Good Decision Trees":
 *
 * 1. Build a **splitting tree** from pattern clauses
 * 2. Traverse the tree to find **uncovered cases** (Missing nodes)
 * 3. Report partiality if any uncovered cases exist
 *
 * ## Key Concepts
 *
 * - **Split Node**: Split on an argument position, with branches for each constructor
 * - **Leaf Node**: A clause successfully matched
 * - **Missing Node**: An uncovered case (partial function detected)
 *
 * ## Wildcard Handling
 *
 * `PVar` patterns (including wildcards like _w0, _w1) match ANY constructor. When building the tree:
 * - They apply to all constructors not explicitly matched by a `PCtor`
 * - This creates "default" coverage that can fill in missing branches
 *
 * IMPORTANT: This operates on TTKTerm (kernel terms), following the project convention
 * that all verification happens in the kernel layer.
 */

import { TTKTerm, TTKContext, TTKClause, mkType } from './tt-kernel';
import { TPattern } from './tt-core';
import { unifyTerms } from './tt-unify';

// ============================================================================
// Types
// ============================================================================

/**
 * Check if a pattern is a wildcard or variable pattern (matches anything).
 * Wildcards are now represented as PVar with names starting with '_'.
 */
function isWildcardOrVar(pattern: TPattern | undefined): boolean {
  return pattern !== undefined && pattern.tag === 'PVar';
}

/** Counter for generating fresh wildcard names during totality checking */
let wildcardCounter = 0;

/** Generate a fresh wildcard pattern */
function freshWildcardPattern(): TPattern {
  return { tag: 'PVar', name: `_tc${wildcardCounter++}` };
}

/**
 * A splitting tree represents the decision structure of pattern matching.
 */
export type SplitTree =
  | SplitNode
  | LeafNode
  | MissingNode;

/**
 * Split on an argument position, with branches for each constructor.
 */
export interface SplitNode {
  tag: 'Split';
  /** The argument position being split on (0-indexed) */
  argIndex: number;
  /** Branches for each constructor name */
  branches: Map<string, SplitTree>;
  /** Default branch for wildcards/variables (applies to unmatched constructors) */
  defaultBranch?: SplitTree;
  /** Constructors that are impossible due to dependent type index constraints */
  impossibleBranches?: string[];
}

/**
 * A clause successfully matched at this point.
 */
export interface LeafNode {
  tag: 'Leaf';
  /** Index of the clause that matches */
  clauseIndex: number;
}

/**
 * An uncovered case - the function is partial.
 */
export interface MissingNode {
  tag: 'Missing';
  /** Path of constructor names leading to this missing case (for debugging) */
  path: string[];
  /** Structured missing patterns (one per original argument) */
  patterns: MissingPattern[];
}

/**
 * A missing pattern for one argument position.
 * Either a wildcard or a constructor with nested patterns.
 */
export type MissingPattern =
  | { tag: 'MWild' }
  | { tag: 'MCtor'; name: string; args: MissingPattern[] };

/**
 * Result of totality analysis.
 */
export interface TotalityAnalysis {
  /** Whether the pattern matching is exhaustive */
  exhaustive: boolean;
  /** List of missing cases as structured patterns */
  missingCases: MissingPattern[][];
  /** The splitting tree (for debugging/visualization) */
  splitTree: SplitTree;
  /** Indices of clauses that are inaccessible (never matched) */
  inaccessibleClauses: number[];
}

/**
 * Internal representation of a clause during tree building.
 * Tracks the remaining patterns to match and the original clause index.
 */
interface ClauseRow {
  /** Remaining patterns (one per remaining argument position) */
  patterns: TPattern[];
  /** Remaining argument types (aligned with patterns) */
  argTypes: ArgTypeInfo[];
  /** Original clause index */
  clauseIndex: number;
}

/**
 * Tracks index refinements from pattern matches.
 *
 * When we match argument position N against a constructor like `Succ n`,
 * we record that Var(N) should be substituted with `Succ (Var fresh)`.
 * This is used to update dependent types for later arguments.
 *
 * Key: original argument position (before specialization)
 * Value: the term it's bound to (e.g., Const "Zero" or App(Const "Succ", Var 0))
 */
type IndexBindings = Map<number, TTKTerm>;

/**
 * Apply index bindings to a type term.
 *
 * This substitutes De Bruijn variables that reference bound argument positions
 * with the constructor patterns they were matched against.
 *
 * For example, if we matched arg 1 against `Succ n`, and we have type `Vec A (Var 1)`,
 * this would substitute to get `Vec A (Succ n)`.
 *
 * The key insight is that De Bruijn indices in the domain of arg N count backwards:
 * - Var 0 refers to arg (N-1)
 * - Var 1 refers to arg (N-2)
 * - Var k refers to arg (N-1-k)
 *
 * @param type - The type to substitute into
 * @param bindings - Map from argument positions to their bound terms
 * @param contextSize - Number of binders in scope for this type (equals arg index)
 * @param depth - Current binding depth within nested binders in the type
 * @returns The type with substitutions applied
 */
function applyIndexBindings(
  type: TTKTerm,
  bindings: IndexBindings,
  contextSize: number,
  depth: number = 0
): TTKTerm {
  if (bindings.size === 0) {
    return type;
  }

  switch (type.tag) {
    case 'Var': {
      // De Bruijn index counting from innermost
      const dbIndex = type.index;

      // Only consider variables that refer outside the current nested binders
      if (dbIndex < depth) {
        // This var refers to a binder inside the type (e.g., in a Pi domain), not an arg
        return type;
      }

      // Compute the original argument position this var refers to
      // Adjusted dbIndex (relative to the arg context) = dbIndex - depth
      // Arg position = (contextSize - 1) - (dbIndex - depth)
      const adjustedDbIndex = dbIndex - depth;
      const argPosition = (contextSize - 1) - adjustedDbIndex;

      const binding = bindings.get(argPosition);
      if (binding) {
        // Shift the binding term to account for any binders we've entered within the type
        return shiftTerm(binding, depth);
      }
      return type;
    }

    case 'App':
      return {
        tag: 'App',
        fn: applyIndexBindings(type.fn, bindings, contextSize, depth),
        arg: applyIndexBindings(type.arg, bindings, contextSize, depth)
      };

    case 'Binder':
      return {
        tag: 'Binder',
        binderKind: type.binderKind,
        name: type.name,
        domain: applyIndexBindings(type.domain, bindings, contextSize, depth),
        body: applyIndexBindings(type.body, bindings, contextSize, depth + 1)
      };

    case 'Const':
    case 'Sort':
    case 'Hole':
    case 'Annot':
    case 'Match':
      // These don't contain free variables that need substitution,
      // or shouldn't appear in types during totality checking
      return type;
  }
}

/**
 * Shift all free variables in a term by a given amount.
 * This is needed when moving a term into a different binding context.
 */
function shiftTerm(term: TTKTerm, amount: number): TTKTerm {
  if (amount === 0) return term;
  return shiftTermAbove(term, 0, amount);
}

/**
 * Shift variables with index >= cutoff by the given amount.
 */
function shiftTermAbove(term: TTKTerm, cutoff: number, amount: number): TTKTerm {
  switch (term.tag) {
    case 'Var':
      if (term.index >= cutoff) {
        return { tag: 'Var', index: term.index + amount };
      }
      return term;

    case 'App':
      return {
        tag: 'App',
        fn: shiftTermAbove(term.fn, cutoff, amount),
        arg: shiftTermAbove(term.arg, cutoff, amount)
      };

    case 'Binder':
      return {
        tag: 'Binder',
        binderKind: term.binderKind,
        name: term.name,
        domain: shiftTermAbove(term.domain, cutoff, amount),
        body: shiftTermAbove(term.body, cutoff + 1, amount)
      };

    case 'Const':
    case 'Sort':
    case 'Hole':
    case 'Annot':
    case 'Match':
      // These don't need shifting for our purposes
      return term;
  }
}

/**
 * Convert a constructor name to a term for index binding.
 * Creates a simple Const application for constructors like Zero or Succ.
 *
 * For example, "Succ" with arity 1 becomes App(Const("Succ"), Var(0))
 * This is used to represent the pattern match constraint in the index bindings.
 */
function constructorToTerm(ctorName: string, arity: number): TTKTerm {
  // Create a placeholder type for the const - we only use this for unification
  // which looks at structure, not the stored type field
  const placeholderType: TTKTerm = { tag: 'Sort', level: 0 };

  let result: TTKTerm = { tag: 'Const', name: ctorName, type: placeholderType };
  for (let i = 0; i < arity; i++) {
    result = {
      tag: 'App',
      fn: result,
      arg: { tag: 'Var', index: i }  // Fresh variables for constructor args
    };
  }
  return result;
}

/**
 * Tracks the pattern being built for each original argument.
 *
 * As we traverse the tree, we commit to constructor choices. When a slot is
 * consumed (either by matching a constructor or by a wildcard), we record what
 * was matched.
 *
 * This is a mutable structure that gets cloned when branching.
 */
interface PatternBuildState {
  /** Pattern being built for each original argument */
  patterns: MutablePattern[];
}

/**
 * A mutable pattern node that can be filled in as we traverse.
 * Starts as a "hole" and gets filled with either a wildcard or constructor.
 */
type MutablePattern =
  | { tag: 'Hole' }  // Not yet determined
  | { tag: 'MWild' }  // Committed to wildcard
  | { tag: 'MCtor'; name: string; args: MutablePattern[] };  // Committed to constructor

/**
 * Maps current pattern positions to where they should write in the pattern state.
 */
interface SlotRef {
  /** Which original argument this slot writes to */
  argIndex: number;
  /** Path to the MutablePattern node to fill (indices into args arrays) */
  nodePath: number[];
}

/**
 * Information about an argument position's type.
 */
interface ArgTypeInfo {
  /** Name of the inductive type (e.g., "Nat", "Bool") */
  typeName: string | null;
  /** The full type expression (e.g., Vec A (Succ n)) - needed for index unification */
  fullType: TTKTerm | null;
  /** All constructor names for this type */
  constructors: string[];
  /** Number of arguments each constructor takes (for decomposition) */
  constructorArities: Map<string, number>;
}

// ============================================================================
// Main Entry Point
// ============================================================================

/**
 * Analyze a function definition for exhaustiveness.
 *
 * @param clauses - The pattern matching clauses
 * @param argTypes - Types of each argument position
 * @param ctx - Typing context (contains constructor information)
 * @param excludeNames - Names to exclude from constructor lookup (e.g., the function being checked)
 * @param knownConstructors - Set of names that are known to be constructors
 * @returns Analysis result with exhaustiveness status and missing cases
 */
export function analyzeTotality(
  clauses: TTKClause[],
  argTypes: TTKTerm[],
  ctx: TTKContext,
  excludeNames: Set<string> = new Set(),
  knownConstructors?: Set<string>
): TotalityAnalysis {
  if (clauses.length === 0) {
    // No clauses means completely missing coverage
    // Create wildcards for each argument
    const wildcardPatterns: MissingPattern[] = argTypes.map(() => ({ tag: 'MWild' as const }));
    return {
      exhaustive: false,
      missingCases: [wildcardPatterns],
      splitTree: { tag: 'Missing', path: [], patterns: wildcardPatterns },
      inaccessibleClauses: []
    };
  }

  if (argTypes.length === 0) {
    // No arguments, so the first clause covers everything
    // All clauses after the first are inaccessible
    const inaccessibleClauses = clauses.length > 1
      ? Array.from({ length: clauses.length - 1 }, (_, i) => i + 1)
      : [];
    return {
      exhaustive: true,
      missingCases: [],
      splitTree: { tag: 'Leaf', clauseIndex: 0 },
      inaccessibleClauses
    };
  }

  // Build type info for each argument position
  const argTypeInfos = argTypes.map(type => getArgTypeInfo(type, ctx, excludeNames, knownConstructors));

  // Convert clauses to internal row representation
  // Each row carries its own copy of argTypeInfos (they may diverge during specialization)
  const rows: ClauseRow[] = clauses.map((clause, index) => ({
    patterns: clause.patterns,
    argTypes: argTypeInfos,
    clauseIndex: index
  }));

  // Initialize pattern state and slot refs
  const initialState: PatternBuildState = {
    patterns: argTypes.map(() => ({ tag: 'Hole' as const }))
  };
  const initialSlotRefs: SlotRef[] = argTypes.map((_, i) => ({
    argIndex: i,
    nodePath: []
  }));

  // Build the splitting tree
  const splitTree = buildSplitTree(rows, ctx, excludeNames, [], initialSlotRefs, initialState, knownConstructors);

  // Find all missing cases
  const missingCases = findMissingCases(splitTree);

  // Find inaccessible clauses (those that don't appear in any Leaf node)
  const reachableIndices = collectReachableClauseIndices(splitTree);
  const inaccessibleClauses: number[] = [];
  for (let i = 0; i < clauses.length; i++) {
    if (!reachableIndices.has(i)) {
      inaccessibleClauses.push(i);
    }
  }

  return {
    exhaustive: missingCases.length === 0,
    missingCases,
    splitTree,
    inaccessibleClauses
  };
}

// ============================================================================
// Type Information Extraction
// ============================================================================

/**
 * Extract type information for an argument position.
 *
 * @param type - The type of the argument
 * @param ctx - The typing context
 * @param excludeNames - Names to exclude from constructor lookup
 * @param knownConstructors - Set of names that are known to be constructors
 */
function getArgTypeInfo(
  type: TTKTerm,
  ctx: TTKContext,
  excludeNames: Set<string> = new Set(),
  knownConstructors?: Set<string>
): ArgTypeInfo {
  const typeName = getHeadConstName(type);

  if (!typeName) {
    // Not an inductive type (e.g., function type, Sort)
    return {
      typeName: null,
      fullType: null,
      constructors: [],
      constructorArities: new Map()
    };
  }

  // Find all constructors for this type
  const constructors = getConstructorsForType(typeName, ctx, excludeNames, knownConstructors);
  const constructorArities = new Map<string, number>();

  for (const ctorName of constructors) {
    const ctorType = lookupTypeByName(ctx, ctorName);
    if (ctorType) {
      constructorArities.set(ctorName, countCtorArgs(ctorType, typeName));
    }
  }

  return {
    typeName,
    fullType: type,  // Preserve the full type for index unification
    constructors,
    constructorArities
  };
}

/**
 * Get the head constant name from a type (unwrapping applications).
 * For `Nat` returns "Nat", for `Vec A n` returns "Vec".
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
 * Find all constructors for a given inductive type.
 *
 * If `knownConstructors` is provided (recommended), it filters to only include
 * names that are actually constructors. This is important because functions
 * like `plus : Nat -> Nat -> Nat` have `Nat` as return type head but are NOT
 * constructors.
 *
 * If `knownConstructors` is not provided (legacy behavior), falls back to
 * scanning the context by return type head (which may include functions).
 *
 * @param typeName - The name of the inductive type
 * @param ctx - The typing context
 * @param excludeNames - Names to exclude (e.g., the function being type-checked)
 * @param knownConstructors - Set of names that are known to be constructors
 */
export function getConstructorsForType(
  typeName: string,
  ctx: TTKContext,
  excludeNames: Set<string> = new Set(),
  knownConstructors?: Set<string>
): string[] {
  const constructors: string[] = [];

  for (const binding of ctx) {
    // Skip excluded names (e.g., the function being type-checked for recursion)
    if (excludeNames.has(binding.name)) {
      continue;
    }

    const returnType = getReturnType(binding.type);
    const headName = getHeadConstName(returnType);
    if (headName === typeName) {
      // If we have known constructors, only include actual constructors
      // This filters out functions like `plus : Nat -> Nat -> Nat`
      if (knownConstructors) {
        if (knownConstructors.has(binding.name)) {
          constructors.push(binding.name);
        }
      } else {
        // Legacy behavior: include anything with matching return type head
        constructors.push(binding.name);
      }
    }
  }

  return constructors;
}

/**
 * Look up a type by name in the context.
 */
function lookupTypeByName(ctx: TTKContext, name: string): TTKTerm | null {
  for (const binding of ctx) {
    if (binding.name === name) {
      return binding.type;
    }
  }
  return null;
}

/**
 * Count the number of arguments a constructor takes (excluding the return type).
 * For `Succ : Nat -> Nat`, returns 1.
 * For `VCons : (A : Type) -> (n : Nat) -> A -> Vec A n -> Vec A (Succ n)`, returns 4.
 */
function countCtorArgs(ctorType: TTKTerm, _inductiveName: string): number {
  let count = 0;
  let current = ctorType;
  while (current.tag === 'Binder' && current.binderKind.tag === 'BPi') {
    count++;
    current = current.body;
  }
  return count;
}

/**
 * Extract type indices (arguments) from an applied type.
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
 * Check if a constructor is possible given an expected type.
 *
 * For indexed inductive types, a constructor may be impossible if its
 * return type indices cannot unify with the expected type's indices.
 *
 * For example, VNil : Vec A Zero cannot match Vec A (Succ n) because
 * Zero cannot unify with (Succ n).
 *
 * @param ctorType - The constructor's full type
 * @param expectedType - The expected type at this position
 * @param ctx - Typing context
 * @returns true if the constructor is possible, false if definitely impossible
 */
function isConstructorPossible(
  ctorType: TTKTerm,
  expectedType: TTKTerm,
  ctx: TTKContext
): boolean {
  // Get the constructor's return type
  const ctorReturnType = getReturnType(ctorType);

  // Extract indices from both types
  const ctorIndices = extractTypeIndices(ctorReturnType);
  const expectedIndices = extractTypeIndices(expectedType);

  // If different number of indices, something is wrong - assume possible
  if (ctorIndices.length !== expectedIndices.length) {
    return true;
  }

  // Try to unify each index
  // Note: For proper handling, we'd need to account for the constructor's
  // parameter bindings, but for simple cases like Zero vs (Succ n),
  // the unification will correctly detect conflicts.
  for (let i = 0; i < ctorIndices.length; i++) {
    const ctorIdx = ctorIndices[i];
    const expIdx = expectedIndices[i];

    // Try unification - we only care about detecting definite conflicts
    const result = unifyTerms(ctorIdx, expIdx, mkType(0), ctx);
    if (result.tag === 'failure') {
      // This constructor is definitely impossible
      return false;
    }
    // If stuck or success, we assume it could be possible
  }

  return true;
}

// ============================================================================
// Pattern State Manipulation
// ============================================================================

/**
 * Deep clone a pattern state so we can modify it without affecting the original.
 */
function clonePatternState(state: PatternBuildState): PatternBuildState {
  return {
    patterns: state.patterns.map(p => cloneMutablePattern(p))
  };
}

/**
 * Deep clone a mutable pattern.
 */
function cloneMutablePattern(pattern: MutablePattern): MutablePattern {
  switch (pattern.tag) {
    case 'Hole':
      return { tag: 'Hole' };
    case 'MWild':
      return { tag: 'MWild' };
    case 'MCtor':
      return {
        tag: 'MCtor',
        name: pattern.name,
        args: pattern.args.map(a => cloneMutablePattern(a))
      };
  }
}

/**
 * Set a pattern at the given slot reference.
 *
 * @param state - The pattern state to modify (mutated in place)
 * @param slot - Where to write the pattern
 * @param pattern - The pattern to write
 */
function setPatternAt(state: PatternBuildState, slot: SlotRef, pattern: MutablePattern): void {
  if (slot.nodePath.length === 0) {
    // Writing to a top-level argument
    state.patterns[slot.argIndex] = pattern;
  } else {
    // Navigate to the nested position
    let current = state.patterns[slot.argIndex];
    for (let i = 0; i < slot.nodePath.length - 1; i++) {
      if (current.tag === 'MCtor') {
        current = current.args[slot.nodePath[i]];
      } else {
        // Can't navigate further - shouldn't happen with correct usage
        return;
      }
    }
    // Set the final position
    if (current.tag === 'MCtor') {
      const lastIndex = slot.nodePath[slot.nodePath.length - 1];
      current.args[lastIndex] = pattern;
    }
  }
}

/**
 * Convert mutable patterns to final MissingPatterns.
 * Holes become wildcards.
 */
function finalizePatterns(state: PatternBuildState): MissingPattern[] {
  return state.patterns.map(p => finalizeMutablePattern(p));
}

/**
 * Convert a mutable pattern to a MissingPattern.
 */
function finalizeMutablePattern(pattern: MutablePattern): MissingPattern {
  switch (pattern.tag) {
    case 'Hole':
      return { tag: 'MWild' };
    case 'MWild':
      return { tag: 'MWild' };
    case 'MCtor':
      return {
        tag: 'MCtor',
        name: pattern.name,
        args: pattern.args.map(a => finalizeMutablePattern(a))
      };
  }
}

// ============================================================================
// Splitting Tree Construction
// ============================================================================

/**
 * Build the splitting tree recursively.
 *
 * The algorithm processes patterns left-to-right. Each row carries its own
 * argTypes array which is updated as patterns are decomposed.
 *
 * @param rows - Remaining clause rows to process (each with patterns and argTypes)
 * @param ctx - Typing context for looking up constructor types
 * @param excludeNames - Names to exclude from constructor lookup
 * @param currentPath - Path of constructor names to this point (for debugging)
 * @param slotRefs - Maps each current pattern position to where it writes in patternState
 * @param patternState - The patterns being built for each original argument
 * @param knownConstructors - Set of names that are known to be constructors
 * @param indexBindings - Tracks index refinements from pattern matches on earlier args
 */
function buildSplitTree(
  rows: ClauseRow[],
  ctx: TTKContext,
  excludeNames: Set<string>,
  currentPath: string[],
  slotRefs: SlotRef[],
  patternState: PatternBuildState,
  knownConstructors?: Set<string>,
  indexBindings: IndexBindings = new Map()
): SplitTree {
  // Base case: no rows means uncovered
  if (rows.length === 0) {
    // Finalize the pattern state into MissingPatterns
    const patterns = finalizePatterns(patternState);
    return { tag: 'Missing', path: currentPath, patterns };
  }

  // Base case: no more patterns to match in first row
  if (rows[0].patterns.length === 0) {
    // First clause covers this case
    return { tag: 'Leaf', clauseIndex: rows[0].clauseIndex };
  }

  // Always work with position 0 in the current patterns
  const patternIndex = 0;

  // Check if first row has a wildcard/var at current position - it covers all
  const firstPattern = rows[0].patterns[patternIndex];
  if (isWildcardOrVar(firstPattern)) {
    // Check if ALL patterns at this position are wildcards/vars
    const allWildcards = rows.every(row => {
      const pat = row.patterns[patternIndex];
      return isWildcardOrVar(pat);
    });

    if (allWildcards) {
      // Mark this slot as a wildcard in the pattern state
      const currentSlot = slotRefs[0];
      const newState = clonePatternState(patternState);
      setPatternAt(newState, currentSlot, { tag: 'MWild' });

      // Remove the first pattern, argType, and slot ref
      const advancedRows = rows.map(row => ({
        ...row,
        patterns: row.patterns.slice(1),
        argTypes: row.argTypes.slice(1)
      }));
      const advancedSlots = slotRefs.slice(1);
      // Wildcards don't refine indices, so pass bindings unchanged
      return buildSplitTree(advancedRows, ctx, excludeNames, currentPath, advancedSlots, newState, knownConstructors, indexBindings);
    }
  }

  // Get type info from first row (all rows should have same type at position 0)
  const typeInfo = rows[0].argTypes[0];

  // If no constructors (non-inductive type), skip this position (treat as wildcard)
  if (!typeInfo || typeInfo.constructors.length === 0) {
    const currentSlot = slotRefs[0];
    const newState = clonePatternState(patternState);
    setPatternAt(newState, currentSlot, { tag: 'MWild' });

    const advancedRows = rows.map(row => ({
      ...row,
      patterns: row.patterns.slice(1),
      argTypes: row.argTypes.slice(1)
    }));
    const advancedSlots = slotRefs.slice(1);
    return buildSplitTree(advancedRows, ctx, excludeNames, currentPath, advancedSlots, newState, knownConstructors, indexBindings);
  }

  // Build branches for each constructor
  const branches = new Map<string, SplitTree>();

  // Collect rows that have wildcards/vars at this position (they match all constructors)
  const wildcardRows = rows.filter(row => {
    const pat = row.patterns[patternIndex];
    return isWildcardOrVar(pat);
  });

  // Collect which constructors are explicitly matched by PCtor patterns
  const explicitlyMatchedCtors = new Set<string>();
  for (const row of rows) {
    const pat = row.patterns[patternIndex];
    if (pat && pat.tag === 'PCtor') {
      explicitlyMatchedCtors.add(pat.name);
    }
  }

  // Track which constructors we actually create branches for
  // (some may be skipped due to impossibility from index constraints)
  const branchedConstructors = new Set<string>();

  // Track constructors that are impossible due to dependent type index constraints
  const impossibleConstructors: string[] = [];

  // Get the current slot ref for position 0
  const currentSlot = slotRefs[0];

  for (const ctorName of typeInfo.constructors) {
    // Check if this constructor is possible given the expected type's indices.
    // For indexed types like Vec, some constructors may be impossible due to
    // index constraints (e.g., VNil can't match Vec A (Succ n)).
    if (typeInfo.fullType) {
      const ctorType = lookupTypeByName(ctx, ctorName);
      // Apply index bindings to get the refined expected type
      // For example, if we matched arg 1 against Succ, and arg 3 is Vec A (Var 1),
      // we need to check against Vec A (Succ _) instead of Vec A (Var 1)
      // The contextSize is the original argument index (how many binders are in scope)
      const contextSize = currentSlot.argIndex;
      const refinedExpectedType = applyIndexBindings(typeInfo.fullType, indexBindings, contextSize);

      if (ctorType && !isConstructorPossible(ctorType, refinedExpectedType, ctx)) {
        // This constructor is impossible - skip it (no missing case for it)
        impossibleConstructors.push(ctorName);
        continue;
      }
    }

    // Specialize rows for this constructor, including updating argTypes
    const specializedRows = specializeRowsWithTypes(rows, patternIndex, ctorName, ctx, excludeNames, knownConstructors);

    // Update pattern state: write the constructor at the current slot
    const ctorArity = typeInfo.constructorArities.get(ctorName) ?? 0;
    const newState = clonePatternState(patternState);

    // Create the constructor pattern with holes for its arguments
    const ctorArgs: MutablePattern[] = [];
    for (let i = 0; i < ctorArity; i++) {
      ctorArgs.push({ tag: 'Hole' });
    }
    setPatternAt(newState, currentSlot, { tag: 'MCtor', name: ctorName, args: ctorArgs });

    // Update slot refs: create refs for each constructor argument
    const newSlotRefs: SlotRef[] = [];
    for (let i = 0; i < ctorArity; i++) {
      newSlotRefs.push({
        argIndex: currentSlot.argIndex,
        nodePath: [...currentSlot.nodePath, i]
      });
    }

    // Add remaining slots (positions 1, 2, ... from original)
    const updatedSlots = [...newSlotRefs, ...slotRefs.slice(1)];

    // Update index bindings: if we're matching at a top-level position (not nested),
    // this constrains the index at that argument position
    const updatedBindings = new Map(indexBindings);
    if (currentSlot.nodePath.length === 0) {
      // Top-level argument: add binding for this arg position
      // The binding maps the original argument index to the constructor term
      updatedBindings.set(currentSlot.argIndex, constructorToTerm(ctorName, ctorArity));
    }

    // Build subtree for this constructor branch
    const subtree = buildSplitTree(
      specializedRows,
      ctx,
      excludeNames,
      [...currentPath, ctorName],
      updatedSlots,
      newState,
      knownConstructors,
      updatedBindings
    );

    branches.set(ctorName, subtree);
    branchedConstructors.add(ctorName);
  }

  // Build default branch if there are wildcard rows AND there are constructors
  // that we didn't create branches for. This can happen if:
  // 1. A constructor was skipped due to being impossible (isConstructorPossible = false)
  // 2. We have wildcards covering cases we don't enumerate
  //
  // IMPORTANT: If we created branches for ALL constructors, don't create a default
  // branch. The default branch without index bindings would incorrectly allow
  // impossible constructor combinations in dependent types.
  let defaultBranch: SplitTree | undefined;
  const hasUnbranchedConstructors = typeInfo.constructors.some(
    ctor => !branchedConstructors.has(ctor)
  );
  if (wildcardRows.length > 0 && hasUnbranchedConstructors) {
    // Mark this slot as wildcard (covers all constructors in the default branch)
    const newState = clonePatternState(patternState);
    setPatternAt(newState, currentSlot, { tag: 'MWild' });

    const defaultRows = wildcardRows.map(row => ({
      ...row,
      patterns: row.patterns.slice(1),
      argTypes: row.argTypes.slice(1)
    }));
    const advancedSlots = slotRefs.slice(1);
    // Wildcards don't refine indices, so pass bindings unchanged
    defaultBranch = buildSplitTree(defaultRows, ctx, excludeNames, [...currentPath, '_'], advancedSlots, newState, knownConstructors, indexBindings);
  }

  return {
    tag: 'Split',
    argIndex: currentPath.length,  // Use path length as a proxy for argument depth
    branches,
    defaultBranch,
    impossibleBranches: impossibleConstructors.length > 0 ? impossibleConstructors : undefined
  };
}

/**
 * Intermediate result from pattern specialization (before argTypes are updated).
 */
interface SpecializedPatternRow {
  patterns: TPattern[];
  clauseIndex: number;
}

/**
 * Specialize rows for a specific constructor at the given argument position.
 *
 * - Rows with PCtor matching the constructor: include, decompose ctor args
 * - Rows with PVar (including wildcards): include, expand with fresh wildcards for ctor args
 * - Rows with PCtor for different constructor: exclude
 *
 * Returns intermediate rows without argTypes (those are added by specializeRowsWithTypes).
 */
function specializeRows(
  rows: ClauseRow[],
  argIndex: number,
  ctorName: string,
  ctorArity: number
): SpecializedPatternRow[] {
  const result: SpecializedPatternRow[] = [];

  for (const row of rows) {
    const pattern = row.patterns[argIndex];

    if (!pattern) {
      // Shouldn't happen, but handle gracefully
      continue;
    }

    if (pattern.tag === 'PCtor') {
      if (pattern.name === ctorName) {
        // Constructor matches - decompose arguments
        const newPatterns = [
          ...row.patterns.slice(0, argIndex),
          ...pattern.args,
          ...row.patterns.slice(argIndex + 1)
        ];
        result.push({
          patterns: newPatterns,
          clauseIndex: row.clauseIndex
        });
      }
      // Different constructor - row doesn't match, exclude it
    } else {
      // PVar (including wildcards) - matches any constructor
      // Expand with fresh wildcards for constructor arguments
      const wildcards: TPattern[] = Array.from({ length: ctorArity }, () => freshWildcardPattern());
      const newPatterns = [
        ...row.patterns.slice(0, argIndex),
        ...wildcards,
        ...row.patterns.slice(argIndex + 1)
      ];
      result.push({
        patterns: newPatterns,
        clauseIndex: row.clauseIndex
      });
    }
  }

  return result;
}

/**
 * Specialize rows for a specific constructor, also updating argTypes.
 *
 * This wraps specializeRows and additionally updates the argTypes array
 * to reflect the decomposed constructor arguments with their proper types.
 */
function specializeRowsWithTypes(
  rows: ClauseRow[],
  argIndex: number,
  ctorName: string,
  ctx: TTKContext,
  excludeNames: Set<string>,
  knownConstructors?: Set<string>
): ClauseRow[] {
  // Get constructor arity from the first row's type info
  const typeInfo = rows[0]?.argTypes[argIndex];
  const ctorArity = typeInfo?.constructorArities.get(ctorName) ?? 0;

  // Look up the constructor type to get proper argument types
  const ctorType = lookupTypeByName(ctx, ctorName);
  const ctorArgTypeInfos = ctorType
    ? extractCtorArgTypeInfos(ctorType, ctx, excludeNames, knownConstructors)
    : Array(ctorArity).fill({
        typeName: null,
        constructors: [],
        constructorArities: new Map()
      });

  // Use base specializeRows for pattern handling
  const specializedPatterns = specializeRows(rows, argIndex, ctorName, ctorArity);

  // Now we need to update argTypes as well
  // For each specialized row, update its argTypes
  const result: ClauseRow[] = [];

  for (let i = 0; i < specializedPatterns.length; i++) {
    const specRow = specializedPatterns[i];

    // Find the original row that this came from
    const origRow = rows.find(r => r.clauseIndex === specRow.clauseIndex);
    if (!origRow) continue;

    // Build new argTypes:
    // - Remove the argType at argIndex
    // - Insert the constructor's argument types
    const newArgTypes = [
      ...origRow.argTypes.slice(0, argIndex),
      ...ctorArgTypeInfos,
      ...origRow.argTypes.slice(argIndex + 1)
    ];

    result.push({
      patterns: specRow.patterns,
      argTypes: newArgTypes,
      clauseIndex: specRow.clauseIndex
    });
  }

  return result;
}

/**
 * Extract ArgTypeInfo for each argument of a constructor type.
 *
 * For `Succ : Nat -> Nat`, returns [ArgTypeInfo for Nat].
 * For `Cons : (A : Type) -> A -> List A -> List A`,
 * returns [ArgTypeInfo for Type, ArgTypeInfo for A, ArgTypeInfo for List A].
 */
function extractCtorArgTypeInfos(
  ctorType: TTKTerm,
  ctx: TTKContext,
  excludeNames: Set<string>,
  knownConstructors?: Set<string>
): ArgTypeInfo[] {
  const argTypeInfos: ArgTypeInfo[] = [];
  let current = ctorType;

  while (current.tag === 'Binder' && current.binderKind.tag === 'BPi') {
    // Get type info for this argument
    const argTypeInfo = getArgTypeInfo(current.domain, ctx, excludeNames, knownConstructors);
    argTypeInfos.push(argTypeInfo);
    current = current.body;
  }

  return argTypeInfos;
}

// ============================================================================
// Missing Case Detection
// ============================================================================

/**
 * Find all missing cases in a splitting tree.
 * Returns structured patterns for each missing case.
 */
function findMissingCases(tree: SplitTree): MissingPattern[][] {
  const missing: MissingPattern[][] = [];
  collectMissingCasesFromTree(tree, missing);
  return missing;
}

/**
 * Collect all clause indices that appear in the tree (as Leaf nodes).
 */
function collectReachableClauseIndices(tree: SplitTree): Set<number> {
  const indices = new Set<number>();
  collectReachableClauseIndicesFromTree(tree, indices);
  return indices;
}

/**
 * Recursively collect clause indices from the tree.
 */
function collectReachableClauseIndicesFromTree(tree: SplitTree, result: Set<number>): void {
  switch (tree.tag) {
    case 'Leaf':
      result.add(tree.clauseIndex);
      break;
    case 'Missing':
      // No clause matched here
      break;
    case 'Split':
      for (const [_ctorName, subtree] of tree.branches) {
        collectReachableClauseIndicesFromTree(subtree, result);
      }
      if (tree.defaultBranch) {
        collectReachableClauseIndicesFromTree(tree.defaultBranch, result);
      }
      break;
  }
}

/**
 * Recursively collect missing cases from the tree.
 */
function collectMissingCasesFromTree(
  tree: SplitTree,
  result: MissingPattern[][]
): void {
  switch (tree.tag) {
    case 'Leaf':
      // This case is covered
      break;

    case 'Missing':
      // Found an uncovered case - use the patterns stored in the node
      result.push(tree.patterns);
      break;

    case 'Split':
      // Recurse into each branch
      for (const [_ctorName, subtree] of tree.branches) {
        collectMissingCasesFromTree(subtree, result);
      }
      // Also check default branch if present
      if (tree.defaultBranch) {
        collectMissingCasesFromTree(tree.defaultBranch, result);
      }
      break;
  }
}

// ============================================================================
// High-Level API for Integration
// ============================================================================

/**
 * Check totality for a function definition with pattern matching.
 *
 * This is the main entry point called from tt-typecheck-decl.ts.
 *
 * @param functionName - The name of the function being defined (to exclude from constructor lookup)
 * @param functionType - The type of the function being defined
 * @param clauses - The pattern matching clauses
 * @param ctx - Typing context
 * @param knownConstructors - Set of names that are known to be constructors (optional but recommended)
 * @returns Totality analysis result
 */
export function checkFunctionTotality(
  functionName: string,
  functionType: TTKTerm,
  clauses: TTKClause[],
  ctx: TTKContext,
  knownConstructors?: Set<string>
): TotalityAnalysis {
  // Extract argument types from the function type
  const argTypes = extractArgTypes(functionType, clauses.length > 0 ? clauses[0].patterns.length : 0);

  // Exclude the function itself from constructor lookup
  // (it's in the context for recursive calls, but it's not a constructor)
  const excludeNames = new Set([functionName]);

  return analyzeTotality(clauses, argTypes, ctx, excludeNames, knownConstructors);
}

/**
 * Extract argument types from a function type.
 * For `(A : Type) -> A -> Nat -> Bool`, returns [Type, A, Nat].
 */
function extractArgTypes(type: TTKTerm, numArgs: number): TTKTerm[] {
  const argTypes: TTKTerm[] = [];
  let current = type;

  for (let i = 0; i < numArgs; i++) {
    if (current.tag === 'Binder' && current.binderKind.tag === 'BPi') {
      argTypes.push(current.domain);
      current = current.body;
    } else {
      break;
    }
  }

  return argTypes;
}

// ============================================================================
// Formatting Utilities
// ============================================================================

/**
 * Format a missing case as a human-readable string.
 *
 * @param functionName - The function name to include (e.g., "plus")
 * @param patterns - The missing patterns for each argument
 * @returns A string like "plus (Succ _) (Succ Zero)"
 */
export function formatMissingCase(functionName: string, patterns: MissingPattern[]): string {
  const formattedPatterns = patterns.map(p => formatMissingPattern(p));
  return `${functionName} ${formattedPatterns.join(' ')}`;
}

/**
 * Format a single missing pattern.
 */
function formatMissingPattern(pattern: MissingPattern): string {
  switch (pattern.tag) {
    case 'MWild':
      return '_';
    case 'MCtor':
      if (pattern.args.length === 0) {
        return pattern.name;
      }
      const argsStr = pattern.args.map(a => formatMissingPattern(a)).join(' ');
      return `(${pattern.name} ${argsStr})`;
  }
}

// ============================================================================
// Debug Utilities
// ============================================================================

/**
 * Pretty-print a splitting tree for debugging.
 */
export function prettyPrintSplitTree(tree: SplitTree, indent: string = ''): string {
  switch (tree.tag) {
    case 'Leaf':
      return `${indent}Leaf(clause=${tree.clauseIndex})`;

    case 'Missing':
      return `${indent}MISSING: ${tree.path.join(' -> ') || '<root>'}`;

    case 'Split': {
      const lines = [`${indent}Split(arg=${tree.argIndex})`];
      for (const [ctorName, subtree] of tree.branches) {
        lines.push(`${indent}  ${ctorName}:`);
        lines.push(prettyPrintSplitTree(subtree, indent + '    '));
      }
      if (tree.defaultBranch) {
        lines.push(`${indent}  _:`);
        lines.push(prettyPrintSplitTree(tree.defaultBranch, indent + '    '));
      }
      return lines.join('\n');
    }
  }
}
