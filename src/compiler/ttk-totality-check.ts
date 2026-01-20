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
 * `PVar` and `PWild` patterns match ANY constructor. When building the tree:
 * - They apply to all constructors not explicitly matched by a `PCtor`
 * - This creates "default" coverage that can fill in missing branches
 *
 * IMPORTANT: This operates on TTKTerm (kernel terms), following the project convention
 * that all verification happens in the kernel layer.
 */

import { TTKTerm, TTKClause, TTKPattern, mkType } from './kernel';
import { DefinitionsMap, InductiveDefinition, countPiBinders } from './term';

// ============================================================================
// Types
// ============================================================================

/**
 * Check if a pattern is a wildcard or variable pattern (matches anything).
 */
function isWildcardOrVar(pattern: TTKPattern | undefined): boolean {
  return pattern !== undefined && (pattern.tag === 'PVar' || pattern.tag === 'PWild');
}

/** Counter for generating fresh wildcard names during totality checking */
let wildcardCounter = 0;

/** Generate a fresh wildcard pattern */
function freshWildcardPattern(): TTKPattern {
  return { tag: 'PWild', name: `_tc${wildcardCounter++}` };
}

/** Reset wildcard counter (useful for testing) */
export function resetTotalityWildcardCounter(): void {
  wildcardCounter = 0;
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
  patterns: TTKPattern[];
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
 */
type IndexBindings = Map<number, TTKTerm>;

/**
 * Tracks the pattern being built for each original argument.
 */
interface PatternBuildState {
  /** Pattern being built for each original argument */
  patterns: MutablePattern[];
}

/**
 * A mutable pattern node that can be filled in as we traverse.
 */
type MutablePattern =
  | { tag: 'Hole' }
  | { tag: 'MWild' }
  | { tag: 'MCtor'; name: string; args: MutablePattern[] };

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
 * @param definitions - The definitions map (contains constructor information)
 * @param excludeNames - Names to exclude from constructor lookup (e.g., the function being checked)
 * @returns Analysis result with exhaustiveness status and missing cases
 */
export function analyzeTotality(
  clauses: TTKClause[],
  argTypes: TTKTerm[],
  definitions: DefinitionsMap,
  excludeNames: Set<string> = new Set()
): TotalityAnalysis {
  if (clauses.length === 0) {
    // No clauses means completely missing coverage
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
  const argTypeInfos = argTypes.map(type => getArgTypeInfo(type, definitions, excludeNames));

  // Convert clauses to internal row representation
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
  const splitTree = buildSplitTree(rows, definitions, excludeNames, [], initialSlotRefs, initialState, new Map());

  // Find all missing cases
  const missingCases = findMissingCases(splitTree);

  // Find inaccessible clauses
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
 */
function getArgTypeInfo(
  type: TTKTerm,
  definitions: DefinitionsMap,
  excludeNames: Set<string> = new Set()
): ArgTypeInfo {
  const typeName = getHeadConstName(type);

  if (!typeName) {
    return {
      typeName: null,
      fullType: null,
      constructors: [],
      constructorArities: new Map()
    };
  }

  // Find the inductive definition
  const inductiveDef = definitions.inductiveTypes.get(typeName);
  if (!inductiveDef) {
    return {
      typeName,
      fullType: type,
      constructors: [],
      constructorArities: new Map()
    };
  }

  // Get constructors from the inductive definition
  const constructors: string[] = [];
  const constructorArities = new Map<string, number>();

  for (const ctor of inductiveDef.constructors) {
    if (!excludeNames.has(ctor.name)) {
      constructors.push(ctor.name);
      constructorArities.set(ctor.name, countPiBinders(ctor.type));
    }
  }

  return {
    typeName,
    fullType: type,
    constructors,
    constructorArities
  };
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
 * Extract type indices (arguments) from an applied type.
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
 * Look up a constructor type from definitions.
 */
function lookupConstructorType(definitions: DefinitionsMap, ctorName: string): TTKTerm | null {
  for (const inductiveDef of definitions.inductiveTypes.values()) {
    for (const ctor of inductiveDef.constructors) {
      if (ctor.name === ctorName) {
        return ctor.type;
      }
    }
  }
  return null;
}

/**
 * Check if a constructor is possible given an expected type.
 *
 * For indexed inductive types, a constructor may be impossible if its
 * return type indices have a DEFINITE conflict with the expected indices.
 *
 * We use a conservative check: only rule out a constructor if there's a
 * head symbol conflict (e.g., Zero vs Succ). If either side has a variable
 * at the head, we assume the constructor could be possible.
 */
function isConstructorPossible(
  ctorType: TTKTerm,
  expectedType: TTKTerm,
  _definitions: DefinitionsMap
): boolean {
  const ctorReturnType = getReturnType(ctorType);
  const ctorIndices = extractTypeIndices(ctorReturnType);
  const expectedIndices = extractTypeIndices(expectedType);

  if (ctorIndices.length !== expectedIndices.length) {
    return true;
  }

  for (let i = 0; i < ctorIndices.length; i++) {
    const ctorIdx = ctorIndices[i];
    const expIdx = expectedIndices[i];

    // Check for definite head conflicts only
    // If either side has a variable, we can't rule out the constructor
    if (hasDefiniteConflict(ctorIdx, expIdx)) {
      return false;
    }
  }

  return true;
}

/**
 * Check if two terms have a definite head symbol conflict.
 * Returns true only if both terms have concrete heads that differ.
 * If either term is or starts with a variable, returns false (no definite conflict).
 */
function hasDefiniteConflict(t1: TTKTerm, t2: TTKTerm): boolean {
  // Peel off applications to get to the head
  let h1 = t1;
  let h2 = t2;
  const args1: TTKTerm[] = [];
  const args2: TTKTerm[] = [];

  while (h1.tag === 'App') {
    args1.unshift(h1.arg);
    h1 = h1.fn;
  }
  while (h2.tag === 'App') {
    args2.unshift(h2.arg);
    h2 = h2.fn;
  }

  // If either head is a variable, no definite conflict
  if (h1.tag === 'Var' || h2.tag === 'Var') {
    return false;
  }

  // If either head is a meta/hole, no definite conflict
  if (h1.tag === 'Meta' || h2.tag === 'Meta' || h1.tag === 'Hole' || h2.tag === 'Hole') {
    return false;
  }

  // If heads are different constants, definite conflict
  if (h1.tag === 'Const' && h2.tag === 'Const') {
    if (h1.name !== h2.name) {
      return true;
    }
    // Same constant head - check arguments recursively
    if (args1.length !== args2.length) {
      return false; // Shouldn't happen, but be safe
    }
    for (let i = 0; i < args1.length; i++) {
      if (hasDefiniteConflict(args1[i], args2[i])) {
        return true;
      }
    }
    return false;
  }

  // Different head types but not both Const - no definite conflict
  return false;
}

// ============================================================================
// Term Manipulation
// ============================================================================

/**
 * Apply index bindings to a type term.
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
      const dbIndex = type.index;
      if (dbIndex < depth) {
        return type;
      }

      const adjustedDbIndex = dbIndex - depth;
      const argPosition = (contextSize - 1) - adjustedDbIndex;

      const binding = bindings.get(argPosition);
      if (binding) {
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
    case 'Meta':
    case 'Annot':
    case 'Match':
      return type;
  }
}

/**
 * Shift all free variables in a term by a given amount.
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
    case 'Meta':
    case 'Annot':
    case 'Match':
      return term;
  }
}

/**
 * Convert a constructor name to a term for index binding.
 */
function constructorToTerm(ctorName: string, arity: number): TTKTerm {
  let result: TTKTerm = { tag: 'Const', name: ctorName };
  for (let i = 0; i < arity; i++) {
    result = {
      tag: 'App',
      fn: result,
      arg: { tag: 'Var', index: i }
    };
  }
  return result;
}

// ============================================================================
// Pattern State Manipulation
// ============================================================================

/**
 * Deep clone a pattern state.
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
 */
function setPatternAt(state: PatternBuildState, slot: SlotRef, pattern: MutablePattern): void {
  if (slot.nodePath.length === 0) {
    state.patterns[slot.argIndex] = pattern;
  } else {
    let current = state.patterns[slot.argIndex];
    for (let i = 0; i < slot.nodePath.length - 1; i++) {
      if (current.tag === 'MCtor') {
        current = current.args[slot.nodePath[i]];
      } else {
        return;
      }
    }
    if (current.tag === 'MCtor') {
      const lastIndex = slot.nodePath[slot.nodePath.length - 1];
      current.args[lastIndex] = pattern;
    }
  }
}

/**
 * Convert mutable patterns to final MissingPatterns.
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
 */
function buildSplitTree(
  rows: ClauseRow[],
  definitions: DefinitionsMap,
  excludeNames: Set<string>,
  currentPath: string[],
  slotRefs: SlotRef[],
  patternState: PatternBuildState,
  indexBindings: IndexBindings
): SplitTree {
  // Base case: no rows means uncovered
  if (rows.length === 0) {
    const patterns = finalizePatterns(patternState);
    return { tag: 'Missing', path: currentPath, patterns };
  }

  // Base case: no more patterns to match in first row
  if (rows[0].patterns.length === 0) {
    return { tag: 'Leaf', clauseIndex: rows[0].clauseIndex };
  }

  // Safety check: slotRefs should match patterns
  if (slotRefs.length === 0) {
    // No more slots but still have patterns - treat remaining patterns as matched
    return { tag: 'Leaf', clauseIndex: rows[0].clauseIndex };
  }

  const patternIndex = 0;

  // Check if first row has a wildcard/var at current position
  const firstPattern = rows[0].patterns[patternIndex];
  if (isWildcardOrVar(firstPattern)) {
    const allWildcards = rows.every(row => {
      const pat = row.patterns[patternIndex];
      return isWildcardOrVar(pat);
    });

    if (allWildcards) {
      const currentSlot = slotRefs[0];
      const newState = clonePatternState(patternState);
      setPatternAt(newState, currentSlot, { tag: 'MWild' });

      const advancedRows = rows.map(row => ({
        ...row,
        patterns: row.patterns.slice(1),
        argTypes: row.argTypes.slice(1)
      }));
      const advancedSlots = slotRefs.slice(1);
      return buildSplitTree(advancedRows, definitions, excludeNames, currentPath, advancedSlots, newState, indexBindings);
    }
  }

  // Get type info from first row
  const typeInfo = rows[0].argTypes[0];

  // If no constructors, skip this position (treat as wildcard)
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
    return buildSplitTree(advancedRows, definitions, excludeNames, currentPath, advancedSlots, newState, indexBindings);
  }

  // Build branches for each constructor
  const branches = new Map<string, SplitTree>();

  // Collect wildcard rows
  const wildcardRows = rows.filter(row => {
    const pat = row.patterns[patternIndex];
    return isWildcardOrVar(pat);
  });

  // Track which constructors are branched
  const branchedConstructors = new Set<string>();
  const impossibleConstructors: string[] = [];
  const currentSlot = slotRefs[0];

  for (const ctorName of typeInfo.constructors) {
    // Check if constructor is possible
    // Note: We use the fullType directly without applying index bindings, because
    // the index bindings mechanism doesn't correctly handle dependent type scoping
    // (de Bruijn indices vs pattern argument positions are different).
    // The hasDefiniteConflict function is conservative and only rejects constructors
    // when there's a clear head symbol conflict.
    if (typeInfo.fullType) {
      const ctorType = lookupConstructorType(definitions, ctorName);

      if (ctorType && !isConstructorPossible(ctorType, typeInfo.fullType, definitions)) {
        impossibleConstructors.push(ctorName);
        continue;
      }
    }

    // Specialize rows for this constructor
    const specializedRows = specializeRowsWithTypes(rows, patternIndex, ctorName, definitions, excludeNames);

    // Update pattern state
    const ctorArity = typeInfo.constructorArities.get(ctorName) ?? 0;
    const newState = clonePatternState(patternState);

    const ctorArgs: MutablePattern[] = [];
    for (let i = 0; i < ctorArity; i++) {
      ctorArgs.push({ tag: 'Hole' });
    }
    setPatternAt(newState, currentSlot, { tag: 'MCtor', name: ctorName, args: ctorArgs });

    // Update slot refs
    const newSlotRefs: SlotRef[] = [];
    for (let i = 0; i < ctorArity; i++) {
      newSlotRefs.push({
        argIndex: currentSlot.argIndex,
        nodePath: [...currentSlot.nodePath, i]
      });
    }
    const updatedSlots = [...newSlotRefs, ...slotRefs.slice(1)];

    // Update index bindings
    const updatedBindings = new Map(indexBindings);
    if (currentSlot.nodePath.length === 0) {
      updatedBindings.set(currentSlot.argIndex, constructorToTerm(ctorName, ctorArity));
    }

    // Build subtree
    const subtree = buildSplitTree(
      specializedRows,
      definitions,
      excludeNames,
      [...currentPath, ctorName],
      updatedSlots,
      newState,
      updatedBindings
    );

    branches.set(ctorName, subtree);
    branchedConstructors.add(ctorName);
  }

  // Build default branch if needed
  let defaultBranch: SplitTree | undefined;
  const hasUnbranchedConstructors = typeInfo.constructors.some(
    ctor => !branchedConstructors.has(ctor)
  );
  if (wildcardRows.length > 0 && hasUnbranchedConstructors) {
    const newState = clonePatternState(patternState);
    setPatternAt(newState, currentSlot, { tag: 'MWild' });

    const defaultRows = wildcardRows.map(row => ({
      ...row,
      patterns: row.patterns.slice(1),
      argTypes: row.argTypes.slice(1)
    }));
    const advancedSlots = slotRefs.slice(1);
    defaultBranch = buildSplitTree(defaultRows, definitions, excludeNames, [...currentPath, '_'], advancedSlots, newState, indexBindings);
  }

  return {
    tag: 'Split',
    argIndex: currentPath.length,
    branches,
    defaultBranch,
    impossibleBranches: impossibleConstructors.length > 0 ? impossibleConstructors : undefined
  };
}

/**
 * Specialize rows for a specific constructor.
 */
function specializeRows(
  rows: ClauseRow[],
  argIndex: number,
  ctorName: string,
  ctorArity: number
): { patterns: TTKPattern[]; clauseIndex: number }[] {
  const result: { patterns: TTKPattern[]; clauseIndex: number }[] = [];

  for (const row of rows) {
    const pattern = row.patterns[argIndex];

    if (!pattern) {
      continue;
    }

    if (pattern.tag === 'PCtor') {
      if (pattern.name === ctorName) {
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
    } else {
      // PVar or PWild - matches any constructor
      const wildcards: TTKPattern[] = Array.from({ length: ctorArity }, () => freshWildcardPattern());
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
 * Specialize rows with type information.
 */
function specializeRowsWithTypes(
  rows: ClauseRow[],
  argIndex: number,
  ctorName: string,
  definitions: DefinitionsMap,
  excludeNames: Set<string>
): ClauseRow[] {
  const typeInfo = rows[0]?.argTypes[argIndex];
  const ctorArity = typeInfo?.constructorArities.get(ctorName) ?? 0;

  const ctorType = lookupConstructorType(definitions, ctorName);
  const ctorArgTypeInfos = ctorType
    ? extractCtorArgTypeInfos(ctorType, definitions, excludeNames)
    : Array(ctorArity).fill({
        typeName: null,
        fullType: null,
        constructors: [],
        constructorArities: new Map()
      });

  const specializedPatterns = specializeRows(rows, argIndex, ctorName, ctorArity);

  const result: ClauseRow[] = [];

  for (const specRow of specializedPatterns) {
    const origRow = rows.find(r => r.clauseIndex === specRow.clauseIndex);
    if (!origRow) continue;

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
 */
function extractCtorArgTypeInfos(
  ctorType: TTKTerm,
  definitions: DefinitionsMap,
  excludeNames: Set<string>
): ArgTypeInfo[] {
  const argTypeInfos: ArgTypeInfo[] = [];
  let current = ctorType;

  while (current.tag === 'Binder' && current.binderKind.tag === 'BPi') {
    const argTypeInfo = getArgTypeInfo(current.domain, definitions, excludeNames);
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
 */
function findMissingCases(tree: SplitTree): MissingPattern[][] {
  const missing: MissingPattern[][] = [];
  collectMissingCasesFromTree(tree, missing);
  return missing;
}

/**
 * Collect all clause indices that appear in the tree.
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
      break;

    case 'Missing':
      result.push(tree.patterns);
      break;

    case 'Split':
      for (const [_ctorName, subtree] of tree.branches) {
        collectMissingCasesFromTree(subtree, result);
      }
      if (tree.defaultBranch) {
        collectMissingCasesFromTree(tree.defaultBranch, result);
      }
      break;
  }
}

// ============================================================================
// High-Level API
// ============================================================================

/**
 * Check totality for a function definition with pattern matching.
 *
 * @param functionName - The name of the function being defined
 * @param functionType - The type of the function being defined
 * @param clauses - The pattern matching clauses
 * @param definitions - The definitions map
 * @returns Totality analysis result
 */
export function checkFunctionTotality(
  functionName: string,
  functionType: TTKTerm,
  clauses: TTKClause[],
  definitions: DefinitionsMap
): TotalityAnalysis {
  const argTypes = extractArgTypes(functionType, clauses.length > 0 ? clauses[0].patterns.length : 0);
  const excludeNames = new Set([functionName]);
  return analyzeTotality(clauses, argTypes, definitions, excludeNames);
}

/**
 * Extract argument types from a function type.
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
