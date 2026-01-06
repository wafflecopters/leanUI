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
 * `PWild` and `PVar` patterns match ANY constructor. When building the tree:
 * - They apply to all constructors not explicitly matched by a `PCtor`
 * - This creates "default" coverage that can fill in missing branches
 *
 * IMPORTANT: This operates on TTKTerm (kernel terms), following the project convention
 * that all verification happens in the kernel layer.
 */

import { TTKTerm, TTKContext, TTKClause } from './tt-kernel';
import { TPattern } from './tt-core';

// ============================================================================
// Types
// ============================================================================

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
  /** Path of constructor names leading to this missing case */
  path: string[];
}

/**
 * Result of totality analysis.
 */
export interface TotalityAnalysis {
  /** Whether the pattern matching is exhaustive */
  exhaustive: boolean;
  /** List of missing cases (paths of constructor names) */
  missingCases: string[][];
  /** The splitting tree (for debugging/visualization) */
  splitTree: SplitTree;
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
 * Information about an argument position's type.
 */
interface ArgTypeInfo {
  /** Name of the inductive type (e.g., "Nat", "Bool") */
  typeName: string | null;
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
 * @returns Analysis result with exhaustiveness status and missing cases
 */
export function analyzeTotality(
  clauses: TTKClause[],
  argTypes: TTKTerm[],
  ctx: TTKContext,
  excludeNames: Set<string> = new Set()
): TotalityAnalysis {
  if (clauses.length === 0) {
    // No clauses means completely missing coverage
    return {
      exhaustive: false,
      missingCases: [['<all cases>']],
      splitTree: { tag: 'Missing', path: [] }
    };
  }

  if (argTypes.length === 0) {
    // No arguments, so the first clause covers everything
    return {
      exhaustive: true,
      missingCases: [],
      splitTree: { tag: 'Leaf', clauseIndex: 0 }
    };
  }

  // Build type info for each argument position
  const argTypeInfos = argTypes.map(type => getArgTypeInfo(type, ctx, excludeNames));

  // Convert clauses to internal row representation
  // Each row carries its own copy of argTypeInfos (they may diverge during specialization)
  const rows: ClauseRow[] = clauses.map((clause, index) => ({
    patterns: clause.patterns,
    argTypes: argTypeInfos,
    clauseIndex: index
  }));

  // Build the splitting tree
  const splitTree = buildSplitTree(rows, ctx, excludeNames, []);

  // Find all missing cases
  const missingCases = findMissingCases(splitTree);

  return {
    exhaustive: missingCases.length === 0,
    missingCases,
    splitTree
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
 */
function getArgTypeInfo(
  type: TTKTerm,
  ctx: TTKContext,
  excludeNames: Set<string> = new Set()
): ArgTypeInfo {
  const typeName = getHeadConstName(type);

  if (!typeName) {
    // Not an inductive type (e.g., function type, Sort)
    return {
      typeName: null,
      constructors: [],
      constructorArities: new Map()
    };
  }

  // Find all constructors for this type
  const constructors = getConstructorsForType(typeName, ctx, excludeNames);
  const constructorArities = new Map<string, number>();

  for (const ctorName of constructors) {
    const ctorType = lookupTypeByName(ctx, ctorName);
    if (ctorType) {
      constructorArities.set(ctorName, countCtorArgs(ctorType, typeName));
    }
  }

  return {
    typeName,
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
 * Find all constructors for a given inductive type by scanning the context.
 * A binding is a constructor for type T if its return type has T as the head.
 *
 * @param typeName - The name of the inductive type
 * @param ctx - The typing context
 * @param excludeNames - Names to exclude (e.g., the function being type-checked)
 */
export function getConstructorsForType(
  typeName: string,
  ctx: TTKContext,
  excludeNames: Set<string> = new Set()
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
      constructors.push(binding.name);
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
 * @param currentPath - Path of constructor names to this point
 */
function buildSplitTree(
  rows: ClauseRow[],
  ctx: TTKContext,
  excludeNames: Set<string>,
  currentPath: string[]
): SplitTree {
  // Base case: no rows means uncovered
  if (rows.length === 0) {
    return { tag: 'Missing', path: currentPath };
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
  if (firstPattern && (firstPattern.tag === 'PWild' || firstPattern.tag === 'PVar')) {
    // Check if ALL patterns at this position are wildcards/vars
    const allWildcards = rows.every(row => {
      const pat = row.patterns[patternIndex];
      return pat && (pat.tag === 'PWild' || pat.tag === 'PVar');
    });

    if (allWildcards) {
      // Remove the first pattern and argType from all rows and continue
      const advancedRows = rows.map(row => ({
        ...row,
        patterns: row.patterns.slice(1),
        argTypes: row.argTypes.slice(1)
      }));
      return buildSplitTree(advancedRows, ctx, excludeNames, currentPath);
    }
  }

  // Get type info from first row (all rows should have same type at position 0)
  const typeInfo = rows[0].argTypes[0];

  // If no constructors (non-inductive type), skip this position
  if (!typeInfo || typeInfo.constructors.length === 0) {
    const advancedRows = rows.map(row => ({
      ...row,
      patterns: row.patterns.slice(1),
      argTypes: row.argTypes.slice(1)
    }));
    return buildSplitTree(advancedRows, ctx, excludeNames, currentPath);
  }

  // Build branches for each constructor
  const branches = new Map<string, SplitTree>();

  // Collect rows that have wildcards/vars at this position (they match all constructors)
  const wildcardRows = rows.filter(row => {
    const pat = row.patterns[patternIndex];
    return pat && (pat.tag === 'PWild' || pat.tag === 'PVar');
  });

  for (const ctorName of typeInfo.constructors) {
    // Specialize rows for this constructor, including updating argTypes
    const specializedRows = specializeRowsWithTypes(rows, patternIndex, ctorName, ctx, excludeNames);

    // Build subtree for this constructor branch
    const subtree = buildSplitTree(
      specializedRows,
      ctx,
      excludeNames,
      [...currentPath, ctorName]
    );

    branches.set(ctorName, subtree);
  }

  // Build default branch if there are wildcard rows
  let defaultBranch: SplitTree | undefined;
  if (wildcardRows.length > 0) {
    // Remove the first pattern and argType from wildcard rows and continue
    const defaultRows = wildcardRows.map(row => ({
      ...row,
      patterns: row.patterns.slice(1),
      argTypes: row.argTypes.slice(1)
    }));
    defaultBranch = buildSplitTree(defaultRows, ctx, excludeNames, [...currentPath, '_']);
  }

  return {
    tag: 'Split',
    argIndex: currentPath.length,  // Use path length as a proxy for argument depth
    branches,
    defaultBranch
  };
}

/**
 * Specialize rows for a specific constructor at the given argument position.
 *
 * - Rows with PCtor matching the constructor: include, decompose ctor args
 * - Rows with PWild/PVar: include, expand with wildcards for ctor args
 * - Rows with PCtor for different constructor: exclude
 */
function specializeRows(
  rows: ClauseRow[],
  argIndex: number,
  ctorName: string,
  ctorArity: number
): ClauseRow[] {
  const result: ClauseRow[] = [];

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
      // PWild or PVar - matches any constructor
      // Expand with wildcards for constructor arguments
      const wildcards: TPattern[] = Array(ctorArity).fill({ tag: 'PWild' });
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
  excludeNames: Set<string>
): ClauseRow[] {
  // Get constructor arity from the first row's type info
  const typeInfo = rows[0]?.argTypes[argIndex];
  const ctorArity = typeInfo?.constructorArities.get(ctorName) ?? 0;

  // Look up the constructor type to get proper argument types
  const ctorType = lookupTypeByName(ctx, ctorName);
  const ctorArgTypeInfos = ctorType
    ? extractCtorArgTypeInfos(ctorType, ctx, excludeNames)
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
  excludeNames: Set<string>
): ArgTypeInfo[] {
  const argTypeInfos: ArgTypeInfo[] = [];
  let current = ctorType;

  while (current.tag === 'Binder' && current.binderKind.tag === 'BPi') {
    // Get type info for this argument
    const argTypeInfo = getArgTypeInfo(current.domain, ctx, excludeNames);
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
 * Returns paths of constructor names leading to Missing nodes.
 */
function findMissingCases(tree: SplitTree): string[][] {
  const missing: string[][] = [];
  collectMissingCases(tree, [], missing);
  return missing;
}

/**
 * Recursively collect missing cases.
 */
function collectMissingCases(
  tree: SplitTree,
  currentPath: string[],
  result: string[][]
): void {
  switch (tree.tag) {
    case 'Leaf':
      // This case is covered
      break;

    case 'Missing':
      // Found an uncovered case
      result.push(tree.path.length > 0 ? tree.path : currentPath);
      break;

    case 'Split':
      // Recurse into each branch
      for (const [ctorName, subtree] of tree.branches) {
        collectMissingCases(subtree, [...currentPath, ctorName], result);
      }
      // Also check default branch if present
      if (tree.defaultBranch) {
        collectMissingCases(tree.defaultBranch, [...currentPath, '_'], result);
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
 * @returns Totality analysis result
 */
export function checkFunctionTotality(
  functionName: string,
  functionType: TTKTerm,
  clauses: TTKClause[],
  ctx: TTKContext
): TotalityAnalysis {
  // Extract argument types from the function type
  const argTypes = extractArgTypes(functionType, clauses.length > 0 ? clauses[0].patterns.length : 0);

  // Exclude the function itself from constructor lookup
  // (it's in the context for recursive calls, but it's not a constructor)
  const excludeNames = new Set([functionName]);

  return analyzeTotality(clauses, argTypes, ctx, excludeNames);
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
