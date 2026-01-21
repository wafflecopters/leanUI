/**
 * Totality Checker - Case Tree Construction and Coverage Analysis
 *
 * This module builds a case tree from elaborated pattern clauses to detect:
 * - Missing patterns (inputs no clause handles)
 * - Unreachable clauses (clauses that can never match)
 *
 * The algorithm enumerates ALL constructors at each split point.
 * Wildcards/variables are "specialized" to match each constructor.
 */

import { TTKPattern } from './kernel';
import { DefinitionsMap } from './term';

// ============================================================================
// Case Tree Types
// ============================================================================

/**
 * A case tree represents the decision structure of pattern matching.
 *
 * - Leaf: A clause has been matched (clauseIndex identifies which one)
 * - Split: We're splitting on a type; branches contains ALL constructors of that type
 * - Uncovered: This path has no clause that handles it (missing pattern)
 */
export type CaseTree =
  | { tag: 'Leaf'; clauseIndex: number }
  | { tag: 'Split'; typeName: string; branches: Map<string, CaseTree> }
  | { tag: 'Uncovered' };

/**
 * Result of totality checking
 */
export interface TotalityResult {
  /** The case tree representing the pattern matching structure */
  caseTree: CaseTree | null;
  /** Indices of clauses that are unreachable (covered by earlier clauses) */
  unreachableClauses: number[];
  /** Whether the patterns are exhaustive (no uncovered cases) */
  isExhaustive: boolean;
}

/**
 * Information about an inductive type's constructors
 */
export interface TypeInfo {
  constructors: string[];
  arities: Map<string, number>;
}

/**
 * Maps type names to their constructor info
 */
export type TypeInfoMap = Map<string, TypeInfo>;

/**
 * Maps constructor names to their parent type
 */
export type ConstructorToTypeMap = Map<string, string>;

/**
 * Build type info maps from definitions
 */
export function buildTypeInfoMaps(definitions: DefinitionsMap): { typeInfo: TypeInfoMap; ctorToType: ConstructorToTypeMap } {
  const typeInfo: TypeInfoMap = new Map();
  const ctorToType: ConstructorToTypeMap = new Map();

  for (const [typeName, inductiveDef] of definitions.inductiveTypes) {
    const constructors: string[] = [];
    const arities = new Map<string, number>();

    for (const ctor of inductiveDef.constructors) {
      constructors.push(ctor.name);
      // Count arity by counting Pi binders in constructor type
      arities.set(ctor.name, countConstructorArity(ctor.type));
      ctorToType.set(ctor.name, typeName);
    }

    typeInfo.set(typeName, { constructors, arities });
  }

  return { typeInfo, ctorToType };
}

/**
 * Count the arity of a constructor (number of arguments it takes)
 */
function countConstructorArity(type: import('./kernel').TTKTerm): number {
  let count = 0;
  let current = type;
  while (current.tag === 'Binder' && current.binderKind.tag === 'BPi') {
    count++;
    current = current.body;
  }
  return count;
}

// ============================================================================
// Internal Clause Representation
// ============================================================================

interface InternalClause {
  patterns: TTKPattern[];
  clauseIndex: number;
}

// ============================================================================
// Building the Case Tree
// ============================================================================

/**
 * Build a case tree from clauses.
 *
 * @param clauses The clauses with their patterns
 * @param typeInfo Map of type names to constructor info
 * @param ctorToType Map of constructor names to their parent type
 * @returns The case tree
 */
function buildTree(
  clauses: InternalClause[],
  typeInfo: TypeInfoMap,
  ctorToType: ConstructorToTypeMap
): CaseTree {
  // Base case: no clauses cover this path
  if (clauses.length === 0) {
    return { tag: 'Uncovered' };
  }

  // Check if first clause has all wildcards/variables (no constructor patterns)
  const firstClause = clauses[0];
  if (firstClause.patterns.length === 0 || allWildcards(firstClause.patterns)) {
    // This clause matches - it's a leaf
    return { tag: 'Leaf', clauseIndex: firstClause.clauseIndex };
  }

  // Find first column with a constructor pattern
  const splitCol = findSplitColumn(clauses);
  if (splitCol === -1) {
    // All patterns are wildcards - first clause matches
    return { tag: 'Leaf', clauseIndex: firstClause.clauseIndex };
  }

  // Get the type being split on (from the first constructor pattern in this column)
  const typeName = getTypeAtColumn(clauses, splitCol, ctorToType);
  if (typeName === null) {
    // Can't determine type - treat as all wildcards matching first clause
    return { tag: 'Leaf', clauseIndex: firstClause.clauseIndex };
  }

  const info = typeInfo.get(typeName);
  if (!info) {
    // Unknown type - treat as all wildcards
    return { tag: 'Leaf', clauseIndex: firstClause.clauseIndex };
  }

  // Build a branch for EACH constructor of this type
  const branches = new Map<string, CaseTree>();
  for (const ctorName of info.constructors) {
    const arity = info.arities.get(ctorName) ?? 0;
    const specialized = specializeClauses(clauses, splitCol, ctorName, arity);
    branches.set(ctorName, buildTree(specialized, typeInfo, ctorToType));
  }

  return { tag: 'Split', typeName, branches };
}

/**
 * Check if all patterns are wildcards or variables
 */
function allWildcards(patterns: TTKPattern[]): boolean {
  return patterns.every(p => p.tag === 'PVar' || p.tag === 'PWild');
}

/**
 * Find the first column (index) that has a constructor pattern in any clause
 */
function findSplitColumn(clauses: InternalClause[]): number {
  if (clauses.length === 0) return -1;

  const numCols = clauses[0].patterns.length;
  for (let col = 0; col < numCols; col++) {
    for (const clause of clauses) {
      if (col < clause.patterns.length && clause.patterns[col].tag === 'PCtor') {
        return col;
      }
    }
  }
  return -1;
}

/**
 * Get the type name for the column being split on
 */
function getTypeAtColumn(
  clauses: InternalClause[],
  col: number,
  ctorToType: ConstructorToTypeMap
): string | null {
  for (const clause of clauses) {
    if (col < clause.patterns.length) {
      const pat = clause.patterns[col];
      if (pat.tag === 'PCtor') {
        return ctorToType.get(pat.name) ?? null;
      }
    }
  }
  return null;
}

/**
 * Specialize clauses for a specific constructor.
 *
 * For each clause:
 * - If pattern at col is a wildcard: expand to `arity` fresh wildcards
 * - If pattern at col is PCtor with matching name: splice in the ctor's args
 * - Otherwise: clause doesn't match this constructor, drop it
 */
function specializeClauses(
  clauses: InternalClause[],
  col: number,
  ctorName: string,
  arity: number
): InternalClause[] {
  const result: InternalClause[] = [];

  for (const clause of clauses) {
    if (col >= clause.patterns.length) {
      // No pattern at this column - treat as wildcard
      // Expand to `arity` wildcards
      const newPatterns = [
        ...clause.patterns.slice(0, col),
        ...Array(arity).fill({ tag: 'PWild' as const, name: '_' }),
        ...clause.patterns.slice(col)
      ];
      result.push({ patterns: newPatterns, clauseIndex: clause.clauseIndex });
      continue;
    }

    const pat = clause.patterns[col];

    if (pat.tag === 'PVar' || pat.tag === 'PWild') {
      // Wildcard matches any constructor
      // Replace with `arity` fresh wildcards for the constructor's arguments
      const newPatterns = [
        ...clause.patterns.slice(0, col),
        ...Array(arity).fill({ tag: 'PWild' as const, name: '_' }),
        ...clause.patterns.slice(col + 1)
      ];
      result.push({ patterns: newPatterns, clauseIndex: clause.clauseIndex });
    } else if (pat.tag === 'PCtor' && pat.name === ctorName) {
      // Constructor pattern matches
      // Splice in the constructor's argument patterns
      const newPatterns = [
        ...clause.patterns.slice(0, col),
        ...pat.args,
        ...clause.patterns.slice(col + 1)
      ];
      result.push({ patterns: newPatterns, clauseIndex: clause.clauseIndex });
    }
    // else: pattern is a different constructor, clause doesn't match
  }

  return result;
}

// ============================================================================
// Coverage Analysis
// ============================================================================

/**
 * Check if a case tree has any uncovered paths
 */
export function isTreeExhaustive(tree: CaseTree): boolean {
  switch (tree.tag) {
    case 'Leaf':
      return true;
    case 'Uncovered':
      return false;
    case 'Split':
      // All branches must be exhaustive
      for (const subTree of tree.branches.values()) {
        if (!isTreeExhaustive(subTree)) return false;
      }
      return true;
  }
}

/**
 * Find which clauses are actually reachable in the tree
 */
function findReachableClauses(tree: CaseTree): Set<number> {
  const reachable = new Set<number>();
  collectReachable(tree, reachable);
  return reachable;
}

function collectReachable(tree: CaseTree, reachable: Set<number>): void {
  switch (tree.tag) {
    case 'Leaf':
      reachable.add(tree.clauseIndex);
      break;
    case 'Uncovered':
      break;
    case 'Split':
      for (const subTree of tree.branches.values()) {
        collectReachable(subTree, reachable);
      }
      break;
  }
}

// ============================================================================
// Printing the Case Tree
// ============================================================================

/**
 * Pretty-print a case tree for debugging
 */
export function printCaseTree(tree: CaseTree, indent: number = 0): string {
  const pad = '  '.repeat(indent);

  switch (tree.tag) {
    case 'Leaf':
      return `${pad}→ clause ${tree.clauseIndex}`;

    case 'Uncovered':
      return `${pad}→ MISSING`;

    case 'Split': {
      const lines: string[] = [];
      for (const [ctorName, subTree] of tree.branches) {
        lines.push(`${pad}${ctorName}:`);
        lines.push(printCaseTree(subTree, indent + 1));
      }
      return lines.join('\n');
    }
  }
}

// ============================================================================
// Main Entry Point
// ============================================================================

/**
 * Build a case tree and check totality.
 */
export function buildCaseTree(
  clauses: { patterns: TTKPattern[] }[],
  definitions: DefinitionsMap
): TotalityResult {
  if (clauses.length === 0) {
    return {
      caseTree: null,
      unreachableClauses: [],
      isExhaustive: false
    };
  }

  const { typeInfo, ctorToType } = buildTypeInfoMaps(definitions);

  // Convert to internal format with clause indices
  const internalClauses: InternalClause[] = clauses.map((c, i) => ({
    patterns: c.patterns,
    clauseIndex: i
  }));

  // Build the tree
  const caseTree = buildTree(internalClauses, typeInfo, ctorToType);

  // Find unreachable clauses
  const reachable = findReachableClauses(caseTree);
  const unreachableClauses: number[] = [];
  for (let i = 0; i < clauses.length; i++) {
    if (!reachable.has(i)) {
      unreachableClauses.push(i);
    }
  }

  return {
    caseTree,
    unreachableClauses,
    isExhaustive: isTreeExhaustive(caseTree)
  };
}

/**
 * Run totality checking on a pattern-matching term.
 */
export function checkTotality(
  termName: string,
  clauses: { patterns: TTKPattern[] }[],
  definitions: DefinitionsMap
): TotalityResult {
  const result = buildCaseTree(clauses, definitions);

  // Log for debugging
  console.log(`\n[Totality] Case tree for '${termName}':`);
  if (result.caseTree) {
    console.log(printCaseTree(result.caseTree));
  }
  if (result.unreachableClauses.length > 0) {
    console.log(`[Totality] Unreachable clauses: ${result.unreachableClauses.join(', ')}`);
  }
  if (!result.isExhaustive) {
    console.log(`[Totality] WARNING: Patterns are not exhaustive`);
  }

  return result;
}
