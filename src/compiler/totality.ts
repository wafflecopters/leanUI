/**
 * Totality Checker - Case Tree Construction
 *
 * This module builds a case tree from elaborated pattern clauses to track
 * coverage and detect unreachable patterns.
 *
 * The case tree represents the decision structure of pattern matching:
 * - Each constructor pattern creates a split (branching on which constructor)
 * - Variable/wildcard patterns don't split (they match anything)
 * - Leaves represent reaching a specific clause
 */

import { TTKPattern, prettyPrintPattern } from './kernel';

// ============================================================================
// Case Tree Types
// ============================================================================

/**
 * A case tree represents the decision structure of pattern matching.
 *
 * - Leaf: A clause has been matched (clauseIndex identifies which one)
 * - Split: We're splitting on a constructor; branches map constructor names
 *   to subtrees, and default_ catches anything not explicitly listed
 */
export type CaseTree =
  | { tag: 'Leaf'; clauseIndex: number }
  | { tag: 'Split'; branches: Map<string, CaseTree>; default_: CaseTree | null };

// ============================================================================
// Building the Case Tree
// ============================================================================

/**
 * Add a clause's patterns to a case tree, returning the updated tree.
 * Returns undefined if the clause is unreachable (doesn't add any new coverage).
 *
 * @param tree The existing case tree (or null for the first clause)
 * @param patterns The patterns for this clause
 * @param clauseIndex The index of this clause
 * @returns Updated tree, or undefined if the clause is unreachable
 */
export function addClausePatternsToCaseTree(
  tree: CaseTree | null,
  patterns: TTKPattern[],
  clauseIndex: number
): CaseTree | undefined {
  // First clause: build initial tree
  if (tree === null) {
    return buildTreeFromPatterns(patterns, clauseIndex);
  }

  // Subsequent clause: walk and extend
  const result = extendTree(tree, patterns, clauseIndex);
  return result.modified ? result.tree : undefined;
}

/**
 * Build a case tree from a single clause's patterns.
 * This is used for the first clause.
 */
function buildTreeFromPatterns(patterns: TTKPattern[], clauseIndex: number): CaseTree {
  return buildRec(patterns, clauseIndex);
}

/**
 * Recursively build tree from a flat list of patterns.
 * When we encounter a PCtor, its args are prepended to the remaining patterns.
 */
function buildRec(patterns: TTKPattern[], clauseIndex: number): CaseTree {
  if (patterns.length === 0) {
    return { tag: 'Leaf', clauseIndex };
  }

  const [first, ...rest] = patterns;

  switch (first.tag) {
    case 'PVar':
    case 'PWild':
      // Variable/wildcard: don't split, continue with rest
      return buildRec(rest, clauseIndex);

    case 'PCtor': {
      // Constructor: split here, recurse into [ctorArgs..., rest...]
      const innerPatterns = [...first.args, ...rest];
      const subTree = buildRec(innerPatterns, clauseIndex);
      return {
        tag: 'Split',
        branches: new Map([[first.name, subTree]]),
        default_: null
      };
    }
  }
}

// ============================================================================
// Extending the Case Tree
// ============================================================================

type ExtendResult = { tree: CaseTree; modified: boolean };

/**
 * Extend an existing tree with a new clause's patterns.
 * Returns the (possibly modified) tree and whether any modification was made.
 */
function extendTree(tree: CaseTree, patterns: TTKPattern[], clauseIndex: number): ExtendResult {
  return extendRec(tree, patterns, clauseIndex);
}

function extendRec(tree: CaseTree, patterns: TTKPattern[], clauseIndex: number): ExtendResult {
  // If we've reached a leaf, this path is already covered - no modification
  if (tree.tag === 'Leaf') {
    return { tree, modified: false };
  }

  // tree.tag === 'Split'
  // Treat empty patterns as an implicit wildcard (match anything remaining)
  if (patterns.length === 0) {
    return extendWithWildcard(tree, [], clauseIndex);
  }

  const [first, ...rest] = patterns;

  switch (first.tag) {
    case 'PVar':
    case 'PWild':
      return extendWithWildcard(tree, rest, clauseIndex);

    case 'PCtor': {
      // Constructor pattern at a split
      const ctorName = first.name;

      // Check if this constructor already has a branch
      if (tree.branches.has(ctorName)) {
        // Extend existing branch with [ctorArgs..., rest...]
        const existingSubTree = tree.branches.get(ctorName)!;
        const innerPatterns = [...first.args, ...rest];
        const extResult = extendRec(existingSubTree, innerPatterns, clauseIndex);

        if (extResult.modified) {
          const newBranches = new Map(tree.branches);
          newBranches.set(ctorName, extResult.tree);
          return { tree: { ...tree, branches: newBranches }, modified: true };
        }
        return { tree, modified: false };
      }

      // No existing branch for this constructor
      // If there's a default, this case is already covered
      if (tree.default_ !== null) {
        // The pattern is more specific than the default, but semantically covered
        // This clause is unreachable for this path
        return { tree, modified: false };
      }

      // No branch and no default: add new branch
      const innerPatterns = [...first.args, ...rest];
      const newSubTree = buildRec(innerPatterns, clauseIndex);
      const newBranches = new Map(tree.branches);
      newBranches.set(ctorName, newSubTree);
      return {
        tree: { tag: 'Split', branches: newBranches, default_: null },
        modified: true
      };
    }
  }
}

/**
 * Extend a Split node with a wildcard/variable pattern.
 * This means the clause matches anything at this split point, so we need to:
 * 1. Set/extend the default (for constructors not explicitly listed)
 * 2. Extend all existing branches (to fill in gaps deeper in the tree)
 */
function extendWithWildcard(
  tree: CaseTree & { tag: 'Split' },
  rest: TTKPattern[],
  clauseIndex: number
): ExtendResult {
  let modified = false;

  // Extend default
  let newDefault: CaseTree | null = tree.default_;
  if (newDefault === null) {
    // No default yet - create one by building tree from remaining patterns
    newDefault = buildRec(rest, clauseIndex);
    modified = true;
  } else {
    // Default exists - try to extend it
    const extResult = extendRec(newDefault, rest, clauseIndex);
    if (extResult.modified) {
      newDefault = extResult.tree;
      modified = true;
    }
  }

  // Extend all existing branches
  // (The wildcard matches any constructor, so we need to extend coverage in each branch)
  const newBranches = new Map(tree.branches);
  for (const [ctor, subTree] of tree.branches) {
    const extResult = extendRec(subTree, rest, clauseIndex);
    if (extResult.modified) {
      newBranches.set(ctor, extResult.tree);
      modified = true;
    }
  }

  return {
    tree: { tag: 'Split', branches: newBranches, default_: newDefault },
    modified
  };
}

// ============================================================================
// Printing the Case Tree
// ============================================================================

/**
 * Pretty-print a case tree for debugging.
 */
export function printCaseTree(tree: CaseTree, indent: number = 0): string {
  const pad = '  '.repeat(indent);

  if (tree.tag === 'Leaf') {
    return `${pad}→ Clause ${tree.clauseIndex}`;
  }

  // Split node
  const lines: string[] = [];

  // Print each constructor branch
  for (const [ctorName, subTree] of tree.branches) {
    lines.push(`${pad}${ctorName}:`);
    lines.push(printCaseTree(subTree, indent + 1));
  }

  // Print default if present
  if (tree.default_ !== null) {
    lines.push(`${pad}_:`);
    lines.push(printCaseTree(tree.default_, indent + 1));
  } else {
    lines.push(`${pad}_ : <uncovered>`);
  }

  return lines.join('\n');
}

/**
 * Build a case tree from all clauses and print it.
 * Returns the final tree (or null if no clauses).
 */
export function buildAndPrintCaseTree(
  clauses: { patterns: TTKPattern[] }[],
  termName: string
): CaseTree | null {
  if (clauses.length === 0) {
    console.log(`[Totality] ${termName}: no clauses`);
    return null;
  }

  let tree: CaseTree | null = null;
  const unreachableClauses: number[] = [];

  for (let i = 0; i < clauses.length; i++) {
    const result = addClausePatternsToCaseTree(tree, clauses[i].patterns, i);
    if (result === undefined) {
      unreachableClauses.push(i);
      // Keep the tree as-is (clause didn't add coverage)
    } else {
      tree = result;
    }
  }

  console.log(`\n[Totality] Case tree for '${termName}':`);
  if (tree) {
    console.log(printCaseTree(tree));
  }

  if (unreachableClauses.length > 0) {
    console.log(`\n[Totality] Unreachable clauses: ${unreachableClauses.join(', ')}`);
  }

  return tree;
}

// ============================================================================
// Main Entry Point
// ============================================================================

/**
 * Run totality checking on a pattern-matching term.
 * For now, this just builds and prints the case tree.
 *
 * @param termName The name of the term being checked
 * @param clauses The elaborated clauses with their patterns
 */
export function checkTotality(
  termName: string,
  clauses: { patterns: TTKPattern[] }[]
): void {
  buildAndPrintCaseTree(clauses, termName);
}
