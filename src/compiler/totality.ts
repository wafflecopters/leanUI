/**
 * Totality Checker - Case Tree Construction and Coverage Analysis
 *
 * This module builds a case tree from elaborated pattern clauses to detect:
 * - Missing patterns (inputs no clause handles)
 * - Unreachable clauses (clauses that can never match)
 *
 * Algorithm:
 * 1. Build a trie by walking each clause's patterns left-to-right, depth-first
 * 2. When we see a constructor, split and create branches for ALL peer constructors
 * 3. Branches SHARE the "rest" node - updates to one path affect all paths
 * 4. When a clause has wildcard but tree has Split, recurse into ALL branches
 * 5. After building, walk tree to find Uncovered leaves and check absurdity
 */

import { TTKPattern } from './kernel';
import { DefinitionsMap } from './term';

// ============================================================================
// Exported Case Tree Types (for visualization)
// ============================================================================

/**
 * A case tree represents the decision structure of pattern matching.
 */
export type CaseTree =
  | { tag: 'Leaf'; clauseIndex: number }
  | { tag: 'Split'; typeName: string; branches: Map<string, CaseTree> }
  | { tag: 'Uncovered' }
  | { tag: 'Absurd' };

/**
 * Result of totality checking
 */
export interface TotalityResult {
  caseTree: CaseTree | null;
  unreachableClauses: number[];
  isExhaustive: boolean;
}

/**
 * Function type for checking if patterns are absurd
 */
export type AbsurdityChecker = (patterns: TTKPattern[]) => boolean;

// ============================================================================
// Type Info Helpers
// ============================================================================

interface TypeInfo {
  constructors: string[];
  arities: Map<string, number>;
}

type TypeInfoMap = Map<string, TypeInfo>;
type ConstructorToTypeMap = Map<string, string>;

function buildTypeInfoMaps(definitions: DefinitionsMap): { typeInfo: TypeInfoMap; ctorToType: ConstructorToTypeMap } {
  const typeInfo: TypeInfoMap = new Map();
  const ctorToType: ConstructorToTypeMap = new Map();

  for (const [typeName, inductiveDef] of definitions.inductiveTypes) {
    const constructors: string[] = [];
    const arities = new Map<string, number>();

    for (const ctor of inductiveDef.constructors) {
      constructors.push(ctor.name);
      arities.set(ctor.name, countConstructorArity(ctor.type));
      ctorToType.set(ctor.name, typeName);
    }

    typeInfo.set(typeName, { constructors, arities });
  }

  return { typeInfo, ctorToType };
}

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
// Internal Pattern Tree (Mutable Trie with Sharing)
// ============================================================================

/**
 * Mutable tree node for building the pattern trie.
 * Uses a `content` field that can be mutated, enabling sharing between branches.
 */
interface MutableNode {
  content: NodeContent;
}

type NodeContent =
  | { tag: 'Wildcard'; child: MutableNode }
  | { tag: 'Split'; typeName: string; branches: Map<string, MutableNode> }
  | { tag: 'Leaf'; clauseIndex: number }
  | { tag: 'Uncovered' }
  | { tag: 'Absurd' };

function makeNode(content: NodeContent): MutableNode {
  return { content };
}

// ============================================================================
// Flattening Patterns (DFS order)
// ============================================================================

function flattenPatterns(patterns: TTKPattern[]): TTKPattern[] {
  const result: TTKPattern[] = [];
  for (const p of patterns) {
    flattenPattern(p, result);
  }
  return result;
}

function flattenPattern(pattern: TTKPattern, result: TTKPattern[]): void {
  result.push(pattern);
  if (pattern.tag === 'PCtor') {
    for (const arg of pattern.args) {
      flattenPattern(arg, result);
    }
  }
}

// ============================================================================
// Building the Tree (with Sharing)
// ============================================================================

/**
 * Add a clause to the pattern tree (mutates the tree).
 * Returns true if the clause annotated at least one new leaf (is reachable).
 */
function addClauseToTree(
  node: MutableNode,
  patterns: TTKPattern[],
  patternIndex: number,
  clauseIndex: number,
  typeInfo: TypeInfoMap,
  ctorToType: ConstructorToTypeMap,
): boolean {
  // End of patterns - try to mark this position
  if (patternIndex >= patterns.length) {
    if (node.content.tag === 'Uncovered') {
      node.content = { tag: 'Leaf', clauseIndex };
      return true;
    } else if (node.content.tag === 'Leaf') {
      // Already covered by earlier clause
      return false;
    } else if (node.content.tag === 'Wildcard') {
      // Continue through remaining wildcards
      return addClauseToTree(node.content.child, patterns, patternIndex, clauseIndex, typeInfo, ctorToType);
    } else if (node.content.tag === 'Split') {
      // Split - recurse into all branches (clause covers all constructors)
      let anyReachable = false;
      for (const branch of node.content.branches.values()) {
        if (addClauseToTree(branch, patterns, patternIndex, clauseIndex, typeInfo, ctorToType)) {
          anyReachable = true;
        }
      }
      return anyReachable;
    } else {
      // Absurd - shouldn't reach here during tree building
      return false;
    }
  }

  const pattern = patterns[patternIndex];

  switch (node.content.tag) {
    case 'Uncovered': {
      if (pattern.tag === 'PVar' || pattern.tag === 'PWild') {
        // Create wildcard node and continue
        const child = makeNode({ tag: 'Uncovered' });
        node.content = { tag: 'Wildcard', child };
        return addClauseToTree(child, patterns, patternIndex + 1, clauseIndex, typeInfo, ctorToType);
      } else {
        // PCtor - create split for all constructors
        const typeName = ctorToType.get(pattern.name);
        if (!typeName) {
          // Unknown constructor - treat as wildcard
          const child = makeNode({ tag: 'Uncovered' });
          node.content = { tag: 'Wildcard', child };
          return addClauseToTree(child, patterns, patternIndex + 1, clauseIndex, typeInfo, ctorToType);
        }

        const info = typeInfo.get(typeName)!;
        const branches = new Map<string, MutableNode>();

        // Create branches for ALL constructors
        // Each constructor gets its own independent subtree (no sharing)
        // because constructors have different arities
        for (const ctorName of info.constructors) {
          const arity = info.arities.get(ctorName) ?? 0;
          // Create wildcard chain for constructor args, ending at Uncovered
          branches.set(ctorName, createWildcardChain(arity, makeNode({ tag: 'Uncovered' })));
        }

        node.content = { tag: 'Split', typeName, branches };

        // Now continue into the matching branch
        const matchingBranch = branches.get(pattern.name)!;
        return addClauseToTree(matchingBranch, patterns, patternIndex + 1, clauseIndex, typeInfo, ctorToType);
      }
    }

    case 'Wildcard': {
      // Continue to child
      return addClauseToTree(node.content.child, patterns, patternIndex + 1, clauseIndex, typeInfo, ctorToType);
    }

    case 'Split': {
      if (pattern.tag === 'PVar' || pattern.tag === 'PWild') {
        // Clause has wildcard but tree has split - recurse into ALL branches
        let anyReachable = false;
        for (const [ctorName, branch] of node.content.branches) {
          const arity = typeInfo.get(node.content.typeName)?.arities.get(ctorName) ?? 0;
          // Create synthetic wildcard patterns for this constructor's args
          const syntheticPatterns = [
            ...patterns.slice(0, patternIndex + 1),
            ...Array(arity).fill({ tag: 'PWild' as const, name: '_' }),
            ...patterns.slice(patternIndex + 1)
          ];
          if (addClauseToTree(branch, syntheticPatterns, patternIndex + 1, clauseIndex, typeInfo, ctorToType)) {
            anyReachable = true;
          }
        }
        return anyReachable;
      } else {
        // Clause has constructor - go into matching branch
        const matchingBranch = node.content.branches.get(pattern.name);
        if (matchingBranch) {
          return addClauseToTree(matchingBranch, patterns, patternIndex + 1, clauseIndex, typeInfo, ctorToType);
        } else {
          // Constructor not in current split - shouldn't happen if types are consistent
          return false;
        }
      }
    }

    case 'Leaf': {
      // Already covered by an earlier clause
      return false;
    }

    case 'Absurd': {
      // Absurd case - shouldn't happen during tree building (only marked later)
      return false;
    }
  }
}

/**
 * Create a chain of N wildcard nodes ending at the given terminal node
 */
function createWildcardChain(n: number, terminal: MutableNode): MutableNode {
  let node = terminal;
  for (let i = 0; i < n; i++) {
    node = makeNode({ tag: 'Wildcard', child: node });
  }
  return node;
}

// ============================================================================
// Converting to CaseTree
// ============================================================================

function mutableToCaseTree(node: MutableNode): CaseTree {
  switch (node.content.tag) {
    case 'Leaf':
      return { tag: 'Leaf', clauseIndex: node.content.clauseIndex };
    case 'Uncovered':
      return { tag: 'Uncovered' };
    case 'Absurd':
      return { tag: 'Absurd' };
    case 'Wildcard':
      // Collapse wildcards
      return mutableToCaseTree(node.content.child);
    case 'Split': {
      const branches = new Map<string, CaseTree>();
      for (const [name, branch] of node.content.branches) {
        branches.set(name, mutableToCaseTree(branch));
      }
      return { tag: 'Split', typeName: node.content.typeName, branches };
    }
  }
}

// ============================================================================
// Helper Functions for Wildcard Handling
// ============================================================================

function countWildcardsAtStart(node: MutableNode): number {
  let count = 0;
  let current = node;
  while (current.content.tag === 'Wildcard') {
    count++;
    current = current.content.child;
  }
  return count;
}

function skipWildcards(node: MutableNode, n: number): MutableNode {
  let current = node;
  for (let i = 0; i < n && current.content.tag === 'Wildcard'; i++) {
    current = current.content.child;
  }
  return current;
}

// ============================================================================
// Absurdity Marking (in mutable tree)
// ============================================================================

/**
 * Mark absurd cases directly in the mutable tree.
 * Must be called BEFORE converting to CaseTree to preserve wildcard info.
 */
function markAbsurdInMutableTree(
  node: MutableNode,
  currentPath: TTKPattern[],
  checker: AbsurdityChecker,
  visited: Set<MutableNode> = new Set()
): void {
  // Prevent infinite loops from shared nodes
  if (visited.has(node)) return;
  visited.add(node);

  switch (node.content.tag) {
    case 'Leaf':
      break;
    case 'Uncovered':
      // Check if this uncovered case is absurd
      if (checker(currentPath)) {
        node.content = { tag: 'Absurd' };
      }
      break;
    case 'Wildcard':
      currentPath.push({ tag: 'PWild', name: '_' });
      markAbsurdInMutableTree(node.content.child, currentPath, checker, visited);
      currentPath.pop();
      break;
    case 'Split':
      for (const [ctorName, branch] of node.content.branches) {
        const arity = countWildcardsAtStart(branch);
        const args: TTKPattern[] = Array(arity).fill(null).map(() => ({ tag: 'PWild' as const, name: '_' }));
        currentPath.push({ tag: 'PCtor', name: ctorName, args });
        const innerNode = skipWildcards(branch, arity);
        markAbsurdInMutableTree(innerNode, currentPath, checker, visited);
        currentPath.pop();
      }
      break;
    case 'Absurd':
      // Already marked
      break;
  }
}

// ============================================================================
// Coverage Analysis
// ============================================================================

function isTreeExhaustive(tree: CaseTree): boolean {
  switch (tree.tag) {
    case 'Leaf':
    case 'Absurd':
      return true;
    case 'Uncovered':
      return false;
    case 'Split':
      for (const subTree of tree.branches.values()) {
        if (!isTreeExhaustive(subTree)) return false;
      }
      return true;
  }
}


// ============================================================================
// Pretty Printing
// ============================================================================

export function printCaseTree(tree: CaseTree, indent: number = 0): string {
  const pad = '  '.repeat(indent);

  switch (tree.tag) {
    case 'Leaf':
      return `${pad}→ clause ${tree.clauseIndex}`;
    case 'Uncovered':
      return `${pad}→ MISSING`;
    case 'Absurd':
      return `${pad}→ absurd`;
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

export function checkTotality(
  termName: string,
  clauses: { patterns: TTKPattern[] }[],
  definitions: DefinitionsMap,
  absurdityChecker?: AbsurdityChecker
): TotalityResult {
  // Don't short-circuit for zero clauses - let absurdity checker determine
  // if zero clauses is valid (e.g., for absurd : Void -> A)

  const { typeInfo, ctorToType } = buildTypeInfoMaps(definitions);

  // Build the mutable pattern tree
  const root = makeNode({ tag: 'Uncovered' });
  const reachableClauses = new Set<number>();

  for (let i = 0; i < clauses.length; i++) {
    const flatPatterns = flattenPatterns(clauses[i].patterns);
    if (addClauseToTree(root, flatPatterns, 0, i, typeInfo, ctorToType)) {
      reachableClauses.add(i);
    }
  }

  // Find unreachable clauses
  const unreachableClauses: number[] = [];
  for (let i = 0; i < clauses.length; i++) {
    if (!reachableClauses.has(i)) {
      unreachableClauses.push(i);
    }
  }

  // If we have an absurdity checker, mark absurd cases in the mutable tree
  // (must do this BEFORE converting to CaseTree to preserve wildcard info)
  if (absurdityChecker) {
    markAbsurdInMutableTree(root, [], absurdityChecker);
  }

  // Convert to immutable CaseTree
  const caseTree = mutableToCaseTree(root);
  const isExhaustive = isTreeExhaustive(caseTree);

  // Debug logging
  console.log(`\n[Totality] Case tree for '${termName}':`);
  console.log(printCaseTree(caseTree));
  if (unreachableClauses.length > 0) {
    console.log(`[Totality] Unreachable clauses: ${unreachableClauses.join(', ')}`);
  }
  if (!isExhaustive) {
    console.log(`[Totality] WARNING: Patterns are not exhaustive`);
  }

  return { caseTree, unreachableClauses, isExhaustive };
}
