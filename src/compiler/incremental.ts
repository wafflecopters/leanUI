/**
 * Incremental compilation support: name-based dependency DAG.
 *
 * When source text changes, we identify which blocks changed and compute
 * the set of blocks that need re-typechecking (changed blocks + transitive
 * dependents). Dependencies are detected via literal word-boundary substring
 * matching: block B depends on block A if B's source text contains any name
 * defined by A.
 */

import { ParsedDeclaration } from '../parser/parser';
import { ParsedBlock, CompiledBlock } from './compile';
import { TermDefinition, InductiveDefinition } from './term';

// ============================================================================
// Types
// ============================================================================

/**
 * Dependency-relevant info for a single block.
 * Input to computeRecheckSet — designed to be easily constructed in tests.
 */
export interface BlockDepInfo {
  /** Index of this block in the block array */
  index: number;
  /** Source text of this block */
  sourceText: string;
  /** Names DEFINED by declarations in this block */
  definesNames: string[];
}

/**
 * What a compiled block contributes to the running global state.
 * Stored in cache; replayed when reusing a cached block.
 */
export interface BlockContributions {
  terms: [string, TermDefinition][];
  inductiveTypes: [string, InductiveDefinition][];
  constructorMappings: [string, string][];
  symbolNames: string[];
  constructorParamEntries: [string, unknown[]][];
}

/**
 * Cached result for a single block.
 */
export interface CachedBlockResult {
  sourceText: string;
  compiledBlock: CompiledBlock;
  contributions: BlockContributions;
  checkErrorCount: number;
  nameErrorCount: number;
}

/**
 * Full incremental compilation cache, stored across renders.
 */
export interface IncrementalCache {
  blocks: (CachedBlockResult | undefined)[];
  /** Cached result from last compilation, for fast early-exit when no block content changed. */
  lastResult?: import('./compile').CompileResult;
}

export function createIncrementalCache(): IncrementalCache {
  return { blocks: [] };
}

// ============================================================================
// Name extraction
// ============================================================================

/**
 * Extract all names that a parsed declaration adds to the symbol context.
 * Includes: declaration name, constructor names, record projection names.
 */
export function extractDefinedNames(decl: ParsedDeclaration): string[] {
  const names: string[] = [];

  // Declaration name
  if (decl.name) {
    names.push(decl.name);
  }

  // Constructor names (inductive types)
  if (decl.constructors) {
    for (const ctor of decl.constructors) {
      names.push(ctor.name);
    }
  }

  // Record: constructor + projection names
  if (decl.kind === 'record' && decl.name) {
    const ctorName = decl.constructorName ?? `Mk${decl.name}`;
    // Only add if not already added via constructors
    if (!names.includes(ctorName)) {
      names.push(ctorName);
    }
    // Projection names: RecordName.fieldName
    if (decl.fields) {
      for (const field of decl.fields) {
        names.push(`${decl.name}.${field.name}`);
      }
    }
  }

  return names;
}

/**
 * Extract BlockDepInfo from a ParsedBlock.
 */
export function extractBlockDepInfo(block: ParsedBlock, index: number): BlockDepInfo {
  const sourceText = block.sourceLines.join('\n');
  const definesNames: string[] = [];

  if (block.kind === 'declarations') {
    for (const decl of block.declarations) {
      definesNames.push(...extractDefinedNames(decl));
    }
  }

  return { index, sourceText, definesNames };
}

// ============================================================================
// Dependency DAG
// ============================================================================

/**
 * Check if sourceText contains `name` as a whole word (word-boundary match).
 * Prevents false positives like `a` matching inside `radd`.
 *
 * For dotted names like `Point.x`, the dot is a non-word character so
 * \bPoint\b.\bx\b works correctly.
 */
export function wordBoundaryMatch(sourceText: string, name: string): boolean {
  // Escape regex special characters in the name
  const escaped = name.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
  const regex = new RegExp(`\\b${escaped}\\b`);
  return regex.test(sourceText);
}

/**
 * Compute the set of block indices that need re-typechecking.
 *
 * Algorithm:
 * 1. Build nameToBlock map (which block defines each name)
 * 2. Build forward dependency graph via word-boundary matching
 * 3. BFS from changedIndices through the dependency graph
 * 4. Return union of changed + transitively reachable blocks
 */
export function computeRecheckSet(
  blocks: BlockDepInfo[],
  changedIndices: Set<number>,
): Set<number> {
  if (changedIndices.size === 0) return new Set();

  // Step 1: Map each defined name to its defining block index
  const nameToBlock = new Map<string, number>();
  for (const block of blocks) {
    for (const name of block.definesNames) {
      nameToBlock.set(name, block.index);
    }
  }

  // Step 2: Build forward dependency graph
  // dependents[i] = set of block indices that depend on block i
  const dependents = new Map<number, Set<number>>();

  for (const block of blocks) {
    for (const [name, defBlockIdx] of nameToBlock) {
      // Only backward dependencies (earlier block defines, later block uses)
      // Skip self-references
      if (defBlockIdx >= block.index) continue;

      if (wordBoundaryMatch(block.sourceText, name)) {
        let deps = dependents.get(defBlockIdx);
        if (!deps) {
          deps = new Set();
          dependents.set(defBlockIdx, deps);
        }
        deps.add(block.index);
      }
    }
  }

  // Step 3: BFS from changed blocks through dependents
  const recheckSet = new Set(changedIndices);
  const queue = [...changedIndices];

  while (queue.length > 0) {
    const current = queue.shift()!;
    const deps = dependents.get(current);
    if (deps) {
      for (const dep of deps) {
        if (!recheckSet.has(dep)) {
          recheckSet.add(dep);
          queue.push(dep);
        }
      }
    }
  }

  return recheckSet;
}
