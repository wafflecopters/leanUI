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

import { TTKPattern, TTKTerm, prettyPrint as prettyPrintTTK } from './kernel';
import { countPiBinders, DefinitionsMap, extractAppSpine } from './term';

// ============================================================================
// Logging
// ============================================================================

let loggingEnabled = false;

export function setTotalityLoggingEnabled(enabled: boolean): void {
  loggingEnabled = enabled;
}

// ============================================================================
// Exported Case Tree Types (for visualization)
// ============================================================================

/**
 * A case tree represents the decision structure of pattern matching.
 */
export type CaseTree =
  | { tag: 'Leaf'; clauseIndex: number }
  | { tag: 'Split'; typeName: string; branches: Map<string, CaseTree>, remainingPatternsAfterContructorCount: number, ctorArities: Map<string, number>, missingCtors: Set<string> }
  | { tag: 'Uncovered' }
  | { tag: 'Absurd' }
  | { tag: 'NoSplit'; branch: CaseTree, debugLabel: string };

/**
 * Result of totality checking
 */
export interface TotalityResult {
  caseTree: CaseTree | null;
  unreachableClauses: { clauseIndex: number, patterns: TTKPattern[] }[];
  isExhaustive: boolean;
  /** Clauses that were annotated with #absurd and successfully validated as absurd */
  annotatedAbsurdClauses?: number[];
  missingValidClauses: { patterns: TTKPattern[] }[];
  missingAbsurdClauses: { patterns: TTKPattern[] }[];
}

/**
 * Function type for checking if patterns are absurd
 */
export type AbsurdityChecker = (patterns: TTKPattern[]) => boolean;

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
    case 'NoSplit':
      return `${pad}${tree.debugLabel}\n${printCaseTree(tree.branch, indent)}`;
  }
}

// ============================================================================
// Main Entry Point
// ============================================================================


let debugging = false

/**
 * A clause for totality checking.
 * - patterns: structural patterns for coverage analysis
 * - elabArgs: optional zonked elaborated args for case tree display
 * - contextNames: optional context names for pretty-printing elabArgs
 */
export interface TotalityClause {
  patterns: TTKPattern[];
  elabArgs?: TTKTerm[];
  contextNames?: string[];
}

export function checkTotality(
  _termName: string,
  clauses: TotalityClause[],
  definitions: DefinitionsMap,
  absurdityChecker: AbsurdityChecker
): TotalityResult {
  // debugging = termName === 'glob' //'vecConcat\'';

  const unreachableClauses: { clauseIndex: number, patterns: TTKPattern[] }[] = [];
  const annotatedAbsurdClauses: number[] = [];

  let caseTree: CaseTree = { tag: 'Uncovered' };

  for (let i = 0; i < clauses.length; i++) {
    const newCaseTree = caseTreeWithClauseAdded(caseTree, i, clauses[i], definitions);
    if (newCaseTree === undefined) {
      unreachableClauses.push({ clauseIndex: i, patterns: clauses[i].patterns });
    } else {
      caseTree = newCaseTree;
    }
  }

  const missingValidClauses: { patterns: TTKPattern[] }[] = [];
  const missingAbsurdClauses: { patterns: TTKPattern[] }[] = [];

  for (const uncoveredPattern of uncoveredPatternsInCaseTree(caseTree, definitions)) {
    const isAbsurd = absurdityChecker(uncoveredPattern.patterns)

    if (isAbsurd) {
      missingAbsurdClauses.push(uncoveredPattern);
    } else {
      missingValidClauses.push(uncoveredPattern);
    }
  }

  return {
    caseTree,
    unreachableClauses,
    isExhaustive: missingValidClauses.length === 0,
    annotatedAbsurdClauses,
    missingValidClauses,
    missingAbsurdClauses,
  }
}

function printCaseTreeAsString(caseTree: CaseTree, depth: number = 0): string {
  const indentStr = '  '
  const prefix = indentStr.repeat(depth);

  if (caseTree.tag === 'Leaf') {
    return `${prefix}Clause#${caseTree.clauseIndex}`;
  } else if (caseTree.tag === 'NoSplit') {
    return `${prefix}${caseTree.debugLabel}\n${printCaseTreeAsString(caseTree.branch, depth + 1)}`;
  } else if (caseTree.tag === 'Split') {
    return `${prefix}${caseTree.typeName} split:\n${Array.from(caseTree.branches.entries()).map(([ctorName, branch]) => `${prefix}${indentStr}${ctorName}\n${printCaseTreeAsString(branch, depth + 2)}`).join('\n')}`;
  } else if (caseTree.tag === 'Uncovered') {
    return `${prefix}Uncovered`;
  } else if (caseTree.tag === 'Absurd') {
    return `${prefix}Absurd`;
  } else {
    const _never: never = caseTree;
    throw new Error(`Unreachable code: ${_never}`);
  }
}

function logCaseTree(caseTree: CaseTree): void {
  console.log(printCaseTreeAsString(caseTree, 0));
}

function caseTreeWithClauseAdded(caseTree: CaseTree, clauseIndex: number, clause: TotalityClause, definitions: DefinitionsMap): CaseTree | undefined {
  if (clause.patterns.length === 0) {
    debugger
    throw new Error('Zero-pattern clauses are not supported');
  }

  // if (debugging) {
  //   debugger;
  // }

  const _x = caseTreeWithPatternsAdded(caseTree, clauseIndex, clause.patterns, clause.elabArgs, clause.contextNames, definitions);

  return _x;
}

/**
 * Pretty-print a TTKTerm for display in the case tree.
 */
function termToLabel(term: TTKTerm | undefined, contextNames: string[] | undefined, pattern: TTKPattern): string {
  if (!term) {
    return pattern.name;
  }
  const context = contextNames ? [...contextNames] : [];
  return prettyPrintTTK(term, context);
}

/**
 * Extract the arguments from an application spine (e.g., (Ctor arg1 arg2) -> [arg1, arg2])
 */
function extractElabArgsFromTerm(term: TTKTerm | undefined): TTKTerm[] | undefined {
  if (!term) return undefined;
  const { args } = extractAppSpine(term);
  return args.length > 0 ? args : undefined;
}

function caseTreeWithPatternsAdded(caseTree: CaseTree, clauseIndex: number, patterns: TTKPattern[], elabArgs: TTKTerm[] | undefined, contextNames: string[] | undefined, definitions: DefinitionsMap): CaseTree | undefined {
  if (patterns.length === 0) {
    if (caseTree.tag === 'Uncovered') {
      return { tag: 'Leaf', clauseIndex };
    } else {
      return undefined
    }
  }

  const pattern = patterns[0];
  const remainingPatterns = patterns.slice(1);
  const remainingElabArgs = elabArgs?.slice(1);
  // Compute display label from elabArg if available, otherwise fall back to pattern name
  const label = termToLabel(elabArgs?.[0], contextNames, pattern);

  if (pattern.tag === 'PWild' || pattern.tag === 'PVar') {
    if (caseTree.tag === 'Uncovered') {
      const branch = caseTreeWithPatternsAdded({ tag: 'Uncovered' }, clauseIndex, remainingPatterns, remainingElabArgs, contextNames, definitions)
      return branch ? {
        tag: 'NoSplit',
        debugLabel: label,
        branch
      } : undefined;
    } else if (caseTree.tag === 'NoSplit') {
      const branch = caseTreeWithPatternsAdded(caseTree.branch, clauseIndex, patterns.slice(1), remainingElabArgs, contextNames, definitions)
      return branch ? {
        tag: 'NoSplit',
        debugLabel: label,
        branch
      } : undefined;
    } else if (caseTree.tag === 'Split') {
      const newBranches = new Map<string, CaseTree>();
      let didUpdateBranch = false

      for (const ctorName of caseTree.missingCtors) {
        const arity = caseTree.ctorArities.get(ctorName)!;
        const patternArgs = Array(arity).fill({ tag: 'PWild', name: '_' })
        const allPatterns = [...patternArgs, ...remainingPatterns]
        const branch = caseTreeWithPatternsAdded({ tag: 'Uncovered' }, clauseIndex, allPatterns, undefined, undefined, definitions)
        if (!branch) {
          throw new Error(`Failed to create branch for ${ctorName} with arity ${arity}`)
        }
        newBranches.set(ctorName, branch)
      }

      for (const [ctorName, branch] of caseTree.branches) {
        const newBranch = caseTreeWithPatternsAdded(branch, clauseIndex, patterns, elabArgs, contextNames, definitions)
        newBranches.set(ctorName, newBranch ?? branch)
        didUpdateBranch ||= newBranch !== undefined
      }

      return {
        tag: 'Split',
        typeName: caseTree.typeName,
        branches: newBranches,
        remainingPatternsAfterContructorCount: caseTree.remainingPatternsAfterContructorCount,
        ctorArities: caseTree.ctorArities,
        missingCtors: new Set()
      };
    } else if (caseTree.tag === 'Leaf') {
      return undefined;
    } else {
      debugger
    }
  } else /* PCtor */ {
    const typeName = definitions.inductiveNameOfConstructor.get(pattern.name);
    if (!typeName) {
      throw new Error(`Constructor ${pattern.name} not found in inductive type registry`);
    }

    const allPatterns = [...pattern.args, ...remainingPatterns];
    // For constructor patterns, extract the sub-elabArgs from the current elabArg's app spine
    const ctorElabArgs = extractElabArgsFromTerm(elabArgs?.[0]);
    const allElabArgs = ctorElabArgs && remainingElabArgs
      ? [...ctorElabArgs, ...remainingElabArgs]
      : ctorElabArgs || remainingElabArgs;
    const remainingPatternsAfterContructorCount = Math.max(0, allPatterns.length - pattern.args.length);

    if (caseTree.tag === 'Uncovered') {
      const branch = caseTreeWithPatternsAdded({ tag: 'Uncovered' }, clauseIndex, allPatterns, allElabArgs, contextNames, definitions)

      if (!branch) {
        return undefined;
      }

      const branches = new Map<string, CaseTree>();
      branches.set(
        pattern.name,
        branch
      );

      const ctorArities = new Map<string, number>();
      const missingCtors = new Set<string>();
      for (const ctor of definitions.inductiveTypes.get(typeName)!.constructors) {
        ctorArities.set(ctor.name, countPiBinders(ctor.type));
        if (ctor.name !== pattern.name) {
          missingCtors.add(ctor.name);
        }
      }

      return { tag: 'Split', typeName, branches, remainingPatternsAfterContructorCount, ctorArities, missingCtors };
    } else if (caseTree.tag === 'Split') {
      const ctorTree = caseTree.branches.get(pattern.name);
      if (ctorTree) {
        const allPatterns = [...pattern.args, ...remainingPatterns]
        const branch = caseTreeWithPatternsAdded(ctorTree, clauseIndex, allPatterns, allElabArgs, contextNames, definitions)
        if (!branch) {
          return undefined;
        }
        const newBranches = new Map<string, CaseTree>(caseTree.branches);
        const missingCtors = new Set<string>(caseTree.missingCtors);
        missingCtors.delete(pattern.name);
        newBranches.set(pattern.name, branch);
        return { tag: 'Split', typeName, branches: newBranches, remainingPatternsAfterContructorCount, ctorArities: caseTree.ctorArities, missingCtors };
      } else {
        const newBranches = new Map<string, CaseTree>(caseTree.branches);
        const branch = caseTreeWithPatternsAdded({ tag: 'Uncovered' }, clauseIndex, allPatterns, allElabArgs, contextNames, definitions)

        if (!branch) {
          return undefined;
        }

        newBranches.set(
          pattern.name,
          branch
        );

        const missingCtors = new Set<string>(caseTree.missingCtors);
        missingCtors.delete(pattern.name);
        return { tag: 'Split', typeName, branches: newBranches, remainingPatternsAfterContructorCount, ctorArities: caseTree.ctorArities, missingCtors };
      }
    } else if (caseTree.tag === 'NoSplit') {
      const branches = new Map<string, CaseTree>();
      const ctorArities = new Map<string, number>();
      for (const ctor of definitions.inductiveTypes.get(typeName)!.constructors) {
        const arity = countPiBinders(ctor.type);
        ctorArities.set(ctor.name, arity);
        if (ctor.name !== pattern.name) {
          let branch = caseTree.branch
          for (let i = 0; i < arity; i++) {
            branch = { tag: 'NoSplit', debugLabel: `_::${i}`, branch }
          }
          branches.set(ctor.name, branch)
        } else {
          const branch = caseTreeWithPatternsAdded(
            caseTree.branch, clauseIndex, allPatterns, allElabArgs, contextNames, definitions
          )
          if (!branch) {
            return undefined;
          }
          branches.set(ctor.name, branch)
        }
      }

      return {
        tag: 'Split',
        typeName,
        branches,
        remainingPatternsAfterContructorCount,
        ctorArities,
        missingCtors: new Set(),
      }
    } else {
      debugger
    }
  }

  debugger
  return caseTree;
}

function* uncoveredPatternsInCaseTree(caseTree: CaseTree, definitions: DefinitionsMap): Generator<{ patterns: TTKPattern[] }> {
  if (caseTree.tag === 'Leaf') {
    return
  } else if (caseTree.tag === 'Split') {
    for (const [ctorName, branch] of caseTree.branches) {
      for (const tail of uncoveredPatternsInCaseTree(branch, definitions)) {
        const ctorArity = caseTree.ctorArities.get(ctorName)!;
        yield { patterns: [{ tag: 'PCtor', name: ctorName, args: tail.patterns.slice(0, ctorArity) }, ...tail.patterns.slice(ctorArity)] }
      }
    }
    for (const ctorName of caseTree.missingCtors) {
      const arity = caseTree.ctorArities.get(ctorName)!;
      yield { patterns: [{ tag: 'PCtor', name: ctorName, args: Array(arity).fill({ tag: 'PWild', name: '_' }) }] }
    }
    return
  } else if (caseTree.tag === 'Uncovered') {
    yield { patterns: [{ tag: 'PWild', name: '_' }] }
  } else if (caseTree.tag === 'Absurd') {
    debugger
    return
  } else if (caseTree.tag === 'NoSplit') {
    for (const tail of uncoveredPatternsInCaseTree(caseTree.branch, definitions)) {
      yield { patterns: [{ tag: 'PWild', name: '_' }, ...tail.patterns] }
    }
  } else {
    const _never: never = caseTree;
    throw new Error(`Unreachable code: ${_never}`);
  }
}
