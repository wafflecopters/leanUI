/**
 * Structural Recursion Checker
 *
 * This module checks that recursive calls in pattern matching are structurally
 * decreasing - ensuring termination.
 *
 * Algorithm:
 * 1. For each clause, build a "structurally smaller" map from De Bruijn indices
 *    to the pattern position they're smaller than (variables bound inside PCtor patterns)
 * 2. Visit the clause RHS to find all recursive call sites
 * 3. For each call site, check if at least one argument is structurally smaller
 *    than the corresponding pattern position
 */

import { TTKPattern, TTKTerm, TTKClause, prettyPrint } from './kernel';
import { IndexPath, fieldSeg, arraySeg } from '../types/source-position';
import { whnf } from './whnf';

// ============================================================================
// Logging
// ============================================================================

let loggingEnabled = false;

export function setRecursionLoggingEnabled(enabled: boolean): void {
  loggingEnabled = enabled;
}

// ============================================================================
// Types
// ============================================================================

/**
 * Maps a De Bruijn index to the pattern position it's structurally smaller than.
 * A variable is "smaller" if it was bound inside a PCtor pattern.
 */
export type StructurallySmallerMap = Map<number, number>;

/**
 * A recursive call site found in the RHS
 */
export interface RecursiveCallSite {
  /** The arguments applied to the recursive function */
  args: TTKTerm[];
  /** The parent term stack leading to this call (for error reporting) */
  parentStack: TTKTerm[];
  /** The actual Const term at this call site (for binder depth computation) */
  constTerm: TTKTerm;
  /** The index path to this call site within the RHS */
  indexPath: IndexPath;
}

/**
 * Result of checking a single call site
 */
export interface CallSiteCheckResult {
  isValid: boolean;
  /** Which argument position was found to be structurally smaller (if valid) */
  decreasingArgPosition?: number;
  /** Error message if invalid */
  error?: string;
}

/**
 * An error from recursion checking with location info
 */
export interface RecursionError {
  message: string;
  /** Path within the clause RHS to the invalid call site */
  rhsPath: IndexPath;
}

/**
 * Result of checking structural recursion for a clause
 */
export interface ClauseRecursionResult {
  clauseIndex: number;
  isValid: boolean;
  /** All call sites found in this clause */
  callSites: RecursiveCallSite[];
  /** Errors for invalid call sites with location info */
  errors: RecursionError[];
}

/**
 * Overall result of structural recursion checking
 */
export interface StructuralRecursionResult {
  isValid: boolean;
  /** Results for each clause */
  clauseResults: ClauseRecursionResult[];
  /** Aggregated errors with clause index and location info */
  errors: Array<{ clauseIndex: number; error: RecursionError }>;
}

// ============================================================================
// Pattern Variable Collection
// ============================================================================

/**
 * Collect all variables bound by patterns, in left-to-right depth-first order.
 * Returns an array of variable names where index corresponds to binding position.
 */
export function collectPatternVars(patterns: TTKPattern[]): string[] {
  const vars: string[] = [];
  for (const p of patterns) {
    collectPatternVarsHelper(p, vars);
  }
  return vars;
}

function collectPatternVarsHelper(pattern: TTKPattern, vars: string[]): void {
  switch (pattern.tag) {
    case 'PVar':
      vars.push(pattern.name);
      break;
    case 'PWild':
      vars.push(pattern.name);
      break;
    case 'PCtor':
      // Visit args in order (left-to-right)
      for (const arg of pattern.args) {
        collectPatternVarsHelper(arg, vars);
      }
      break;
  }
}

// ============================================================================
// Building the Structurally Smaller Map
// ============================================================================

/**
 * Build the structurally smaller map for a clause.
 *
 * A variable is structurally smaller than pattern position p if:
 * - It is bound INSIDE a PCtor pattern at position p
 *
 * For example, with patterns [(Succ n), m]:
 * - n is bound inside PCtor at position 0, so n is smaller than position 0
 * - m is just a PVar at position 1, NOT smaller than anything
 *
 * The map is from De Bruijn index to pattern position.
 * De Bruijn index = (total_vars - 1 - binding_position)
 */
export function buildStructurallySmallerMap(patterns: TTKPattern[]): StructurallySmallerMap {
  const result: StructurallySmallerMap = new Map();

  // First, collect all variables to know total count
  const allVars = collectPatternVars(patterns);
  const totalVars = allVars.length;

  // Track current binding position as we traverse
  let bindingPosition = 0;

  for (let patternPos = 0; patternPos < patterns.length; patternPos++) {
    const pattern = patterns[patternPos];
    bindingPosition = collectSmallerVarsFromPattern(
      pattern,
      patternPos,
      bindingPosition,
      totalVars,
      result,
      false  // Top-level patterns are not inside a PCtor
    );
  }

  return result;
}

/**
 * Recursively collect variables that are structurally smaller.
 * @param pattern The pattern to traverse
 * @param patternPosition The top-level pattern position this is under
 * @param bindingPosition Current binding position counter
 * @param totalVars Total number of variables bound by all patterns
 * @param result Map to populate
 * @param insidePCtor Whether we're currently inside a PCtor
 * @returns Updated binding position
 */
function collectSmallerVarsFromPattern(
  pattern: TTKPattern,
  patternPosition: number,
  bindingPosition: number,
  totalVars: number,
  result: StructurallySmallerMap,
  insidePCtor: boolean
): number {
  switch (pattern.tag) {
    case 'PVar':
    case 'PWild': {
      // If we're inside a PCtor, this variable is smaller than patternPosition
      if (insidePCtor) {
        // Convert binding position to De Bruijn index
        // De Bruijn index = (total_vars - 1 - binding_position)
        const deBruijnIndex = totalVars - 1 - bindingPosition;
        result.set(deBruijnIndex, patternPosition);
      }
      return bindingPosition + 1;
    }

    case 'PCtor': {
      // All variables inside this PCtor are smaller than patternPosition
      for (const arg of pattern.args) {
        bindingPosition = collectSmallerVarsFromPattern(
          arg,
          patternPosition,
          bindingPosition,
          totalVars,
          result,
          true  // Now we're inside a PCtor
        );
      }
      return bindingPosition;
    }
  }
}

// ============================================================================
// App Spine Extraction from Parent Stack
// ============================================================================

/**
 * Given a parent stack (terms above the current term in the AST) and the current term,
 * extract the App spine if the current position is a Const being applied.
 *
 * The stack grows from root to parent of current node.
 * We walk backwards to collect App nodes, but ONLY those where the current term
 * (or the accumulated App chain) is in the fn position.
 *
 * For example, in `Succ (Succ (f x))`, when at `f`:
 * - Parent is App(f, x), f is the fn, so collect x
 * - Grandparent is App(Succ, App(f,x)), App(f,x) is the arg NOT fn, so stop
 * This correctly gives us [x] as the args to f.
 *
 * @param currentTerm The current term we're visiting (typically a Const)
 * @param parentStack Stack of parent terms (stack[0] is root, stack[length-1] is immediate parent)
 * @returns The arguments being applied, or null if not in an App spine
 */
export function extractAppSpineFromParentStack(currentTerm: TTKTerm, parentStack: TTKTerm[]): TTKTerm[] | null {
  const args: TTKTerm[] = [];

  // The term we expect to be in the fn position, starting with currentTerm
  let expectedFn: TTKTerm = currentTerm;

  // Walk backwards from immediate parent
  for (let i = parentStack.length - 1; i >= 0; i--) {
    const parent = parentStack[i];
    if (parent.tag === 'App' && parent.fn === expectedFn) {
      // This App applies to our term/chain, collect the arg
      args.push(parent.arg);
      // Now the whole App becomes what we expect in the fn position above
      expectedFn = parent;
    } else {
      // Either not an App, or our term is the arg (not fn), stop collecting
      break;
    }
  }

  return args.length > 0 ? args : null;
}

// ============================================================================
// Index Path Segments (matching term.ts conventions)
// ============================================================================

const AppPartIndex = {
  Fn: fieldSeg('fn'),
  Arg: fieldSeg('arg'),
};

const BinderPartSegment = {
  Domain: fieldSeg('domain'),
  Body: fieldSeg('body'),
  Value: fieldSeg('value'),
};

const AnnotPartIndex = {
  Term: fieldSeg('term'),
  Type: fieldSeg('type'),
};

const MatchPartIndex = {
  Scrutinee: fieldSeg('scrutinee'),
  Clauses: fieldSeg('clauses'),
};

const ClausePartIndex = {
  Rhs: fieldSeg('rhs'),
};

// ============================================================================
// Term Visitor with Parent Stack and Index Path
// ============================================================================

/**
 * Visitor function type for visiting terms with parent stack and index path context.
 * @param term The current term being visited
 * @param parentStack Stack of parent terms (excludes current term)
 * @param indexPath The index path to this term within the root term
 */
export type TermVisitorWithStack = (term: TTKTerm, parentStack: TTKTerm[], indexPath: IndexPath) => void;

/**
 * Visit all subterms of a term in pre-order, passing the parent stack and index path to the visitor.
 * The parent stack is the path from root to the parent of the current node.
 *
 * @param term The term to visit
 * @param visitor Function to call for each subterm
 * @param parentStack Current parent stack (initially empty)
 * @param indexPath Current index path (initially empty)
 */
export function visitTermWithParentStack(
  term: TTKTerm,
  visitor: TermVisitorWithStack,
  parentStack: TTKTerm[] = [],
  indexPath: IndexPath = []
): void {
  // First, visit the current term
  visitor(term, parentStack, indexPath);

  // Then recursively visit children with updated stack
  const newStack = [...parentStack, term];

  switch (term.tag) {
    case 'Var':
    case 'Sort':
    case 'Const':
    case 'Hole':
    case 'Meta':
    case 'ULevel':
      // No children
      break;

    case 'Binder':
      visitTermWithParentStack(term.domain, visitor, newStack, [...indexPath, BinderPartSegment.Domain]);
      visitTermWithParentStack(term.body, visitor, newStack, [...indexPath, BinderPartSegment.Body]);
      if (term.binderKind.tag === 'BLet') {
        visitTermWithParentStack(term.binderKind.defVal, visitor, newStack, [...indexPath, BinderPartSegment.Value]);
      }
      break;

    case 'App':
      visitTermWithParentStack(term.fn, visitor, newStack, [...indexPath, AppPartIndex.Fn]);
      visitTermWithParentStack(term.arg, visitor, newStack, [...indexPath, AppPartIndex.Arg]);
      break;

    case 'Annot':
      visitTermWithParentStack(term.term, visitor, newStack, [...indexPath, AnnotPartIndex.Term]);
      visitTermWithParentStack(term.type, visitor, newStack, [...indexPath, AnnotPartIndex.Type]);
      break;

    case 'Match':
      visitTermWithParentStack(term.scrutinee, visitor, newStack, [...indexPath, MatchPartIndex.Scrutinee]);
      for (let i = 0; i < term.clauses.length; i++) {
        visitTermWithParentStack(
          term.clauses[i].rhs,
          visitor,
          newStack,
          [...indexPath, MatchPartIndex.Clauses, arraySeg(i), ClausePartIndex.Rhs]
        );
      }
      break;
  }
}

// ============================================================================
// Binder Depth Computation
// ============================================================================

/**
 * Compute how many binder bodies we've entered to reach the current term.
 * This is needed because de Bruijn indices are shifted by each enclosing binder,
 * so when checking recursive call arguments against the structurally-smaller map
 * (which uses pattern-level indices), we must adjust for the depth offset.
 *
 * Only binder BODIES increase depth (not domains or let defVals), since only
 * the body introduces a new variable in scope.
 *
 * @param parentStack Stack of parent terms (from root to immediate parent)
 * @param currentTerm The term we're currently visiting
 */
export function computeBinderDepth(parentStack: TTKTerm[], currentTerm: TTKTerm): number {
  let depth = 0;
  for (let i = 0; i < parentStack.length; i++) {
    const parent = parentStack[i];
    const child = (i < parentStack.length - 1) ? parentStack[i + 1] : currentTerm;
    if (parent.tag === 'Binder' && parent.body === child) {
      depth++;
    }
  }
  return depth;
}

// ============================================================================
// Recursive Call Site Checking
// ============================================================================

/**
 * Check if a single recursive call site is valid (structurally decreasing).
 *
 * A call is valid if at least one argument at position i is:
 * - A Var with De Bruijn index k, where (k - binderDepth) is smaller than pattern position i
 *
 * The binderDepth adjustment accounts for let/lambda binders that shift de Bruijn
 * indices relative to the pattern-level indices in the smallerMap.
 *
 * @param args The arguments applied to the recursive function
 * @param smallerMap Map of De Bruijn indices that are structurally smaller
 * @param contextNames Variable names for error reporting
 * @param binderDepth Number of binder bodies between the clause RHS root and this call site
 */
export function checkRecursiveCallSite(
  args: TTKTerm[],
  smallerMap: StructurallySmallerMap,
  contextNames: string[],
  binderDepth: number = 0
): CallSiteCheckResult {
  // Check each argument position
  for (let i = 0; i < args.length; i++) {
    const arg = args[i];

    // β-reduce the argument to whnf before checking
    // This handles cases like `(\x => x) m` which should reduce to `m`
    const reducedArg = whnf(arg);

    // Check if the reduced argument is a Var
    if (reducedArg.tag === 'Var') {
      const varIndex = reducedArg.index;
      // Adjust for binder depth: pattern-level index = varIndex - binderDepth
      const adjustedIndex = varIndex - binderDepth;
      if (adjustedIndex >= 0) {
        const smallerThanPos = smallerMap.get(adjustedIndex);

        // If this variable is smaller than position i, the call is valid
        if (smallerThanPos === i) {
          return {
            isValid: true,
            decreasingArgPosition: i
          };
        }
      }
    }
  }

  // No valid decreasing argument found
  const argsStr = args.map(a => prettyPrint(a, contextNames)).join(', ');
  return {
    isValid: false,
    error: `Recursive call with arguments (${argsStr}) is not structurally decreasing. No argument is smaller than the corresponding pattern position.`
  };
}

// ============================================================================
// Clause Recursion Checking
// ============================================================================

/**
 * Find all recursive call sites in a clause RHS.
 */
export function findRecursiveCallSites(
  rhs: TTKTerm,
  functionName: string
): RecursiveCallSite[] {
  const callSites: RecursiveCallSite[] = [];

  visitTermWithParentStack(rhs, (term, parentStack, indexPath) => {
    if (term.tag === 'Const' && term.name === functionName) {
      // Found a reference to the recursive function
      const args = extractAppSpineFromParentStack(term, parentStack);

      // Only record if there are arguments (a bare Const with no args is also invalid,
      // but extractAppSpineFromParentStack returns null in that case)
      if (args !== null) {
        callSites.push({ args, parentStack: [...parentStack], constTerm: term, indexPath: [...indexPath] });
      } else {
        // Bare Const reference with zero args - still a call site (invalid one)
        callSites.push({ args: [], parentStack: [...parentStack], constTerm: term, indexPath: [...indexPath] });
      }
    }
  });

  return callSites;
}

/**
 * Check structural recursion for a single clause.
 */
export function checkClauseRecursion(
  clause: TTKClause,
  clauseIndex: number,
  functionName: string
): ClauseRecursionResult {
  const smallerMap = buildStructurallySmallerMap(clause.patterns);
  const callSites = findRecursiveCallSites(clause.rhs, functionName);
  const errors: RecursionError[] = [];
  const contextNames = clause.contextNames ?? collectPatternVars(clause.patterns).reverse();

  for (const callSite of callSites) {
    const binderDepth = computeBinderDepth(callSite.parentStack, callSite.constTerm);
    const result = checkRecursiveCallSite(callSite.args, smallerMap, contextNames, binderDepth);
    if (!result.isValid && result.error) {
      errors.push({
        message: result.error,
        rhsPath: callSite.indexPath
      });
    }
  }

  return {
    clauseIndex,
    isValid: errors.length === 0,
    callSites,
    errors
  };
}

// ============================================================================
// Top-Level Recursion Checking
// ============================================================================

/**
 * Check structural recursion for all clauses of a function.
 *
 * @param functionName Name of the function being defined
 * @param clauses The checked clauses with patterns and RHS
 * @returns Result indicating whether all recursive calls are valid
 */
export function checkStructuralRecursion(
  functionName: string,
  clauses: TTKClause[]
): StructuralRecursionResult {
  const clauseResults: ClauseRecursionResult[] = [];
  const allErrors: Array<{ clauseIndex: number; error: RecursionError }> = [];

  for (let i = 0; i < clauses.length; i++) {
    const result = checkClauseRecursion(clauses[i], i, functionName);
    clauseResults.push(result);
    for (const error of result.errors) {
      allErrors.push({ clauseIndex: i, error });
    }
  }

  const isValid = allErrors.length === 0;

  // Log results
  if (loggingEnabled && allErrors.length > 0) {
    console.log(`\n[Recursion] Structural recursion check for '${functionName}':`);
    for (const { clauseIndex, error } of allErrors) {
      console.log(`  ERROR: Clause ${clauseIndex}: ${error.message}`);
    }
  }

  return {
    isValid,
    clauseResults,
    errors: allErrors
  };
}
