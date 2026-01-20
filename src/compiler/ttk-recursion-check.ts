/**
 * Structural Recursion Analysis for TTK (Kernel Terms)
 *
 * This module analyzes recursive calls in kernel term definitions to determine
 * if they are structurally recursive (guaranteed to terminate) or potentially unsafe.
 *
 * IMPORTANT: This operates on TTKTerm (kernel terms), not TTerm (surface terms).
 * All verification passes should happen in the kernel layer.
 *
 * ## The Algorithm (based on Coq's guard condition and Abel's foetus)
 *
 * 1. When we pattern match on variable `x` with pattern `C(y₁, ..., yₙ)`,
 *    each `yᵢ` becomes **structurally smaller** than `x`.
 *
 * 2. A recursive call is **safe** if at least one argument position contains
 *    a term that is **structurally smaller** than the corresponding original
 *    pattern-matched variable.
 *
 * 3. "Structurally smaller" is defined inductively:
 *    - A variable bound by a constructor pattern is structurally smaller
 *    - If `t` is structurally smaller, then `(t u)` and `λ_.t` are too
 *
 * ## References
 * - Coq Reference Manual: Guard Condition (rocq-prover.org)
 * - Abel, A. "foetus - Termination Checker for Simple Functional Programs"
 * - Agda Documentation: Termination Checking
 */

import { TTKTerm, TTKClause, TTKPattern } from './kernel';
import { IndexPath } from '../types/source-position';

/**
 * Path segment type for term traversal
 */
type TermPathSegment = 'domain' | 'body' | 'defVal' | 'fn' | 'arg' | 'type' | 'term' | 'scrutinee' | 'clauses' | 'rhs' | number;
type TermPath = TermPathSegment[];

/**
 * Information about an unsafe recursive call.
 */
export interface UnsafeRecursion {
  /** Path to the unsafe recursive call (internal format) */
  termPath: TermPath;
  /** Human-readable error message explaining why it's unsafe */
  error: string;
}

/**
 * Result of analyzing recursion in a term.
 */
export interface RecursionAnalysis {
  /** Paths to safe structurally recursive calls */
  safeRecursion: TermPath[];
  /** Paths to unsafe recursive calls with error messages */
  unsafeRecursion: UnsafeRecursion[];
}

/**
 * Tracks which variables are structurally smaller than the original scrutinee.
 * Key: De Bruijn index of a variable that is structurally smaller
 * Value: true (just using as a set)
 */
type StructurallySmaller = Set<number>;

/**
 * Context for tracking pattern-bound variables during traversal.
 */
interface RecursionContext {
  /** Variables that are structurally smaller than the original argument */
  structurallySmaller: StructurallySmaller;
  /** The name of the function being defined (to detect self-calls) */
  functionName: string;
  /** Current depth (number of binders traversed) */
  depth: number;
}

/**
 * Analyze a kernel term definition for recursive calls.
 *
 * @param functionName - The name of the function being defined
 * @param body - The body of the function definition (kernel term)
 * @returns Analysis of safe and unsafe recursive calls
 */
export function analyzeRecursionTTK(
  functionName: string,
  body: TTKTerm
): RecursionAnalysis {
  const safe: TermPath[] = [];
  const unsafe: UnsafeRecursion[] = [];

  const context: RecursionContext = {
    structurallySmaller: new Set(),
    functionName,
    depth: 0,
  };

  analyzeRecursionHelper(body, [], context, safe, unsafe);

  return {
    safeRecursion: safe,
    unsafeRecursion: unsafe,
  };
}

/**
 * Convert internal TermPath to IndexPath for error reporting
 */
export function termPathToIndexPath(termPath: TermPath): IndexPath {
  return termPath.map(segment =>
    typeof segment === 'number'
      ? { kind: 'array' as const, index: segment }
      : { kind: 'field' as const, name: segment }
  );
}

/**
 * Helper function for recursion analysis.
 * Traverses the term tree and identifies recursive calls.
 */
function analyzeRecursionHelper(
  term: TTKTerm,
  currentPath: TermPath,
  context: RecursionContext,
  safe: TermPath[],
  unsafe: UnsafeRecursion[]
): void {
  switch (term.tag) {
    case 'Var':
    case 'Sort':
    case 'Hole':
    case 'Meta':
      // No recursion possible
      break;

    case 'Const':
      // Check if this is a recursive call (unapplied reference)
      if (term.name === context.functionName) {
        // This is a self-reference, but not applied - potentially unsafe
        unsafe.push({
          termPath: currentPath,
          error: `Direct reference to '${context.functionName}' without application`,
        });
      }
      break;

    case 'App': {
      // Check if this is a recursive call
      const isRecursiveCall = isRecursiveApplication(term, context.functionName);

      if (isRecursiveCall) {
        // Extract the arguments to check if they're structurally smaller
        const args = extractApplicationArgs(term);
        const checkResult = checkStructuralRecursion(args, context);

        if (checkResult.isSafe) {
          safe.push(currentPath);
        } else {
          unsafe.push({
            termPath: currentPath,
            error: checkResult.error,
          });
        }

        // Still traverse arguments to find any nested recursive calls
        // (e.g., f (f x) has two recursive calls)
        for (const arg of args) {
          analyzeRecursionHelper(arg, [...currentPath, 'arg'], context, safe, unsafe);
        }
      } else {
        // Not a recursive call, traverse normally
        analyzeRecursionHelper(
          term.fn,
          [...currentPath, 'fn'],
          context,
          safe,
          unsafe
        );
        analyzeRecursionHelper(
          term.arg,
          [...currentPath, 'arg'],
          context,
          safe,
          unsafe
        );
      }
      break;
    }

    case 'Binder': {
      // Traverse domain
      analyzeRecursionHelper(
        term.domain,
        [...currentPath, 'domain'],
        context,
        safe,
        unsafe
      );

      // Enter body with incremented depth
      // Shift all structurally smaller indices up by 1 since we're going under a binder
      const shiftedSmaller = new Set<number>();
      for (const idx of context.structurallySmaller) {
        shiftedSmaller.add(idx + 1);
      }

      const newContext: RecursionContext = {
        ...context,
        structurallySmaller: shiftedSmaller,
        depth: context.depth + 1,
      };

      analyzeRecursionHelper(
        term.body,
        [...currentPath, 'body'],
        newContext,
        safe,
        unsafe
      );

      // Also check defVal for let bindings
      if (term.binderKind.tag === 'BLet') {
        analyzeRecursionHelper(
          term.binderKind.defVal,
          [...currentPath, 'defVal'],
          context,
          safe,
          unsafe
        );
      }
      break;
    }

    case 'Match': {
      // Analyze scrutinee
      analyzeRecursionHelper(
        term.scrutinee,
        [...currentPath, 'scrutinee'],
        context,
        safe,
        unsafe
      );

      // Check if scrutinee is a variable - if so, pattern-bound variables are smaller
      const scrutineeVar = getScrutineeVariable(term.scrutinee);

      // Check if scrutinee is a Hole - this happens at the top level of function definitions
      // with pattern matching (e.g., `plus Zero b = b`). In this case, the Hole represents
      // the function arguments being matched, and constructor pattern variables ARE smaller.
      const scrutineeIsHole = term.scrutinee.tag === 'Hole';

      // Analyze each clause
      for (let i = 0; i < term.clauses.length; i++) {
        const clause = term.clauses[i];
        const clausePath: TermPath = [...currentPath, 'clauses', i];

        // Count how many variables are bound by all patterns
        const numPatternVars = countPatternVariables(clause.patterns);

        // Create new context with pattern-bound variables marked as structurally smaller
        // The pattern variables get indices 0, 1, 2, ... (numPatternVars-1) in the RHS
        // But only if we're matching on something that could decrease
        const clauseSmaller = new Set<number>();

        // Shift existing structurally smaller indices
        for (const idx of context.structurallySmaller) {
          clauseSmaller.add(idx + numPatternVars);
        }

        // If the scrutinee is a variable, Hole (top-level pattern match), or structurally smaller,
        // then constructor pattern variables are structurally smaller
        if (scrutineeVar !== undefined || scrutineeIsHole || hasStructurallySmallerScrutinee(term.scrutinee, context)) {
          // Mark variables bound by constructor patterns as structurally smaller
          // IMPORTANT: De Bruijn indices are assigned right-to-left, so the rightmost
          // pattern variable gets index 0, and indices increase as we go left.
          // We need to calculate offsets correctly.
          //
          // For patterns [P1, P2] where P1 binds vars at local indices 0..m-1
          // and P2 binds vars at local indices 0..n-1:
          // - P2's vars get De Bruijn indices 0..n-1
          // - P1's vars get De Bruijn indices n..n+m-1
          //
          // Strategy: process patterns right-to-left
          let varIndex = 0;
          for (let patIdx = clause.patterns.length - 1; patIdx >= 0; patIdx--) {
            const pattern = clause.patterns[patIdx];
            varIndex = markPatternVarsAsSmaller(pattern, varIndex, clauseSmaller);
          }
        }

        const clauseContext: RecursionContext = {
          ...context,
          structurallySmaller: clauseSmaller,
          depth: context.depth + numPatternVars,
        };

        // Analyze clause RHS
        analyzeRecursionHelper(
          clause.rhs,
          [...clausePath, 'rhs'],
          clauseContext,
          safe,
          unsafe
        );
      }
      break;
    }

    case 'Annot':
      analyzeRecursionHelper(
        term.term,
        [...currentPath, 'term'],
        context,
        safe,
        unsafe
      );
      analyzeRecursionHelper(
        term.type,
        [...currentPath, 'type'],
        context,
        safe,
        unsafe
      );
      break;

    default:
      const _exhaustive: never = term;
      break;
  }
}

/**
 * Check if an application is a recursive call to the function being defined.
 */
function isRecursiveApplication(app: TTKTerm, functionName: string): boolean {
  let fn = app;
  while (fn.tag === 'App') {
    fn = fn.fn;
  }
  return fn.tag === 'Const' && fn.name === functionName;
}

/**
 * Extract all arguments from a curried application.
 * Returns arguments in order (leftmost first).
 */
function extractApplicationArgs(app: TTKTerm): TTKTerm[] {
  const args: TTKTerm[] = [];
  let current = app;
  while (current.tag === 'App') {
    args.unshift(current.arg);
    current = current.fn;
  }
  return args;
}

/**
 * If the term is a variable, return its index. Otherwise undefined.
 */
function getScrutineeVariable(term: TTKTerm): number | undefined {
  if (term.tag === 'Var') {
    return term.index;
  }
  return undefined;
}

/**
 * Check if the scrutinee is structurally smaller than the original argument.
 */
function hasStructurallySmallerScrutinee(term: TTKTerm, context: RecursionContext): boolean {
  return isStructurallySmaller(term, context);
}

/**
 * Check if a term is structurally smaller than the original argument.
 *
 * A term is structurally smaller if:
 * - It's a variable in the structurallySmaller set
 * - It's an application (t u) where t is structurally smaller
 * - It's a lambda where the body is structurally smaller (after shifting)
 */
function isStructurallySmaller(term: TTKTerm, context: RecursionContext): boolean {
  switch (term.tag) {
    case 'Var':
      return context.structurallySmaller.has(term.index);

    case 'App':
      // (t u) is structurally smaller if t is
      return isStructurallySmaller(term.fn, context);

    case 'Binder':
      if (term.binderKind.tag === 'BLam') {
        // λ_.t is structurally smaller if t is (with shifted indices)
        const shiftedSmaller = new Set<number>();
        for (const idx of context.structurallySmaller) {
          shiftedSmaller.add(idx + 1);
        }
        const shiftedContext = { ...context, structurallySmaller: shiftedSmaller };
        return isStructurallySmaller(term.body, shiftedContext);
      }
      return false;

    default:
      return false;
  }
}

/**
 * Count total variables bound by a list of kernel patterns.
 */
function countPatternVariables(patterns: TTKPattern[]): number {
  let count = 0;
  for (const pattern of patterns) {
    count += countPatternVarsHelper(pattern);
  }
  return count;
}

function countPatternVarsHelper(pattern: TTKPattern): number {
  switch (pattern.tag) {
    case 'PVar':
    case 'PWild':
      return 1;
    case 'PCtor':
      // With uniform identifier parsing, a PCtor with no args is treated as a variable
      if (pattern.args.length === 0) {
        return 1;
      }
      // Otherwise, count variables in arguments
      let count = 0;
      for (const arg of pattern.args) {
        count += countPatternVarsHelper(arg);
      }
      return count;
  }
}

/**
 * Mark pattern variables as structurally smaller.
 * Only variables from CONSTRUCTOR patterns are marked (not top-level variable patterns).
 *
 * @param pattern - The pattern to process
 * @param startIndex - The starting De Bruijn index for variables in this pattern
 * @param smaller - Set to add structurally smaller indices to
 * @returns The next available index after processing this pattern
 */
function markPatternVarsAsSmaller(
  pattern: TTKPattern,
  startIndex: number,
  smaller: Set<number>
): number {
  switch (pattern.tag) {
    case 'PVar':
    case 'PWild':
      // A top-level variable pattern (including wildcards) does NOT make the variable
      // structurally smaller. It's just binding the scrutinee itself.
      // All PVars/PWild consume one index slot.
      return startIndex + 1;

    case 'PCtor':
      // With uniform identifier parsing, a top-level PCtor with no args is a variable pattern.
      // Like PVar, it does NOT make the variable structurally smaller, but it consumes a slot.
      if (pattern.args.length === 0) {
        return startIndex + 1;
      }
      // Constructor pattern: all nested variables ARE structurally smaller
      let index = startIndex;
      for (const arg of pattern.args) {
        index = markCtorPatternVarsAsSmaller(arg, index, smaller);
      }
      return index;
  }
}

/**
 * Mark all variables in a pattern as structurally smaller.
 * Used for variables inside constructor patterns.
 */
function markCtorPatternVarsAsSmaller(
  pattern: TTKPattern,
  startIndex: number,
  smaller: Set<number>
): number {
  switch (pattern.tag) {
    case 'PVar':
    case 'PWild':
      // This variable (including wildcards) is inside a constructor pattern,
      // so it's structurally smaller. All PVars/PWild consume one index slot.
      smaller.add(startIndex);
      return startIndex + 1;

    case 'PCtor':
      // With uniform identifier parsing, a PCtor with no args that's not a known
      // constructor is treated as a variable binding.
      if (pattern.args.length === 0) {
        // Treat as a variable - mark it as structurally smaller
        smaller.add(startIndex);
        return startIndex + 1;
      }
      // Otherwise, it's a real constructor - process its arguments
      let index = startIndex;
      for (const arg of pattern.args) {
        index = markCtorPatternVarsAsSmaller(arg, index, smaller);
      }
      return index;
  }
}

/**
 * Check if a recursive call is structurally recursive.
 *
 * A call is safe if at least one argument is structurally smaller than
 * the corresponding parameter.
 */
function checkStructuralRecursion(
  args: TTKTerm[],
  context: RecursionContext
): { isSafe: boolean; error: string } {
  // Check if any argument is structurally smaller
  for (let i = 0; i < args.length; i++) {
    const arg = args[i];
    if (isStructurallySmaller(arg, context)) {
      return { isSafe: true, error: '' };
    }
  }

  // No structurally smaller argument found
  // Generate a helpful error message
  if (context.structurallySmaller.size === 0) {
    return {
      isSafe: false,
      error: 'Recursive call outside of pattern matching context (no structurally smaller variables available)',
    };
  }

  // Check what's wrong with each argument
  const argDescriptions: string[] = [];
  for (let i = 0; i < args.length; i++) {
    const arg = args[i];
    if (arg.tag === 'Var') {
      if (!context.structurallySmaller.has(arg.index)) {
        argDescriptions.push(`argument ${i + 1} is not structurally smaller than the pattern`);
      }
    } else {
      argDescriptions.push(`argument ${i + 1} is not a subterm of the pattern-matched variable`);
    }
  }

  return {
    isSafe: false,
    error: `Recursive call does not decrease structurally: ${argDescriptions.join('; ')}`,
  };
}
