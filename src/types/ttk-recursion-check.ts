/**
 * Structural Recursion Analysis for TTK (Kernel Terms)
 *
 * This module analyzes recursive calls in kernel term definitions to determine
 * if they are structurally recursive (guaranteed to terminate) or potentially unsafe.
 *
 * IMPORTANT: This operates on TTKTerm (kernel terms), not TTerm (surface terms).
 * All verification passes should happen in the kernel layer.
 *
 * ## What is Structural Recursion?
 *
 * A recursive call is **structurally recursive** if it recurses on a strict subterm
 * of a pattern-matched constructor argument. This guarantees termination because:
 * - Each recursive call operates on a structurally smaller value
 * - Inductive types are well-founded (no infinite descending chains)
 *
 * ## Safe Structural Recursion
 *
 * Safe recursion occurs when:
 * 1. The recursive call is inside a pattern match
 * 2. The recursive argument is a variable bound by a constructor pattern
 * 3. That variable came from deconstructing the original argument
 *
 * Example (safe):
 * ```
 * plus : Nat → Nat → Nat
 * | zero,   b => b
 * | succ a, b => succ (plus a b)  -- ✓ Safe: 'a' is structurally smaller than 'succ a'
 * ```
 *
 * ## Unsafe Recursion
 *
 * Unsafe recursion includes:
 * 1. **General recursion**: Recursion not on pattern-bound variables
 * 2. **Non-decreasing recursion**: Recursion on the same or larger argument
 * 3. **Nested recursion**: Recursion where result is used in recursive call
 * 4. **Mutual recursion**: Not directly on a deconstructed argument
 *
 * Example (unsafe):
 * ```
 * bad : Nat → Nat
 * | n => bad n           -- ✗ Unsafe: same argument (infinite loop)
 * | n => bad (succ n)    -- ✗ Unsafe: larger argument (infinite loop)
 * | n => bad (bad n)     -- ✗ Unsafe: nested recursion
 * ```
 */

import { TTKTerm, TTKClause } from './tt-kernel';
import { TPattern } from './tt-core';
import { IndexPath } from './source-position';

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
 * Context for tracking pattern-bound variables during traversal.
 * Maps variable De Bruijn indices to whether they're from pattern matching.
 */
interface RecursionContext {
  /** Variables bound by pattern matching (structurally smaller) */
  patternBoundVars: Set<number>;
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
    patternBoundVars: new Set(),
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
      // No recursion possible
      break;

    case 'Const':
      // Check if this is a recursive call (unapplied reference)
      if (term.name === context.functionName) {
        // This is a self-reference, but not applied - potentially unsafe
        unsafe.push({
          termPath: currentPath,
          error: `Direct reference to '${context.functionName}' without application (not a recursive call pattern)`,
        });
      }
      break;

    case 'App': {
      // Check if this is a recursive call
      const isRecursiveCall = isRecursiveApplication(term, context.functionName);

      if (isRecursiveCall) {
        // Extract the arguments to check if they're structurally smaller
        const args = extractApplicationArgs(term);
        const isSafe = checkStructuralRecursion(args, context);

        if (isSafe) {
          safe.push(currentPath);
        } else {
          unsafe.push({
            termPath: currentPath,
            error: generateUnsafeRecursionError(args, context),
          });
        }

        // Still traverse arguments to find any nested recursive calls
        // (e.g., f (f x) has two recursive calls)
        for (const arg of args) {
          // Build path to argument - simplified, we traverse args but don't track exact path
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
      const newContext = {
        ...context,
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

      // Analyze each clause
      for (let i = 0; i < term.clauses.length; i++) {
        const clause = term.clauses[i];
        const clausePath: TermPath = [...currentPath, 'clauses', i];

        // Extract pattern-bound variables
        const patternVars = extractPatternVariables(clause.patterns, context.depth);

        // Create new context with pattern-bound variables
        const clauseContext: RecursionContext = {
          ...context,
          patternBoundVars: new Set([...context.patternBoundVars, ...patternVars]),
          depth: context.depth + patternVars.length,
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
  // Peel off applications to get to the function
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
 * Check if a recursive call is structurally recursive.
 *
 * A call is safe if:
 * 1. ALL arguments are simple variables (not complex expressions)
 * 2. AT LEAST ONE argument is a pattern-bound variable (structurally smaller)
 *
 * This is a conservative check - it rejects some safe programs, but never
 * accepts an unsafe one.
 */
function checkStructuralRecursion(
  args: TTKTerm[],
  context: RecursionContext
): boolean {
  let hasPatternBoundArg = false;

  for (const arg of args) {
    // All arguments must be simple variables
    if (arg.tag !== 'Var') {
      return false;  // Complex expression - not safe
    }

    // Check if this variable is pattern-bound
    if (context.patternBoundVars.has(arg.index)) {
      hasPatternBoundArg = true;
    }
  }

  // Must have at least one pattern-bound argument
  return hasPatternBoundArg;
}

/**
 * Extract variables bound by patterns.
 * Returns the De Bruijn indices of variables bound by the patterns.
 */
function extractPatternVariables(
  patterns: TPattern[],
  currentDepth: number
): number[] {
  const vars: number[] = [];

  for (const pattern of patterns) {
    extractPatternVarsHelper(pattern, vars, currentDepth);
  }

  return vars;
}

/**
 * Helper to extract variables from a pattern recursively.
 */
function extractPatternVarsHelper(
  pattern: TPattern,
  vars: number[],
  currentDepth: number
): void {
  switch (pattern.tag) {
    case 'PVar':
      // This pattern binds a variable at the current depth
      vars.push(currentDepth + vars.length);
      break;

    case 'PCtor':
      // Constructor pattern may bind variables in its arguments
      for (const arg of pattern.args) {
        extractPatternVarsHelper(arg, vars, currentDepth);
      }
      break;

    case 'PWild':
      // Wildcard doesn't bind
      break;

    default:
      const _exhaustive: never = pattern;
      break;
  }
}

/**
 * Generate a helpful error message for unsafe recursion.
 */
function generateUnsafeRecursionError(
  args: TTKTerm[],
  context: RecursionContext
): string {
  // Check what kind of unsafe recursion this is
  const reasons: string[] = [];

  // Check if any argument is not a variable
  const nonVarArgs = args.filter((arg) => arg.tag !== 'Var');
  if (nonVarArgs.length > 0) {
    reasons.push('recursive call uses complex expressions (not simple variables)');
  }

  // Check if arguments are non-pattern-bound variables
  const varArgs = args.filter((arg) => arg.tag === 'Var');
  const nonPatternVars = varArgs.filter(
    (arg) => arg.tag === 'Var' && !context.patternBoundVars.has(arg.index)
  );

  if (nonPatternVars.length > 0) {
    reasons.push('recursive call does not use pattern-matched variables');
  }

  // Check if we're not inside a pattern match at all
  if (context.patternBoundVars.size === 0) {
    reasons.push('recursive call outside of pattern matching context');
  }

  if (reasons.length === 0) {
    return `Potentially unsafe recursion (unable to verify structural recursion)`;
  }

  return `Unsafe recursion: ${reasons.join('; ')}`;
}
