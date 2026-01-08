/**
 * Type Query System
 *
 * This module provides APIs to query the type of expressions at specific paths
 * in ASTs. The architecture is layered:
 *
 * 1. Core API: Query type by IndexPath in kernel term + context
 * 2. Source Resolution (separate module): Map source selection → IndexPath
 * 3. UI (separate module): Display selected expression and its type
 *
 * This design allows type queries on machine-assembled ASTs that never have source.
 */

import { TTKTerm, TTKContext, TTKClause, prettyPrint } from './tt-kernel';
import type { TPattern } from './tt-core';
import { inferType, extendContext } from './tt-typecheck';
import { IndexPath, serializeIndexPath } from './source-position';
import type { FunctionClausesResult, ClauseCheckResult } from './tt-pattern-elab';
import { Substitution, applySubstitution } from './tt-unify';

// ============================================================================
// Elaboration Context for Solved Types
// ============================================================================

/**
 * Optional elaboration context that contains solved/unified type information.
 * When provided, type queries will return the "solved" types with unification
 * results applied, rather than the original telescope types.
 *
 * For example, given:
 *   foo : (a : Nat) -> (b : Nat) -> Equal Nat a b -> Nat
 *   foo a b eq = Zero
 *
 * Without elaboration context: eq has type "Equal Nat a b"
 * With elaboration context:    eq has type "Equal Nat a a" (unification solved b = a)
 */
export interface ElaborationContext {
  /**
   * Per-clause elaboration results. Index corresponds to clause index in Match.
   * Each result contains solved bindings with substitutions already applied.
   */
  clauseResults?: ClauseCheckResult[];

  /**
   * The full function type being matched against.
   * Used to correlate patterns with telescope positions.
   */
  functionType?: TTKTerm;
}

// ============================================================================
// Pattern Binding Counting
// ============================================================================

/**
 * Count the number of bindings introduced by a pattern.
 * Variable patterns bind 1, wildcards bind 1 (for telescope purposes),
 * constructor patterns bind the sum of their argument patterns.
 */
function countPatternBindings(pattern: TPattern): number {
  switch (pattern.tag) {
    case 'PVar':
      // All PVars (including wildcards like _w0, _w1) count as one binding
      return 1;
    case 'PCtor':
      if (pattern.args.length === 0) {
        // Zero-arg constructor treated as variable binding
        return 1;
      }
      return pattern.args.reduce((sum, arg) => sum + countPatternBindings(arg), 0);
  }
}

// ============================================================================
// Type Utilities
// ============================================================================

/**
 * Check if a type contains any holes at the "value level".
 * Used to determine if we should prefer an expected type over an inferred type.
 *
 * This checks for holes that would appear in the displayed type, NOT holes in
 * type annotations of constants (e.g., `Nat` is represented as `Const("Nat", Hole("Nat_type"))`
 * but we don't consider this a hole in the type - `Nat` is a concrete type).
 */
function typeContainsHoles(type: TTKTerm): boolean {
  switch (type.tag) {
    case 'Hole':
      return true;
    case 'Binder':
      return typeContainsHoles(type.domain) || typeContainsHoles(type.body);
    case 'App':
      return typeContainsHoles(type.fn) || typeContainsHoles(type.arg);
    case 'Annot':
      return typeContainsHoles(type.term) || typeContainsHoles(type.type);
    case 'Const':
      // Don't check const.type - that's the "sort" annotation, not part of the value type
      // e.g., Nat is Const("Nat", Hole("Nat_type")) but Nat is a concrete type
      return false;
    case 'Match':
      if (typeContainsHoles(type.scrutinee)) return true;
      return type.clauses.some(c => typeContainsHoles(c.rhs));
    case 'Var':
    case 'Sort':
      return false;
  }
}

// ============================================================================
// De Bruijn Index Shifting
// ============================================================================

/**
 * Shift De Bruijn indices in a term by a given amount.
 * Indices >= cutoff are shifted; indices < cutoff are unchanged.
 */
function shiftTerm(term: TTKTerm, amount: number, cutoff: number = 0): TTKTerm {
  switch (term.tag) {
    case 'Var':
      return term.index >= cutoff
        ? { tag: 'Var', index: term.index + amount }
        : term;

    case 'Sort':
    case 'Const':
      return term;

    case 'Binder': {
      const newDomain = shiftTerm(term.domain, amount, cutoff);
      const newBody = shiftTerm(term.body, amount, cutoff + 1);

      let newBinderKind = term.binderKind;
      if (term.binderKind.tag === 'BLet') {
        const newDefVal = shiftTerm(term.binderKind.defVal, amount, cutoff);
        newBinderKind = { tag: 'BLet', defVal: newDefVal };
      }

      return {
        tag: 'Binder',
        name: term.name,
        binderKind: newBinderKind,
        domain: newDomain,
        body: newBody
      };
    }

    case 'App':
      return {
        tag: 'App',
        fn: shiftTerm(term.fn, amount, cutoff),
        arg: shiftTerm(term.arg, amount, cutoff)
      };

    case 'Hole':
      return {
        tag: 'Hole',
        id: term.id,
        type: shiftTerm(term.type, amount, cutoff),
        context: term.context
      };

    case 'Annot':
      return {
        tag: 'Annot',
        term: shiftTerm(term.term, amount, cutoff),
        type: shiftTerm(term.type, amount, cutoff)
      };

    case 'Match':
      return {
        tag: 'Match',
        scrutinee: shiftTerm(term.scrutinee, amount, cutoff),
        clauses: term.clauses.map(c => ({
          patterns: c.patterns,
          rhs: shiftTerm(c.rhs, amount, cutoff)
        }))
      };
  }
}

// ============================================================================
// Canonical Name Resolution
// ============================================================================

/**
 * Build canonical names for pattern bindings based on substitution equivalences.
 *
 * When unification determines that variables are equal (e.g., `i = #3` and `#1 = #3`),
 * we want to display all equivalent variables using the "best" name - preferring
 * named variables over wildcards (#N).
 *
 * Example: bindings = ['i', '_', '_', '_'], substitution has var:3 = Var(0), var:2 = Var(0)
 * This means binding 3 (i) equals binding 0, and binding 2 equals binding 0.
 * The canonical name for all of {0, 2, 3} should be 'i' (the non-wildcard name).
 *
 * @param solvedBindings - The pattern bindings with names
 * @param substitution - The unification substitution
 * @returns Array of canonical names, one per binding
 */
function buildCanonicalNames(
  solvedBindings: Array<{ name: string; type: TTKTerm }>,
  substitution?: Substitution
): string[] {
  const numBindings = solvedBindings.length;
  const result: string[] = solvedBindings.map(b => b.name);

  if (!substitution || substitution.size === 0) {
    return result;
  }

  // Build equivalence classes using union-find
  // parent[i] = j means binding i is equivalent to binding j
  const parent: number[] = [];
  for (let i = 0; i < numBindings; i++) {
    parent[i] = i;
  }

  function find(x: number): number {
    if (parent[x] !== x) {
      parent[x] = find(parent[x]);
    }
    return parent[x];
  }

  function union(x: number, y: number): void {
    const px = find(x);
    const py = find(y);
    if (px !== py) {
      parent[px] = py;
    }
  }

  // Process substitution to build equivalence classes
  // Substitution has var:index -> term, where term is usually Var(anotherIndex)
  for (const [key, value] of substitution.entries()) {
    if (key.startsWith('var:') && value.tag === 'Var') {
      const fromIdx = parseInt(key.slice(4), 10);
      const toIdx = value.index;
      if (fromIdx < numBindings && toIdx < numBindings) {
        // Convert De Bruijn to array index: DB 0 = last, DB n-1 = first
        // solvedBindings[0] = first pattern = De Bruijn (n-1)
        // solvedBindings[n-1] = last pattern = De Bruijn 0
        const fromArrayIdx = numBindings - 1 - fromIdx;
        const toArrayIdx = numBindings - 1 - toIdx;
        if (fromArrayIdx >= 0 && toArrayIdx >= 0) {
          union(fromArrayIdx, toArrayIdx);
        }
      }
    }
  }

  // For each equivalence class, find the "best" name (prefer non-wildcard)
  // Group bindings by their representative
  const groups = new Map<number, number[]>();
  for (let i = 0; i < numBindings; i++) {
    const rep = find(i);
    if (!groups.has(rep)) {
      groups.set(rep, []);
    }
    groups.get(rep)!.push(i);
  }

  // For each group, pick the best name
  for (const indices of groups.values()) {
    let bestName: string | null = null;
    for (const idx of indices) {
      const name = solvedBindings[idx].name;
      // Prefer non-wildcard names (names that don't start with '_' or '#')
      const isWildcard = name === '_' || name.startsWith('#');
      if (!isWildcard) {
        bestName = name;
        break;
      }
    }
    // If all names are wildcards, use the first one
    if (bestName === null) {
      bestName = solvedBindings[indices[0]].name;
    }
    // Apply best name to all in the group
    for (const idx of indices) {
      result[idx] = bestName;
    }
  }

  return result;
}

// ============================================================================
// Pattern Binding Helpers
// ============================================================================

/**
 * Extract the telescope (parameter types) from a Pi type.
 * Returns an array of {name, type} for each parameter.
 */
function extractTelescope(type: TTKTerm): Array<{ name: string; type: TTKTerm }> {
  const telescope: Array<{ name: string; type: TTKTerm }> = [];
  let current = type;
  while (current.tag === 'Binder' && current.binderKind.tag === 'BPi') {
    telescope.push({ name: current.name, type: current.domain });
    current = current.body;
  }
  return telescope;
}

/**
 * Look up a name in the context and return its type.
 */
function lookupInContext(name: string, context: TTKContext): TTKTerm | null {
  for (const binding of context) {
    if (binding.name === name) {
      return binding.type;
    }
  }
  return null;
}

/**
 * Compute the bindings introduced by a pattern given its expected type.
 *
 * For constructor patterns like (Succ a), we look up the constructor type in context
 * to determine the types of nested pattern variables.
 */
function computePatternBindings(
  pattern: TPattern,
  expectedType: TTKTerm,
  context: TTKContext
): Array<{ name: string; type: TTKTerm }> {
  switch (pattern.tag) {
    case 'PVar':
      // All PVars (including wildcards like _w0, _w1) bind their name to the expected type
      return [{ name: pattern.name, type: expectedType }];
    case 'PCtor':
      // For constructor patterns with no args (like type variables A, B),
      // treat as binding that name to the expected type
      if (pattern.args.length === 0) {
        return [{ name: pattern.name, type: expectedType }];
      }

      // For constructor patterns with args, look up the constructor type
      const ctorType = lookupInContext(pattern.name, context);
      if (ctorType) {
        // Extract the telescope from the constructor type
        const ctorTelescope = extractTelescope(ctorType);

        const bindings: Array<{ name: string; type: TTKTerm }> = [];
        for (let i = 0; i < pattern.args.length; i++) {
          const argPattern = pattern.args[i];
          // Use the corresponding telescope type if available
          const argType = i < ctorTelescope.length
            ? ctorTelescope[i].type
            : { tag: 'Hole' as const, id: '?', type: { tag: 'Sort' as const, level: 0 }, context: [] };
          bindings.push(...computePatternBindings(argPattern, argType, context));
        }
        return bindings;
      }

      // Fallback: if constructor not found in context, use placeholder types
      const bindings: Array<{ name: string; type: TTKTerm }> = [];
      for (const arg of pattern.args) {
        bindings.push(...computePatternBindings(arg, { tag: 'Hole', id: '?', type: { tag: 'Sort', level: 0 }, context: [] }, context));
      }
      return bindings;
  }
}

/**
 * Compute the context extension for a clause RHS given the patterns and function type.
 *
 * For a function like: swap : (A : Type) -> (f : A -> A -> A) -> (A -> A -> A)
 * with clause: swap A = \f => ...
 *
 * The pattern A binds a variable of type Type (the first parameter type).
 * The RHS is typed with context extended by A : Type.
 */
function computeClauseBindings(
  clause: TTKClause,
  functionType: TTKTerm | undefined,
  baseContext: TTKContext
): TTKContext {
  if (!functionType) {
    // No function type available, can't compute bindings
    return baseContext;
  }

  // Extract the telescope from the function type
  const telescope = extractTelescope(functionType);

  // Match patterns to telescope positions
  let ctx = baseContext;
  let telescopeIndex = 0;

  for (const pattern of clause.patterns) {
    if (telescopeIndex >= telescope.length) {
      // More patterns than telescope entries - shouldn't happen for well-typed code
      break;
    }

    // Get the type for this telescope position
    // The type is relative to bindings already in scope
    const paramType = telescope[telescopeIndex].type;

    // Compute bindings from this pattern, passing the current context for constructor lookup
    const bindings = computePatternBindings(pattern, paramType, ctx);

    // Extend context with pattern bindings
    for (const binding of bindings) {
      ctx = extendContext(ctx, binding.name, binding.type);
    }

    telescopeIndex++;
  }

  return ctx;
}

/**
 * Compute the expected type for a clause RHS by stripping off matched patterns.
 *
 * For a function type: (A : Type) -> (f : A -> A -> A) -> (A -> A -> A)
 * After matching pattern A, the RHS expected type is: (f : A -> A -> A) -> (A -> A -> A)
 *
 * Note: This is an approximation - proper handling would require substitution.
 */
function computeClauseRhsExpectedType(
  clause: TTKClause,
  functionType: TTKTerm | undefined
): TTKTerm | undefined {
  if (!functionType) return undefined;

  let current = functionType;
  for (let i = 0; i < clause.patterns.length; i++) {
    if (current.tag === 'Binder' && current.binderKind.tag === 'BPi') {
      current = current.body;
    } else {
      // No more Pi types to strip
      break;
    }
  }

  return current;
}

/**
 * Query the type of a pattern or a subpattern.
 *
 * Patterns have a different structure than terms:
 * - PVar: a variable pattern, type is the expected type for this position (wildcards are PVar with _wN names)
 * - PCtor: a constructor pattern, type is the expected type; can navigate into args
 *
 * @param pattern - The pattern to query
 * @param expectedType - The expected type for this pattern position
 * @param context - The current context
 * @param path - The full path being navigated
 * @param pathIndex - Current position in the path
 * @param solvedBindings - Optional solved bindings with unification applied
 * @param bindingOffset - Offset into solvedBindings for this pattern's variables
 * @returns TypeQueryResult with a synthetic term representing the pattern
 */
function queryPatternType(
  pattern: TPattern,
  expectedType: TTKTerm,
  context: TTKContext,
  path: IndexPath,
  pathIndex: number,
  solvedBindings?: Array<{ name: string; type: TTKTerm }>,
  bindingOffset: number = 0
): TypeQueryResult {
  // If we've consumed the whole path, return the pattern's type
  if (pathIndex >= path.length) {
    // Create a synthetic term to represent the pattern for display purposes
    let syntheticTerm: TTKTerm;
    let patternType: TTKTerm;

    switch (pattern.tag) {
      case 'PVar':
        // Variable pattern (including wildcards _w0, _w1) - use solved binding type if available
        patternType = expectedType;
        if (solvedBindings && bindingOffset < solvedBindings.length) {
          patternType = solvedBindings[bindingOffset].type;
        }
        // Wildcards (names starting with _) display as Hole, others as Const
        if (pattern.name.startsWith('_')) {
          syntheticTerm = { tag: 'Hole', id: pattern.name, type: patternType, context: [] };
        } else {
          syntheticTerm = { tag: 'Const', name: pattern.name, type: patternType };
        }
        break;
      case 'PCtor':
        // Constructor pattern - the type is the expectedType (the result type of applying the constructor)
        // NOT the type of the first sub-binding (which would be wrong)
        patternType = expectedType;
        const ctorType = lookupInContext(pattern.name, context);
        if (ctorType) {
          syntheticTerm = { tag: 'Const', name: pattern.name, type: ctorType };
          // If there are args, create applications
          if (pattern.args.length > 0) {
            // The full applied constructor has the expected type
            syntheticTerm = { tag: 'Const', name: `${pattern.name} ...`, type: expectedType };
          }
        } else {
          syntheticTerm = { tag: 'Const', name: pattern.name, type: expectedType };
        }
        break;
    }
    return {
      success: true,
      term: syntheticTerm,
      type: patternType,
      context
    };
  }

  // Navigate into the pattern structure
  const segment = path[pathIndex];

  if (pattern.tag === 'PCtor' && segment.kind === 'field') {
    if (segment.name === 'name') {
      // Navigate to the constructor name itself - return the constructor's type
      const ctorType = lookupInContext(pattern.name, context);
      if (ctorType) {
        return {
          success: true,
          term: { tag: 'Const', name: pattern.name, type: ctorType },
          type: ctorType,
          context
        };
      } else {
        // Constructor not found in context, return what we have
        return {
          success: true,
          term: { tag: 'Const', name: pattern.name, type: expectedType },
          type: expectedType,
          context
        };
      }
    } else if (segment.name === 'args') {
      // Navigate into constructor arguments
      pathIndex++;
      if (pathIndex < path.length && path[pathIndex].kind === 'array') {
        const argIndex = (path[pathIndex] as { kind: 'array'; index: number }).index;
        if (argIndex < 0 || argIndex >= pattern.args.length) {
          return { success: false, error: `Pattern arg index ${argIndex} out of bounds` };
        }

        // Get the constructor type to determine argument types
        const ctorType = lookupInContext(pattern.name, context);
        let argType: TTKTerm = { tag: 'Hole', id: '?arg_type', type: { tag: 'Sort', level: 0 }, context: [] };

        if (ctorType) {
          const ctorTelescope = extractTelescope(ctorType);
          if (argIndex < ctorTelescope.length) {
            argType = ctorTelescope[argIndex].type;
          }
        }

        // Calculate the new binding offset for nested pattern
        // We need to count bindings from previous args
        let newBindingOffset = bindingOffset;
        for (let i = 0; i < argIndex; i++) {
          newBindingOffset += countPatternBindings(pattern.args[i]);
        }

        // Recurse into the argument pattern
        pathIndex++;
        return queryPatternType(pattern.args[argIndex], argType, context, path, pathIndex, solvedBindings, newBindingOffset);
      } else {
        return { success: false, error: `Expected array index after 'args' in pattern` };
      }
    }
  }

  return { success: false, error: `Cannot navigate '${JSON.stringify(segment)}' in pattern` };
}

// ============================================================================
// Core Types
// ============================================================================

/**
 * Result of a type query.
 */
export type TypeQueryResult =
  | { success: true; term: TTKTerm; type: TTKTerm; context: TTKContext }
  | { success: false; error: string };

/**
 * A navigable node in a term tree.
 * Contains the term, its type, and the local context.
 */
export interface TermNode {
  term: TTKTerm;
  type: TTKTerm;
  context: TTKContext;
  path: IndexPath;
}

// ============================================================================
// Path Navigation
// ============================================================================

/**
 * Navigate to a subterm at the given path.
 *
 * Returns the subterm or null if the path is invalid.
 * This does NOT perform type-checking - just structural navigation.
 *
 * @param term - The root term to navigate from
 * @param path - The path to navigate
 * @returns The subterm at the path, or null if invalid
 */
export function navigateToPath(term: TTKTerm, path: IndexPath): TTKTerm | null {
  let current: TTKTerm = term;

  for (const segment of path) {
    if (segment.kind === 'field') {
      const fieldName = segment.name;

      switch (current.tag) {
        case 'Binder':
          if (fieldName === 'domain') {
            current = current.domain;
          } else if (fieldName === 'body') {
            current = current.body;
          } else if (fieldName === 'binderKind' && current.binderKind.tag === 'BLet') {
            // Navigate into binderKind for BLet
            if (path.length > 0) {
              // Need to check next segment
              continue; // Let the next iteration handle it
            }
            return null;
          } else {
            return null;
          }
          break;

        case 'App':
          if (fieldName === 'fn') {
            current = current.fn;
          } else if (fieldName === 'arg') {
            current = current.arg;
          } else {
            return null;
          }
          break;

        case 'Const':
          if (fieldName === 'type') {
            current = current.type;
          } else {
            return null;
          }
          break;

        case 'Annot':
          if (fieldName === 'term') {
            current = current.term;
          } else if (fieldName === 'type') {
            current = current.type;
          } else {
            return null;
          }
          break;

        case 'Hole':
          if (fieldName === 'type') {
            current = current.type;
          } else {
            return null;
          }
          break;

        case 'Match':
          if (fieldName === 'scrutinee') {
            current = current.scrutinee;
          } else if (fieldName === 'clauses') {
            // Need array index next
            continue;
          } else {
            return null;
          }
          break;

        default:
          // Var, Sort don't have navigable fields
          return null;
      }
    } else if (segment.kind === 'array') {
      const index = segment.index;

      // Handle array navigation (e.g., clauses[0])
      if (current.tag === 'Match') {
        if (index >= 0 && index < current.clauses.length) {
          // We're at a clause, but clauses aren't terms themselves
          // The next segment should be 'rhs' or 'patterns'
          continue;
        } else {
          return null;
        }
      } else if (current.tag === 'Hole' && 'context' in current) {
        // Navigating hole context
        if (index >= 0 && index < current.context.length) {
          current = current.context[index].type;
        } else {
          return null;
        }
      } else {
        return null;
      }
    }
  }

  return current;
}

/**
 * Navigate to a clause RHS in a Match expression.
 * Handles the special case of Match clauses which aren't direct TTKTerm children.
 */
function navigateToClauseRhs(term: TTKTerm, clauseIndex: number): TTKTerm | null {
  if (term.tag !== 'Match') return null;
  if (clauseIndex < 0 || clauseIndex >= term.clauses.length) return null;
  return term.clauses[clauseIndex].rhs;
}

// ============================================================================
// Type Query Core API
// ============================================================================

/**
 * Query the type of a subterm at a given path.
 *
 * This is the CORE API that works with paths directly.
 * It performs type inference to determine the type at the path.
 *
 * @param rootTerm - The root term to query within
 * @param rootContext - The context at the root term
 * @param path - The path to the subterm
 * @param expectedType - Optional expected type of rootTerm (used for pattern binding types)
 * @returns TypeQueryResult with the term and its type, or an error
 *
 * @example
 * ```typescript
 * // Query the type of a lambda's body
 * const result = queryTypeAtPath(
 *   lambdaTerm,
 *   [],
 *   [{ kind: 'field', name: 'body' }]
 * );
 * if (result.success) {
 *   console.log('Body type:', prettyPrint(result.type));
 * }
 * ```
 */
export function queryTypeAtPath(
  rootTerm: TTKTerm,
  rootContext: TTKContext,
  path: IndexPath,
  expectedType?: TTKTerm,
  elabContext?: ElaborationContext
): TypeQueryResult {
  try {
    // Navigate through the term, building context as we go under binders
    let currentTerm = rootTerm;
    let currentContext = rootContext;
    let currentExpectedType = expectedType;  // Track expected type through navigation
    let pathIndex = 0;

    while (pathIndex < path.length) {
      const segment = path[pathIndex];

      if (segment.kind === 'field') {
        const fieldName = segment.name;

        switch (currentTerm.tag) {
          case 'Binder': {
            if (fieldName === 'domain') {
              currentTerm = currentTerm.domain;
              currentExpectedType = undefined;  // Domain doesn't have an expected type from parent
              pathIndex++;
            } else if (fieldName === 'body') {
              // When entering a binder body, extend the context
              // If the domain is a hole and we have an expected Pi type, use the Pi's domain
              let domainType = currentTerm.domain;
              if (domainType.tag === 'Hole' && currentExpectedType?.tag === 'Binder' &&
                  currentExpectedType.binderKind.tag === 'BPi') {
                domainType = currentExpectedType.domain;
              }
              currentContext = extendContext(currentContext, currentTerm.name, domainType);

              // Update expected type: if current expected is Pi, body expected is Pi's body
              if (currentExpectedType?.tag === 'Binder' && currentExpectedType.binderKind.tag === 'BPi') {
                currentExpectedType = currentExpectedType.body;
              } else {
                currentExpectedType = undefined;
              }

              currentTerm = currentTerm.body;
              pathIndex++;
            } else if (fieldName === 'binderKind') {
              // Handle BLet defVal
              if (currentTerm.binderKind.tag === 'BLet') {
                pathIndex++;
                if (pathIndex < path.length && path[pathIndex].kind === 'field' &&
                    (path[pathIndex] as { kind: 'field'; name: string }).name === 'defVal') {
                  currentTerm = currentTerm.binderKind.defVal;
                  pathIndex++;
                } else {
                  return { success: false, error: `Invalid path after binderKind` };
                }
              } else {
                return { success: false, error: `Cannot navigate binderKind of ${currentTerm.binderKind.tag}` };
              }
            } else {
              return { success: false, error: `Unknown field '${fieldName}' on Binder` };
            }
            break;
          }

          case 'App':
            if (fieldName === 'fn') {
              currentTerm = currentTerm.fn;
              pathIndex++;
            } else if (fieldName === 'arg') {
              currentTerm = currentTerm.arg;
              pathIndex++;
            } else {
              return { success: false, error: `Unknown field '${fieldName}' on App` };
            }
            break;

          case 'Const':
            if (fieldName === 'type') {
              currentTerm = currentTerm.type;
              pathIndex++;
            } else {
              return { success: false, error: `Unknown field '${fieldName}' on Const` };
            }
            break;

          case 'Annot':
            if (fieldName === 'term') {
              currentTerm = currentTerm.term;
              pathIndex++;
            } else if (fieldName === 'type') {
              currentTerm = currentTerm.type;
              pathIndex++;
            } else {
              return { success: false, error: `Unknown field '${fieldName}' on Annot` };
            }
            break;

          case 'Hole':
            if (fieldName === 'type') {
              currentTerm = currentTerm.type;
              pathIndex++;
            } else if (fieldName === 'context') {
              // Need array index next
              pathIndex++;
            } else {
              return { success: false, error: `Unknown field '${fieldName}' on Hole` };
            }
            break;

          case 'Match':
            if (fieldName === 'value') {
              // 'value' is a virtual field - the Match term IS the value
              // This allows paths like "value.clauses[0].rhs" to work
              pathIndex++;
            } else if (fieldName === 'scrutinee') {
              currentTerm = currentTerm.scrutinee;
              pathIndex++;
            } else if (fieldName === 'clauses') {
              // Need array index next
              pathIndex++;
            } else {
              return { success: false, error: `Unknown field '${fieldName}' on Match` };
            }
            break;

          default:
            return { success: false, error: `Cannot navigate field on ${currentTerm.tag}` };
        }
      } else if (segment.kind === 'array') {
        const index = segment.index;

        if (currentTerm.tag === 'Match') {
          // We should be at 'clauses' field
          if (index < 0 || index >= currentTerm.clauses.length) {
            return { success: false, error: `Clause index ${index} out of bounds` };
          }
          // The next segment should be 'rhs' or 'patterns'
          pathIndex++;
          if (pathIndex < path.length && path[pathIndex].kind === 'field') {
            const nextField = (path[pathIndex] as { kind: 'field'; name: string }).name;
            if (nextField === 'rhs') {
              // Extend context with pattern bindings
              const clause = currentTerm.clauses[index];

              // If we have elaboration context with solved bindings, use those
              // This gives us types with unification results applied
              if (elabContext?.clauseResults && index < elabContext.clauseResults.length) {
                const clauseResult = elabContext.clauseResults[index];
                // Use the solved bindings from elaboration
                for (const binding of clauseResult.solvedBindings) {
                  currentContext = extendContext(currentContext, binding.name, binding.type);
                }
              } else {
                // Fall back to computing bindings without unification results
                currentContext = computeClauseBindings(clause, currentExpectedType, currentContext);
              }

              // Update expected type for the RHS by stripping matched patterns
              currentExpectedType = computeClauseRhsExpectedType(clause, currentExpectedType);
              currentTerm = clause.rhs;
              pathIndex++;
            } else if (nextField === 'patterns') {
              // Navigate into patterns array
              pathIndex++;
              if (pathIndex < path.length && path[pathIndex].kind === 'array') {
                const patternIndex = (path[pathIndex] as { kind: 'array'; index: number }).index;
                const clause = currentTerm.clauses[index];
                if (patternIndex < 0 || patternIndex >= clause.patterns.length) {
                  return { success: false, error: `Pattern index ${patternIndex} out of bounds` };
                }

                // Try to get the solved type from elaboration context
                let patternType: TTKTerm;
                let patternContext = currentContext;
                const pattern = clause.patterns[patternIndex];

                if (elabContext?.clauseResults && index < elabContext.clauseResults.length) {
                  // Use solved bindings from elaboration
                  const clauseResult = elabContext.clauseResults[index];
                  const solvedBindings = clauseResult.solvedBindings;
                  const substitution = clauseResult.substitution;

                  // Find the cumulative binding index for this pattern
                  // (patterns can bind multiple variables for constructor patterns)
                  let bindingOffset = 0;
                  for (let i = 0; i < patternIndex; i++) {
                    const pat = clause.patterns[i];
                    bindingOffset += countPatternBindings(pat);
                  }

                  // Build context with ALL solved bindings for proper display
                  // The substituted type uses De Bruijn indices relative to the full binding context,
                  // so we need all bindings present for pretty-printing to work correctly.
                  //
                  // Also build a canonical name map: for each binding, if it's equivalent to another
                  // binding via the substitution, use the "best" name (prefer non-wildcard names).
                  const canonicalNames = buildCanonicalNames(solvedBindings, substitution);
                  for (let i = 0; i < solvedBindings.length; i++) {
                    const canonicalName = canonicalNames[i];
                    patternContext = [{ name: canonicalName, type: solvedBindings[i].type }, ...patternContext];
                  }

                  // Get the pattern type:
                  // - For variable patterns, use the solved binding type directly
                  // - For constructor/wildcard patterns, use telescope type with substitution
                  if (pattern.tag === 'PVar' && bindingOffset < solvedBindings.length) {
                    patternType = solvedBindings[bindingOffset].type;
                  } else {
                    // For constructor patterns, use telescope type with substitution applied
                    const telescope = currentExpectedType ? extractTelescope(currentExpectedType) : [];
                    patternType = patternIndex < telescope.length
                      ? telescope[patternIndex].type
                      : { tag: 'Hole' as const, id: '?pattern_type', type: { tag: 'Sort' as const, level: 0 }, context: [] };

                    // Apply unification substitution to get the solved type.
                    // The telescope type uses De Bruijn indices relative to telescope positions 0..(patternIndex-1).
                    // The substitution uses indices relative to the full pattern binding context.
                    // We need to shift the telescope type to match the substitution's index space.
                    if (substitution && substitution.size > 0) {
                      const totalBindings = solvedBindings.length;
                      const shiftAmount = totalBindings - patternIndex;
                      patternType = shiftTerm(patternType, shiftAmount);
                      patternType = applySubstitution(substitution, patternType);
                    }
                  }
                } else {
                  // Compute the type for this pattern position from the function type
                  const telescope = currentExpectedType ? extractTelescope(currentExpectedType) : [];
                  patternType = patternIndex < telescope.length
                    ? telescope[patternIndex].type
                    : { tag: 'Hole' as const, id: '?pattern_type', type: { tag: 'Sort' as const, level: 0 }, context: [] };

                  // Build the context with bindings from patterns 0 through patternIndex-1
                  // This is needed so that De Bruijn indices in patternType resolve correctly
                  for (let i = 0; i < patternIndex && i < telescope.length; i++) {
                    // Get the pattern name (or use telescope name as fallback)
                    const pat = clause.patterns[i];
                    const patName = pat.tag === 'PVar' ? pat.name : telescope[i].name;
                    patternContext = [{ name: patName, type: telescope[i].type }, ...patternContext];
                  }
                }

                // Now navigate into the pattern structure
                pathIndex++;
                // Pass solved bindings for nested pattern queries
                const clauseSolvedBindings = elabContext?.clauseResults?.[index]?.solvedBindings;
                const clauseBindingOffset = (() => {
                  let offset = 0;
                  for (let i = 0; i < patternIndex; i++) {
                    offset += countPatternBindings(clause.patterns[i]);
                  }
                  return offset;
                })();
                return queryPatternType(pattern, patternType, patternContext, path, pathIndex, clauseSolvedBindings, clauseBindingOffset);
              } else {
                return { success: false, error: `Expected array index after 'patterns'` };
              }
            } else {
              return { success: false, error: `Cannot navigate to '${nextField}' in clause` };
            }
          } else {
            return { success: false, error: `Expected field segment after clause index` };
          }
        } else if (currentTerm.tag === 'Hole') {
          // Navigating hole context bindings
          if (index < 0 || index >= currentTerm.context.length) {
            return { success: false, error: `Context index ${index} out of bounds` };
          }
          pathIndex++;
          if (pathIndex < path.length && path[pathIndex].kind === 'field') {
            const nextField = (path[pathIndex] as { kind: 'field'; name: string }).name;
            if (nextField === 'type') {
              currentTerm = currentTerm.context[index].type;
              pathIndex++;
            } else {
              return { success: false, error: `Cannot navigate to '${nextField}' in context binding` };
            }
          } else {
            return { success: false, error: `Expected field segment after context index` };
          }
        } else {
          return { success: false, error: `Cannot use array index on ${currentTerm.tag}` };
        }
      }
    }

    // Now infer the type of the term we navigated to
    // If we have an expected type, prefer it over inference when:
    // 1. The inferred type contains holes (from unannotated binders)
    // 2. Inference fails
    let type: TTKTerm;
    try {
      type = inferType(currentTerm, currentContext);
      // If the inferred type contains holes and we have an expected type, use the expected type
      // This handles cases like \x => body where x has no type annotation
      if (currentExpectedType && typeContainsHoles(type)) {
        type = currentExpectedType;
      }
    } catch (inferError) {
      // If inference fails but we have an expected type, use it
      if (currentExpectedType) {
        type = currentExpectedType;
      } else {
        throw inferError;
      }
    }

    return {
      success: true,
      term: currentTerm,
      type,
      context: currentContext
    };
  } catch (e) {
    return {
      success: false,
      error: e instanceof Error ? e.message : String(e)
    };
  }
}

/**
 * Get a human-readable description of the type at a path.
 *
 * @param rootTerm - The root term
 * @param rootContext - The context at the root
 * @param path - Path to the subterm
 * @returns A formatted string with the term and its type
 */
export function describeTypeAtPath(
  rootTerm: TTKTerm,
  rootContext: TTKContext,
  path: IndexPath
): string {
  const result = queryTypeAtPath(rootTerm, rootContext, path);

  if (!result.success) {
    return `Error: ${result.error}`;
  }

  const termStr = prettyPrint(result.term, result.context.map(b => b.name));
  const typeStr = prettyPrint(result.type, result.context.map(b => b.name));

  return `${termStr} : ${typeStr}`;
}

// ============================================================================
// Path Finding (for UI integration)
// ============================================================================

/**
 * Information about a term at a path, including display strings.
 */
export interface TermInfo {
  path: IndexPath;
  pathString: string;
  term: TTKTerm;
  termString: string;
  type: TTKTerm;
  typeString: string;
  context: TTKContext;
}

/**
 * Enumerate all navigable subterms of a term with their types.
 *
 * This is useful for building UI components that show all
 * selectable subexpressions.
 *
 * @param rootTerm - The root term
 * @param rootContext - The context at the root
 * @param maxDepth - Maximum depth to traverse (default: 10)
 * @returns Array of TermInfo for all subterms
 */
export function enumerateSubterms(
  rootTerm: TTKTerm,
  rootContext: TTKContext,
  maxDepth: number = 10
): TermInfo[] {
  const results: TermInfo[] = [];

  function visit(term: TTKTerm, context: TTKContext, path: IndexPath, depth: number): void {
    if (depth > maxDepth) return;

    // Try to infer type for this term
    try {
      const type = inferType(term, context);
      const names = context.map(b => b.name);

      results.push({
        path,
        pathString: serializeIndexPath(path),
        term,
        termString: prettyPrint(term, names),
        type,
        typeString: prettyPrint(type, names),
        context
      });
    } catch {
      // Skip terms that don't type-check
    }

    // Recurse into children
    switch (term.tag) {
      case 'Binder': {
        visit(term.domain, context, [...path, { kind: 'field', name: 'domain' }], depth + 1);

        const extCtx = extendContext(context, term.name, term.domain);
        visit(term.body, extCtx, [...path, { kind: 'field', name: 'body' }], depth + 1);

        if (term.binderKind.tag === 'BLet') {
          visit(
            term.binderKind.defVal,
            context,
            [...path, { kind: 'field', name: 'binderKind' }, { kind: 'field', name: 'defVal' }],
            depth + 1
          );
        }
        break;
      }

      case 'App':
        visit(term.fn, context, [...path, { kind: 'field', name: 'fn' }], depth + 1);
        visit(term.arg, context, [...path, { kind: 'field', name: 'arg' }], depth + 1);
        break;

      case 'Const':
        visit(term.type, context, [...path, { kind: 'field', name: 'type' }], depth + 1);
        break;

      case 'Annot':
        visit(term.term, context, [...path, { kind: 'field', name: 'term' }], depth + 1);
        visit(term.type, context, [...path, { kind: 'field', name: 'type' }], depth + 1);
        break;

      case 'Hole':
        visit(term.type, context, [...path, { kind: 'field', name: 'type' }], depth + 1);
        break;

      case 'Match':
        visit(term.scrutinee, context, [...path, { kind: 'field', name: 'scrutinee' }], depth + 1);
        for (let i = 0; i < term.clauses.length; i++) {
          // TODO: Extend context with pattern bindings
          visit(
            term.clauses[i].rhs,
            context,
            [...path, { kind: 'field', name: 'clauses' }, { kind: 'array', index: i }, { kind: 'field', name: 'rhs' }],
            depth + 1
          );
        }
        break;

      // Var, Sort have no children
    }
  }

  visit(rootTerm, rootContext, [], 0);
  return results;
}
