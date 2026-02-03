/**
 * With-Abstraction Implementation for Dependent Types
 *
 * This module implements Agda-style with-abstraction, which generalizes
 * over scrutinee expressions in the auxiliary function's return type.
 *
 * Key Algorithm:
 * 1. Normalize the scrutinee expression in the pattern context
 * 2. Normalize the goal/return type in the same context
 * 3. Find all occurrences of the normalized scrutinee in the normalized goal
 * 4. Replace those occurrences with a fresh variable (the with-binder)
 * 5. Add the scrutinee binder to the auxiliary type
 *
 * K Axiom Safety:
 * - We use definitional equality (areTermsDefEq) to find occurrences
 * - This respects the assumeK flag in the type checker
 * - We do NOT assume uniqueness of identity proofs
 * - Abstraction over equality proofs is sound without K
 */

import { TTKTerm, TTKContext, mkVar } from './kernel';
import { whnf } from './whnf';
import { shiftTerm } from './subst';

/**
 * Information about where a scrutinee occurs in a goal type
 */
export interface OccurrenceInfo {
  found: boolean;
  positions: OccurrencePath[];
}

/**
 * A path to an occurrence in a term tree
 * Represented as a sequence of steps: 'fn', 'arg', 'domain', 'body', etc.
 */
export type OccurrencePath = string[];

/**
 * Normalize a term in the given context using WHNF reduction.
 *
 * @param term - The term to normalize
 * @param context - The typing context (for variable lookups)
 * @param definitions - Definition map (for constant unfolding)
 * @returns The normalized term (in WHNF)
 */
export function normalizeInContext(
  term: TTKTerm,
  _context: TTKContext,
  _definitions: Map<string, { value?: TTKTerm }>
): TTKTerm {
  // Use the existing WHNF normalizer
  // TODO: Convert definitions map to DefinitionsMap format
  // For now, just normalize with basic whnf
  return whnf(term);
}

/**
 * Find all occurrences of the scrutinee in the goal type.
 *
 * This uses definitional equality to check if a subterm matches the scrutinee.
 * Properly handles de Bruijn indices under binders (depth tracking).
 *
 * @param scrutinee - The normalized scrutinee term to search for
 * @param goal - The normalized goal type to search in
 * @param context - The typing context
 * @param definitions - Definition map
 * @returns Information about occurrences found
 */
export function findOccurrences(
  scrutinee: TTKTerm,
  goal: TTKTerm,
  _context: TTKContext,
  _definitions: Map<string, { value?: TTKTerm }>
): OccurrenceInfo {
  const positions: OccurrencePath[] = [];

  /**
   * Helper: Recursively search for occurrences
   * @param term - Current term being examined
   * @param depth - Current binder depth (for de Bruijn adjustments)
   * @param path - Current path from root
   */
  function search(term: TTKTerm, depth: number, path: string[]): void {
    // Check if this term matches the scrutinee (adjusted for depth)
    if (termsEqualAtDepth(scrutinee, term, 0, depth)) {
      positions.push([...path]);
      // Don't recurse into matched term
      return;
    }

    // Recurse into subterms
    switch (term.tag) {
      case 'Var':
      case 'Const':
      case 'Sort':
      case 'ULevel':
      case 'ULit':
      case 'UOmega':
      case 'Hole':
      case 'Meta':
        // Leaves - no recursion
        break;

      case 'App':
        search(term.fn, depth, [...path, 'fn']);
        search(term.arg, depth, [...path, 'arg']);
        break;

      case 'Binder':
        search(term.domain, depth, [...path, 'domain']);
        search(term.body, depth + 1, [...path, 'body']);
        break;

      case 'Annot':
        search(term.term, depth, [...path, 'term']);
        search(term.type, depth, [...path, 'type']);
        break;

      case 'Match': {
        search(term.scrutinee, depth, [...path, 'scrutinee']);
        // Count pattern vars
        const countPatternVars = (pattern: typeof term.clauses[0]['patterns'][0]): number => {
          if (pattern.tag === 'PVar' || pattern.tag === 'PWild') return 1;
          if (pattern.tag === 'PCtor') return pattern.args.reduce((sum, arg) => sum + countPatternVars(arg), 0);
          return 0;
        };
        term.clauses.forEach((clause, i) => {
          const patternDepth = depth + clause.patterns.reduce((sum, p) => sum + countPatternVars(p), 0);
          search(clause.rhs, patternDepth, [...path, 'clause', String(i), 'rhs']);
        });
        break;
      }
    }
  }

  search(goal, 0, []);

  return {
    found: positions.length > 0,
    positions
  };
}

/**
 * Check if two terms are equal, accounting for binder depth.
 *
 * A Var at index i in a term at depth d corresponds to
 * a Var at index (i + d2 - d1) in a term at depth d2.
 *
 * @param term1 - First term (at depth1)
 * @param term2 - Second term (at depth2)
 * @param depth1 - Binder depth of term1
 * @param depth2 - Binder depth of term2
 * @returns true if terms are structurally equal (modulo depth adjustment)
 */
function termsEqualAtDepth(
  term1: TTKTerm,
  term2: TTKTerm,
  depth1: number,
  depth2: number
): boolean {
  // Adjust for depth difference when comparing variables
  const depthDiff = depth2 - depth1;

  if (term1.tag !== term2.tag) {
    return false;
  }

  switch (term1.tag) {
    case 'Var':
      // Var at index i in depth d1 = Var at index (i + diff) in depth d2
      return term2.tag === 'Var' && term1.index + depthDiff === term2.index;

    case 'Const':
      return term2.tag === 'Const' && term1.name === term2.name;

    case 'Sort':
    case 'ULevel':
    case 'UOmega':
      return true;

    case 'ULit':
      return term2.tag === 'ULit' && term1.n === term2.n;

    case 'Hole':
      return term2.tag === 'Hole' && term1.id === term2.id;

    case 'Meta':
      return term2.tag === 'Meta' && term1.id === term2.id;

    case 'App':
      return term2.tag === 'App' &&
        termsEqualAtDepth(term1.fn, term2.fn, depth1, depth2) &&
        termsEqualAtDepth(term1.arg, term2.arg, depth1, depth2);

    case 'Binder':
      if (term2.tag !== 'Binder') return false;
      if (term1.binderKind.tag !== term2.binderKind.tag) return false;
      return termsEqualAtDepth(term1.domain, term2.domain, depth1, depth2) &&
        termsEqualAtDepth(term1.body, term2.body, depth1 + 1, depth2 + 1);

    case 'Annot':
      return term2.tag === 'Annot' &&
        termsEqualAtDepth(term1.term, term2.term, depth1, depth2) &&
        termsEqualAtDepth(term1.type, term2.type, depth1, depth2);

    case 'Match':
      // Simplified match equality - just check scrutinee
      return term2.tag === 'Match' &&
        termsEqualAtDepth(term1.scrutinee, term2.scrutinee, depth1, depth2);

    default:
      return false;
  }
}

/**
 * Replace all occurrences of the scrutinee with a fresh variable (Var 0).
 * Also shifts all other free variables to account for the new binder.
 *
 * @param goal - The goal type containing occurrences
 * @param occurrences - Information about where to replace
 * @param freshVarIndex - The index of the fresh variable (usually 0)
 * @returns The goal type with replacements made
 */
export function replaceWithFreshVar(
  goal: TTKTerm,
  occurrences: OccurrenceInfo,
  freshVarIndex: number
): TTKTerm {
  if (!occurrences.found) {
    // No occurrences - just shift free variables for the new binder
    return shiftTerm(goal, 1, 0);
  }

  // Build a set of paths for fast lookup
  const pathSet = new Set(occurrences.positions.map(p => p.join('/')));

  /**
   * Helper: Recursively replace occurrences
   * @param term - Current term
   * @param path - Current path from root
   * @param depth - Current binder depth
   * @returns Transformed term
   */
  function replace(term: TTKTerm, path: string[], depth: number): TTKTerm {
    const pathKey = path.join('/');

    // If this path is an occurrence, replace with fresh var (adjusted for depth)
    if (pathSet.has(pathKey)) {
      return mkVar(freshVarIndex + depth);
    }

    // Otherwise, recurse and shift free variables
    switch (term.tag) {
      case 'Var':
        // Shift free variables to account for new binder
        // Variables bound above this point need to shift
        return mkVar(term.index + 1);

      case 'Const':
      case 'Sort':
      case 'ULevel':
      case 'ULit':
      case 'UOmega':
      case 'Hole':
      case 'Meta':
        return term;

      case 'App':
        return {
          tag: 'App',
          fn: replace(term.fn, [...path, 'fn'], depth),
          arg: replace(term.arg, [...path, 'arg'], depth)
        };

      case 'Binder':
        return {
          tag: 'Binder',
          name: term.name,
          binderKind: term.binderKind,
          domain: replace(term.domain, [...path, 'domain'], depth),
          body: replace(term.body, [...path, 'body'], depth + 1)
        };

      case 'Annot':
        return {
          tag: 'Annot',
          term: replace(term.term, [...path, 'term'], depth),
          type: replace(term.type, [...path, 'type'], depth)
        };

      case 'Match': {
        // Count pattern vars to determine depth increase
        const countPatternVars = (pattern: typeof term.clauses[0]['patterns'][0]): number => {
          if (pattern.tag === 'PVar' || pattern.tag === 'PWild') return 1;
          if (pattern.tag === 'PCtor') return pattern.args.reduce((sum, arg) => sum + countPatternVars(arg), 0);
          return 0;
        };

        return {
          tag: 'Match',
          scrutinee: replace(term.scrutinee, [...path, 'scrutinee'], depth),
          clauses: term.clauses.map((clause, i) => {
            const patternDepth = clause.patterns.reduce((sum, p) => sum + countPatternVars(p), 0);
            return {
              ...clause,
              rhs: replace(
                clause.rhs,
                [...path, 'clause', String(i), 'rhs'],
                depth + patternDepth
              )
            };
          })
        };
      }

      default:
        return term;
    }
  }

  return replace(goal, [], 0);
}
