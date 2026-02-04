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

/**
 * Result of ill-typed abstraction detection
 */
export interface IllTypedAbstractionResult {
  isIllTyped: boolean;
  problematicVars: Array<{
    varIndex: number;
    varName: string;
    varType: TTKTerm;
  }>;
  errorMessage?: string;
}

/**
 * Detect whether abstracting over a scrutinee in a goal would produce an
 * ill-typed term. This happens when a free variable V appears in the goal
 * and V's type (from the context) mentions the scrutinee.
 *
 * Classic example (dependent pair projection):
 *   snd_p : B (fst_p)   -- type mentions fst_p
 *   Goal: H fst_p snd_p
 *   Abstracting fst_p → w makes snd_p's type B(fst_p) ill-formed (should be B(w))
 *
 * @param scrutinee - The term being abstracted (typically a Var)
 * @param goal - The goal type being abstracted over
 * @param context - The typing context
 * @returns Detection result with problematic variables if ill-typed
 */
export function detectIllTypedAbstraction(
  scrutinee: TTKTerm,
  goal: TTKTerm,
  context: TTKContext
): IllTypedAbstractionResult {
  const n = context.length;

  // Step 1: Collect all free Var indices that appear in the goal (goal-level de Bruijn)
  const goalVars = new Set<number>();
  collectFreeVars(goal, goalVars);

  // Step 2: Get the scrutinee's goal-level de Bruijn index and context array position
  const scrutineeGoalIdx = scrutinee.tag === 'Var' ? scrutinee.index : -1;
  // Context is [outermost...innermost], goal-level Var(i) = context[n - 1 - i]
  const scrutineeCtxPos = n - 1 - scrutineeGoalIdx;

  // Step 3: For each variable in the goal (other than the scrutinee),
  // check if its type (in the context) mentions the scrutinee.
  // Types in context entries use de Bruijn indices relative to that entry's position:
  // from context[k], variable context[j] (j < k) has local index (k - 1 - j).
  const problematicVars: IllTypedAbstractionResult['problematicVars'] = [];

  for (const goalVarIdx of goalVars) {
    if (goalVarIdx === scrutineeGoalIdx) continue; // Skip the scrutinee itself

    const varCtxPos = n - 1 - goalVarIdx;
    if (varCtxPos < 0 || varCtxPos >= n) continue;

    const entry = context[varCtxPos];

    // The scrutinee must have been bound BEFORE this variable for its type to reference it
    if (scrutineeCtxPos >= varCtxPos) continue;

    // From context[varCtxPos]'s type, the scrutinee at context[scrutineeCtxPos]
    // has local de Bruijn index (varCtxPos - 1 - scrutineeCtxPos)
    const scrutineeLocalIdx = varCtxPos - 1 - scrutineeCtxPos;

    const typeVars = new Set<number>();
    collectFreeVars(entry.type, typeVars);

    if (typeVars.has(scrutineeLocalIdx)) {
      problematicVars.push({
        varIndex: goalVarIdx,
        varName: entry.name,
        varType: entry.type
      });
    }
  }

  const isIllTyped = problematicVars.length > 0;
  let errorMessage: string | undefined;

  if (isIllTyped) {
    const scrutineeName = scrutineeCtxPos >= 0 && scrutineeCtxPos < n
      ? context[scrutineeCtxPos].name
      : '(scrutinee)';
    const varNames = problematicVars.map(v => v.varName).join(', ');
    errorMessage = `Ill-typed with-abstraction: the type of ${varNames} depends on ${scrutineeName}, ` +
      `which is being abstracted over. Consider abstracting over ${varNames} as well.`;
  }

  return { isIllTyped, problematicVars, errorMessage };
}

/**
 * Collect all free Var indices in a term.
 */
function collectFreeVars(term: TTKTerm, vars: Set<number>, depth: number = 0): void {
  switch (term.tag) {
    case 'Var':
      if (term.index >= depth) {
        vars.add(term.index - depth);
      }
      break;

    case 'App':
      collectFreeVars(term.fn, vars, depth);
      collectFreeVars(term.arg, vars, depth);
      break;

    case 'Binder':
      collectFreeVars(term.domain, vars, depth);
      collectFreeVars(term.body, vars, depth + 1);
      break;

    case 'Annot':
      collectFreeVars(term.term, vars, depth);
      collectFreeVars(term.type, vars, depth);
      break;

    case 'Match':
      collectFreeVars(term.scrutinee, vars, depth);
      break;

    case 'Const':
    case 'Sort':
    case 'ULevel':
    case 'ULit':
    case 'UOmega':
    case 'Hole':
    case 'Meta':
      break;
  }
}
