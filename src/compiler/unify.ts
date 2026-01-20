import { Level, levelsEqual, mkVar, TTKTerm } from "./kernel";
import { whnf } from "./whnf";

// ============================================================================
// Unification Result Types
// ============================================================================

export type Substitutions = Map<number, TTKTerm>

/** Constraint: metavariable ?m should equal rhs */
export type MetaConstraint = { meta: string; rhs: TTKTerm }

/** Constraint: level metavariable ?l should equal rhs */
export type LevelConstraint = { lmvar: string; rhs: Level }

export type UnifyResult = {
  success: true;
  substitutions: Substitutions;
  metaConstraints: MetaConstraint[];
  levelConstraints: LevelConstraint[];
} | {
  success: false;
  reason: 'conflict' | 'cycle';
}

// ============================================================================
// Occurs Checks
// ============================================================================

/**
 * Check if a variable index occurs free in a term.
 * Used for the occurs check to prevent cyclic substitutions.
 */
function varOccursIn(varIndex: number, term: TTKTerm): boolean {
  switch (term.tag) {
    case 'Var':
      return term.index === varIndex;

    case 'Sort':
    case 'Const':
    case 'Hole':
    case 'Meta':
      return false;

    case 'App':
      return varOccursIn(varIndex, term.fn) || varOccursIn(varIndex, term.arg);

    case 'Binder':
      // In the body, indices shift up by 1 due to the binder
      if (varOccursIn(varIndex, term.domain)) return true;
      if (varOccursIn(varIndex + 1, term.body)) return true;
      if (term.binderKind.tag === 'BLet') {
        if (varOccursIn(varIndex, term.binderKind.defVal)) return true;
      }
      return false;

    case 'Annot':
      return varOccursIn(varIndex, term.term) || varOccursIn(varIndex, term.type);

    case 'Match':
      if (varOccursIn(varIndex, term.scrutinee)) return true;
      for (const clause of term.clauses) {
        // Conservative: patterns bind variables, shifting indices in RHS
        // For proper check, we'd count pattern binders
        if (varOccursIn(varIndex, clause.rhs)) return true;
      }
      return false;
  }
}

/**
 * Check if a level metavariable occurs in a level.
 * Used for the occurs check to prevent cyclic level constraints.
 */
function levelMVarOccursIn(lmvarId: string, level: Level): boolean {
  switch (level.tag) {
    case 'LZero':
    case 'LParam':
      return false;

    case 'LMVar':
      return level.id === lmvarId;

    case 'LSucc':
      return levelMVarOccursIn(lmvarId, level.pred);

    case 'LMax':
    case 'LIMax':
      return levelMVarOccursIn(lmvarId, level.left) ||
             levelMVarOccursIn(lmvarId, level.right);
  }
}

// ============================================================================
// Result Combinators
// ============================================================================

const emptySuccess: UnifyResult = {
  success: true,
  substitutions: new Map(),
  metaConstraints: [],
  levelConstraints: [],
};

/** Combine two successful unification results */
function combineResults(r1: UnifyResult, r2: UnifyResult): UnifyResult {
  if (!r1.success) return r1;
  if (!r2.success) return r2;
  return {
    success: true,
    substitutions: new Map([...r1.substitutions, ...r2.substitutions]),
    metaConstraints: [...r1.metaConstraints, ...r2.metaConstraints],
    levelConstraints: [...r1.levelConstraints, ...r2.levelConstraints],
  };
}

// ============================================================================
// Level Unification
// ============================================================================

/**
 * Unify two universe levels.
 *
 * Handles:
 * - Concrete levels (LZero, LSucc chains)
 * - Level metavariables (LMVar) → generates constraints
 * - Level parameters (LParam) → must match exactly
 * - Max/IMax → structural unification
 */
function unifyLevels(l1: Level, l2: Level): UnifyResult {
  // Quick structural equality check first
  if (levelsEqual(l1, l2)) {
    return emptySuccess;
  }

  // ─────────────────────────────────────────────────────────────────────────
  // LMVAR - Level metavariable: generate constraint
  // ─────────────────────────────────────────────────────────────────────────
  if (l1.tag === 'LMVar') {
    if (levelMVarOccursIn(l1.id, l2)) {
      return { success: false, reason: 'cycle' };
    }
    return {
      success: true,
      substitutions: new Map(),
      metaConstraints: [],
      levelConstraints: [{ lmvar: l1.id, rhs: l2 }],
    };
  }

  if (l2.tag === 'LMVar') {
    if (levelMVarOccursIn(l2.id, l1)) {
      return { success: false, reason: 'cycle' };
    }
    return {
      success: true,
      substitutions: new Map(),
      metaConstraints: [],
      levelConstraints: [{ lmvar: l2.id, rhs: l1 }],
    };
  }

  // ─────────────────────────────────────────────────────────────────────────
  // LZERO - Both zero
  // ─────────────────────────────────────────────────────────────────────────
  if (l1.tag === 'LZero' && l2.tag === 'LZero') {
    return emptySuccess;
  }

  // ─────────────────────────────────────────────────────────────────────────
  // LSUCC - Successor: unify predecessors
  // ─────────────────────────────────────────────────────────────────────────
  if (l1.tag === 'LSucc' && l2.tag === 'LSucc') {
    return unifyLevels(l1.pred, l2.pred);
  }

  // ─────────────────────────────────────────────────────────────────────────
  // LMAX - Maximum: structural unification
  //
  // Note: max is not injective (max(1,2) = max(2,1) = 2), but for
  // unification we do structural matching. Full level solving would
  // need constraint solving.
  // ─────────────────────────────────────────────────────────────────────────
  if (l1.tag === 'LMax' && l2.tag === 'LMax') {
    const leftResult = unifyLevels(l1.left, l2.left);
    if (!leftResult.success) return leftResult;
    const rightResult = unifyLevels(l1.right, l2.right);
    return combineResults(leftResult, rightResult);
  }

  // ─────────────────────────────────────────────────────────────────────────
  // LIMAX - Impredicative max: structural unification
  // ─────────────────────────────────────────────────────────────────────────
  if (l1.tag === 'LIMax' && l2.tag === 'LIMax') {
    const leftResult = unifyLevels(l1.left, l2.left);
    if (!leftResult.success) return leftResult;
    const rightResult = unifyLevels(l1.right, l2.right);
    return combineResults(leftResult, rightResult);
  }

  // ─────────────────────────────────────────────────────────────────────────
  // LPARAM - Level parameter: must have same name
  // ─────────────────────────────────────────────────────────────────────────
  if (l1.tag === 'LParam' && l2.tag === 'LParam') {
    if (l1.name === l2.name) {
      return emptySuccess;
    }
    return { success: false, reason: 'conflict' };
  }

  // Different level constructors that can't unify
  return { success: false, reason: 'conflict' };
}

// ============================================================================
// Term Unification
// ============================================================================

/**
 * Unify two terms, producing substitutions and constraints.
 *
 * This implements first-order unification with extensions for:
 * - Metavariables (deferred as constraints)
 * - Universe levels (including level metavariables)
 * - Dependent types (Binders)
 *
 * Both terms are reduced to WHNF before comparison.
 *
 * Returns:
 * - substitutions: Map from de Bruijn indices to terms
 * - metaConstraints: Deferred ?m = t constraints
 * - levelConstraints: Deferred ?l = level constraints
 */
export function unifyTerms(lhs: TTKTerm, rhs: TTKTerm): UnifyResult {
  // Reduce both to weak head normal form
  const a = whnf(lhs);
  const b = whnf(rhs);

  // ─────────────────────────────────────────────────────────────────────────
  // META - Metavariable
  //
  // We can't solve ?m = t without knowing ?m's typing context, so we
  // defer these as constraints to be solved later.
  // ─────────────────────────────────────────────────────────────────────────
  if (a.tag === 'Meta') {
    return {
      success: true,
      substitutions: new Map(),
      metaConstraints: [{ meta: a.id, rhs: b }],
      levelConstraints: [],
    };
  }

  if (b.tag === 'Meta') {
    return {
      success: true,
      substitutions: new Map(),
      metaConstraints: [{ meta: b.id, rhs: a }],
      levelConstraints: [],
    };
  }

  // ─────────────────────────────────────────────────────────────────────────
  // HOLE - Unelaborated hole
  //
  // Holes should be elaborated to Metas before unification. If we see
  // one, treat it similarly to Meta (defer as constraint).
  // ─────────────────────────────────────────────────────────────────────────
  if (a.tag === 'Hole') {
    return {
      success: true,
      substitutions: new Map(),
      metaConstraints: [{ meta: `hole:${a.id}`, rhs: b }],
      levelConstraints: [],
    };
  }

  if (b.tag === 'Hole') {
    return {
      success: true,
      substitutions: new Map(),
      metaConstraints: [{ meta: `hole:${b.id}`, rhs: a }],
      levelConstraints: [],
    };
  }

  // ─────────────────────────────────────────────────────────────────────────
  // VAR - Variable
  //
  // Var x vs Var x: trivially equal
  // Var x vs Var y: substitute lower index with higher (arbitrary choice
  //                 that tends to preserve more bound structure)
  // Var x vs t:     substitute x with t (with occurs check)
  // ─────────────────────────────────────────────────────────────────────────
  if (a.tag === 'Var' && b.tag === 'Var') {
    if (a.index === b.index) {
      return emptySuccess;
    }
    // Substitute lower index with higher
    const [lower, higher] = a.index < b.index
      ? [a.index, b.index]
      : [b.index, a.index];
    return {
      success: true,
      substitutions: new Map([[lower, mkVar(higher)]]),
      metaConstraints: [],
      levelConstraints: [],
    };
  }

  if (a.tag === 'Var') {
    // Occurs check: prevent x = ... x ...
    if (varOccursIn(a.index, b)) {
      return { success: false, reason: 'cycle' };
    }
    return {
      success: true,
      substitutions: new Map([[a.index, b]]),
      metaConstraints: [],
      levelConstraints: [],
    };
  }

  if (b.tag === 'Var') {
    // Occurs check: prevent x = ... x ...
    if (varOccursIn(b.index, a)) {
      return { success: false, reason: 'cycle' };
    }
    return {
      success: true,
      substitutions: new Map([[b.index, a]]),
      metaConstraints: [],
      levelConstraints: [],
    };
  }

  // ─────────────────────────────────────────────────────────────────────────
  // SORT - Universe/Type
  //
  // Sort l1 vs Sort l2: unify the levels
  // ─────────────────────────────────────────────────────────────────────────
  if (a.tag === 'Sort' && b.tag === 'Sort') {
    return unifyLevels(a.level, b.level);
  }

  // ─────────────────────────────────────────────────────────────────────────
  // CONST - Named constant
  //
  // Constants are equal iff they have the same name.
  // (Universe polymorphic constants would also need level arg unification)
  // ─────────────────────────────────────────────────────────────────────────
  if (a.tag === 'Const' && b.tag === 'Const') {
    if (a.name !== b.name) {
      return { success: false, reason: 'conflict' };
    }
    return emptySuccess;
  }

  // ─────────────────────────────────────────────────────────────────────────
  // APP - Application
  //
  // (f a) vs (g b): unify f with g, then a with b
  // ─────────────────────────────────────────────────────────────────────────
  if (a.tag === 'App' && b.tag === 'App') {
    const fnResult = unifyTerms(a.fn, b.fn);
    if (!fnResult.success) return fnResult;

    const argResult = unifyTerms(a.arg, b.arg);
    return combineResults(fnResult, argResult);
  }

  // ─────────────────────────────────────────────────────────────────────────
  // BINDER - Pi, Lambda, Let
  //
  // Must have same binder kind, then unify domain and body.
  // For Let, also unify the definition value.
  //
  // Note: We're doing structural unification here. Full higher-order
  // unification would need to handle η-conversion, but that's undecidable
  // in the general case.
  // ─────────────────────────────────────────────────────────────────────────
  if (a.tag === 'Binder' && b.tag === 'Binder') {
    // Must be same kind of binder
    if (a.binderKind.tag !== b.binderKind.tag) {
      return { success: false, reason: 'conflict' };
    }

    // Unify domains
    const domResult = unifyTerms(a.domain, b.domain);
    if (!domResult.success) return domResult;

    // Unify bodies (both are under a binder, so indices align)
    const bodyResult = unifyTerms(a.body, b.body);
    if (!bodyResult.success) return bodyResult;

    let result = combineResults(domResult, bodyResult);

    // For Let, also unify the definition values
    if (a.binderKind.tag === 'BLet' && b.binderKind.tag === 'BLet') {
      const valResult = unifyTerms(a.binderKind.defVal, b.binderKind.defVal);
      result = combineResults(result, valResult);
    }

    return result;
  }

  // ─────────────────────────────────────────────────────────────────────────
  // ANNOT - Type annotation
  //
  // Annotations don't affect computational content. We unify the inner
  // term, stripping the annotation.
  // ─────────────────────────────────────────────────────────────────────────
  if (a.tag === 'Annot') {
    return unifyTerms(a.term, b);
  }

  if (b.tag === 'Annot') {
    return unifyTerms(a, b.term);
  }

  // ─────────────────────────────────────────────────────────────────────────
  // MATCH - Pattern matching
  //
  // Structural unification: same scrutinee, same number of clauses,
  // matching patterns and RHS for each clause.
  //
  // This is a simplification - full match unification would need to
  // handle clause reordering, pattern coverage, etc.
  // ─────────────────────────────────────────────────────────────────────────
  if (a.tag === 'Match' && b.tag === 'Match') {
    // Unify scrutinees
    const scrutResult = unifyTerms(a.scrutinee, b.scrutinee);
    if (!scrutResult.success) return scrutResult;

    // Must have same number of clauses
    if (a.clauses.length !== b.clauses.length) {
      return { success: false, reason: 'conflict' };
    }

    let result: UnifyResult = scrutResult;

    for (let i = 0; i < a.clauses.length; i++) {
      const clauseA = a.clauses[i];
      const clauseB = b.clauses[i];

      // Check patterns have same structure
      if (!patternsMatch(clauseA.patterns, clauseB.patterns)) {
        return { success: false, reason: 'conflict' };
      }

      // Unify RHS (under pattern bindings - indices align if patterns match)
      const rhsResult = unifyTerms(clauseA.rhs, clauseB.rhs);
      if (!rhsResult.success) return rhsResult;
      result = combineResults(result, rhsResult);
    }

    return result;
  }

  // ─────────────────────────────────────────────────────────────────────────
  // CONFLICT - Different term constructors cannot unify
  // ─────────────────────────────────────────────────────────────────────────
  return { success: false, reason: 'conflict' };
}

// ============================================================================
// Pattern Matching Helpers
// ============================================================================

import { TTKPattern } from "./kernel";

/**
 * Check if two pattern lists are structurally identical.
 * Used to ensure match clauses align before unifying RHS.
 */
function patternsMatch(ps1: TTKPattern[], ps2: TTKPattern[]): boolean {
  if (ps1.length !== ps2.length) return false;

  for (let i = 0; i < ps1.length; i++) {
    if (!patternMatches(ps1[i], ps2[i])) return false;
  }

  return true;
}

/**
 * Check if two patterns are structurally identical.
 */
function patternMatches(p1: TTKPattern, p2: TTKPattern): boolean {
  if (p1.tag !== p2.tag) return false;

  switch (p1.tag) {
    case 'PVar':
      // Variable patterns always match structurally
      // (they bind different names but same position)
      return true;

    case 'PCtor':
      if (p2.tag !== 'PCtor') return false;
      if (p1.name !== p2.name) return false;
      return patternsMatch(p1.args, p2.args);

    case 'PWild':
      return p2.tag === 'PWild';
  }
}
