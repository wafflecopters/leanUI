import { levelsEqual, mkVar, prettyPrint, TTKTerm, isDefinitionallyEqual } from "./kernel";
import { DefinitionsMap, extractAppSpine } from "./term";
import { shiftTerm } from "./subst";
import { whnf } from "./whnf";

// ============================================================================
// Unification Options
// ============================================================================

/**
 * Options for unification behavior.
 *
 * - flexibleVars: If true, de Bruijn variables can be substituted (like metas).
 *   Use this for pattern LHS elaboration where we discover variable bindings.
 *   Default false: variables are rigid skolems that only unify with themselves.
 *
 * - rigidVarsAtOrAbove: When flexibleVars is true, vars with de Bruijn index >= this
 *   value are treated as rigid (cannot be substituted with each other). This allows
 *   pattern-local bindings (lower indices) to be flexible while function parameters
 *   (higher indices) remain rigid. If undefined, all vars are flexible.
 */
export type UnifyOptions = {
  flexibleVars?: boolean;
  rigidVarsAtOrAbove?: number;
  mode: 'pattern' | 'check';
  definitions?: DefinitionsMap;
  fuel?: number;  // Fuel for whnf reduction to prevent infinite loops
  assumeK?: boolean;  // If false, disable deletion rule (reject x=x equations)
}

const DEFAULT_UNIFY_FUEL = 1000;

// ============================================================================
// Unification Result Types
// ============================================================================

export type Substitutions = [number, TTKTerm][]

/** Constraint: metavariable ?m should equal rhs */
export type MetaConstraint = { meta: string; rhs: TTKTerm }

/** Constraint: level metavariable ?l should equal rhs (now a term) */
export type LevelConstraint = { lmvar: string; rhs: TTKTerm }

export type UnifyResult = {
  success: true;
  substitutions: Substitutions;
  metaConstraints: MetaConstraint[];
  levelConstraints: LevelConstraint[];
} | {
  success: false;
  reason: 'conflict' | 'cycle' | 'deletion-rule';
}

// ============================================================================
// Occurs Checks
// ============================================================================

/**
 * Check if a level metavariable (now a Meta term) occurs in a level term.
 * Used for the occurs check to prevent cyclic level constraints.
 */
function levelMVarOccursIn(lmvarId: string, level: TTKTerm): boolean {
  switch (level.tag) {
    case 'ULit':
    case 'UOmega':
    case 'Var':
    case 'ULevel':
    case 'Const':
      return false;

    case 'Meta':
      return level.id === lmvarId;

    case 'App':
      return levelMVarOccursIn(lmvarId, level.fn) ||
        levelMVarOccursIn(lmvarId, level.arg);

    default:
      // For other term types, conservatively check recursively
      return false;
  }
}

/**
 * Check if a variable index occurs free in a term.
 * Used for the occurs check to prevent cyclic substitutions when vars are flexible.
 */
function varOccursIn(varIndex: number, term: TTKTerm): boolean {
  switch (term.tag) {
    case 'Var':
      return term.index === varIndex;

    case 'Sort':
    case 'Const':
    case 'Hole':
    case 'Meta':
    case 'ULevel':
    case 'ULit':
    case 'UOmega':
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
        if (varOccursIn(varIndex, clause.rhs)) return true;
      }
      return false;
  }
}

// ============================================================================
// Result Combinators
// ============================================================================

const emptySuccess: UnifyResult = {
  success: true,
  substitutions: [],
  metaConstraints: [],
  levelConstraints: [],
};

function combineUnificationResults(r1: UnifyResult, r2: UnifyResult, options: UnifyOptions): UnifyResult {
  if (!r1.success) return r1;
  if (!r2.success) return r2;

  // Early return only if both have empty substitutions, metaConstraints, and levelConstraints
  // Otherwise we must combine to preserve all constraints
  if (r1.substitutions.length === 0 && r1.metaConstraints.length === 0 && r1.levelConstraints.length === 0) {
    return r2;
  }
  if (r2.substitutions.length === 0 && r2.metaConstraints.length === 0 && r2.levelConstraints.length === 0) {
    return r1;
  }

  // If only substitutions are empty but we have constraints, combine them
  if (r1.substitutions.length === 0 && r2.substitutions.length === 0) {
    return {
      success: true,
      substitutions: [],
      metaConstraints: [...r1.metaConstraints, ...r2.metaConstraints],
      levelConstraints: [...r1.levelConstraints, ...r2.levelConstraints],
    };
  }

  let adjustedSubstitutions: [number, TTKTerm][] = [];
  let derivedEquations: [number, TTKTerm][] = [];

  for (const [idx2, val2] of r2.substitutions) {
    let currentVal = val2;
    let foundMatch = false;

    for (const [idx1, val1] of r1.substitutions) {
      // Apply substitution to the value
      currentVal = applyNonShiftingSubstitutionToTerm(idx1, val1, currentVal);

      if (idx2 === idx1) {
        // Transitivity: idx = val1 AND idx = val2
        // Derive: val1 = currentVal
        const derived = unifyTerms(val1, currentVal, options);
        if (!derived.success) {
          return derived;
        }
        derivedEquations.push(...derived.substitutions);
        foundMatch = true;
        break;
      }
    }

    if (!foundMatch) {
      adjustedSubstitutions.push([idx2, currentVal]);
    }
  }

  let result: UnifyResult = {
    success: true,
    substitutions: [...r1.substitutions, ...adjustedSubstitutions],
    metaConstraints: [...r1.metaConstraints, ...r2.metaConstraints],
    levelConstraints: [...r1.levelConstraints, ...r2.levelConstraints],
  };

  if (derivedEquations.length > 0) {
    result = combineUnificationResults(result, {
      success: true,
      substitutions: derivedEquations,
      metaConstraints: [],
      levelConstraints: [],
    }, options);
  }

  return result;
}

function applyNonShiftingSubstitutionToTerm(varIndex: number, value: TTKTerm, term: TTKTerm): TTKTerm {
  // Replace occurrences of varIndex with value, but DON'T adjust other indices
  return transformVarsInTerm(term, (idx) => {
    if (idx === varIndex) {
      return value;
    }
    return mkVar(idx);  // Keep index as-is
  });
}

// ============================================================================
// Level Unification
// ============================================================================

/**
 * Unify two universe level terms.
 *
 * Now that levels are terms, this handles:
 * - ULit (numeric literals)
 * - UOmega (ω)
 * - Var (level variables via de Bruijn)
 * - Meta (level metavariables) → generates constraints
 * - App of USucc/UMax/UIMax → structural unification
 */
function unifyLevels(l1: TTKTerm, l2: TTKTerm, options: UnifyOptions): UnifyResult {
  // Quick structural equality check first
  if (levelsEqual(l1, l2)) {
    return emptySuccess;
  }

  // ─────────────────────────────────────────────────────────────────────────
  // META - Level metavariable: generate constraint
  //
  // Meta terms in level position are term metas with type ULevel, so we
  // generate metaConstraints (not levelConstraints) to ensure they get
  // solved alongside other term metas.
  // ─────────────────────────────────────────────────────────────────────────
  if (l1.tag === 'Meta') {
    if (levelMVarOccursIn(l1.id, l2)) {
      return { success: false, reason: 'cycle' };
    }
    return {
      success: true,
      substitutions: [],
      metaConstraints: [{ meta: l1.id, rhs: l2 }],
      levelConstraints: [],
    };
  }

  if (l2.tag === 'Meta') {
    if (levelMVarOccursIn(l2.id, l1)) {
      return { success: false, reason: 'cycle' };
    }
    return {
      success: true,
      substitutions: [],
      metaConstraints: [{ meta: l2.id, rhs: l1 }],
      levelConstraints: [],
    };
  }

  // ─────────────────────────────────────────────────────────────────────────
  // ULIT - Numeric level literals
  // ─────────────────────────────────────────────────────────────────────────
  if (l1.tag === 'ULit' && l2.tag === 'ULit') {
    if (l1.n === l2.n) {
      return emptySuccess;
    }
    return { success: false, reason: 'conflict' };
  }

  // ─────────────────────────────────────────────────────────────────────────
  // UOMEGA - Both omega
  // ─────────────────────────────────────────────────────────────────────────
  if (l1.tag === 'UOmega' && l2.tag === 'UOmega') {
    return emptySuccess;
  }

  // ─────────────────────────────────────────────────────────────────────────
  // VAR - Level variable (de Bruijn)
  // ─────────────────────────────────────────────────────────────────────────
  if (l1.tag === 'Var' && l2.tag === 'Var') {
    if (l1.index === l2.index) {
      return emptySuccess;
    }
    return { success: false, reason: 'conflict' };
  }

  // ─────────────────────────────────────────────────────────────────────────
  // APP - Level operations (USucc, UMax, UIMax as applications)
  // ─────────────────────────────────────────────────────────────────────────
  if (l1.tag === 'App' && l2.tag === 'App') {
    const fnResult = unifyLevels(l1.fn, l2.fn, options);
    if (!fnResult.success) return fnResult;
    const argResult = unifyLevels(l1.arg, l2.arg, options);
    return combineUnificationResults(fnResult, argResult, options);
  }

  // ─────────────────────────────────────────────────────────────────────────
  // CONST - Level operation names (USucc, UMax, UIMax)
  // ─────────────────────────────────────────────────────────────────────────
  if (l1.tag === 'Const' && l2.tag === 'Const') {
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
 * Options:
 * - flexibleVars: If true, de Bruijn variables can be substituted.
 *   Default false (variables are rigid skolems).
 *
 * Returns:
 * - substitutions: Map from de Bruijn indices to terms
 * - metaConstraints: Deferred ?m = t constraints
 * - levelConstraints: Deferred ?l = level constraints
 */
/**
 * Shift Var indices in metaConstraint rhs terms down by 1 when exiting a binder.
 *
 * When unifying Pi bodies, constraints are generated at depth+1 (inside the binder).
 * Level metas don't track their depth, so Var indices in constraint rhs terms need
 * to be decremented by 1 to be correct at the outer depth.
 *
 * Example: Inside Pi body at context [x, B, A, v, u], Var(3) = v.
 * At the outer depth [B, A, v, u], v = Var(2). So the rhs must shift from Var(3) to Var(2).
 *
 * If the rhs contains Var(0) (referring to the binder variable itself), the constraint
 * can't be shifted — but this shouldn't happen for well-formed level constraints since
 * level metas represent universe levels which don't depend on term-level binders.
 */
function adjustMetaConstraintDepth(result: UnifyResult): UnifyResult {
  if (!result.success) return result;
  if (result.metaConstraints.length === 0) return result;

  const adjusted = result.metaConstraints.map(mc => ({
    meta: mc.meta,
    rhs: shiftTerm(mc.rhs, -1, 0),
  }));

  return {
    ...result,
    metaConstraints: adjusted,
  };
}

/**
 * Check if a term contains any variables (recursively).
 * Used for deletion rule checking: if a term contains variables and is
 * unified with itself, those are reflexive variable equations requiring K.
 */
function containsVars(term: TTKTerm): boolean {
  switch (term.tag) {
    case 'Var':
      return true;
    case 'App':
      return containsVars(term.fn) || containsVars(term.arg);
    case 'Binder':
      return containsVars(term.domain) || containsVars(term.body);
    case 'Sort':
      return containsVars(term.level);
    case 'Annot':
      return containsVars(term.term) || containsVars(term.type);
    default:
      // Const, Meta, Hole, ULevel, ULit, UOmega, Match - no vars
      return false;
  }
}

export function unifyTerms(lhs: TTKTerm, rhs: TTKTerm, options: UnifyOptions): UnifyResult {
  // OPTIMIZATION: If terms are structurally identical, they unify immediately.
  // This avoids expensive whnf reduction for identical terms like matching Match
  // expressions containing recursive function calls.
  //
  // EXCEPTION: Reflexive variable equations (x = x) need deletion rule check
  if (isDefinitionallyEqual(lhs, rhs)) {
    // Check if this is a reflexive variable equation without K
    // This includes:
    // 1. Direct variable equations: Var(i) = Var(i)
    // 2. Structurally equal terms containing variables: (f x) = (f x) contains x = x
    if (options.assumeK === false && containsVars(lhs)) {
      return { success: false, reason: 'deletion-rule' };
    }
    return emptySuccess;
  }

  // Check fuel to prevent infinite recursion
  const fuel = options.fuel ?? DEFAULT_UNIFY_FUEL;
  if (fuel <= 0) {
    return { success: false, reason: 'conflict' };
  }
  const nextOptions: UnifyOptions = { ...options, fuel: fuel - 1 };

  // Reduce both to weak head normal form, sharing fuel with unification
  const whnfCtx = { definitions: options.definitions, fuel };
  const a = whnf(lhs, whnfCtx);
  const b = whnf(rhs, whnfCtx);

  // ─────────────────────────────────────────────────────────────────────────
  // META - Metavariable
  //
  // We can't solve ?m = t without knowing ?m's typing context, so we
  // defer these as constraints to be solved later.
  //
  // IMPORTANT: Store the ORIGINAL term (before whnf) as the constraint RHS
  // to avoid exponential term expansion. When whnf expands definitions like
  // `plus n b` → `(match ...) n b`, storing the expanded form causes blowup
  // because nested definitions get expanded repeatedly.
  // ─────────────────────────────────────────────────────────────────────────
  if (a.tag === 'Meta') {
    // a = whnf(lhs) is a Meta. Store the ORIGINAL rhs (before whnf) to avoid expansion.
    return {
      success: true,
      substitutions: [],
      metaConstraints: [{ meta: a.id, rhs: rhs }],
      levelConstraints: [],
    };
  }

  if (b.tag === 'Meta') {
    // b = whnf(rhs) is a Meta. Store the ORIGINAL lhs (before whnf) to avoid expansion.
    return {
      success: true,
      substitutions: [],
      metaConstraints: [{ meta: b.id, rhs: lhs }],
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
      substitutions: [],
      metaConstraints: [{ meta: `hole:${a.id}`, rhs: b }],
      levelConstraints: [],
    };
  }

  if (b.tag === 'Hole') {
    return {
      success: true,
      substitutions: [],
      metaConstraints: [{ meta: `hole:${b.id}`, rhs: a }],
      levelConstraints: [],
    };
  }

  // ─────────────────────────────────────────────────────────────────────────
  // VAR - Variable
  //
  // By default, context variables are rigid/skolem - they represent universally
  // quantified type parameters and cannot be instantiated.
  //
  // With flexibleVars: true, variables can be substituted (like pattern vars
  // during LHS elaboration). If rigidVarsAtOrAbove is set, vars at or above
  // that index are treated as rigid even when flexibleVars is true.
  //
  // Var x vs Var x: trivially equal
  // Var x vs Var y: rigid -> conflict; flexible -> substitute lower with higher
  // Var x vs t:     rigid -> conflict; flexible -> substitute x with t
  // ─────────────────────────────────────────────────────────────────────────

  // Helper: check if a var index is rigid (cannot be substituted)
  const isRigidVar = (index: number): boolean => {
    if (!options.flexibleVars) return true;
    if (options.rigidVarsAtOrAbove !== undefined && index >= options.rigidVarsAtOrAbove) return true;
    return false;
  };

  if (a.tag === 'Var' && b.tag === 'Var') {
    if (a.index === b.index) {
      // Reflexive equation: x = x
      // WITHOUT K: This is the deletion rule - reject it!
      if (options.assumeK === false) {
        return { success: false, reason: 'deletion-rule' };
      }
      // WITH K: Deletion rule succeeds (trivially true)
      return emptySuccess;
    }

    const aRigid = isRigidVar(a.index);
    const bRigid = isRigidVar(b.index);

    // Both rigid: still allowed! This is a refinement (e.g., x = y in dependent matching)
    // Substitute the higher index with the lower (arbitrary choice, but consistent)
    if (aRigid && bRigid) {
      if (options.mode === 'pattern') {
        const [lower, higher] = a.index < b.index
          ? [a.index, b.index]
          : [b.index, a.index];
        return {
          success: true,
          substitutions: [[higher, mkVar(lower)]],
          metaConstraints: [],
          levelConstraints: [],
        };
      } else {
        return { success: false, reason: 'conflict' };
      }
    }

    // At least one is flexible: substitute the flexible one
    if (!aRigid && !bRigid) {
      // Both flexible: substitute lower index with higher (preserves more structure)
      const [lower, higher] = a.index < b.index
        ? [a.index, b.index]
        : [b.index, a.index];
      return {
        success: true,
        substitutions: [[lower, mkVar(higher)]],
        metaConstraints: [],
        levelConstraints: [],
      };
    }

    // One rigid, one flexible: substitute the flexible one with the rigid one
    const [flexibleIdx, rigidIdx] = aRigid ? [b.index, a.index] : [a.index, b.index];
    return {
      success: true,
      substitutions: [[flexibleIdx, mkVar(rigidIdx)]],
      metaConstraints: [],
      levelConstraints: [],
    };
  }

  if (a.tag === 'Var') {
    if (isRigidVar(a.index)) {
      // In pattern mode, rigid variables can be refined by terms
      // e.g., n0 = Succ n2 is valid when learning index constraints
      if (options.mode === 'pattern') {
        if (varOccursIn(a.index, b)) {
          return { success: false, reason: 'cycle' };
        }
        return {
          success: true,
          substitutions: [[a.index, b]],
          metaConstraints: [],
          levelConstraints: [],
        };
      }
      return { success: false, reason: 'conflict' };
    }
    // Occurs check: prevent x = ... x ...
    if (varOccursIn(a.index, b)) {
      return { success: false, reason: 'cycle' };
    }
    return {
      success: true,
      substitutions: [[a.index, b]],
      metaConstraints: [],
      levelConstraints: [],
    };
  }

  if (b.tag === 'Var') {
    if (isRigidVar(b.index)) {
      // In pattern mode, rigid variables can be refined by terms
      if (options.mode === 'pattern') {
        if (varOccursIn(b.index, a)) {
          return { success: false, reason: 'cycle' };
        }
        return {
          success: true,
          substitutions: [[b.index, a]],
          metaConstraints: [],
          levelConstraints: [],
        };
      }
      return { success: false, reason: 'conflict' };
    }
    // Occurs check: prevent x = ... x ...
    if (varOccursIn(b.index, a)) {
      return { success: false, reason: 'cycle' };
    }
    return {
      success: true,
      substitutions: [[b.index, a]],
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
    return unifyLevels(a.level, b.level, nextOptions);
  }

  // ─────────────────────────────────────────────────────────────────────────
  // ULEVEL - Universe level type
  //
  // ULevel is a singleton type - there's only one ULevel, so they always unify.
  // ─────────────────────────────────────────────────────────────────────────
  if (a.tag === 'ULevel' && b.tag === 'ULevel') {
    return emptySuccess;
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
  //
  // SPECIAL CASE: Constructor injectivity with self-unifiability check
  // When both sides are applications of the same constructor from an indexed
  // datatype, check that the indices are self-unifiable before proceeding.
  // ─────────────────────────────────────────────────────────────────────────
  if (a.tag === 'App' && b.tag === 'App') {
    // Extract spines to check if both are constructor applications
    const spineA = extractAppSpine(a);
    const spineB = extractAppSpine(b);

    // Check if both heads are the same constructor
    if (spineA.fn.tag === 'Const' && spineB.fn.tag === 'Const' &&
        spineA.fn.name === spineB.fn.name && options.definitions) {

      const constructorName = spineA.fn.name;

      // Check if this constructor is from an indexed datatype
      const inductiveName = options.definitions.inductiveNameOfConstructor.get(constructorName);
      const inductiveDef = inductiveName ? options.definitions.inductiveTypes.get(inductiveName) : undefined;

      if (inductiveDef && inductiveDef.indexPositions && inductiveDef.indexPositions.length > 0) {
        // This is a constructor of an indexed family
        // Check self-unifiability of indices before applying injectivity

        const indexCount = inductiveDef.indexPositions.length;

        // Extract the last N arguments as indices
        const indicesA = spineA.args.slice(-indexCount);
        const indicesB = spineB.args.slice(-indexCount);

        // Check if indices are self-unifiable
        // We unify indicesA with itself to check if reflexive equations arise
        for (let i = 0; i < indexCount; i++) {
          const indexA = indicesA[i];

          // Defensive check: if index is undefined, skip self-unifiability check
          // This can happen with partially applied constructors or during elaboration
          if (!indexA) continue;

          const selfUnifyResult = unifyTerms(indexA, indexA, nextOptions);
          if (!selfUnifyResult.success && selfUnifyResult.reason === 'deletion-rule') {
            // Indices are not self-unifiable → injectivity blocked
            return {
              success: false,
              reason: 'deletion-rule' // Propagate the deletion-rule failure
            };
          }
        }
      }
    }

    // Proceed with normal App unification
    const fnResult = unifyTerms(a.fn, b.fn, nextOptions);
    if (!fnResult.success) return fnResult;

    const argResult = unifyTerms(a.arg, b.arg, nextOptions);
    return combineUnificationResults(fnResult, argResult, nextOptions);
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
    const domResult = unifyTerms(a.domain, b.domain, nextOptions);
    if (!domResult.success) return domResult;

    // Unify bodies (both are under a binder, so indices align)
    const bodyResult = unifyTerms(a.body, b.body, nextOptions);
    if (!bodyResult.success) return bodyResult;

    // Shift metaConstraint rhs values down by 1 when exiting the binder.
    // Body unification generates constraints at depth+1 (inside the binder),
    // but level metas are used at the outer depth. Var indices in constraint
    // rhs terms need adjustment to refer to the correct binders.
    const adjustedBodyResult = adjustMetaConstraintDepth(bodyResult);

    let result = combineUnificationResults(domResult, adjustedBodyResult, nextOptions);

    // For Let, also unify the definition values
    if (a.binderKind.tag === 'BLet' && b.binderKind.tag === 'BLet') {
      const valResult = unifyTerms(a.binderKind.defVal, b.binderKind.defVal, nextOptions);
      result = combineUnificationResults(result, valResult, nextOptions);
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
    return unifyTerms(a.term, b, nextOptions);
  }

  if (b.tag === 'Annot') {
    return unifyTerms(a, b.term, nextOptions);
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
    const scrutResult = unifyTerms(a.scrutinee, b.scrutinee, nextOptions);
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
      const rhsResult = unifyTerms(clauseA.rhs, clauseB.rhs, nextOptions);
      if (!rhsResult.success) return rhsResult;
      result = combineUnificationResults(result, rhsResult, nextOptions);
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
import { subst } from "./subst";
import { transformVarsInTerm } from "./term";

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
