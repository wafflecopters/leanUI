import { TTKTerm, levelsEqual } from "./kernel";
import { Constraint, MetaVar, TTKContext, TCEnv } from "./term";

/**
 * Get the type of a Var term from the context.
 */
function getVarTypeFromContext(varIndex: number, ctx: TTKContext): TTKTerm | undefined {
  // de Bruijn index: 0 is most recent binding
  // Context is stored with most recent at the END
  const ctxIndex = ctx.length - 1 - varIndex;
  if (ctxIndex >= 0 && ctxIndex < ctx.length) {
    return ctx[ctxIndex].type;
  }
  return undefined;
}

/**
 * Check if a level term contains only concrete values (ULit, or USucc/UMax applied to concrete values).
 */
function levelIsConcrete(level: TTKTerm): boolean {
  switch (level.tag) {
    case 'ULit':
    case 'UOmega':
      return true;
    case 'App':
      // Check if this is USucc or UMax applied to concrete levels
      if (level.fn.tag === 'Const') {
        return levelIsConcrete(level.arg);
      }
      if (level.fn.tag === 'App') {
        // Binary operation like UMax
        return levelIsConcrete(level.fn) && levelIsConcrete(level.arg);
      }
      return false;
    default:
      return false;
  }
}

/**
 * Check if a level term contains a Var (is polymorphic).
 */
function levelContainsVar(level: TTKTerm): boolean {
  switch (level.tag) {
    case 'Var':
      return true;
    case 'ULit':
    case 'UOmega':
    case 'Meta':
    case 'Const':
      return false;
    case 'App':
      return levelContainsVar(level.fn) || levelContainsVar(level.arg);
    default:
      return false;
  }
}

/**
 * Check if two types are compatible for constraint solving.
 * This is specifically checking that when we solve ?M = t, the type of t
 * is compatible with the expected type of ?M.
 *
 * Returns true if compatible, false if definitely incompatible.
 *
 * This is a conservative check that only fails for clear incompatibilities:
 * - Type 0 (concrete) vs Type u (polymorphic) - concrete level vs polymorphic level
 */
function areTypesCompatibleForConstraint(metaType: TTKTerm, rhsType: TTKTerm): boolean {
  // If both are Sort (Type/universe), check for definite incompatibility
  if (metaType.tag === 'Sort' && rhsType.tag === 'Sort') {
    const metaLevel = metaType.level;
    const rhsLevel = rhsType.level;

    // One is concrete (like 0 or Succ(0)), the other contains a Var (like u or Succ(u))
    // This is incompatible: we can't unify a concrete level with a polymorphic one
    const metaConcrete = levelIsConcrete(metaLevel);
    const rhsContainsVar = levelContainsVar(rhsLevel);
    const rhsConcrete = levelIsConcrete(rhsLevel);
    const metaContainsVar = levelContainsVar(metaLevel);

    if ((metaConcrete && rhsContainsVar) || (rhsConcrete && metaContainsVar)) {
      return false;
    }
  }

  // For other cases, be conservative and allow (might be compatible)
  return true;
}

/**
 * Checks if two terms are DEFINITELY incompatible (cannot possibly be unified).
 * Returns true only when the terms definitely cannot be equal, false otherwise.
 *
 * This is conservative: returns false (not definitely different) for cases like:
 * - Different Var indices (might be unified via pattern matching)
 * - Metas/Holes (might be solved to the same value)
 *
 * Returns true only for clear conflicts like different Const names.
 */
function areTermsDefinitelyDifferent(a: TTKTerm, b: TTKTerm): boolean {
  // Get the head of each term (unwrap Apps)
  const headA = getHead(a);
  const headB = getHead(b);

  // If heads are different Consts, they're definitely different
  if (headA.tag === 'Const' && headB.tag === 'Const') {
    return headA.name !== headB.name;
  }

  // If one is a Const and the other is a Var, we can't say they're definitely different
  // (the Var might be instantiated to that Const in a pattern match, or they might
  // both be in scope and the pattern match forces them to be equal)

  // For all other cases, be conservative and say they might be equal
  return false;
}

/**
 * Get the head of a term (unwrap applications).
 */
function getHead(term: TTKTerm): TTKTerm {
  while (term.tag === 'App') {
    term = term.fn;
  }
  return term;
}

export function solveConstraints(
  metaVars: Map<string, MetaVar>,
  constraints: Constraint[],
  liftContext?: TTKContext
): { constraints: Constraint[], metaVars: Map<string, MetaVar> } {
  const stillStuck: Constraint[] = [];

  const newMetaVars = new Map(metaVars);

  for (const constraint of constraints) {
    const meta = newMetaVars.get(constraint.meta);

    // Skip constraints for metas that don't exist in the map.
    // This happens when unification creates constraints for unelaborated Holes
    // (with names like 'hole:f_type') which haven't been converted to Metas yet.
    if (!meta) continue;

    // If meta already has a solution, check that the new constraint is compatible
    // This catches cases like ?B=Bool and ?B=Nat which are conflicting
    if (meta.solution !== undefined) {
      // Only fail if the terms are DEFINITELY different (like different Const names)
      // Be lenient for cases like different Var indices (might be unified via pattern matching)
      if (areTermsDefinitelyDifferent(meta.solution, constraint.rhs)) {
        // Throw an error for conflicting constraints
        throw new Error(`Conflicting constraints for meta ${constraint.meta}: already solved to different value`);
      }
      continue;
    }

    // When liftContext is provided, use it for the scope check.
    // This allows solving constraints where the RHS references variables
    // that weren't in scope when the meta was created, but are in the current context.
    const effectiveContext = liftContext ?? meta.ctx;
    if (canSolveMetaInContext(constraint.rhs, effectiveContext.length)) {
      // Type compatibility check: if RHS is a Var, verify its type matches meta's expected type
      // This catches cases like Type 0 vs Type u (concrete level vs polymorphic level)
      if (constraint.rhs.tag === 'Var') {
        const rhsType = getVarTypeFromContext(constraint.rhs.index, constraint.ctx);
        if (rhsType && !areTypesCompatibleForConstraint(meta.type, rhsType)) {
          throw new Error(`Type mismatch for meta ${constraint.meta}: expected type and actual type are incompatible`);
        }
      }
      newMetaVars.set(constraint.meta, { ...meta, solution: constraint.rhs, ctx: effectiveContext });
    } else {
      stillStuck.push(constraint);
    }
  }

  return { constraints: stillStuck, metaVars: newMetaVars };
}

export function canSolveMeta(meta: MetaVar, rhs: TTKTerm): boolean {
  return canSolveMetaInContext(rhs, meta.ctx.length);
}

function canSolveMetaInContext(rhs: TTKTerm, contextLength: number): boolean {
  return maxFreeVarIndex(rhs) < contextLength;
}

function maxFreeVarIndex(term: TTKTerm): number {
  return maxFreeVarIndexAt(term, 0)
}

function maxFreeVarIndexAt(term: TTKTerm, depth: number): number {
  switch (term.tag) {
    case 'Var':
      return term.index >= depth ? term.index - depth : -1;
    case 'Sort':
    case 'Const':
      return -1;
    case 'Binder':
      if (term.binderKind.tag === 'BLet') {
        // In Let, defVal is at depth, body is at depth+1
        return Math.max(
          maxFreeVarIndexAt(term.domain, depth),
          maxFreeVarIndexAt(term.binderKind.defVal, depth),
          maxFreeVarIndexAt(term.body, depth + 1)
        );
      } else {
        // Pi, Lam, etc.
        return Math.max(
          maxFreeVarIndexAt(term.domain, depth),
          maxFreeVarIndexAt(term.body, depth + 1)
        );
      }
    case 'App':
      return Math.max(
        maxFreeVarIndexAt(term.fn, depth),
        maxFreeVarIndexAt(term.arg, depth),
      );
    case 'Hole':
    case 'Meta':
      return -Infinity; // No free variables
    case 'Annot':
      return Math.max(maxFreeVarIndexAt(term.term, depth), maxFreeVarIndexAt(term.type, depth));
    case 'Match':
      return Math.max(maxFreeVarIndexAt(term.scrutinee, depth), ...term.clauses.map(c => maxFreeVarIndexAt(c.rhs, depth)));

    case 'ULevel':
    case 'ULit':
    case 'UOmega':
      return -1;
  }
}