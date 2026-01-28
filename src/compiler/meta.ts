import { TTKTerm, levelsEqual } from "./kernel";
import { Constraint, MetaVar, TTKContext } from "./term";

/**
 * Checks if two terms are DEFINITELY incompatible (cannot possibly be unified).
 * Returns true only when the terms definitely cannot be equal, false otherwise.
 *
 * This is conservative: returns false (not definitely different) for cases like:
 * - Different Var indices (might be unified via pattern matching)
 * - Metas/Holes (might be solved to the same value)
 * - Function applications (might reduce to the same value)
 *
 * Returns true only for clear conflicts like different Const names with no applications.
 */
function areTermsDefinitelyDifferent(a: TTKTerm, b: TTKTerm): boolean {
  // If either term is an application, it might reduce, so we can't say they're
  // definitely different. E.g., `plus Zero Zero` might reduce to `Zero`.
  if (a.tag === 'App' || b.tag === 'App') {
    return false;
  }

  // Both terms are not applications - compare directly
  // If both are Consts with different names, they're definitely different
  if (a.tag === 'Const' && b.tag === 'Const') {
    return a.name !== b.name;
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

/**
 * Check if a level contains a bound level variable (de Bruijn Var).
 * Returns true if the level contains any Var (bound level variable).
 */
function levelContainsBoundVar(level: TTKTerm): boolean {
  switch (level.tag) {
    case 'ULit':
    case 'UOmega':
    case 'ULevel':
    case 'Const':
    case 'Meta':
    case 'Hole':
      return false;
    case 'Var':
      return true;
    case 'App':
      return levelContainsBoundVar(level.fn) || levelContainsBoundVar(level.arg);
    default:
      return false;
  }
}

/**
 * Check if a level contains a solvable meta or hole.
 * Returns true if the level contains any Meta or Hole (which can be solved).
 */
function levelContainsMeta(level: TTKTerm): boolean {
  switch (level.tag) {
    case 'ULit':
    case 'UOmega':
    case 'ULevel':
    case 'Const':
    case 'Var':
      return false;
    case 'Meta':
    case 'Hole':
      return true;
    case 'App':
      return levelContainsMeta(level.fn) || levelContainsMeta(level.arg);
    default:
      return false;
  }
}

/**
 * Check type compatibility when solving a constraint ?m = t.
 *
 * When the meta has type Sort(l1) and the rhs has type Sort(l2),
 * we need to ensure the levels are compatible:
 * - If meta's level is concrete (no metas) and rhs's level has a bound Var, REJECT
 * - If meta's level has a solvable meta, it can be unified with any level
 *
 * This catches the case where an inductive has {A : Type} but a constructor
 * has {A : Type u} with u being a bound level variable - these are incompatible.
 *
 * Returns null if types are compatible, or an error message if not.
 */
function checkTypeCompatibility(
  metaType: TTKTerm,
  rhsType: TTKTerm
): string | null {
  // Both must be Sorts for this check to apply
  if (metaType.tag !== 'Sort' || rhsType.tag !== 'Sort') {
    return null;  // Not a Sort type mismatch - let other checks handle it
  }

  const metaLevel = metaType.level;
  const rhsLevel = rhsType.level;

  // If levels are equal, types are compatible
  if (levelsEqual(metaLevel, rhsLevel)) {
    return null;
  }

  // If meta's level contains a solvable meta/hole, it can be unified with anything
  // The level unification will handle ensuring consistency
  if (levelContainsMeta(metaLevel)) {
    return null;
  }

  // If meta's level contains a bound var, be permissive
  // The bound vars might refer to the same binding with different de Bruijn indices
  // due to context depth differences
  if (levelContainsBoundVar(metaLevel)) {
    return null;
  }

  // Meta's level is concrete (no metas, no bound vars)
  // If rhs's level has a bound Var, they're incompatible:
  // the concrete level cannot be unified with a bound level variable
  if (levelContainsBoundVar(rhsLevel)) {
    return `type level mismatch: expected concrete level but got bound level variable`;
  }

  // Both levels are fully concrete but different
  return `type level mismatch: different concrete levels`;
}

/**
 * Get the type of a variable from the context.
 * Returns undefined if the index is out of bounds.
 */
function getVarTypeFromContext(ctx: TTKContext, varIndex: number): TTKTerm | undefined {
  const binding = ctx[ctx.length - 1 - varIndex];
  return binding?.type;
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
      // Type compatibility check: if rhs is a Var, check that its type is compatible
      // with the meta's type. This catches cases where an inductive has {A : Type}
      // but a constructor has {A : Type u} with a bound level variable.
      if (constraint.rhs.tag === 'Var') {
        const rhsType = getVarTypeFromContext(constraint.ctx, constraint.rhs.index);
        if (rhsType) {
          const typeError = checkTypeCompatibility(meta.type, rhsType);
          if (typeError) {
            throw new Error(`Type mismatch for meta ${constraint.meta}: ${typeError}`);
          }
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