import { TTKTerm, levelsEqual, prettyPrint } from "./kernel";
import { shiftTerm, minFreeVarIndex } from "./subst";
import { Constraint, DefinitionsMap, MetaVar, TTKContext } from "./term";
import { unifyTerms } from "./unify";
import { whnf } from "./whnf";

/**
 * Checks if two terms are DEFINITELY incompatible (cannot possibly be unified).
 * Returns true only when the terms definitely cannot be equal, false otherwise.
 *
 * This is conservative: returns false (not definitely different) for cases like:
 * - Different Var indices at the top level (might be the same variable at
 *   different de Bruijn indices due to context depth changes)
 * - Metas/Holes (might be solved to the same value)
 * - Defined function applications (might reduce to the same value)
 *
 * Returns true when:
 * - Both terms have different constructor heads (disjointness)
 * - Same constructor head but some argument is definitely different (injectivity)
 *
 * Constructor injectivity enables deeper Var comparison: when two terms share
 * the same constructor head (e.g., both are `Succ _`), their arguments must be
 * equal. Inside these arguments, Var-Var differences are checked using context
 * binding name lookup when contexts are available. This catches cases like
 * `Succ x` vs `Succ y` where x and y are genuinely different variables.
 *
 * The Var name check is restricted to constructor argument positions because
 * at the top level, Var index differences commonly arise from context depth
 * shifts (e.g., let-bindings), not genuine variable differences. Inside
 * constructor arguments, the terms were produced by the same unification
 * decomposition, making Var index differences more reliable indicators of
 * genuine variable differences.
 */
function areTermsDefinitelyDifferent(
  a: TTKTerm, b: TTKTerm,
  definitions?: DefinitionsMap,
  ctxA?: TTKContext, ctxB?: TTKContext,
  _insideConstructorArg = false
): boolean {
  // If definitions are available, reduce to WHNF first.
  // This handles cases like `plus Zero Zero` reducing to `Zero`.
  let wa = a, wb = b;
  if (definitions) {
    wa = whnf(a, { definitions });
    wb = whnf(b, { definitions });
  }

  // Compare heads (unwrap applications)
  const headA = getHead(wa);
  const headB = getHead(wb);

  if (headA.tag === 'Const' && headB.tag === 'Const') {
    const isConstructorOrType = (name: string): boolean => {
      if (!definitions) return false;
      return definitions.inductiveNameOfConstructor.has(name)
        || definitions.inductiveTypes.has(name);
    };

    if (headA.name !== headB.name) {
      if (definitions) {
        // Only report conflict if BOTH heads are constructors (not defined functions).
        // A defined function might reduce further with different arguments,
        // but constructors are injective and distinct — different constructor heads
        // means definitely different terms.
        return isConstructorOrType(headA.name) && isConstructorOrType(headB.name);
      }
      // Without definitions, we can only detect conflicts between bare Const terms
      // (no App wrapping) since we can't distinguish constructors from functions.
      return wa.tag === 'Const' && wb.tag === 'Const';
    }

    // Same constructor head — constructors are injective, so if any corresponding
    // argument is definitely different, the whole terms are definitely different.
    // e.g., Succ Zero ≠ Succ (Succ x) because Zero ≠ Succ x
    if (definitions && isConstructorOrType(headA.name)) {
      const argsA = getSpine(wa);
      const argsB = getSpine(wb);
      if (argsA.length === argsB.length) {
        for (let i = 0; i < argsA.length; i++) {
          if (areTermsDefinitelyDifferent(argsA[i], argsB[i], definitions, ctxA, ctxB, true)) {
            return true;
          }
        }
      }
    }

    return false;
  }

  // Var vs constructor conflict: a named (non-wildcard) rigid variable cannot
  // equal a constructor application. E.g., if a meta is solved to `y` (a named
  // function parameter) and the constraint says `Succ x`, that's a definite
  // conflict. However, pattern wildcards (`?0`, `?1`, `_`) CAN match constructors
  // since they're flexible binding positions.
  if (definitions) {
    const isConstructorHead = (head: TTKTerm): boolean =>
      head.tag === 'Const' && definitions.inductiveNameOfConstructor.has(head.name);
    const isNamedVar = (head: TTKTerm, ctx?: TTKContext): boolean => {
      if (head.tag !== 'Var' || !ctx) return false;
      const binding = ctx[ctx.length - 1 - head.index];
      if (!binding) return false;
      // Pattern wildcards start with '?' or '_' — they're flexible and can match anything
      return !binding.name.startsWith('?') && !binding.name.startsWith('_');
    };
    if ((isNamedVar(headA, ctxA) && isConstructorHead(headB))
      || (isNamedVar(headB, ctxB) && isConstructorHead(headA))) {
      return true;
    }
  }

  // Var-Var comparison with context-based name lookup — ONLY inside constructor
  // arguments. At the top level, different Var indices commonly arise from
  // context depth shifts (e.g., a let-binding for a recursive call shifts all
  // indices by 1), so Var-Var differences are not reliable. But inside
  // constructor arguments (reached via injectivity), both terms were decomposed
  // from the same constructor application, so Var differences are meaningful.
  //
  // We look up binding names in the provided contexts. Different names indicate
  // genuinely different variables (e.g., x vs y). Same names are treated
  // conservatively (might be the same variable at shifted indices).
  if (_insideConstructorArg && headA.tag === 'Var' && headB.tag === 'Var' && ctxA && ctxB) {
    if (headA.index !== headB.index) {
      const bindingA = ctxA[ctxA.length - 1 - headA.index];
      const bindingB = ctxB[ctxB.length - 1 - headB.index];
      if (bindingA && bindingB && bindingA.name !== bindingB.name) {
        return true;
      }
    }
  }

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
 * Get the argument spine of a term (collect App arguments left to right).
 * e.g., App(App(f, a), b) → [a, b]
 */
function getSpine(term: TTKTerm): TTKTerm[] {
  const args: TTKTerm[] = [];
  while (term.tag === 'App') {
    args.push(term.arg);
    term = term.fn;
  }
  args.reverse();
  return args;
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

  // Both levels are fully concrete but different - this is OK
  // Different concrete levels can arise from context depth differences or
  // zonking that resolved levels at different points. Let the constraint be solved.
  return null;
}

/**
 * Get the type of a variable from the context.
 * Returns undefined if the index is out of bounds.
 */
function getVarTypeFromContext(ctx: TTKContext, varIndex: number): TTKTerm | undefined {
  const binding = ctx[ctx.length - 1 - varIndex];
  return binding?.type;
}

/**
 * Normalize a constraint's RHS to a target context depth by shifting de Bruijn
 * indices. This ensures constraints for the same meta use a consistent index
 * scheme, making Var-vs-Var conflict detection a simple index comparison.
 *
 * Returns null if the constraint references inner-scope variables that cannot
 * be shifted away (the constraint is "stuck" at its current depth).
 */
export function normalizeConstraintDepth(
  constraint: Constraint,
  targetContext: TTKContext
): { normalized: Constraint; shifted: boolean } | null {
  const depthDiff = constraint.ctx.length - targetContext.length;
  if (depthDiff === 0) {
    return { normalized: constraint, shifted: false };
  }
  if (depthDiff > 0) {
    // Constraint from deeper context: shift down to target depth.
    // Only safe if no free variables would go negative after shifting.
    const minIdx = minFreeVarIndex(constraint.rhs);
    if (minIdx < depthDiff) return null; // stuck: references inner-scope variables
    const rhs = shiftTerm(constraint.rhs, -depthDiff, 0);
    const rhsType = constraint.rhsType ? shiftTerm(constraint.rhsType, -depthDiff, 0) : undefined;
    return { normalized: { ...constraint, rhs, rhsType, ctx: targetContext }, shifted: true };
  }
  // Constraint from shallower context: shift up to target depth.
  const rhs = shiftTerm(constraint.rhs, -depthDiff, 0);
  const rhsType = constraint.rhsType ? shiftTerm(constraint.rhsType, -depthDiff, 0) : undefined;
  return { normalized: { ...constraint, rhs, rhsType, ctx: targetContext }, shifted: true };
}

export function solveConstraints(
  metaVars: Map<string, MetaVar>,
  constraints: Constraint[],
  liftContext?: TTKContext,
  definitions?: DefinitionsMap
): { constraints: Constraint[], metaVars: Map<string, MetaVar> } {
  const stillStuck: Constraint[] = [];

  const newMetaVars = new Map(metaVars);

  // Use a queue so forwarded constraints can be processed in the same pass
  const queue = [...constraints];
  let fuel = queue.length * 3; // Prevent infinite loops from cyclic meta chains
  while (queue.length > 0 && fuel-- > 0) {
    const constraint = queue.shift()!;
    const meta = newMetaVars.get(constraint.meta);

    // Skip constraints for metas that don't exist in the map.
    // This happens when unification creates constraints for unelaborated Holes
    // (with names like 'hole:f_type') which haven't been converted to Metas yet.
    if (!meta) continue;

    // Determine the effective context for this meta. When liftContext is provided,
    // it overrides the meta's creation context for scope checking.
    const effectiveContext = liftContext ?? meta.ctx;

    // Normalize the constraint's RHS to the effective context depth.
    // This ensures all subsequent code can assume consistent de Bruijn indices.
    const normResult = normalizeConstraintDepth(constraint, effectiveContext);
    if (normResult === null) {
      // Constraint references inner-scope variables that can't be shifted away.
      // However, if the meta already has a solution, we can still detect structural
      // conflicts (constructor head mismatches) using the original non-normalized terms,
      // since constructor heads are depth-independent.
      if (meta.solution !== undefined && meta.solution.tag !== 'Meta') {
        // Resolve the constraint RHS through meta chains
        let resolvedRhs = constraint.rhs;
        while (resolvedRhs.tag === 'Meta') {
          const rhsMeta = newMetaVars.get(resolvedRhs.id);
          if (rhsMeta?.solution) {
            resolvedRhs = rhsMeta.solution;
          } else {
            break;
          }
        }
        // Check structural conflicts using original contexts (safe for constructor heads)
        if (areTermsDefinitelyDifferent(meta.solution, resolvedRhs, definitions, effectiveContext, constraint.ctx)) {
          const names = effectiveContext.map(c => c.name).reverse();
          const metaTypeStr = prettyPrint(meta.type, names);
          throw new Error(`Implicit argument conflict for ${constraint.meta} : ${metaTypeStr}: inferred ${prettyPrint(meta.solution, names)} but required to be ${prettyPrint(resolvedRhs, constraint.ctx.map(c => c.name).reverse())}`);
        }
        // Try unification — may detect conflicts even when normalization can't shift
        const unifyResult = unifyTerms(meta.solution, resolvedRhs, {
          mode: 'pattern',
          flexibleVars: true,
          definitions,
        });
        if (!unifyResult.success) {
          const names = effectiveContext.map(c => c.name).reverse();
          const metaTypeStr = prettyPrint(meta.type, names);
          throw new Error(`Implicit argument conflict for ${constraint.meta} : ${metaTypeStr}: inferred ${prettyPrint(meta.solution, names)} but required to be ${prettyPrint(resolvedRhs, constraint.ctx.map(c => c.name).reverse())}`);
        }
        // Queue propagated sub-constraints from unification
        for (const mc of unifyResult.metaConstraints) {
          queue.push({ ctx: effectiveContext, meta: mc.meta, rhs: mc.rhs });
        }
      }
      stillStuck.push(constraint);
      continue;
    }
    const normConstraint = normResult.normalized;

    // If meta already has a solution, propagate the constraint through the solution.
    // This handles meta chains (e.g., _10 := Meta(_14), then _10 := Succ x → forward to _14)
    // and structural decomposition (e.g., _14 := Succ _12, then _14 := Succ x → _12 := x).
    if (meta.solution !== undefined) {
      // Resolve the constraint RHS through meta solutions so we compare concrete
      // terms, not Meta wrappers. E.g., if rhs is Meta(_7) and _7 is solved to Succ y,
      // we need to compare against Succ y, not Meta(_7).
      let resolvedRhs = normConstraint.rhs;
      while (resolvedRhs.tag === 'Meta') {
        const rhsMeta = newMetaVars.get(resolvedRhs.id);
        if (rhsMeta?.solution) {
          resolvedRhs = rhsMeta.solution;
        } else {
          break;
        }
      }

      if (meta.solution.tag === 'Meta') {
        // Forward constraint to the meta in the solution
        queue.push({ ...normConstraint, meta: meta.solution.id, rhs: resolvedRhs });
      } else {
        // Check for definite structural conflicts (constructor head mismatches
        // or context-verified Var differences).
        // After normalization, both solution and resolvedRhs are at effectiveContext depth.
        if (areTermsDefinitelyDifferent(meta.solution, resolvedRhs, definitions, effectiveContext, effectiveContext)) {
          const names = effectiveContext.map(c => c.name).reverse();
          const metaTypeStr = prettyPrint(meta.type, names);
          throw new Error(`Implicit argument conflict for ${normConstraint.meta} : ${metaTypeStr}: inferred ${prettyPrint(meta.solution, names)} but required to be ${prettyPrint(resolvedRhs, names)}`);
        }
        // Var-vs-Var conflict detection.
        // After normalization, both solution and resolvedRhs are at effectiveContext
        // depth, so different indices mean genuinely different variables — with guards:
        //
        // 1. Both indices must be in-scope (< effectiveContext.length). A free variable
        //    (index >= context length) references the outer scope and may alias a
        //    captured variable at a different index.
        //
        // 2. The meta's type must not be Sort. In with-clause contexts, Type-valued
        //    metas often get constraints from pattern wildcards that capture the same
        //    type variable at different indices. Since these wildcards refer to the same
        //    type, the index difference is a false positive.
        //
        // 3. The meta's type must not be an unsolved Meta (too early to check).
        //    Resolve through solved metas first — the type might be Meta(?m0) where
        //    ?m0 has been solved to Nat in this same pass.
        let resolvedMetaType = meta.type;
        while (resolvedMetaType.tag === 'Meta') {
          const typeMeta = newMetaVars.get(resolvedMetaType.id);
          if (typeMeta?.solution) {
            resolvedMetaType = typeMeta.solution;
          } else {
            break;
          }
        }
        if (meta.solution.tag === 'Var' && resolvedRhs.tag === 'Var'
          && meta.solution.index !== resolvedRhs.index
          && resolvedMetaType.tag !== 'Meta'
          && resolvedMetaType.tag !== 'Sort'
          && meta.solution.index < effectiveContext.length
          && resolvedRhs.index < effectiveContext.length) {
          // Both variables must be named (non-wildcard) to be a real conflict.
          // Pattern wildcards (?0, _x, etc.) are flexible — they represent pattern
          // variables that may be unified, not rigid program variables.
          const solBinding = effectiveContext[effectiveContext.length - 1 - meta.solution.index];
          const rhsBinding = effectiveContext[effectiveContext.length - 1 - resolvedRhs.index];
          const isWildcard = (name: string) => name.startsWith('?') || name.startsWith('_');
          const solIsRigid = solBinding && !isWildcard(solBinding.name);
          const rhsIsRigid = rhsBinding && !isWildcard(rhsBinding.name);
          if (solIsRigid && rhsIsRigid) {
            // Type compatibility guard: only flag as a conflict if both Vars have
            // types that match the meta's type. This prevents false positives from
            // imprecise constraint propagation where a Var with a mismatched type
            // (e.g., a Type-valued wildcard) gets propagated as a solution for a
            // Nat-valued meta.
            const solType = getVarTypeFromContext(effectiveContext, meta.solution.index);
            const rhsType = getVarTypeFromContext(effectiveContext, resolvedRhs.index);
            const metaIsConst = resolvedMetaType.tag === 'Const';
            const solTypeMatches = !metaIsConst || !solType || (solType.tag === 'Const' && solType.name === (resolvedMetaType as any).name);
            const rhsTypeMatches = !metaIsConst || !rhsType || (rhsType.tag === 'Const' && rhsType.name === (resolvedMetaType as any).name);
            if (solTypeMatches && rhsTypeMatches) {
              const names = effectiveContext.map(c => c.name).reverse();
              const metaTypeStr = prettyPrint(resolvedMetaType, names);
              throw new Error(`Implicit argument conflict for ${normConstraint.meta} : ${metaTypeStr}: inferred ${prettyPrint(meta.solution, names)} but required to be ${prettyPrint(resolvedRhs, names)}`);
            }
          }
        }
        // Use pattern mode unification for meta decomposition and propagation.
        // E.g., if solution is Succ(?m) and rhs is Succ(x), this creates ?m := x.
        // Both sides are at effectiveContext depth after normalization.
        const unifyResult = unifyTerms(meta.solution, resolvedRhs, {
          mode: 'pattern',
          flexibleVars: true,
          definitions,
        });
        if (!unifyResult.success) {
          const names = effectiveContext.map(c => c.name).reverse();
          const metaTypeStr = prettyPrint(meta.type, names);
          throw new Error(`Implicit argument conflict for ${normConstraint.meta} : ${metaTypeStr}: inferred ${prettyPrint(meta.solution, names)} but required to be ${prettyPrint(resolvedRhs, names)}`);
        }
        // Queue any new meta constraints from the unification.
        // These inherit effectiveContext as their ctx — when dequeued, they'll
        // be re-normalized to the TARGET meta's effective context.
        for (const mc of unifyResult.metaConstraints) {
          queue.push({ ctx: effectiveContext, meta: mc.meta, rhs: mc.rhs });
        }
      }
      continue;
    }

    // No solution yet: try to solve
    if (canSolveMetaInContext(normConstraint.rhs, effectiveContext.length)) {
      // Type compatibility check: if rhs is a Var, check that its type is compatible
      // with the meta's type. This catches cases where an inductive has {A : Type}
      // but a constructor has {A : Type u} with a bound level variable.
      if (normConstraint.rhs.tag === 'Var') {
        const rhsType = getVarTypeFromContext(effectiveContext, normConstraint.rhs.index);
        if (rhsType) {
          const typeError = checkTypeCompatibility(meta.type, rhsType);
          if (typeError) {
            throw new Error(`Type mismatch for meta ${normConstraint.meta}: ${typeError}`);
          }
        }
      }
      newMetaVars.set(normConstraint.meta, { ...meta, solution: normConstraint.rhs, ctx: effectiveContext });
    } else {
      stillStuck.push(constraint); // original constraint, retains original ctx for future attempts
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
