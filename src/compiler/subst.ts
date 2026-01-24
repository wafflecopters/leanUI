import { mkVar, TTKBinderKind, TTKTerm } from "./kernel";
import { Constraint, MetaVar, TTKContext, transformVarsInTerm } from "./term";

/**
 * Substitute term s for variable with index n in term t
 * This is the core operation for beta-reduction and let-expansion
 */
export function subst(index: number, replacement: TTKTerm, term: TTKTerm): TTKTerm {
  return substHelper(index, replacement, term, 0);
}

function substHelper(targetIndex: number, replacement: TTKTerm, term: TTKTerm, depth: number): TTKTerm {
  switch (term.tag) {
    case 'Var':
      if (term.index === targetIndex + depth) {
        // Replace with the replacement, shifted to account for binders we've gone under
        return shift(depth, replacement, 0);
      } else if (term.index > targetIndex + depth) {
        // Decrement indices above the substituted variable
        // because we're removing that binder from the context
        return { tag: 'Var', index: term.index - 1 };
      }
      return term;

    case 'Sort':
    case 'Const':
      return term;

    case 'Binder': {
      const newDomain = substHelper(targetIndex, replacement, term.domain, depth);
      const newBody = substHelper(targetIndex, replacement, term.body, depth + 1);

      let newBinderKind: TTKBinderKind;
      if (term.binderKind.tag === 'BLet') {
        const newDefVal = substHelper(targetIndex, replacement, term.binderKind.defVal, depth);
        newBinderKind = { tag: 'BLet', defVal: newDefVal };
      } else {
        newBinderKind = term.binderKind;
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
        fn: substHelper(targetIndex, replacement, term.fn, depth),
        arg: substHelper(targetIndex, replacement, term.arg, depth)
      };

    case 'Hole':
      return { tag: 'Hole', id: term.id };

    case 'Meta':
      return { tag: 'Meta', id: term.id };

    case 'Annot':
      return {
        tag: 'Annot',
        term: substHelper(targetIndex, replacement, term.term, depth),
        type: substHelper(targetIndex, replacement, term.type, depth)
      };

    case 'Match':
      return {
        tag: 'Match',
        scrutinee: substHelper(targetIndex, replacement, term.scrutinee, depth),
        clauses: term.clauses.map(c => ({
          patterns: c.patterns,
          rhs: substHelper(targetIndex, replacement, c.rhs, depth)
        }))
      };

    case 'ULevel':
    case 'ULit':
    case 'UOmega':
      return term;
  }
}

/**
 * Shift De Bruijn indices in a term
 */
function shift(amount: number, term: TTKTerm, cutoff: number): TTKTerm {
  switch (term.tag) {
    case 'Var':
      return term.index >= cutoff
        ? { tag: 'Var', index: term.index + amount }
        : term;

    case 'Sort':
    case 'Const':
      return term;

    case 'Binder': {
      const newDomain = shift(amount, term.domain, cutoff);
      const newBody = shift(amount, term.body, cutoff + 1);

      let newBinderKind: TTKBinderKind;
      if (term.binderKind.tag === 'BLet') {
        const newDefVal = shift(amount, term.binderKind.defVal, cutoff);
        newBinderKind = { tag: 'BLet', defVal: newDefVal };
      } else {
        newBinderKind = term.binderKind;
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
        fn: shift(amount, term.fn, cutoff),
        arg: shift(amount, term.arg, cutoff)
      };

    case 'Hole':
      return { tag: 'Hole', id: term.id };

    case 'Meta':
      return { tag: 'Meta', id: term.id };

    case 'Annot':
      return {
        tag: 'Annot',
        term: shift(amount, term.term, cutoff),
        type: shift(amount, term.type, cutoff)
      };

    case 'Match':
      return {
        tag: 'Match',
        scrutinee: shift(amount, term.scrutinee, cutoff),
        clauses: term.clauses.map(c => ({
          patterns: c.patterns,
          rhs: shift(amount, c.rhs, cutoff)
        }))
      };

    case 'ULevel':
    case 'ULit':
    case 'UOmega':
      return term;
  }
}

/**
 * Substitute multiple pattern bindings simultaneously.
 *
 * Unlike `subst`, this does NOT shift indices after substitution.
 * It replaces Var(0) with bindings[n-1], Var(1) with bindings[n-2], etc.
 * (where n = bindings.length), and shifts remaining variables down by n.
 *
 * This is used for pattern matching evaluation where we replace pattern
 * variables with their matched values all at once.
 *
 * @param bindings - The values to substitute, in order of pattern appearance
 *                   (first pattern's binding is bindings[0])
 * @param term - The term to substitute into
 */
export function substPatternBindings(bindings: TTKTerm[], term: TTKTerm): TTKTerm {
  return substPatternBindingsHelper(bindings, term, 0);
}

function substPatternBindingsHelper(bindings: TTKTerm[], term: TTKTerm, depth: number): TTKTerm {
  const n = bindings.length;

  switch (term.tag) {
    case 'Var': {
      const adjustedIndex = term.index - depth;
      if (adjustedIndex >= 0 && adjustedIndex < n) {
        // This is a pattern variable - replace with corresponding binding
        // Var(0) -> bindings[n-1] (last binding, most recent)
        // Var(n-1) -> bindings[0] (first binding)
        const binding = bindings[n - 1 - adjustedIndex];
        // Shift the binding up by depth to account for binders we've entered
        return depth > 0 ? shiftTerm(binding, depth, 0) : binding;
      } else if (adjustedIndex >= n) {
        // This references something outside the pattern bindings - shift down
        return { tag: 'Var', index: term.index - n };
      }
      // adjustedIndex < 0 means this is bound by an inner binder
      return term;
    }

    case 'Sort':
    case 'Const':
      return term;

    case 'Hole':
      return { tag: 'Hole', id: term.id };

    case 'Meta':
      return { tag: 'Meta', id: term.id };

    case 'Binder': {
      const newDomain = substPatternBindingsHelper(bindings, term.domain, depth);
      const newBody = substPatternBindingsHelper(bindings, term.body, depth + 1);

      let newBinderKind: TTKBinderKind;
      if (term.binderKind.tag === 'BLet') {
        const newDefVal = substPatternBindingsHelper(bindings, term.binderKind.defVal, depth);
        newBinderKind = { tag: 'BLet', defVal: newDefVal };
      } else {
        newBinderKind = term.binderKind;
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
        fn: substPatternBindingsHelper(bindings, term.fn, depth),
        arg: substPatternBindingsHelper(bindings, term.arg, depth)
      };

    case 'Annot':
      return {
        tag: 'Annot',
        term: substPatternBindingsHelper(bindings, term.term, depth),
        type: substPatternBindingsHelper(bindings, term.type, depth)
      };

    case 'Match':
      return {
        tag: 'Match',
        scrutinee: substPatternBindingsHelper(bindings, term.scrutinee, depth),
        clauses: term.clauses.map(c => ({
          patterns: c.patterns,
          rhs: substPatternBindingsHelper(bindings, c.rhs, depth)
        }))
      };

    case 'ULevel':
    case 'ULit':
    case 'UOmega':
      return term;
  }
}

/**
 * Shift De Bruijn indices in a term (exported version)
 */
export function shiftTerm(term: TTKTerm, amount: number, cutoff: number): TTKTerm {
  return shift(amount, term, cutoff);
}

/**
 * Find the minimum free variable index in a term.
 * Returns Infinity if the term has no free variables.
 * Used to check for escaping variables before shifting.
 */
export function minFreeVarIndex(term: TTKTerm): number {
  return minFreeVarIndexHelper(term, 0);
}

/**
 * Check if a term contains a reference to a specific free variable index.
 */
export function containsVarIndex(term: TTKTerm, targetIndex: number): boolean {
  return containsVarIndexHelper(term, targetIndex, 0);
}

/**
 * Get all free variable indices in a term.
 * Returns an array of indices (De Bruijn levels) that appear free in the term.
 */
export function freeVarIndices(term: TTKTerm): number[] {
  const indices = new Set<number>();
  freeVarIndicesHelper(term, 0, indices);
  return Array.from(indices);
}

function freeVarIndicesHelper(term: TTKTerm, depth: number, indices: Set<number>): void {
  switch (term.tag) {
    case 'Var':
      // Only count as free if index >= depth (not bound by local binders)
      if (term.index >= depth) {
        indices.add(term.index - depth);
      }
      break;
    case 'Sort':
    case 'Const':
      break;
    case 'Binder':
      freeVarIndicesHelper(term.domain, depth, indices);
      freeVarIndicesHelper(term.body, depth + 1, indices);
      if (term.binderKind.tag === 'BLet') {
        freeVarIndicesHelper(term.binderKind.defVal, depth, indices);
      }
      break;
    case 'App':
      freeVarIndicesHelper(term.fn, depth, indices);
      freeVarIndicesHelper(term.arg, depth, indices);
      break;
    case 'Hole':
    case 'Meta':
      // No free variables in holes/metas
      break;
    case 'Annot':
      freeVarIndicesHelper(term.term, depth, indices);
      freeVarIndicesHelper(term.type, depth, indices);
      break;
    case 'Match':
      freeVarIndicesHelper(term.scrutinee, depth, indices);
      for (const clause of term.clauses) {
        freeVarIndicesHelper(clause.rhs, depth, indices);
      }
      break;

    case 'ULevel':
    case 'ULit':
    case 'UOmega':
      // No free variables in these
      break;
  }
}

function containsVarIndexHelper(term: TTKTerm, targetIndex: number, depth: number): boolean {
  switch (term.tag) {
    case 'Var':
      return term.index === targetIndex + depth;
    case 'Sort':
    case 'Const':
      return false;
    case 'Binder':
      if (containsVarIndexHelper(term.domain, targetIndex, depth)) return true;
      if (containsVarIndexHelper(term.body, targetIndex, depth + 1)) return true;
      if (term.binderKind.tag === 'BLet' &&
        containsVarIndexHelper(term.binderKind.defVal, targetIndex, depth)) return true;
      return false;
    case 'App':
      return containsVarIndexHelper(term.fn, targetIndex, depth) ||
        containsVarIndexHelper(term.arg, targetIndex, depth);
    case 'Hole':
    case 'Meta':
      return false; // No variables in holes/metas
    case 'Annot':
      return containsVarIndexHelper(term.term, targetIndex, depth) ||
        containsVarIndexHelper(term.type, targetIndex, depth);
    case 'Match':
      if (containsVarIndexHelper(term.scrutinee, targetIndex, depth)) return true;
      return term.clauses.some(c => containsVarIndexHelper(c.rhs, targetIndex, depth));

    case 'ULevel':
    case 'ULit':
    case 'UOmega':
      return false;
  }
}

function minFreeVarIndexHelper(term: TTKTerm, depth: number): number {
  switch (term.tag) {
    case 'Var':
      // Only count as free if index >= depth (not bound by local binders)
      return term.index >= depth ? term.index - depth : Infinity;

    case 'Sort':
    case 'Const':
      return Infinity;

    case 'Binder': {
      const domainMin = minFreeVarIndexHelper(term.domain, depth);
      const bodyMin = minFreeVarIndexHelper(term.body, depth + 1);
      let defValMin = Infinity;
      if (term.binderKind.tag === 'BLet') {
        defValMin = minFreeVarIndexHelper(term.binderKind.defVal, depth);
      }
      return Math.min(domainMin, bodyMin, defValMin);
    }

    case 'App':
      return Math.min(
        minFreeVarIndexHelper(term.fn, depth),
        minFreeVarIndexHelper(term.arg, depth)
      );

    case 'Hole':
    case 'Meta':
      return Infinity; // No free variables in holes/metas

    case 'Annot':
      return Math.min(
        minFreeVarIndexHelper(term.term, depth),
        minFreeVarIndexHelper(term.type, depth)
      );

    case 'Match': {
      const scrutineeMin = minFreeVarIndexHelper(term.scrutinee, depth);
      const clauseMins = term.clauses.map(c => minFreeVarIndexHelper(c.rhs, depth));
      return Math.min(scrutineeMin, ...clauseMins);
    }

    case 'ULevel':
    case 'ULit':
    case 'UOmega':
      return Infinity; // No free variables in these
  }
}

/**
 * Replace variables according to a mapping WITHOUT shifting other indices.
 * This is for parallel substitution where indices should stay in place.
 *
 * @param mapping - Maps variable index to replacement term
 * @param term - The term to transform
 */
export function replaceVars(mapping: Map<number, TTKTerm>, term: TTKTerm): TTKTerm {
  return replaceVarsHelper(mapping, term, 0);
}

function replaceVarsHelper(mapping: Map<number, TTKTerm>, term: TTKTerm, depth: number): TTKTerm {
  switch (term.tag) {
    case 'Var': {
      const adjustedIndex = term.index - depth;
      if (adjustedIndex >= 0 && mapping.has(adjustedIndex)) {
        // Replace with the mapped term, shifted to account for binders we've gone under
        const replacement = mapping.get(adjustedIndex)!;
        return depth > 0 ? shift(depth, replacement, 0) : replacement;
      }
      // Leave other variables unchanged
      return term;
    }

    case 'Sort':
    case 'Const':
      return term;

    case 'Hole':
      return { tag: 'Hole', id: term.id };

    case 'Meta':
      return { tag: 'Meta', id: term.id };

    case 'Binder': {
      const newDomain = replaceVarsHelper(mapping, term.domain, depth);
      const newBody = replaceVarsHelper(mapping, term.body, depth + 1);

      let newBinderKind: TTKBinderKind;
      if (term.binderKind.tag === 'BLet') {
        const newDefVal = replaceVarsHelper(mapping, term.binderKind.defVal, depth);
        newBinderKind = { tag: 'BLet', defVal: newDefVal };
      } else {
        newBinderKind = term.binderKind;
      }

      return { tag: 'Binder', binderKind: newBinderKind, name: term.name, domain: newDomain, body: newBody };
    }

    case 'App': {
      const newFn = replaceVarsHelper(mapping, term.fn, depth);
      const newArg = replaceVarsHelper(mapping, term.arg, depth);
      return { tag: 'App', fn: newFn, arg: newArg };
    }

    case 'Annot':
      return {
        tag: 'Annot',
        term: replaceVarsHelper(mapping, term.term, depth),
        type: replaceVarsHelper(mapping, term.type, depth)
      };

    case 'Match':
      return {
        tag: 'Match',
        scrutinee: replaceVarsHelper(mapping, term.scrutinee, depth),
        clauses: term.clauses.map(c => ({
          patterns: c.patterns,
          rhs: replaceVarsHelper(mapping, c.rhs, depth)
        }))
      };

    case 'ULevel':
    case 'ULit':
    case 'UOmega':
      return term;
  }
}

export function* enumerateAppliedSubstitutions(substitutions: [number, TTKTerm][]) {
  let remaining = substitutions.slice();
  while (remaining.length > 0) {
    const [varIndex, value] = remaining.shift() as [number, TTKTerm];

    // Apply the current substitution to all remaining substitutions
    // and adjust their indices since we're removing varIndex from the context
    const updated: [number, TTKTerm][] = [];
    for (const [otherIndex, otherValue] of remaining) {
      if (otherIndex === varIndex) {
        throw new Error(`Duplicate substitution index: ${varIndex}. combineUnificationResults should have merged these.`);
      }

      // Apply substitution to the value
      const newValue = subst(varIndex, value, otherValue);

      // Indices above varIndex shift down by 1 after the variable is removed
      const newIndex = otherIndex > varIndex ? otherIndex - 1 : otherIndex;
      updated.push([newIndex, newValue]);
    }
    remaining = updated;

    yield { varIndex, value };
  }
}

// Removes the binder at varIndex, applies the substitution, and shifts indices accordingly.
//
// Each entry's type in TTKContext is stored with de Bruijn indices relative to that entry's
// position (entry at position i has type with indices 0..i-1). The varIndex parameter is
// a de Bruijn index from the tail (0 = last entry, most recently bound).
export function applySubstitutionToContext(
  ctx: TTKContext,
  varIndex: number,
  value: TTKTerm
): TTKContext {
  const n = ctx.length;
  const cutoff = n - varIndex - 1; // array index of the variable being removed

  // First, adjust value for the removal in main context
  // Indices > varIndex in value need to be decremented
  const adjustedValueInMain = transformVarsInTerm(value, (idx, _sig) => {
    if (idx > varIndex) {
      return mkVar(idx - 1);
    }
    return mkVar(idx);
  });

  // Remove the binder at cutoff
  const newCtx = ctx.slice(0, cutoff).concat(ctx.slice(cutoff + 1));

  return newCtx.map((s, i) => {
    if (i < cutoff) {
      // Entry before the removed variable - the removed var wasn't in scope for this type
      return s;
    }

    // Entry at position i in newCtx came from position i+1 in original ctx
    const origPos = i + 1;

    // From this entry's perspective, the removed var (at array position cutoff)
    // had de Bruijn index: origPos - cutoff - 1 = i - cutoff
    const localIdx = i - cutoff;

    // Shift adjustedValueInMain from new main context (n-1 vars) to this entry's new context (origPos-1 vars)
    // New main context has n-1 entries, this entry's new context has origPos-1 entries
    const shiftAmount = (origPos - 1) - (n - 1);
    const shiftedValue = shiftAmount !== 0 ? shiftTerm(adjustedValueInMain, shiftAmount, 0) : adjustedValueInMain;

    // subst replaces Var(localIdx) with shiftedValue and decrements indices above localIdx
    const newType = subst(localIdx, shiftedValue, s.type);

    // Handle value field if present
    const newValue = s.value !== undefined
      ? subst(localIdx, shiftedValue, s.value)
      : undefined;

    return { ...s, type: newType, value: newValue };
  });
}

/**
 * Apply a substitution to a map of metavariables.
 *
 * Each metavar has its own context (a snapshot of the signature when it was created).
 * The metavar's ctx is a PREFIX of the main signature (entries 0..m-1 where m = ctx.length).
 *
 * If the variable being removed is within a metavar's context, we need to:
 * 1. Apply the substitution to the metavar's context
 * 2. Apply the substitution to the metavar's type and solution
 *
 * @param metaVars - The map of metavariables
 * @param mainSigLength - Length of the main signature BEFORE the substitution
 * @param varIndex - De Bruijn index (from tail) of variable being removed in main signature
 * @param value - The value to substitute (in main signature's context)
 */
export function applySubstitutionToMetaVars(
  metaVars: Map<string, MetaVar>,
  mainSigLength: number,
  varIndex: number,
  value: TTKTerm
): Map<string, MetaVar> {
  const result = new Map<string, MetaVar>();

  for (const [name, meta] of metaVars) {
    const m = meta.ctx.length;

    // Check if the variable being removed is in this metavar's context.
    // MetaVar.ctx corresponds to array positions 0..m-1 of main signature,
    // which are de Bruijn indices (mainSigLength-1) down to (mainSigLength-m).
    // So varIndex is in metavar's ctx if varIndex >= mainSigLength - m.
    if (varIndex >= mainSigLength - m) {
      // Compute local de Bruijn index in metavar's context
      const localVarIndex = varIndex - (mainSigLength - m);

      // Check if anything actually references the removed variable.
      // Only if something needs the value do we need to check for escaping.
      const typeNeedsValue = containsVarIndex(meta.type, localVarIndex);
      const solutionNeedsValue = meta.solution !== undefined &&
        containsVarIndex(meta.solution, localVarIndex);

      // Check if any context entry after the removed one references it
      const cutoff = m - localVarIndex - 1;
      let ctxNeedsValue = false;
      for (let i = cutoff + 1; i < m; i++) {
        const localIdx = i - cutoff - 1;
        const entryValue = meta.ctx[i].value;
        if (containsVarIndex(meta.ctx[i].type, localIdx) ||
          (entryValue !== undefined && containsVarIndex(entryValue, localIdx))) {
          ctxNeedsValue = true;
          break;
        }
      }

      if (typeNeedsValue || solutionNeedsValue || ctxNeedsValue) {
        // Check for escaping variables: value must not reference variables
        // outside the metavar's scope (indices < mainSigLength - m)
        const minFreeVar = minFreeVarIndex(value);
        const contextBoundary = mainSigLength - m;
        if (minFreeVar < contextBoundary) {
          throw new Error(
            `Escaping variable in substitution for metavar ${name}: ` +
            `value references Var(${minFreeVar}) but metavar context only has ` +
            `variables with index >= ${contextBoundary}`
          );
        }
      }

      // Shift value from main context (mainSigLength vars) to metavar context (m vars)
      const shiftAmount = m - mainSigLength;
      const shiftedValue = shiftAmount !== 0 ? shiftTerm(value, shiftAmount, 0) : value;

      // Apply substitution to ctx (handles adjustment internally)
      const newCtx = applySubstitutionToContext(meta.ctx, localVarIndex, shiftedValue);

      // Adjust value for removal before applying to type/solution
      // (applySubstitutionToContext does this internally, but subst does not)
      const adjustedValue = transformVarsInTerm(shiftedValue, (idx) => {
        return idx > localVarIndex ? mkVar(idx - 1) : mkVar(idx);
      });

      // Apply substitution to type (in metavar's original context)
      const newType = subst(localVarIndex, adjustedValue, meta.type);

      // Apply substitution to solution if present
      const newSolution = meta.solution !== undefined
        ? subst(localVarIndex, adjustedValue, meta.solution)
        : undefined;

      result.set(name, { ctx: newCtx, type: newType, solution: newSolution });
    } else {
      // Variable not in this metavar's context, no changes needed
      result.set(name, meta);
    }
  }

  return result;
}

/**
 * Apply a substitution to a list of constraints.
 *
 * Each constraint has its own context (a snapshot of the signature when it was created).
 * If the variable being removed is within a constraint's context, we need to:
 * 1. Apply the substitution to the constraint's context
 * 2. Apply the substitution to the rhs term
 *
 * @param constraints - The list of constraints
 * @param mainSigLength - Length of the main signature BEFORE the substitution
 * @param varIndex - De Bruijn index (from tail) of variable being removed in main signature
 * @param value - The value to substitute (in main signature's context)
 */
export function applySubstitutionToConstraints(
  constraints: Constraint[],
  mainSigLength: number,
  varIndex: number,
  value: TTKTerm
): Constraint[] {
  return constraints.map(constraint => {
    const m = constraint.ctx.length;

    if (varIndex >= mainSigLength - m) {
      const localVarIndex = varIndex - (mainSigLength - m);

      // Check if anything actually references the removed variable.
      const rhsNeedsValue = containsVarIndex(constraint.rhs, localVarIndex);

      // Check if any context entry after the removed one references it
      const cutoff = m - localVarIndex - 1;
      let ctxNeedsValue = false;
      for (let i = cutoff + 1; i < m; i++) {
        const localIdx = i - cutoff - 1;
        const entryValue = constraint.ctx[i].value;
        if (containsVarIndex(constraint.ctx[i].type, localIdx) ||
          (entryValue !== undefined && containsVarIndex(entryValue, localIdx))) {
          ctxNeedsValue = true;
          break;
        }
      }

      if (rhsNeedsValue || ctxNeedsValue) {
        // Check for escaping variables: value must not reference variables
        // outside the constraint's scope (indices < mainSigLength - m)
        const minFreeVar = minFreeVarIndex(value);
        const contextBoundary = mainSigLength - m;
        if (minFreeVar < contextBoundary) {
          throw new Error(
            `Escaping variable in substitution for constraint (meta ${constraint.meta}): ` +
            `value references Var(${minFreeVar}) but constraint context only has ` +
            `variables with index >= ${contextBoundary}`
          );
        }
      }

      const shiftAmount = m - mainSigLength;
      const shiftedValue = shiftAmount !== 0 ? shiftTerm(value, shiftAmount, 0) : value;

      // Apply substitution to ctx (handles adjustment internally)
      const newCtx = applySubstitutionToContext(constraint.ctx, localVarIndex, shiftedValue);

      // Adjust value for removal before applying to rhs
      const adjustedValue = transformVarsInTerm(shiftedValue, (idx) => {
        return idx > localVarIndex ? mkVar(idx - 1) : mkVar(idx);
      });

      const newRhs = subst(localVarIndex, adjustedValue, constraint.rhs);

      return { ...constraint, ctx: newCtx, rhs: newRhs };
    } else {
      return constraint;
    }
  });
}