import { TTKBinderKind, TTKTerm } from "../types/tt-kernel";

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
      return {
        tag: 'Hole',
        id: term.id,
        type: substHelper(targetIndex, replacement, term.type, depth),
        context: term.context
      };

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
      return {
        tag: 'Hole',
        id: term.id,
        type: shift(amount, term.type, cutoff),
        context: term.context
      };

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
      return {
        tag: 'Hole',
        id: term.id,
        type: substPatternBindingsHelper(bindings, term.type, depth),
        context: term.context
      };

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
  }
}

/**
 * Shift De Bruijn indices in a term (exported version)
 */
export function shiftTerm(term: TTKTerm, amount: number, cutoff: number): TTKTerm {
  return shift(amount, term, cutoff);
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
      return {
        tag: 'Hole',
        id: term.id,
        type: replaceVarsHelper(mapping, term.type, depth),
        context: term.context
      };

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
  }
}