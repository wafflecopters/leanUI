import { TTKTerm } from "../types/tt-kernel";
import { subst } from "./subst";

/**
 * Check if a variable index is free in a term.
 */
function isFreeIn(index: number, term: TTKTerm): boolean {
  switch (term.tag) {
    case 'Var':
      return term.index === index;
    case 'Sort':
    case 'Const':
      return false;
    case 'Hole':
      return isFreeIn(index, term.type);
    case 'App':
      return isFreeIn(index, term.fn) || isFreeIn(index, term.arg);
    case 'Binder':
      if (isFreeIn(index, term.domain)) return true;
      if (isFreeIn(index + 1, term.body)) return true;
      if (term.binderKind.tag === 'BLet') {
        return isFreeIn(index, term.binderKind.defVal);
      }
      return false;
    case 'Annot':
      return isFreeIn(index, term.term) || isFreeIn(index, term.type);

    case 'Match':
      if (isFreeIn(index, term.scrutinee)) return true;
      for (const clause of term.clauses) {
        if (isFreeIn(index, clause.rhs)) return true;
      }
      return false;
  }
}

/**
 * Check if two types are definitionally equal.
 * 
 * Implements:
 * - β-reduction: (λx. e) a ≃ e[a/x]
 * - ζ-reduction: let x := t; u ≃ u[t/x]
 * - η-conversion: λx. f x ≃ f (when x not free in f)
 * - δ-reduction: unfold definitions (todo)
 * - ι-reduction: recursor on constructor (todo)
 */
export function areTypesDefEq(t1: TTKTerm, t2: TTKTerm): boolean {
  // Normalize both terms
  const n1 = whnf(t1);
  const n2 = whnf(t2);

  // Quick structural check first
  if (isDefinitionallyEqual(n1, n2)) {
    return true;
  }

  // Eta conversion for lambdas
  // λx. f x ≃ f (when x not free in f)
  if (n1.tag === 'Binder' && n1.binderKind.tag === 'BLam') {
    // Check if n1 is of the form λx. f x where x is not free in f
    if (n1.body.tag === 'App' && n1.body.arg.tag === 'Var' && n1.body.arg.index === 0) {
      if (!isFreeIn(0, n1.body.fn)) {
        // Eta contract: compare f with n2 (f needs index shift down)
        const contracted = subst(0, { tag: 'Var', index: 0 }, n1.body.fn);
        return areTypesDefEq(contracted, n2);
      }
    }
  }

  // Symmetric case
  if (n2.tag === 'Binder' && n2.binderKind.tag === 'BLam') {
    if (n2.body.tag === 'App' && n2.body.arg.tag === 'Var' && n2.body.arg.index === 0) {
      if (!isFreeIn(0, n2.body.fn)) {
        const contracted = subst(0, { tag: 'Var', index: 0 }, n2.body.fn);
        return areTypesDefEq(n1, contracted);
      }
    }
  }

  // Deep structural comparison after normalization
  switch (n1.tag) {
    case 'Var':
      return n2.tag === 'Var' && n1.index === n2.index;

    case 'Sort':
      return n2.tag === 'Sort' && n1.level === n2.level;

    case 'Const':
      return n2.tag === 'Const' && n1.name === n2.name;

    case 'Binder':
      if (n2.tag !== 'Binder' || n1.binderKind.tag !== n2.binderKind.tag) {
        return false;
      }
      if (!areTypesDefEq(n1.domain, n2.domain)) return false;
      if (!areTypesDefEq(n1.body, n2.body)) return false;
      if (n1.binderKind.tag === 'BLet' && n2.binderKind.tag === 'BLet') {
        return areTypesDefEq(n1.binderKind.defVal, n2.binderKind.defVal);
      }
      return true;

    case 'App':
      return n2.tag === 'App' &&
        areTypesDefEq(n1.fn, n2.fn) &&
        areTypesDefEq(n1.arg, n2.arg);

    case 'Hole':
      return n2.tag === 'Hole' && n1.id === n2.id;

    case 'Annot':
      return areTypesDefEq(n1.term, n2);

    case 'Match':
      if (n2.tag !== 'Match') return false;
      if (!areTypesDefEq(n1.scrutinee, n2.scrutinee)) return false;
      if (n1.clauses.length !== n2.clauses.length) return false;
      for (let i = 0; i < n1.clauses.length; i++) {
        if (!areTypesDefEq(n1.clauses[i].rhs, n2.clauses[i].rhs)) return false;
      }
      return true;
  }
}


/**
 * Check if two kernel terms are definitionally equal (structural).
 */
export function isDefinitionallyEqual(term1: TTKTerm, term2: TTKTerm): boolean {
  if (term1.tag !== term2.tag) return false;

  switch (term1.tag) {
    case 'Var':
      return term2.tag === 'Var' && term1.index === term2.index;

    case 'Sort':
      return term2.tag === 'Sort' && term1.level === term2.level;

    case 'Const':
      return term2.tag === 'Const' && term1.name === term2.name;

    case 'Hole':
      return term2.tag === 'Hole' && term1.id === term2.id;

    case 'Binder': {
      if (term2.tag !== 'Binder') return false;
      if (term1.binderKind.tag !== term2.binderKind.tag) return false;
      if (term1.binderKind.tag === 'BLet' && term2.binderKind.tag === 'BLet') {
        if (!isDefinitionallyEqual(term1.binderKind.defVal, term2.binderKind.defVal)) {
          return false;
        }
      }
      return isDefinitionallyEqual(term1.domain, term2.domain) &&
        isDefinitionallyEqual(term1.body, term2.body);
    }

    case 'App': {
      if (term2.tag !== 'App') return false;
      return isDefinitionallyEqual(term1.fn, term2.fn) &&
        isDefinitionallyEqual(term1.arg, term2.arg);
    }

    case 'Annot': {
      if (term2.tag !== 'Annot') return false;
      return isDefinitionallyEqual(term1.term, term2.term) &&
        isDefinitionallyEqual(term1.type, term2.type);
    }

    case 'Match': {
      if (term2.tag !== 'Match') return false;
      if (!isDefinitionallyEqual(term1.scrutinee, term2.scrutinee)) return false;
      if (term1.clauses.length !== term2.clauses.length) return false;
      for (let i = 0; i < term1.clauses.length; i++) {
        if (!isDefinitionallyEqual(term1.clauses[i].rhs, term2.clauses[i].rhs)) return false;
      }
      return true;
    }
  }
}

export function whnf(term: TTKTerm): TTKTerm {
  switch (term.tag) {
    case 'App': {
      const fn = whnf(term.fn);
      if (fn.tag === 'Binder' && fn.binderKind.tag === 'BLam') {
        // Beta reduction: (λx. t) s → t[x := s]
        return whnf(subst(0, term.arg, fn.body));
      }
      return { tag: 'App', fn, arg: term.arg };
    }
    case 'Binder': {
      if (term.binderKind.tag === 'BLet') {
        // Let expansion: let x := v in t → t[x := v]
        return whnf(subst(0, term.binderKind.defVal, term.body));
      }
      return term;
    }
    default:
      return term;
  }
}