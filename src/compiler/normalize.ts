/**
 * Full normalization of TTK terms.
 *
 * Unlike whnf (weak head normal form) which only normalizes the head,
 * this fully normalizes all subterms recursively.
 */

import { TTKTerm, TTKBinderKind } from "./kernel";
import { subst, substPatternBindings } from "./subst";

function collectAppSpine(term: TTKTerm): { head: TTKTerm; args: TTKTerm[] } {
  const args: TTKTerm[] = [];
  let current = term;
  while (current.tag === 'App') {
    args.unshift(current.arg);
    current = current.fn;
  }
  return { head: current, args };
}

function matchPattern(pattern: import("./kernel").TTKPattern, term: TTKTerm): TTKTerm[] | null {
  switch (pattern.tag) {
    case 'PVar':
      return [term];
    case 'PWild':
      return [];
    case 'PCtor': {
      const { head, args } = collectAppSpine(term);
      if (head.tag !== 'Const' || head.name !== pattern.name) {
        return null;
      }
      if (pattern.args.length !== args.length) {
        return null;
      }

      const bindings: TTKTerm[] = [];
      for (let i = 0; i < pattern.args.length; i++) {
        const argBindings = matchPattern(pattern.args[i], args[i]);
        if (argBindings === null) {
          return null;
        }
        bindings.push(...argBindings);
      }
      return bindings;
    }
  }
}

/**
 * Fully normalize a term by recursively reducing all redexes.
 *
 * Performs:
 * - Beta reduction: (λx. t) s → t[x := s]
 * - Zeta reduction: let x := v in t → t[x := v]
 * - Recursive normalization of all subterms
 */
export function normalize(term: TTKTerm): TTKTerm {
  switch (term.tag) {
    case 'Var':
    case 'Sort':
    case 'Const':
    case 'Hole':
    case 'Meta':
    case 'NatLit':
      return term;

    case 'App': {
      const fn = normalize(term.fn);
      const arg = normalize(term.arg);

      if (fn.tag === 'Binder' && fn.binderKind.tag === 'BLam') {
        // Beta reduction: (λx. t) s → t[x := s]
        return normalize(subst(0, arg, fn.body));
      }

      return { tag: 'App', fn, arg };
    }

    case 'Binder': {
      if (term.binderKind.tag === 'BLet') {
        // Zeta reduction: let x := v in t → t[x := v]
        return normalize(subst(0, term.binderKind.defVal, term.body));
      }

      // For Pi and Lambda, normalize subterms
      const domain = normalize(term.domain);
      const body = normalize(term.body);

      return {
        tag: 'Binder',
        name: term.name,
        binderKind: term.binderKind,
        domain,
        body
      };
    }

    case 'Annot':
      // Annotations can be dropped after type checking
      return normalize(term.term);

    case 'Match': {
      const scrutinee = normalize(term.scrutinee);
      const clauses = term.clauses.map(c => ({
        ...c,
        rhs: normalize(c.rhs)
      }));

      for (const clause of clauses) {
        if (clause.patterns.length !== 1) continue;

        const bindings = matchPattern(clause.patterns[0], scrutinee);
        if (bindings !== null) {
          return normalize(substPatternBindings(bindings, clause.rhs));
        }
      }

      return { tag: 'Match', scrutinee, clauses };
    }

    case 'ULevel':
    case 'ULit':
    case 'UOmega':
      return term;
  }
}
