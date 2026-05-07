/**
 * Full normalization of TTK terms.
 *
 * Unlike whnf (weak head normal form) which only normalizes the head,
 * this fully normalizes all subterms recursively.
 */

import { TTKTerm, TTKBinderKind } from "./kernel";
import { subst } from "./subst";

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
        patterns: c.patterns,
        rhs: normalize(c.rhs)
      }));

      // TODO: If scrutinee is a constructor, we could reduce the match
      // For now, just return the normalized match
      return { tag: 'Match', scrutinee, clauses };
    }

    case 'ULevel':
    case 'ULit':
    case 'UOmega':
      return term;
  }
}
