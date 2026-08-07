/**
 * How many branches does splitting on this scrutinee open?
 *
 * `cases`/`induction` need a branch per constructor of the scrutinee's type,
 * and only Lean knows what that type is. Before this, the editor printed TWO
 * cases labelled `n = 0` and `n = k'` for every split — Nat's shape, hard-coded
 * in a generic layer — which is right for Nat, wrong for a one-constructor
 * structure (a spurious empty branch), and wrong for anything with three.
 *
 * The facts come from the extractor: `ctors` on a hypothesis is its type's
 * constructor count; `conclCtors` on a declaration is the constructor count of
 * what that declaration CONCLUDES, which is what a split on an application like
 * `leTotal a b` opens.
 */
import type { LeanDeclaration } from './types';

export interface ScrutineeHyp {
  name: string;
  ctors?: number;
}

/** The head identifier of a scrutinee expression: `leTotal a b` → `leTotal`,
 *  `(foo x)` → `foo`, a bare `hF` → `hF`. Returns null if there isn't one. */
export function scrutineeHead(expr: string): string | null {
  const m = expr.trim().replace(/^\(+/, '').match(/^[A-Za-z_ε-ω][A-Za-z0-9_'.Ͱ-Ͽ]*/);
  return m ? m[0] : null;
}

/**
 * Branches a split on `scrutinee` opens, or `null` when nothing in scope says.
 * A caller with no answer should fall back to one branch and let the round-trip
 * correct it — never to a guessed shape.
 */
export function caseBranchCount(
  declarations: readonly LeanDeclaration[],
  hypotheses: readonly ScrutineeHyp[],
  scrutinee: string,
): number | null {
  const head = scrutineeHead(scrutinee);
  if (!head) return null;

  // A bare hypothesis: its own type's constructors. Checked first — a local
  // name shadows a global one, and Lean resolves it the same way.
  const hyp = hypotheses.find((h) => h.name === head);
  if (hyp) return typeof hyp.ctors === 'number' && hyp.ctors > 0 ? hyp.ctors : null;

  // An application of a file lemma: the constructors of its conclusion.
  const decl = declarations.find((d) => d.name === head);
  if (decl) return typeof decl.conclCtors === 'number' && decl.conclCtors > 0 ? decl.conclCtors : null;

  return null;
}
