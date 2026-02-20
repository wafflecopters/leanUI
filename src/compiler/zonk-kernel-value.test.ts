/**
 * Test: kernelValue should be zonked in CompiledDeclaration so that UI
 * consumers don't display unsolved metas for solved type annotations.
 *
 * Bug: The lambda `\ih => PeanoNat.succ N ih` in `plus` gets elaborated with
 * an unresolved meta for `ih`'s type annotation. The meta IS solved during
 * type checking, but `kernelValue` stores the pre-zonk elaborated term.
 * The UI then displays `\(ih : ?ih_type) => ...` instead of the solved type.
 */
import { describe, test, expect } from 'vitest';
import { compileTTFromText } from './compile';
import { TTKTerm } from './kernel';

/** Recursively check if a term contains any Meta or Hole nodes.
 *  Skips the Match scrutinee (which uses a placeholder Hole '_scrutinee'). */
function containsUnsolvedMeta(term: TTKTerm): boolean {
  switch (term.tag) {
    case 'Meta': return true;
    case 'Hole': return term.id !== '_scrutinee';
    case 'App': return containsUnsolvedMeta(term.fn) || containsUnsolvedMeta(term.arg);
    case 'Binder':
      return containsUnsolvedMeta(term.domain) || containsUnsolvedMeta(term.body) ||
        (term.binderKind.tag === 'BLet' && containsUnsolvedMeta(term.binderKind.defVal));
    case 'Sort': return containsUnsolvedMeta(term.level);
    case 'Annot': return containsUnsolvedMeta(term.term) || containsUnsolvedMeta(term.type);
    case 'Match':
      return containsUnsolvedMeta(term.scrutinee) ||
        term.clauses.some(c => containsUnsolvedMeta(c.rhs));
    default: return false;
  }
}

describe('kernelValue zonking', () => {
  test('lambda type annotations in kernelValue should be zonked', () => {
    const source = `
inductive Equal : {u : ULevel} -> {A : Type u} -> A -> A -> Type where
  refl : {u : ULevel} -> {A : Type u} -> {a : A} -> (Equal a a)

inductive Void : Type where

Not : {u : ULevel} -> Type u -> Type ω
Not A = A -> Void

record PeanoNat : Type 1 where
  carrier : Type
  zero : carrier
  succ : carrier -> carrier
  zeroNeqSucc : {n : carrier} -> Not (Equal zero (succ n))
  succInj : {m n : carrier} -> Equal (succ m) (succ n) -> Equal m n
  ind : {P : carrier -> Type} -> P zero -> ({n : carrier} -> P n -> P (succ n)) -> (n : carrier) -> P n
  indZero : {P : carrier -> Type} -> (base : P zero) -> (step : {n : carrier} -> P n -> P (succ n)) -> Equal (ind base step zero) base
  indSucc : {P : carrier -> Type} -> (base : P zero) -> (step : {n : carrier} -> P n -> P (succ n)) -> (n : carrier) -> Equal (ind base step (succ n)) (step (ind base step n))

plus : (N : PeanoNat) -> PeanoNat.carrier N -> PeanoNat.carrier N -> PeanoNat.carrier N
plus N n m = PeanoNat.ind N m (\\ih => PeanoNat.succ N ih) n
`;

    const result = compileTTFromText(source);
    const plusDecl = result.blocks
      .flatMap(b => b.declarations)
      .find(d => d.name === 'plus');

    expect(plusDecl).toBeDefined();
    expect(plusDecl!.checkSuccess).toBe(true);

    // The kernelValue should not contain unsolved metas — all type annotations
    // (like the lambda domain for `ih`) should be fully resolved.
    expect(plusDecl!.kernelValue).toBeDefined();
    expect(containsUnsolvedMeta(plusDecl!.kernelValue!)).toBe(false);

    // The prettyValue should not contain '?' (unsolved meta markers)
    expect(plusDecl!.prettyValue).toBeDefined();
    expect(plusDecl!.prettyValue).not.toContain('?');
  });
});
