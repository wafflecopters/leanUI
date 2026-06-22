import { describe, expect, test } from 'vitest';
import { equalityLemmas, rankByGoalOverlap, unfoldableDefs } from './rewriteCandidates';
import type { LeanDeclaration } from './types';

function decl(name: string, prettyType: string, kind: LeanDeclaration['kind'] = 'def'): LeanDeclaration {
  return { name, kind, prettyType, line: 1, col: 0 };
}

describe('equalityLemmas', () => {
  test('keeps decls whose conclusion is an equality, drops non-equalities', () => {
    const decls = [
      decl('plusComm', '∀ (n m : MyNat), n + m = m + n'),
      decl('plus', 'MyNat → MyNat → MyNat'), // not an equality
      decl('summationSplit', '∀ (i n : MyNat), Leq i n → ∀ (f : MyNat → MyNat), sum i n.succ f = sum i n f + f n.succ'),
      decl('natSemiring', 'Semiring MyNat'),
    ];
    const got = equalityLemmas(decls);
    expect(got.map((c) => c.name)).toEqual(['plusComm', 'summationSplit']);
    // Binders stripped from the LHS.
    expect(got[0].lhs).toBe('n + m');
    expect(got[1].lhs).toBe('sum i n.succ f');
  });

  test('excludes the current declaration and congruence combinators', () => {
    const decls = [
      decl('triangleSum', '∀ (n : MyNat), 2 * sum 0 n id = (n + 1) * n'),
      decl('eqTrans', '∀ {x y z : MyNat}, x = y → y = z → x = z'), // takes equality hyps
      decl('congSucc', '∀ {n m : MyNat}, n = m → n.succ = m.succ'), // takes equality hyp
      decl('plusComm', '∀ (n m : MyNat), n + m = m + n'),
    ];
    const got = equalityLemmas(decls, 'triangleSum');
    expect(got.map((c) => c.name)).toEqual(['plusComm']);
  });
});

describe('unfoldableDefs', () => {
  test('returns function/data defs, skipping equality lemmas, instances, projections, self', () => {
    const decls = [
      decl('sum', 'MyNat → MyNat → (MyNat → MyNat) → MyNat'),
      decl('plus', 'MyNat → MyNat → MyNat'),
      decl('plusComm', '∀ (n m : MyNat), n + m = m + n'), // equality lemma — not an unfold target
      decl('instOfNatMyNat', 'OfNat MyNat 0'), // auto instance
      decl('Semiring.add', 'MyNat → MyNat → MyNat'), // projection
      decl('triangleSum', 'MyNat → MyNat'),
    ];
    expect(unfoldableDefs(decls, 'triangleSum')).toEqual(['sum', 'plus']);
  });

  test('respects the cap', () => {
    const decls = Array.from({ length: 30 }, (_, i) => decl(`f${i}`, 'MyNat → MyNat'));
    expect(unfoldableDefs(decls, undefined, 5)).toHaveLength(5);
  });
});

describe('rankByGoalOverlap', () => {
  test('a sum-headed lemma outranks a generic + lemma for a sum goal', () => {
    const cands = equalityLemmas([
      decl('plusComm', '∀ (n m : MyNat), n + m = m + n'),
      decl('summationSplit', '∀ (i n : MyNat), Leq i n → ∀ (f : MyNat → MyNat), sum i n.succ f = sum i n f + f n.succ'),
    ]);
    const ranked = rankByGoalOverlap(cands, '2 * sum 0 a.succ f = (a.succ + 1) * a.succ');
    expect(ranked[0].name).toBe('summationSplit'); // shares sum, succ, f vs plusComm's lone +
  });

  test('boosts head-operator matches (a *-focus surfaces mulComm despite low token overlap)', () => {
    const cands = equalityLemmas([
      decl('plusComm', '∀ (n m : MyNat), n + m = m + n'),
      decl('plusAssoc', '∀ (n m p : MyNat), n + m + p = n + (m + p)'),
      decl('mulComm', '∀ (n m : MyNat), n * m = m * n'),
    ]);
    // Focus is `*`-headed; mulComm shares only `*` but its head matches → top.
    const ranked = rankByGoalOverlap(cands, '(1 + a.succ) * a.succ', 10);
    expect(ranked[0].name).toBe('mulComm');
  });

  test('drops zero-overlap candidates and respects the cap', () => {
    const cands = equalityLemmas([
      decl('plusComm', '∀ (n m : MyNat), n + m = m + n'),
      decl('mulComm', '∀ (n m : MyNat), n * m = m * n'),
      decl('unrelated', '∀ (x : Foo), bar x = baz x'),
    ]);
    const ranked = rankByGoalOverlap(cands, 'p + q = q + p', 5);
    expect(ranked.map((c) => c.name)).toEqual(['plusComm']); // only + overlaps
  });
});
