import { describe, expect, test } from 'vitest';
import { applyCandidates, comparisonCandidates, equalityLemmas, rankByGoalOverlap, unfoldableDefs, valueCandidates } from './rewriteCandidates';
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

  // `unfold zeroLeOne` is meaningless — a lemma is a proof ABOUT terms, not a
  // definition of one. Before this filter the list was mostly lemmas, crowding
  // the actual definitions out from under the cap (in the real-analysis preset
  // `rtwo` — the thing behind a displayed `2` — sat at position 64 of 137).
  test('lemmas are not unfold targets; definitions are', () => {
    const decls = [
      decl('zeroLeOne', '(R : Real) → 0 ≤ 1'),
      decl('leTrans', '{R : Real} → (a b c : ℝ) → a ≤ b → b ≤ c → a ≤ c'),
      decl('plusComm', '∀ (n m : MyNat), n + m = m + n'),
      decl('rtwo', '(R : Real) → ℝ'),
      decl('radd', '{R : Real} → ℝ → ℝ → ℝ'),
    ];
    expect(unfoldableDefs(decls)).toEqual(['rtwo', 'radd']);
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


describe('applyCandidates (the core-Lean apply? stand-in)', () => {
  test('ranks lemmas whose conclusion matches the goal head', async () => {
    const { applyCandidates } = await import('./rewriteCandidates');
    const decls = [
      { name: 'divTwoPos', kind: 'def', prettyType: '{R : Real} → (e : ℝ) → 0 < e → 0 < e / 2', line: 1, col: 0 },
      { name: 'divPos', kind: 'def', prettyType: '{R : Real} → (a b : ℝ) → 0 < a → 0 < b → 0 < a / b', line: 2, col: 0 },
      { name: 'plusComm', kind: 'def', prettyType: '∀ (n m : MyNat), n + m = m + n', line: 3, col: 0 },
      { name: 'sum', kind: 'def', prettyType: 'MyNat → MyNat', line: 4, col: 0 },
    ] as any;
    const c = applyCandidates(decls, '0 < ε / 2', 'limitAdd');
    expect(c[0]).toBe('divTwoPos'); // highest conclusion-token overlap
    expect(c).toContain('divPos');
    expect(c).not.toContain('plusComm'); // = head, not <
    expect(c).not.toContain('sum'); // no relational conclusion
  });

  test('no head operator in the goal → no candidates', async () => {
    const { applyCandidates } = await import('./rewriteCandidates');
    expect(applyCandidates([] as any, 'Limit f x0 L')).toEqual([]);
  });

  // Regression: the panel used to pass `cursorGoal.plain` — the WHOLE goal
  // state, hypotheses included. At `0 < ε / 2` the context carries
  // `limF : lim⟦x0⟧ f = L`, whose ` = ` made headOp read the goal as an
  // EQUALITY, so every `<` lemma (divTwoPos, divPos, …) was filtered out and
  // the pills were eight equality lemmas that all failed validation.
  test('a full goal state ranks against the target, not the hypotheses', async () => {
    const { applyCandidates } = await import('./rewriteCandidates');
    const decls = [
      { name: 'divTwoPos', kind: 'def', prettyType: '{R : Real} → (e : ℝ) → 0 < e → 0 < e / 2', line: 1, col: 0 },
      { name: 'divPos', kind: 'def', prettyType: '{R : Real} → (a b : ℝ) → 0 < a → 0 < b → 0 < a / b', line: 2, col: 0 },
      { name: 'limitExt', kind: 'def', prettyType: '{R : Real} → (f g : ℝ → ℝ) → f = g', line: 3, col: 0 },
    ] as any;
    const plain = [
      'R : Real',
      'f g : ℝ → ℝ',
      'limF : lim⟦x0⟧ f = L',
      'ε : ℝ',
      'epsPos : 0 < ε',
      '⊢ 0 < ε / 2',
    ].join('\n');
    const c = applyCandidates(decls, plain, 'limitAdd');
    expect(c[0]).toBe('divTwoPos');
    expect(c).toContain('divPos');
    expect(c).not.toContain('limitExt'); // the hypotheses' ` = ` must not win
  });

  // Numerals are meaningful symbols in these goals. Without them `0 ≤ 1`
  // tokenizes to just {≤} — the same as every other ≤ statement in the file —
  // so the lemma whose conclusion IS the goal scores no better than an
  // unrelated one and gets lost under the cap.
  test('a lemma whose conclusion IS the goal wins on the numerals', async () => {
    const { applyCandidates } = await import('./rewriteCandidates');
    const decls = [
      { name: 'addLeRight', kind: 'def', prettyType: '{R : Real} → (a b c : ℝ) → a ≤ b → a + c ≤ b + c', line: 1, col: 0 },
      { name: 'absNonneg', kind: 'def', prettyType: '{R : Real} → (a : ℝ) → 0 ≤ |a|', line: 2, col: 0 },
      { name: 'zeroLeOne', kind: 'def', prettyType: '(R : Real) → 0 ≤ 1', line: 3, col: 0 },
      { name: 'oneLeTwo', kind: 'def', prettyType: '(R : Real) → 1 ≤ 2', line: 4, col: 0 },
    ] as any;
    expect(applyCandidates(decls, '0 ≤ 1', 'x')[0]).toBe('zeroLeOne');
  });
});

describe('applyCandidates reserves room for the general moves', () => {
  // Ranking by token overlap systematically buries STRUCTURAL lemmas: a
  // conclusion made of bound variables (`a < c`) shares almost nothing with a
  // concrete goal, so transitivity loses to every lemma that mentions a `0` and
  // falls off the cap. Those are exactly the moves a user reaches for when the
  // direct lemma isn't the path they want.
  const specific = (n: number) =>
    Array.from({ length: n }, (_, i) => ({
      name: `fact${i}`,
      kind: 'def',
      prettyType: `(R : Real) → 0 < ${i + 3}`,
      line: i,
      col: 0,
    }));
  const decls = [
    ...specific(12),
    { name: 'zeroLtTwo', kind: 'def', prettyType: '(R : Real) → 0 < 2', line: 90, col: 0 },
    { name: 'leLtTrans', kind: 'def', prettyType: '{R : Real} → (a b c : ℝ) → a ≤ b → b < c → a < c', line: 91, col: 0 },
    { name: 'ltLeTrans', kind: 'def', prettyType: '{R : Real} → (a b c : ℝ) → a < b → b ≤ c → a < c', line: 92, col: 0 },
  ] as any;

  test('the exact match still leads', () => {
    expect(applyCandidates(decls, '0 < 2', 'x')[0]).toBe('zeroLtTwo');
  });

  test('transitivity survives the cap even with many better-scoring facts', () => {
    const got = applyCandidates(decls, '0 < 2', 'x');
    expect(got).toContain('leLtTrans');
    expect(got).toContain('ltLeTrans');
  });

  // `divPos : 0 < a / b` is ABOUT zero — it fits `0 < …` goals, not any `<`
  // goal — so it competes on overlap like any other specific fact.
  test('a conclusion carrying a numeral is specific, not structural', () => {
    const withDivPos = [
      ...specific(12),
      { name: 'divPos', kind: 'def', prettyType: '{R : Real} → (a b : ℝ) → 0 < a → 0 < b → 0 < a / b', line: 93, col: 0 },
      { name: 'leLtTrans', kind: 'def', prettyType: '{R : Real} → (a b c : ℝ) → a ≤ b → b < c → a < c', line: 94, col: 0 },
    ] as any;
    // The structural slot goes to transitivity, not to divPos.
    expect(applyCandidates(withDivPos, '5 < 9', 'x')).toContain('leLtTrans');
  });
});

describe('targetOfGoalText', () => {
  test('strips a goal-state prelude (hypotheses + ⊢)', async () => {
    const { targetOfGoalText } = await import('./rewriteCandidates');
    expect(targetOfGoalText('n : Nat\n⊢ n + 0 = n')).toBe('n + 0 = n');
    expect(targetOfGoalText('⊢ a')).toBe('a');
  });

  test('a multi-line target keeps all its lines', async () => {
    const { targetOfGoalText } = await import('./rewriteCandidates');
    expect(targetOfGoalText('n : Nat\n⊢ foo n →\n  bar n')).toBe('foo n →\n  bar n');
  });

  test('plain expression text passes through untouched', async () => {
    const { targetOfGoalText } = await import('./rewriteCandidates');
    expect(targetOfGoalText('0 < ε / 2')).toBe('0 < ε / 2');
  });
});

// Fixtures below are the facts Lean actually emits for these declarations
// (verified against the real-analysis preset), not guesses about their text.
const fact = (
  name: string,
  conclHead: string | null,
  argHeads: (string | null)[],
  premises: number,
  conclIsInductive = false,
): LeanDeclaration => ({
  name, kind: 'def', prettyType: '', line: 1, col: 0,
  conclHead, argHeads, premises, conclIsInductive,
});

describe('comparisonCandidates ("compare these two")', () => {
  const LIB = [
    // (a b : ℝ) → Either (a ≤ b) (b ≤ a): two args of one type, nothing else
    // asked for, inductive result.
    fact('leTotal', 'Either', ['Carrier', 'Carrier'], 0, true),
    // Same shape but PREMISED — not a "just compare them" move.
    fact('ltTotalOf', 'Either', ['Carrier', 'Carrier'], 1, true),
    // Two args, but returns data rather than a case split.
    fact('rmin', 'Carrier', ['Carrier', 'Carrier'], 2),
    // One arg.
    fact('absCases', 'Either', ['Carrier'], 0, true),
  ];
  // The context at the seeded limitAdd sorry. `typeHead` is what Lean says each
  // hypothesis IS — `ℝ` is `Carrier R`.
  const H = (name: string, typeHead: string | null) => ({ name, type: '', typeHead });
  const HYPS = [
    H('x0', 'Carrier'), H('L', 'Carrier'), H('M', 'Carrier'), H('\u03b5', 'Carrier'),
    H('epsPos', 'rlt'), H('deltaF', 'Carrier'), H('fProof', 'EpsDeltaWitness'), H('deltaG', 'Carrier'),
  ];

  test('offers the two most recent values first — the ones you are working with', () => {
    const out = comparisonCandidates(LIB, HYPS, 'limitAdd');
    expect(out[0]).toEqual({ lemma: 'leTotal', left: 'deltaF', right: 'deltaG' });
    expect(out.map((c) => `${c.left},${c.right}`)).not.toContain('x0,L');
  });

  test('only lemmas of the comparison SHAPE qualify', () => {
    expect(new Set(comparisonCandidates(LIB, HYPS, 'limitAdd').map((c) => c.lemma)))
      .toEqual(new Set(['leTotal']));
  });

  test('needs two values of the same type in scope', () => {
    expect(comparisonCandidates(LIB, [H('deltaF', 'Carrier')], 'limitAdd')).toEqual([]);
    expect(comparisonCandidates(LIB, [H('h', 'rlt')], 'limitAdd')).toEqual([]);
  });

  test('nothing to compare with when no lemma has an inductive result', () => {
    expect(comparisonCandidates(LIB.filter((d) => !d.conclIsInductive), HYPS, 'limitAdd')).toEqual([]);
  });
});

describe('valueCandidates ("what could I put here?")', () => {
  const LIB = [
    fact('rmin', 'Carrier', ['Carrier', 'Carrier'], 2),
    fact('radd', 'Carrier', ['Carrier', 'Carrier'], 2),
    fact('rneg', 'Carrier', ['Carrier'], 1),
    // Result is a proposition, not a value of the goal's type.
    fact('rlt', null, ['Carrier', 'Carrier'], 2),
    // Argument isn't the goal's type.
    fact('realOfRat', 'Carrier', ['Real', 'MyRat'], 2),
    // Three arguments — not a one-step combination.
    fact('rmid3', 'Carrier', ['Carrier', 'Carrier', 'Carrier'], 3),
  ];
  const H = (name: string, typeHead: string | null) => ({ name, type: '', typeHead });
  const HYPS = [
    H('x0', 'Carrier'), H('L', 'Carrier'), H('\u03b5', 'Carrier'),
    H('epsPos', 'rlt'), H('deltaF', 'Carrier'), H('deltaG', 'Carrier'),
  ];

  test('offers the δ the proof actually needs, and in scope order', () => {
    const out = valueCandidates(LIB, 'Carrier', HYPS, 'limitAdd');
    // Never a bare hypothesis — it has to be BUILT.
    expect(out).toContain('rmin deltaF deltaG');
    expect(out).not.toContain('rmin deltaG deltaF');
  });

  test('in-scope values come first, most recent first', () => {
    expect(valueCandidates(LIB, 'Carrier', HYPS, 'limitAdd').slice(0, 2)).toEqual(['deltaG', 'deltaF']);
  });

  test('only operations that take and return the goal type', () => {
    const built = valueCandidates(LIB, 'Carrier', HYPS, 'limitAdd').filter((e) => e.includes(' '));
    expect(built).toEqual(expect.arrayContaining(['rmin deltaF deltaG', 'radd deltaF deltaG', 'rneg deltaG']));
    expect(built.some((e) => e.startsWith('rlt '))).toBe(false);
    expect(built.some((e) => e.startsWith('realOfRat '))).toBe(false);
    expect(built.some((e) => e.startsWith('rmid3 '))).toBe(false);
  });

  test('nothing to offer when no value of that type is in scope', () => {
    expect(valueCandidates(LIB, 'Carrier', [H('h', 'rlt')], 'limitAdd')).toEqual([]);
    expect(valueCandidates(LIB, 'MyNat', HYPS, 'limitAdd')).toEqual([]);
    expect(valueCandidates(LIB, null, HYPS, 'limitAdd')).toEqual([]);
  });
});
