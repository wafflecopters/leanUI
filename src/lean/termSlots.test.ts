import { describe, expect, test } from 'vitest';
import { parseSlots, appliedExpr, slotSuggestionNames, projectionCandidates } from './termSlots';

describe('parseSlots', () => {
  test('eps_delta shape: named binder + anonymous Prop antecedent', () => {
    const r = parseSlots('(epsilon : ℝ) → 0 < epsilon → DPair ℝ fun delta => EpsDeltaWitness f x0 L epsilon delta');
    expect(r.slots).toEqual([
      { name: 'epsilon', type: 'ℝ' },
      { type: '0 < epsilon' },
    ]);
    expect(r.returnType).toContain('DPair');
  });

  test('multi-name group: (a b : T) → one slot per name', () => {
    const r = parseSlots('(a b : MyNat) → a + b = b + a');
    expect(r.slots).toEqual([
      { name: 'a', type: 'MyNat' },
      { name: 'b', type: 'MyNat' },
    ]);
    expect(r.returnType).toBe('a + b = b + a');
  });

  test('∀-spelled binders', () => {
    const r = parseSlots('∀ (n m : MyNat), n + m = m + n');
    expect(r.slots).toEqual([
      { name: 'n', type: 'MyNat' },
      { name: 'm', type: 'MyNat' },
    ]);
    expect(r.returnType).toBe('n + m = m + n');
  });

  test('implicit and instance binders are skipped (Lean infers them)', () => {
    const r = parseSlots('{R : Real} → [inst : Foo R] → (x : ℝ) → 0 < x → P x');
    expect(r.slots).toEqual([
      { name: 'x', type: 'ℝ' },
      { type: '0 < x' },
    ]);
  });

  test('non-function type → no slots, itself the return type', () => {
    const r = parseSlots('lim⟦x0⟧ f = L');
    expect(r.slots).toEqual([]);
    expect(r.returnType).toBe('lim⟦x0⟧ f = L');
  });

  test('parenthesized anonymous antecedent (function-typed arg)', () => {
    const r = parseSlots('(ℝ → ℝ) → ℝ');
    expect(r.slots).toEqual([{ type: 'ℝ → ℝ' }]);
    expect(r.returnType).toBe('ℝ');
  });
});

describe('appliedExpr', () => {
  test('single tokens stay bare; compounds get parens; empties skipped', () => {
    expect(appliedExpr('limF.eps_delta', ['eps', ''])).toBe('limF.eps_delta eps');
    expect(appliedExpr('limF.eps_delta', ['rdiv eps (rtwo R)', 'divTwoPos eps epsPos'])).toBe(
      'limF.eps_delta (rdiv eps (rtwo R)) (divTwoPos eps epsPos)',
    );
    expect(appliedExpr('f', ['(a + b)'])).toBe('f (a + b)');
  });
});

describe('slotSuggestionNames', () => {
  const hyps = [
    { name: 'eps', type: 'ℝ' },
    { name: 'epsPos', type: '0 < eps' },
    { name: 'limF', type: 'lim⟦x0⟧ f = L' },
    { name: 'x0', type: 'ℝ' },
  ];

  test('exact type match ranks first', () => {
    const s = slotSuggestionNames('0 < eps', hyps);
    expect(s[0]).toBe('epsPos');
  });

  test('head-shape match when no exact match', () => {
    const s = slotSuggestionNames('ℝ', hyps);
    expect(s).toEqual(['eps', 'x0']);
  });
});

describe('projectionCandidates', () => {
  // Nothing to rank and nothing to guess: Lean reports the structure's fields
  // (after unfolding, so an abbreviation like `EpsDeltaWitness` gives `Pair`'s
  // fields), and every one of them is a real projection. The version this
  // replaced scored dotted declarations by token overlap — it missed
  // `Pair.fst` on a hypothesis printing as `EpsDeltaWitness …`, and offered
  // `limF.supUpperBound`, which cannot typecheck.
  test('offers exactly the fields Lean reported', () => {
    expect(projectionCandidates('fProof', ['fst', 'snd'])).toEqual(['fProof.fst', 'fProof.snd']);
    expect(projectionCandidates('limF', ['eps_delta'])).toEqual(['limF.eps_delta']);
  });

  test('a hypothesis that is not a structure has no projections', () => {
    expect(projectionCandidates('deltaF', [])).toEqual([]);
  });
});

describe('appliedExprWithHoles / parseApplied (builder ⟷ have round-trip)', () => {
  test('holes print as ?_ and parse back to null', async () => {
    const { appliedExprWithHoles, parseApplied } = await import('./termSlots');
    const expr = appliedExprWithHoles('limF.eps_delta', [null, 'divTwoPos eps epsPos']);
    expect(expr).toBe('limF.eps_delta ?_ (divTwoPos eps epsPos)');
    const back = parseApplied(expr);
    expect(back.fn).toBe('limF.eps_delta');
    expect(back.values).toEqual([null, 'divTwoPos eps epsPos']);
  });

  test('bare fn round-trips with no values', async () => {
    const { parseApplied } = await import('./termSlots');
    expect(parseApplied('limF.eps_delta')).toEqual({ fn: 'limF.eps_delta', values: [] });
  });
});

describe('resolveGreekToHypNames', () => {
  test('ε resolves to the unique prefix-named hypothesis (eps ⊂ epsilon)', async () => {
    const { resolveGreekToHypNames } = await import('./termSlots');
    expect(resolveGreekToHypNames('ε / 2', ['eps', 'epsPos', 'limF'])).toBe('eps / 2');
  });

  test('a real unicode-named hypothesis is left alone (→ null, no change needed)', async () => {
    const { resolveGreekToHypNames } = await import('./termSlots');
    expect(resolveGreekToHypNames('ε / 2', ['ε', 'h'])).toBeNull();
  });

  test('ambiguous or unmatched → null', async () => {
    const { resolveGreekToHypNames } = await import('./termSlots');
    expect(resolveGreekToHypNames('ε / 2', ['eps', 'epsilon'])).toBeNull(); // two candidates
    expect(resolveGreekToHypNames('δ + 1', ['eps'])).toBeNull(); // no candidate
  });
});
