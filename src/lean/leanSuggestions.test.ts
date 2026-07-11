import { describe, expect, test } from 'vitest';
import { parseTryThis, suggestionsFromMessages, targetedSuggestions } from './leanSuggestions';
import type { LeanMessage } from './types';

const info = (text: string): LeanMessage => ({
  severity: 'information',
  startLine: 1,
  startCol: 0,
  endLine: 1,
  endCol: 1,
  text,
});

describe('parseTryThis', () => {
  test('parses a plain exact suggestion', () => {
    const s = parseTryThis('Try this:\n  exact Nat.add_comm a b', 'exact');
    expect(s).toHaveLength(1);
    expect(s[0].tactic).toBe('exact Nat.add_comm a b');
    expect(s[0].kind).toBe('exact');
    expect(s[0].id).toContain('lean-exact:');
  });

  test('strips a leading [apply] tag', () => {
    const s = parseTryThis('Try this:\n  [apply] exact Nat.add_left_inj.mpr h', 'exact');
    expect(s[0].tactic).toBe('exact Nat.add_left_inj.mpr h');
  });

  test('drops trailing -- comments (rw? form)', () => {
    const s = parseTryThis('Try this: rw [h]\n  -- no goals', 'rw');
    expect(s).toHaveLength(1);
    expect(s[0].tactic).toBe('rw [h]');
  });

  test('handles simp? only form', () => {
    const s = parseTryThis('Try this:\n  [apply] simp only [Nat.add_zero]', 'simp');
    expect(s[0].tactic).toBe('simp only [Nat.add_zero]');
  });

  test('no marker → empty', () => {
    expect(parseTryThis('some other message', 'exact')).toEqual([]);
  });

  test('dedups identical tactic lines', () => {
    const s = parseTryThis('Try this:\n  exact h\n  exact h', 'exact');
    expect(s).toHaveLength(1);
  });
});

describe('suggestionsFromMessages', () => {
  test('collects from info messages only, deduped', () => {
    const msgs: LeanMessage[] = [
      info('Try this:\n  exact h1'),
      { ...info('Try this:\n  exact h2'), severity: 'error' }, // ignored (error)
      info('Try this:\n  exact h1'), // dup
      info('Try this:\n  exact h3'),
    ];
    const s = suggestionsFromMessages(msgs, 'exact');
    expect(s.map((x) => x.tactic)).toEqual(['exact h1', 'exact h3']);
  });
});

describe('targetedSuggestions', () => {
  test('a bare variable offers induction and cases on it', () => {
    const s = targetedSuggestions('n');
    expect(s.map((x) => x.label)).toEqual(['induction n', 'cases n']);
    expect(s[0].tactic).toContain('induction n');
    expect(s[0].tactic).toContain('·');
  });

  test("primed/underscored identifiers count as variables", () => {
    expect(targetedSuggestions("k'").map((x) => x.label)).toEqual(['induction k\'', 'cases k\'']);
  });

  test('a compound expression offers no targeted tactics', () => {
    expect(targetedSuggestions('a + b')).toEqual([]);
    expect(targetedSuggestions('f x')).toEqual([]);
    expect(targetedSuggestions('0')).toEqual([]); // numeral, not a var
  });

  test('an equality goal offers rfl (the tactic — reduces both sides and closes)', () => {
    const s = targetedSuggestions('2 * ∑[i,0,0] i = (0 + 1) * 0');
    expect(s).toHaveLength(1);
    expect(s[0].label).toBe('rfl');
    expect(s[0].tactic).toBe('rfl');
  });

  test('a non-equality compound (e.g. ≤) offers no refl', () => {
    expect(targetedSuggestions('a ≤ b')).toEqual([]);
  });
});

describe('freshHypName', () => {
  test('h when free, else h1, h2, …', async () => {
    const { freshHypName } = await import('./leanSuggestions');
    expect(freshHypName([])).toBe('h');
    expect(freshHypName(['h'])).toBe('h1');
    expect(freshHypName(['h', 'h1', 'h2'])).toBe('h3');
    expect(freshHypName(['limF', 'eps'])).toBe('h');
  });
});

describe('hypothesisSuggestions', () => {
  test('offers exact/apply/cases for a clicked hypothesis', async () => {
    const { hypothesisSuggestions } = await import('./leanSuggestions');
    const s = hypothesisSuggestions('limF');
    expect(s.map((x) => x.label)).toEqual(['exact limF', 'apply limF', 'cases limF']);
    // cases validates via the bare form but applies with a case-bullet hole.
    const cases = s.find((x) => x.label === 'cases limF')!;
    expect(cases.validateTactic).toBe('cases limF');
    expect(cases.tactic).toContain('·');
  });
});
