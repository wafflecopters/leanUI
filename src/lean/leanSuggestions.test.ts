import { describe, expect, test } from 'vitest';
import { parseTryThis, suggestionsFromMessages } from './leanSuggestions';
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
