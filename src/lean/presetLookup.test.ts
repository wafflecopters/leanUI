import { describe, expect, test } from 'vitest';
import { presetSlug, findPresetBySlug, parseEditorUrlParams, resolveSymbolName } from './presetLookup';
import { LEAN_PRESETS } from './presets';

describe('presetSlug', () => {
  test('kebab-cases display names, dropping punctuation', () => {
    expect(presetSlug('Real Analysis (chain rule)')).toBe('real-analysis-chain-rule');
    expect(presetSlug('Nat Math (from scratch)')).toBe('nat-math-from-scratch');
    expect(presetSlug('Basics')).toBe('basics');
    expect(presetSlug('Mathlib (∑, ring)')).toBe('mathlib-ring');
  });
});

describe('findPresetBySlug (against the real preset list)', () => {
  test('short form real-analysis resolves by prefix', () => {
    expect(findPresetBySlug(LEAN_PRESETS, 'real-analysis')?.name).toBe('Real Analysis (chain rule)');
  });

  test('exact slug resolves', () => {
    expect(findPresetBySlug(LEAN_PRESETS, 'nat-math-from-scratch')?.name).toBe('Nat Math (from scratch)');
    expect(findPresetBySlug(LEAN_PRESETS, 'basics')?.name).toBe('Basics');
  });

  test('exact slug beats a competing prefix match', () => {
    // 'nat-math-tactics' must NOT fall to the prefix rule picking 'from scratch'.
    expect(findPresetBySlug(LEAN_PRESETS, 'nat-math-tactics')?.name).toBe('Nat Math (tactics)');
  });

  test('ambiguous prefix picks the first preset in declaration order', () => {
    expect(findPresetBySlug(LEAN_PRESETS, 'nat-math')?.name).toBe('Nat Math (from scratch)');
  });

  test('case/format-insensitive: display-name-ish input still resolves', () => {
    expect(findPresetBySlug(LEAN_PRESETS, 'Real Analysis (chain rule)')?.name).toBe('Real Analysis (chain rule)');
    expect(findPresetBySlug(LEAN_PRESETS, 'REAL-ANALYSIS')?.name).toBe('Real Analysis (chain rule)');
  });

  test('unknown or empty → null', () => {
    expect(findPresetBySlug(LEAN_PRESETS, 'no-such-preset')).toBeNull();
    expect(findPresetBySlug(LEAN_PRESETS, '')).toBeNull();
    expect(findPresetBySlug(LEAN_PRESETS, '   ')).toBeNull();
  });
});

describe('parseEditorUrlParams', () => {
  test('parses both params from a search string', () => {
    const r = parseEditorUrlParams('?preset=real-analysis&symbol=limitAdd', LEAN_PRESETS);
    expect(r.preset?.name).toBe('Real Analysis (chain rule)');
    expect(r.symbol).toBe('limitAdd');
  });

  test('missing params → nulls', () => {
    const r = parseEditorUrlParams('', LEAN_PRESETS);
    expect(r.preset).toBeNull();
    expect(r.symbol).toBeNull();
  });

  test('symbol alone works (no preset)', () => {
    const r = parseEditorUrlParams('?symbol=triangleSum', LEAN_PRESETS);
    expect(r.preset).toBeNull();
    expect(r.symbol).toBe('triangleSum');
  });

  test('unknown preset param → null preset, symbol still parsed', () => {
    const r = parseEditorUrlParams('?preset=bogus&symbol=foo', LEAN_PRESETS);
    expect(r.preset).toBeNull();
    expect(r.symbol).toBe('foo');
  });

  test('accepts a URLSearchParams instance', () => {
    const r = parseEditorUrlParams(new URLSearchParams({ preset: 'basics' }), LEAN_PRESETS);
    expect(r.preset?.name).toBe('Basics');
  });
});

describe('resolveSymbolName', () => {
  const decls = [{ name: 'limitAdd' }, { name: 'Limit' }, { name: 'lim' }];

  test('exact match wins', () => {
    expect(resolveSymbolName(decls, 'limitAdd')).toBe('limitAdd');
    // exact beats case-insensitive: 'lim' resolves to 'lim', not 'Limit'.
    expect(resolveSymbolName(decls, 'lim')).toBe('lim');
  });

  test('falls back to case-insensitive and returns the canonical name', () => {
    expect(resolveSymbolName(decls, 'limitadd')).toBe('limitAdd');
    expect(resolveSymbolName(decls, 'LIMIT')).toBe('Limit');
  });

  test('unknown → null', () => {
    expect(resolveSymbolName(decls, 'nope')).toBeNull();
    expect(resolveSymbolName([], 'limitAdd')).toBeNull();
  });
});
