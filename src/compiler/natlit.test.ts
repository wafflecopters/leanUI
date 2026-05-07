/**
 * Phase 1 tests for NatLit kernel primitive.
 *
 * NatLit is an inert primitive: parser produces it, renderer prints it,
 * WHNF/unify/subst/shift treat it as opaque. Iota-reduction and coercion
 * are deferred to Phase 2 / Phase 3.
 */

import { describe, test, expect } from 'vitest';
import { TTKTerm, prettyPrint, isDefinitionallyEqual } from './kernel';
import { whnf } from './whnf';
import { subst, shiftTerm } from './subst';
import { unifyTerms } from './unify';
import { parseExactExpr } from '../proof-tree/goal-computation';

describe('NatLit kernel primitive', () => {
  test('prettyPrint renders NatLit as decimal', () => {
    const t: TTKTerm = { tag: 'NatLit', value: 1784n };
    expect(prettyPrint(t)).toBe('1784');
  });

  test('prettyPrint handles zero', () => {
    const t: TTKTerm = { tag: 'NatLit', value: 0n };
    expect(prettyPrint(t)).toBe('0');
  });

  test('prettyPrint handles BigInt-range literals', () => {
    const big = 12345678901234567890n;
    const t: TTKTerm = { tag: 'NatLit', value: big };
    expect(prettyPrint(t)).toBe('12345678901234567890');
  });

  test('whnf is identity on NatLit', () => {
    const t: TTKTerm = { tag: 'NatLit', value: 5n };
    const reduced = whnf(t);
    expect(reduced).toEqual(t);
  });

  test('isDefinitionallyEqual: same value succeeds', () => {
    const a: TTKTerm = { tag: 'NatLit', value: 42n };
    const b: TTKTerm = { tag: 'NatLit', value: 42n };
    expect(isDefinitionallyEqual(a, b)).toBe(true);
  });

  test('isDefinitionallyEqual: different value fails', () => {
    const a: TTKTerm = { tag: 'NatLit', value: 42n };
    const b: TTKTerm = { tag: 'NatLit', value: 43n };
    expect(isDefinitionallyEqual(a, b)).toBe(false);
  });

  test('unifyTerms: same value succeeds', () => {
    const a: TTKTerm = { tag: 'NatLit', value: 5n };
    const b: TTKTerm = { tag: 'NatLit', value: 5n };
    const r = unifyTerms(a, b, { mode: 'check' });
    expect(r.success).toBe(true);
  });

  test('unifyTerms: different value fails', () => {
    const a: TTKTerm = { tag: 'NatLit', value: 5n };
    const b: TTKTerm = { tag: 'NatLit', value: 6n };
    const r = unifyTerms(a, b, { mode: 'check' });
    expect(r.success).toBe(false);
  });

  test('shiftTerm is identity on NatLit (no free vars)', () => {
    const t: TTKTerm = { tag: 'NatLit', value: 5n };
    expect(shiftTerm(t, 1, 0)).toEqual(t);
    expect(shiftTerm(t, 100, 50)).toEqual(t);
  });

  test('subst is identity on NatLit (no Var refs)', () => {
    const t: TTKTerm = { tag: 'NatLit', value: 5n };
    const replacement: TTKTerm = { tag: 'Const', name: 'foo' };
    expect(subst(0, replacement, t)).toEqual(t);
  });
});

describe('NatLit parser (parseExactExpr)', () => {
  test('parses "0" as NatLit(0n)', () => {
    const t = parseExactExpr('0', [], undefined);
    expect(t).toEqual({ tag: 'NatLit', value: 0n });
  });

  test('parses "1784" as NatLit(1784n)', () => {
    const t = parseExactExpr('1784', [], undefined);
    expect(t).toEqual({ tag: 'NatLit', value: 1784n });
  });

  test('parses BigInt-range literal', () => {
    const t = parseExactExpr('12345678901234567890', [], undefined);
    expect(t).toEqual({ tag: 'NatLit', value: 12345678901234567890n });
  });

  test('does NOT parse non-digit names as NatLit', () => {
    const t = parseExactExpr('foo', [], undefined);
    expect((t as any).tag).toBe('Const');
    expect((t as any).name).toBe('foo');
  });

  test('does NOT parse mixed digit/letter as NatLit (e.g., "x1")', () => {
    const t = parseExactExpr('x1', [], undefined);
    expect((t as any).tag).toBe('Const');
    expect((t as any).name).toBe('x1');
  });

  test('roundtrip: parse → prettyPrint preserves value', () => {
    for (const s of ['0', '1', '42', '1784', '999999999999']) {
      const t = parseExactExpr(s, [], undefined);
      expect(t).not.toBeNull();
      expect(prettyPrint(t!)).toBe(s);
    }
  });
});
