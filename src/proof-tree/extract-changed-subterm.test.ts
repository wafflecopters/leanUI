/**
 * Tests for extractChangedSubterm — the lockstep diff that lets suggestion
 * previews show only the part of the goal a tactic actually rewrote.
 *
 * Each test pairs an "old" and "new" kernel term that differ at exactly one
 * position. The walker should return that minimal divergent subtree.
 */
import { describe, test, expect } from 'vitest';
import { extractChangedSubterm } from './tactic-suggestions';

const C = (name: string): any => ({ tag: 'Const', name });
const A = (fn: any, arg: any): any => ({ tag: 'App', fn, arg });
const V = (i: number): any => ({ tag: 'Var', index: i });
const N = (v: bigint): any => ({ tag: 'NatLit', value: v });
const Pi = (name: string, dom: any, body: any): any => ({ tag: 'Binder', binderKind: { tag: 'BPi' }, name, domain: dom, body });

describe('extractChangedSubterm', () => {
  test('returns null when terms are equal', () => {
    const term = A(C('f'), N(1n));
    expect(extractChangedSubterm(term, term, [])).toBeNull();
  });

  test('descends into App argument when only arg changed', () => {
    const oldT = A(C('f'), N(1n));
    const newT = A(C('f'), N(2n));
    const change = extractChangedSubterm(oldT, newT, []);
    expect(change).not.toBeNull();
    expect(change!.old).toEqual(N(1n));
    expect(change!.new).toEqual(N(2n));
    expect(change!.ctx).toEqual([]);
  });

  test('descends into App function when only fn changed', () => {
    const oldT = A(C('f'), N(1n));
    const newT = A(C('g'), N(1n));
    const change = extractChangedSubterm(oldT, newT, []);
    expect(change!.old).toEqual(C('f'));
    expect(change!.new).toEqual(C('g'));
  });

  test('stops at App when both fn and arg differ — returns the App, not deeper', () => {
    const oldT = A(C('f'), N(1n));
    const newT = A(C('g'), N(2n));
    const change = extractChangedSubterm(oldT, newT, []);
    expect(change!.old).toEqual(oldT);
    expect(change!.new).toEqual(newT);
  });

  test('descends through nested Apps to deepest single difference', () => {
    // Goal-like: le (radd 1 (-1)) (radd 2 (-1)). User unfolds radd in LHS.
    // Suppose unfolded form changes only the leftmost subtree:
    // before: le (radd 1 (-1)) (radd 2 (-1))
    // after:  le (UNFOLDED_RADD_1) (radd 2 (-1))
    const before = A(A(C('le'), A(A(C('radd'), N(1n)), C('m1'))), A(A(C('radd'), N(2n)), C('m1')));
    const after  = A(A(C('le'), A(A(C('add_unfolded'), N(1n)), C('m1'))), A(A(C('radd'), N(2n)), C('m1')));
    const change = extractChangedSubterm(before, after, []);
    expect(change).not.toBeNull();
    // Should land at the 'radd' vs 'add_unfolded' difference, not at the whole goal
    expect(change!.old).toEqual(C('radd'));
    expect(change!.new).toEqual(C('add_unfolded'));
  });

  test('descends into Binder domain', () => {
    const oldT = Pi('x', C('Nat'), V(0));
    const newT = Pi('x', C('Int'), V(0));
    const change = extractChangedSubterm(oldT, newT, []);
    expect(change!.old).toEqual(C('Nat'));
    expect(change!.new).toEqual(C('Int'));
  });

  test('descends into Binder body and extends ctx', () => {
    const oldT = Pi('x', C('Nat'), A(C('f'), V(0)));
    const newT = Pi('x', C('Nat'), A(C('g'), V(0)));
    const change = extractChangedSubterm(oldT, newT, []);
    expect(change!.old).toEqual(C('f'));
    expect(change!.new).toEqual(C('g'));
    // Ctx should be extended with the binder we descended through.
    expect(change!.ctx).toHaveLength(1);
    expect(change!.ctx[0].name).toBe('x');
    expect(change!.ctx[0].type).toEqual(C('Nat'));
  });

  test('stops at Binder when both domain and body differ', () => {
    const oldT = Pi('x', C('Nat'), V(0));
    const newT = Pi('x', C('Int'), A(C('f'), V(0)));
    const change = extractChangedSubterm(oldT, newT, []);
    expect(change!.old).toEqual(oldT);
    expect(change!.new).toEqual(newT);
  });
});
