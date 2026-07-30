import { describe, expect, test } from 'vitest';
import { introBinderNames } from './introBinders';

describe('introBinderNames', () => {
  // The first move of every ε-δ proof.
  test('names a value binder after itself and its hypothesis h', () => {
    // `epsilon` is introduced as ε — the letter the editor already displays, so
    // what the user reads is what they can type.
    expect(introBinderNames('(epsilon : ℝ) → 0 < epsilon → DPair ℝ (fun delta => P delta)')).toEqual([
      'ε',
      'h',
    ]);
  });

  test('a spelled-out Greek binder becomes its letter; plain names are untouched', () => {
    expect(introBinderNames('(delta : ℝ) → P delta')).toEqual(['δ']);
    expect(introBinderNames('(n : MyNat) → P n')).toEqual(['n']);
    expect(introBinderNames('(eps : ℝ) → P eps')).toEqual(['eps']);
  });

  test('several anonymous antecedents get h, h1, h2', () => {
    expect(
      introBinderNames('(x : ℝ) → 0 < |x - x0| → |x - x0| < delta → |f x - L| < eps'),
    ).toEqual(['x', 'h', 'h1']);
  });

  test('a ∀-spelled binder is introduced too', () => {
    expect(introBinderNames('∀ (n : MyNat), P n')).toEqual(['n']);
  });

  test('a goal with nothing at the front introduces nothing', () => {
    expect(introBinderNames('0 < ε / 2')).toEqual([]);
    expect(introBinderNames('ℝ')).toEqual([]);
  });

  // Shadowing a hypothesis makes the earlier one unusable by name — the exact
  // thing a beginner then can't diagnose.
  test('never shadows a name already in scope', () => {
    expect(introBinderNames('(epsilon : ℝ) → 0 < epsilon → P', ['ε', 'h'])).toEqual(['ε1', 'h1']);
  });

  test('two binders of the same name are kept distinct', () => {
    expect(introBinderNames('(a : ℝ) → (a : ℝ) → P')).toEqual(['a', 'a1']);
  });

  test('an inaccessible or placeholder binder falls back to h', () => {
    expect(introBinderNames('(a✝ : ℝ) → P')).toEqual(['a']);
    expect(introBinderNames('(_ : ℝ) → P')).toEqual(['h']);
  });

  test('Greek binder names survive (they render as the letter)', () => {
    expect(introBinderNames('(δ : ℝ) → 0 < δ → P')).toEqual(['δ', 'h']);
  });
});
