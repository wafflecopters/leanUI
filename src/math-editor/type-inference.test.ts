import { describe, test, expect, beforeEach } from 'vitest';
import { resetIds, mkRow, mkSymbol, mkHole, mkText, mkDelimiter, mkSub, mkFrac } from './types';
import { inferTypeSignature } from './type-inference';

beforeEach(() => resetIds());

describe('inferTypeSignature', () => {
  test('empty row → null', () => {
    expect(inferTypeSignature(mkRow([]))).toBe(null);
  });

  test('no relation symbol → null', () => {
    const row = mkRow([mkSymbol('a'), mkSymbol('b')]);
    expect(inferTypeSignature(row)).toBe(null);
  });

  test('incomplete: a ∈ (nothing after) → null', () => {
    const row = mkRow([mkSymbol('a'), mkSymbol('\\in')]);
    expect(inferTypeSignature(row)).toBe(null);
  });

  test('a ∈ ℝ → {R : Real} -> (a : Carrier R) -> ?', () => {
    const row = mkRow([mkSymbol('a'), mkSymbol('\\in'), mkSymbol('\\mathbb{R}')]);
    expect(inferTypeSignature(row)).toBe('{R : Real} -> (a : Carrier R) -> ?');
  });

  test('a, b ∈ ℝ → {R : Real} -> (a b : Carrier R) -> ?', () => {
    const row = mkRow([
      mkSymbol('a'), mkSymbol(','), mkSymbol('b'),
      mkSymbol('\\in'), mkSymbol('\\mathbb{R}'),
    ]);
    expect(inferTypeSignature(row)).toBe('{R : Real} -> (a b : Carrier R) -> ?');
  });

  test('f : ℝ → ℝ → {R : Real} -> (f : Carrier R -> Carrier R) -> ?', () => {
    const row = mkRow([
      mkSymbol('f'), mkSymbol(':'),
      mkSymbol('\\mathbb{R}'), mkSymbol('\\to'), mkSymbol('\\mathbb{R}'),
    ]);
    expect(inferTypeSignature(row)).toBe('{R : Real} -> (f : Carrier R -> Carrier R) -> ?');
  });

  test('a, b ∈ ℝ and f, g : ℝ → ℝ → full combined output', () => {
    const row = mkRow([
      mkSymbol('a'), mkSymbol(','), mkSymbol('b'),
      mkSymbol('\\in'), mkSymbol('\\mathbb{R}'),
      mkText('and'),
      mkSymbol('f'), mkSymbol(','), mkSymbol('g'),
      mkSymbol(':'),
      mkSymbol('\\mathbb{R}'), mkSymbol('\\to'), mkSymbol('\\mathbb{R}'),
    ]);
    expect(inferTypeSignature(row)).toBe(
      '{R : Real} -> (a b : Carrier R) -> (f g : Carrier R -> Carrier R) -> ?'
    );
  });

  test('n ∈ ℕ → (n : Nat) -> ? (no implicit R)', () => {
    const row = mkRow([mkSymbol('n'), mkSymbol('\\in'), mkSymbol('\\mathbb{N}')]);
    expect(inferTypeSignature(row)).toBe('(n : Nat) -> ?');
  });

  test('n ∈ ℕ and x ∈ ℝ → {R : Real} -> (n : Nat) -> (x : Carrier R) -> ?', () => {
    const row = mkRow([
      mkSymbol('n'), mkSymbol('\\in'), mkSymbol('\\mathbb{N}'),
      mkText('and'),
      mkSymbol('x'), mkSymbol('\\in'), mkSymbol('\\mathbb{R}'),
    ]);
    expect(inferTypeSignature(row)).toBe('{R : Real} -> (n : Nat) -> (x : Carrier R) -> ?');
  });

  test('f : ℝ → ℝ → ℝ → arrow chain', () => {
    const row = mkRow([
      mkSymbol('f'), mkSymbol(':'),
      mkSymbol('\\mathbb{R}'), mkSymbol('\\to'),
      mkSymbol('\\mathbb{R}'), mkSymbol('\\to'),
      mkSymbol('\\mathbb{R}'),
    ]);
    expect(inferTypeSignature(row)).toBe(
      '{R : Real} -> (f : Carrier R -> Carrier R -> Carrier R) -> ?'
    );
  });

  test('f : (ℝ → ℝ) → ℝ → parenthesized type via Delimiter', () => {
    const row = mkRow([
      mkSymbol('f'), mkSymbol(':'),
      mkDelimiter('(', ')',
        mkRow([mkSymbol('\\mathbb{R}'), mkSymbol('\\to'), mkSymbol('\\mathbb{R}')])
      ),
      mkSymbol('\\to'), mkSymbol('\\mathbb{R}'),
    ]);
    expect(inferTypeSignature(row)).toBe(
      '{R : Real} -> (f : (Carrier R -> Carrier R) -> Carrier R) -> ?'
    );
  });

  test('partial: first segment complete, second incomplete → null', () => {
    const row = mkRow([
      mkSymbol('a'), mkSymbol('\\in'), mkSymbol('\\mathbb{R}'),
      mkText('and'),
      mkSymbol('f'), // incomplete — no relation symbol
    ]);
    expect(inferTypeSignature(row)).toBe(null);
  });

  test('single variable with colon and Nat', () => {
    const row = mkRow([
      mkSymbol('n'), mkSymbol(':'), mkSymbol('\\mathbb{N}'),
    ]);
    expect(inferTypeSignature(row)).toBe('(n : Nat) -> ?');
  });
});
