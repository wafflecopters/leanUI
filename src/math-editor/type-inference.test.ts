import { describe, test, expect, beforeEach } from 'vitest';
import { resetIds, mkRow, mkSymbol, mkHole, mkText, mkDelimiter, mkSub, mkFrac, mkBigOp } from './types';
import { inferTypeSignature } from './type-inference';

beforeEach(() => resetIds());

describe('inferTypeSignature', () => {
  test('empty row → null', () => {
    expect(inferTypeSignature(mkRow([]))).toBe(null);
  });

  test('no relation symbol → anonymous hypothesis', () => {
    const row = mkRow([mkSymbol('a'), mkSymbol('b')]);
    expect(inferTypeSignature(row)).toBe('(_ : a b) -> ?');
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

  test('partial: first segment complete, second has no relation → anonymous hypothesis', () => {
    const row = mkRow([
      mkSymbol('a'), mkSymbol('\\in'), mkSymbol('\\mathbb{R}'),
      mkText('and'),
      mkSymbol('f'), // no relation symbol — becomes anonymous hypothesis
    ]);
    expect(inferTypeSignature(row)).toBe('{R : Real} -> (a : Carrier R) -> (_ : f) -> ?');
  });

  test('single variable with colon and Nat', () => {
    const row = mkRow([
      mkSymbol('n'), mkSymbol(':'), mkSymbol('\\mathbb{N}'),
    ]);
    expect(inferTypeSignature(row)).toBe('(n : Nat) -> ?');
  });
});

// ============================================================================
// Body separators
// ============================================================================

describe('body separators', () => {
  test('a ∈ ℝ, then a = a → body converted via registry', () => {
    const row = mkRow([
      mkSymbol('a'), mkSymbol('\\in'), mkSymbol('\\mathbb{R}'),
      mkSymbol(','), mkText('then'),
      mkSymbol('a'), mkSymbol('='), mkSymbol('a'),
    ]);
    expect(inferTypeSignature(row)).toBe('{R : Real} -> (a : Carrier R) -> Equal a a');
  });

  test('a ∈ ℝ then a = a (space-then-space)', () => {
    const row = mkRow([
      mkSymbol('a'), mkSymbol('\\in'), mkSymbol('\\mathbb{R}'),
      mkText('then'),
      mkSymbol('a'), mkSymbol('='), mkSymbol('a'),
    ]);
    expect(inferTypeSignature(row)).toBe('{R : Real} -> (a : Carrier R) -> Equal a a');
  });

  test('a ∈ ℝ. Then a = a (dot-Then)', () => {
    const row = mkRow([
      mkSymbol('a'), mkSymbol('\\in'), mkSymbol('\\mathbb{R}'),
      mkSymbol('.'), mkText('Then'),
      mkSymbol('a'), mkSymbol('='), mkSymbol('a'),
    ]);
    expect(inferTypeSignature(row)).toBe('{R : Real} -> (a : Carrier R) -> Equal a a');
  });

  test('body with ℝ adds implicit R', () => {
    const row = mkRow([
      mkSymbol('n'), mkSymbol('\\in'), mkSymbol('\\mathbb{N}'),
      mkText('then'),
      mkSymbol('n'), mkSymbol('\\in'), mkSymbol('\\mathbb{R}'),
    ]);
    // \in matches element-of pattern: elem n (Carrier R)
    expect(inferTypeSignature(row)).toBe('{R : Real} -> (n : Nat) -> elem n (Carrier R)');
  });

  test('combined: a, b ∈ ℝ and f : ℝ → ℝ, then f(a) + f(b)', () => {
    const row = mkRow([
      mkSymbol('a'), mkSymbol(','), mkSymbol('b'),
      mkSymbol('\\in'), mkSymbol('\\mathbb{R}'),
      mkText('and'),
      mkSymbol('f'), mkSymbol(':'),
      mkSymbol('\\mathbb{R}'), mkSymbol('\\to'), mkSymbol('\\mathbb{R}'),
      mkSymbol(','), mkText('then'),
      mkSymbol('f'),
      mkDelimiter('(', ')', mkRow([mkSymbol('a')])),
      mkSymbol('+'),
      mkSymbol('f'),
      mkDelimiter('(', ')', mkRow([mkSymbol('b')])),
    ]);
    // + pattern matches: radd (f (a)) (f (b))
    expect(inferTypeSignature(row)).toBe(
      '{R : Real} -> (a b : Carrier R) -> (f : Carrier R -> Carrier R) -> radd (f (a)) (f (b))'
    );
  });

  test('no body separator → ? as before', () => {
    const row = mkRow([mkSymbol('a'), mkSymbol('\\in'), mkSymbol('\\mathbb{R}')]);
    expect(inferTypeSignature(row)).toBe('{R : Real} -> (a : Carrier R) -> ?');
  });

  test('body separator with empty body → ?', () => {
    const row = mkRow([
      mkSymbol('a'), mkSymbol('\\in'), mkSymbol('\\mathbb{R}'),
      mkText('then'),
    ]);
    expect(inferTypeSignature(row)).toBe('{R : Real} -> (a : Carrier R) -> ?');
  });
});

// ============================================================================
// Anonymous hypothesis bindings (segments without ∈ or :)
// ============================================================================

describe('anonymous hypothesis bindings', () => {
  test('a ∈ ℝ and lim_{x→x₀} f(x) = L → anonymous hypothesis', () => {
    const row = mkRow([
      mkSymbol('a'), mkSymbol('\\in'), mkSymbol('\\mathbb{R}'),
      mkText('and'),
      mkBigOp('lim', mkRow([mkSymbol('x'), mkSymbol('\\to'), mkSub(mkRow([mkSymbol('x')]), mkRow([mkSymbol('0')]))]), null),
      mkSymbol('f'),
      mkDelimiter('(', ')', mkRow([mkSymbol('x')])),
      mkSymbol('='),
      mkSymbol('L'),
    ]);
    const result = inferTypeSignature(row);
    expect(result).toBe('{R : Real} -> (a : Carrier R) -> (_ : Limit (\\x => f (x)) x0 L) -> ?');
  });

  test('x₀, L, m ∈ ℝ and f, g : ℝ → ℝ and lim_{x→x₀} f(x) = L', () => {
    const row = mkRow([
      mkSub(mkRow([mkSymbol('x')]), mkRow([mkSymbol('0')])),
      mkSymbol(','), mkSymbol('L'), mkSymbol(','), mkSymbol('m'),
      mkSymbol('\\in'), mkSymbol('\\mathbb{R}'),
      mkText('and'),
      mkSymbol('f'), mkSymbol(','), mkSymbol('g'),
      mkSymbol(':'),
      mkSymbol('\\mathbb{R}'), mkSymbol('\\to'), mkSymbol('\\mathbb{R}'),
      mkText('and'),
      mkBigOp('lim', mkRow([mkSymbol('x'), mkSymbol('\\to'), mkSub(mkRow([mkSymbol('x')]), mkRow([mkSymbol('0')]))]), null),
      mkSymbol('f'),
      mkDelimiter('(', ')', mkRow([mkSymbol('x')])),
      mkSymbol('='),
      mkSymbol('L'),
    ]);
    const result = inferTypeSignature(row);
    expect(result).toBe('{R : Real} -> (x0 L m : Carrier R) -> (f g : Carrier R -> Carrier R) -> (_ : Limit (\\x => f (x)) x0 L) -> ?');
  });

  test('a ∈ ℝ and a = a → anonymous equality hypothesis', () => {
    const row = mkRow([
      mkSymbol('a'), mkSymbol('\\in'), mkSymbol('\\mathbb{R}'),
      mkText('and'),
      mkSymbol('a'), mkSymbol('='), mkSymbol('a'),
    ]);
    expect(inferTypeSignature(row)).toBe('{R : Real} -> (a : Carrier R) -> (_ : Equal a a) -> ?');
  });

  test('incomplete segment with ∈ but no type → skipped gracefully', () => {
    const row = mkRow([
      mkSymbol('a'), mkSymbol('\\in'), mkSymbol('\\mathbb{R}'),
      mkText('and'),
      mkSymbol('b'), mkSymbol('\\in'), // incomplete — skipped
    ]);
    expect(inferTypeSignature(row)).toBe('{R : Real} -> (a : Carrier R) -> ?');
  });
});

// ============================================================================
// Leading token stripping
// ============================================================================

describe('leading token stripping', () => {
  test('Let a ∈ ℝ. Then a = a', () => {
    const row = mkRow([
      mkText('Let'),
      mkSymbol('a'), mkSymbol('\\in'), mkSymbol('\\mathbb{R}'),
      mkSymbol('.'), mkText('Then'),
      mkSymbol('a'), mkSymbol('='), mkSymbol('a'),
    ]);
    expect(inferTypeSignature(row)).toBe('{R : Real} -> (a : Carrier R) -> Equal a a');
  });

  test('If a ∈ ℝ then a = a', () => {
    const row = mkRow([
      mkText('If'),
      mkSymbol('a'), mkSymbol('\\in'), mkSymbol('\\mathbb{R}'),
      mkText('then'),
      mkSymbol('a'), mkSymbol('='), mkSymbol('a'),
    ]);
    expect(inferTypeSignature(row)).toBe('{R : Real} -> (a : Carrier R) -> Equal a a');
  });

  test('Assume a ∈ ℝ, then a = a', () => {
    const row = mkRow([
      mkText('Assume'),
      mkSymbol('a'), mkSymbol('\\in'), mkSymbol('\\mathbb{R}'),
      mkSymbol(','), mkText('then'),
      mkSymbol('a'), mkSymbol('='), mkSymbol('a'),
    ]);
    expect(inferTypeSignature(row)).toBe('{R : Real} -> (a : Carrier R) -> Equal a a');
  });

  test('case-insensitive: let, if, assume', () => {
    const row = mkRow([
      mkText('let'),
      mkSymbol('a'), mkSymbol('\\in'), mkSymbol('\\mathbb{R}'),
    ]);
    expect(inferTypeSignature(row)).toBe('{R : Real} -> (a : Carrier R) -> ?');
  });

  test('leading Let with no bindings → null', () => {
    const row = mkRow([mkText('Let')]);
    expect(inferTypeSignature(row)).toBe(null);
  });

  test('non-leading text is NOT stripped', () => {
    const row = mkRow([
      mkSymbol('a'), mkSymbol('\\in'), mkSymbol('\\mathbb{R}'),
      mkText('and'),
      mkSymbol('b'), mkSymbol('\\in'), mkSymbol('\\mathbb{R}'),
    ]);
    // "and" splits into two separate binding groups — not stripped
    expect(inferTypeSignature(row)).toBe('{R : Real} -> (a : Carrier R) -> (b : Carrier R) -> ?');
  });
});

// ============================================================================
// Quantifier stripping (∀ / forall / for all)
// ============================================================================

describe('quantifier stripping', () => {
  test('∀ n ∈ ℕ → (n : Nat) -> ?', () => {
    const row = mkRow([
      mkSymbol('\\forall'), mkSymbol('n'), mkSymbol('\\in'), mkSymbol('\\mathbb{N}'),
    ]);
    expect(inferTypeSignature(row)).toBe('(n : Nat) -> ?');
  });

  test('∀ n ∈ ℕ, then n ≥ 0 → with body', () => {
    const row = mkRow([
      mkSymbol('\\forall'), mkSymbol('n'), mkSymbol('\\in'), mkSymbol('\\mathbb{N}'),
      mkSymbol(','), mkText('then'),
      mkSymbol('n'), mkSymbol('\\geq'), mkSymbol('0'),
    ]);
    // ≥ not in default registry → falls through to literal
    expect(inferTypeSignature(row)).toContain('(n : Nat) ->');
  });

  test('Let ∀ a ∈ ℝ. Then a = a → preamble + quantifier combo', () => {
    const row = mkRow([
      mkText('Let'),
      mkSymbol('\\forall'), mkSymbol('a'), mkSymbol('\\in'), mkSymbol('\\mathbb{R}'),
      mkSymbol('.'), mkText('Then'),
      mkSymbol('a'), mkSymbol('='), mkSymbol('a'),
    ]);
    expect(inferTypeSignature(row)).toBe('{R : Real} -> (a : Carrier R) -> Equal a a');
  });

  test('a ∈ ℝ and ∀ b ∈ ℝ → quantifier on second segment only', () => {
    const row = mkRow([
      mkSymbol('a'), mkSymbol('\\in'), mkSymbol('\\mathbb{R}'),
      mkText('and'),
      mkSymbol('\\forall'), mkSymbol('b'), mkSymbol('\\in'), mkSymbol('\\mathbb{R}'),
    ]);
    expect(inferTypeSignature(row)).toBe('{R : Real} -> (a : Carrier R) -> (b : Carrier R) -> ?');
  });

  test('Text "forall" n ∈ ℕ → stripped (case-insensitive)', () => {
    const row = mkRow([
      mkText('forall'), mkSymbol('n'), mkSymbol('\\in'), mkSymbol('\\mathbb{N}'),
    ]);
    expect(inferTypeSignature(row)).toBe('(n : Nat) -> ?');
  });

  test('Text "Forall" n ∈ ℕ → stripped (case-insensitive)', () => {
    const row = mkRow([
      mkText('Forall'), mkSymbol('n'), mkSymbol('\\in'), mkSymbol('\\mathbb{N}'),
    ]);
    expect(inferTypeSignature(row)).toBe('(n : Nat) -> ?');
  });

  test('Text "for" "all" n ∈ ℕ → two-word quantifier stripped', () => {
    const row = mkRow([
      mkText('for'), mkText('all'), mkSymbol('n'), mkSymbol('\\in'), mkSymbol('\\mathbb{N}'),
    ]);
    expect(inferTypeSignature(row)).toBe('(n : Nat) -> ?');
  });

  test('∀ a + b = 0 → quantifier on anonymous hypothesis', () => {
    const row = mkRow([
      mkSymbol('a'), mkSymbol('\\in'), mkSymbol('\\mathbb{R}'),
      mkText('and'),
      mkSymbol('\\forall'), mkSymbol('a'), mkSymbol('+'), mkSymbol('b'), mkSymbol('='), mkSymbol('0'),
    ]);
    // Second segment: ∀ stripped, "a + b = 0" becomes anonymous hypothesis
    expect(inferTypeSignature(row)).toBe('{R : Real} -> (a : Carrier R) -> (_ : Equal (radd a b) 0) -> ?');
  });
});
