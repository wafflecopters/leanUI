import { describe, expect, test } from 'vitest';
import { extractTacticBlock, proofSeedBlock } from './extractTacticBlock';
import type { LeanDeclaration } from './types';

const decl = (line: number, kind: LeanDeclaration['kind'] = 'theorem'): LeanDeclaration => ({
  name: 't',
  kind,
  prettyType: '',
  line,
  col: 0,
});

describe('extractTacticBlock', () => {
  test('extracts a multi-line by block', () => {
    const src = [
      'theorem t (a b : Nat) : a + b = b + a := by',
      '  induction a with',
      '  | zero => simp',
      '  | succ k ih => rw [Nat.succ_add, ih, Nat.add_succ]',
    ].join('\n');
    const block = extractTacticBlock(src, decl(1), undefined);
    expect(block).toBe(
      ['  induction a with', '  | zero => simp', '  | succ k ih => rw [Nat.succ_add, ih, Nat.add_succ]'].join('\n'),
    );
  });

  test('stops at the next declaration', () => {
    const src = [
      'theorem a : True := by',
      '  trivial',
      'theorem b : True := by',
      '  trivial',
    ].join('\n');
    const block = extractTacticBlock(src, decl(1), 3);
    expect(block).toBe('  trivial');
  });

  test('returns null for term-mode def (no by)', () => {
    const src = 'def x : Nat := 42';
    expect(extractTacticBlock(src, decl(1, 'def'), undefined)).toBeNull();
  });

  test('handles inline single-line by proof', () => {
    const src = 'theorem t : n = n := by rfl';
    expect(extractTacticBlock(src, decl(1), undefined)).toBe('rfl');
  });

  test('returns null when block is empty', () => {
    const src = 'theorem t : True := by\n';
    expect(extractTacticBlock(src, decl(1), undefined)).toBeNull();
  });
});

describe('proofSeedBlock', () => {
  test('uses the by-block when present', () => {
    const src = 'theorem t : a = b := by\n  rw [h]';
    expect(proofSeedBlock(src, decl(1, 'theorem'), undefined)).toBe('  rw [h]');
  });

  test('theorem with a term body seeds sorry (build a proof)', () => {
    const src = 'theorem t : a = b := myProof';
    expect(proofSeedBlock(src, decl(1, 'theorem'), undefined)).toBe('sorry');
  });

  test('def := sorry seeds sorry (wants a proof)', () => {
    const src = 'def t : a = b := sorry';
    expect(proofSeedBlock(src, decl(1, 'def'), undefined)).toBe('sorry');
  });

  test('computational def := <term> (no sorry) → null (value editor)', () => {
    const src = 'def double (n : Nat) : Nat := n + n';
    expect(proofSeedBlock(src, decl(1, 'def'), undefined)).toBeNull();
  });

  test('inductive → null', () => {
    const src = 'inductive Foo where | bar';
    expect(proofSeedBlock(src, decl(1, 'inductive'), undefined)).toBeNull();
  });
});
