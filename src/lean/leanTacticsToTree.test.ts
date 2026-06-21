import { describe, expect, test } from 'vitest';
import { leanTacticsToTree } from './leanTacticsToTree';
import { proofTreeToLean, proofTreeToSource } from './proofTreeToLean';
import { resetProofIds } from '../proof-tree/proof-tree';

/** Parse a block, re-print it, and return the normalized printed source. */
function roundTrip(block: string): string {
  resetProofIds();
  const tree = leanTacticsToTree(block);
  return proofTreeToLean(tree).source;
}

describe('leanTacticsToTree', () => {
  test('empty block → single hole', () => {
    resetProofIds();
    const tree = leanTacticsToTree('');
    expect(tree.tag).toBe('hole');
  });

  test('intro + exact', () => {
    resetProofIds();
    const tree = leanTacticsToTree('  intro n\n  exact rfl');
    expect(tree.tag).toBe('intros');
    expect((tree as any).names).toEqual(['n']);
    expect((tree as any).child.tag).toBe('exact');
  });

  test('rw forward and reverse', () => {
    resetProofIds();
    expect((leanTacticsToTree('  rw [foo]') as any).tag).toBe('rewrite');
    expect((leanTacticsToTree('  rw [foo]') as any).reverse).toBe(false);
    expect((leanTacticsToTree('  rw [← foo]') as any).reverse).toBe(true);
  });

  test('rw with multiple lemmas becomes a chain of rewrites (none dropped)', () => {
    resetProofIds();
    const tree = leanTacticsToTree('  rw [a, ← b, c]') as any;
    expect(tree.tag).toBe('rewrite');
    expect(tree.name).toBe('a');
    expect(tree.reverse).toBe(false);
    expect(tree.child.tag).toBe('rewrite');
    expect(tree.child.name).toBe('b');
    expect(tree.child.reverse).toBe(true);
    expect(tree.child.child.tag).toBe('rewrite');
    expect(tree.child.child.name).toBe('c');
  });

  test('simp with and without lemmas', () => {
    resetProofIds();
    expect((leanTacticsToTree('  simp') as any).lemmas).toEqual([]);
    expect((leanTacticsToTree('  simp [a, b]') as any).lemmas).toEqual(['a', 'b']);
  });

  test('sorry → hole', () => {
    resetProofIds();
    expect(leanTacticsToTree('  sorry').tag).toBe('hole');
  });

  test('induction with cases', () => {
    resetProofIds();
    const block = ['induction n with', '| zero => exact rfl', '| succ k ih =>', '  simp'].join('\n');
    const tree = leanTacticsToTree(block);
    expect(tree.tag).toBe('induction');
    const ind = tree as any;
    expect(ind.scrutinee).toBe('n');
    expect(ind.cases).toHaveLength(2);
    expect(ind.cases[0].constructorName).toBe('zero');
    expect(ind.cases[1].constructorName).toBe('succ');
    expect(ind.cases[1].constructorParamNames).toEqual(['k', 'ih']);
  });

  test('bare induction with · bullet cases (no constructor names known)', () => {
    resetProofIds();
    const block = ['induction n', '·', '  simp', '·', '  exact rfl'].join('\n');
    const tree = leanTacticsToTree(block) as any;
    expect(tree.tag).toBe('induction');
    expect(tree.scrutinee).toBe('n');
    expect(tree.cases).toHaveLength(2);
    // No real constructor names → printer must emit valid bullet Lean, NOT `| label =>`
    // (source printer omits chaining tactics' fabricated trailing sorry).
    expect(proofTreeToSource(tree, 1)).toBe(
      ['  induction n', '  ·', '    simp', '  ·', '    exact rfl'].join('\n'),
    );
  });

  test('unrecognized tactic is preserved as exact (nothing dropped)', () => {
    resetProofIds();
    const tree = leanTacticsToTree('  omega');
    expect(tree.tag).toBe('exact');
    expect((tree as any).expr).toBe('omega');
  });

  // Round-trip stability: printing a parsed tree reproduces the canonical form.
  describe('parse → print round-trip is stable', () => {
    const cases: Array<[string, string]> = [
      ['intro/exact', '  intro a b\n  exact h'],
      ['rw chain', '  rw [foo]\n  rw [← bar]\n  sorry'],
      ['simp', '  simp [x, y]\n  sorry'],
      [
        'induction',
        ['  induction n with', '  | zero =>', '    exact rfl', '  | succ k ih =>', '    simp'].join('\n'),
      ],
      ['conv-scoped rewrite', '  conv in (a.succ + 1) => rw [plusComm]\n  sorry'],
      ['conv-scoped reverse rewrite', '  conv in (sum i n f) => rw [← summationSplit]\n  sorry'],
    ];
    for (const [name, src] of cases) {
      test(name, () => {
        // Re-printing the parse of a printed form is idempotent.
        const once = roundTrip(src);
        const twice = roundTrip(once);
        expect(twice).toBe(once);
      });
    }
  });
});
