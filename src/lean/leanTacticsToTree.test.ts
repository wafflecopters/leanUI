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
    // The ctor arg and the induction hypothesis are kept apart.
    expect(ind.cases[1].constructorParamNames).toEqual(['k']);
    expect(ind.cases[1].ihNames).toEqual(['ih']);
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

  test('constructor parses as a CHAINING raw apply (opened field gets a hole)', () => {
    resetProofIds();
    const tree = leanTacticsToTree('constructor') as any;
    expect(tree.tag).toBe('apply');
    expect(tree.raw).toBe(true);
    expect(tree.name).toBe('constructor');
    expect(tree.children).toHaveLength(1);
    expect(tree.children[0].tag).toBe('hole');
  });

  test('constructor with case blocks parses tags + children (order preserved)', () => {
    resetProofIds();
    const tree = leanTacticsToTree(
      ['constructor', 'case fst =>', '  exact d', 'case snd =>', '  sorry'].join('\n'),
    ) as any;
    expect(tree.tag).toBe('apply');
    expect(tree.childTags).toEqual(['fst', 'snd']);
    expect(tree.children[0].tag).toBe('exact');
    expect(tree.children[1].tag).toBe('hole');
  });

  test('constructor with bullet branches parses them as its subgoals', () => {
    resetProofIds();
    const tree = leanTacticsToTree(['constructor', '·', '  intro d', '·', '  sorry'].join('\n')) as any;
    expect(tree.tag).toBe('apply');
    expect(tree.raw).toBe(true);
    expect(tree.children).toHaveLength(2);
    expect(tree.children[0].tag).toBe('intros');
    expect(tree.children[1].tag).toBe('hole');
  });

  test('constructor followed by a tactic chains it as the subgoal proof', () => {
    resetProofIds();
    const tree = leanTacticsToTree('constructor\nintro eps heps') as any;
    expect(tree.tag).toBe('apply');
    expect(tree.children[0].tag).toBe('intros');
  });

  test('conditional rewrite parses into main child + side goals', () => {
    resetProofIds();
    const tree = leanTacticsToTree(
      ['  rw [summationSplit]', '  ·', '    simp', '  ·', '    exact .LeqZero'].join('\n'),
    ) as any;
    expect(tree.tag).toBe('rewrite');
    expect(tree.name).toBe('summationSplit');
    expect(tree.child.tag).toBe('simp'); // first bullet = rewritten (main) goal
    expect(tree.sideGoals).toHaveLength(1); // second bullet = side goal
    expect(tree.sideGoals[0].tag).toBe('exact');
  });

  test('single bullet after rw is NOT treated as a side-goal branch', () => {
    resetProofIds();
    // Only ≥2 bullets form the conditional shape; a lone bullet stays a plain rw.
    const tree = leanTacticsToTree('  rw [foo]\n  sorry') as any;
    expect(tree.tag).toBe('rewrite');
    expect(tree.sideGoals).toBeUndefined();
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
      ['simp only', '  simp only [plusComm, mulComm]\n  sorry'],
      ['terminal tactic (omega)', '  omega'],
      ['terminal tactic (rfl)', '  rfl'],
      ['constructor with continuation', '  constructor\n  sorry'],
      [
        'constructor with two subgoal bullets (DPair: body + witness)',
        ['  constructor', '  ·', '    sorry', '  ·', '    sorry'].join('\n'),
      ],
      [
        'constructor with case-tagged subgoals (witness-first order)',
        ['  constructor', '  case fst =>', '    sorry', '  case snd =>', '    sorry'].join('\n'),
      ],
      ['unrecognized tactic prints verbatim (not exact)', '  refine leqAntisym ?_ ?_'],
      [
        'conditional rewrite (side goal as bullet branches)',
        ['  rw [summationSplit]', '  ·', '    rw [foo]', '    simp', '  ·', '    exact .LeqZero'].join('\n'),
      ],
      [
        'conditional rewrite with two side goals',
        ['  rw [lem]', '  ·', '    sorry', '  ·', '    exact h1', '  ·', '    exact h2'].join('\n'),
      ],
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
