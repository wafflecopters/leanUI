import { describe, expect, test } from 'vitest';
import { proofTreeToLean, proofTreeToSource } from './proofTreeToLean';
import {
  mkHole,
  mkIntros,
  mkExact,
  mkUnfold,
  mkRewrite,
  mkSimp,
  mkApply,
  mkHave,
  mkSuffices,
  mkInduction,
  mkCase,
  resetProofIds,
} from '../proof-tree/proof-tree';

describe('proofTreeToLean', () => {
  test('a bare hole becomes sorry and is tracked', () => {
    resetProofIds();
    const h = mkHole();
    const out = proofTreeToLean(h);
    expect(out.source).toBe('  sorry');
    expect(out.holeNodeIds.has(h.id)).toBe(true);
    expect(out.nodeRanges.get(h.id)).toMatchObject({ startLine: 1, startCol: 2 });
  });

  test('intros → intro with names, then child', () => {
    resetProofIds();
    const tree = mkIntros(['a', 'b'], mkExact('Nat.add_comm a b'));
    const out = proofTreeToLean(tree);
    expect(out.source).toBe('  intro a b\n  exact Nat.add_comm a b');
  });

  test('empty intro names degrade to _', () => {
    resetProofIds();
    expect(proofTreeToLean(mkIntros([], mkHole())).source).toBe('  intro _\n  sorry');
  });

  test('rewrite forward and reverse', () => {
    resetProofIds();
    expect(proofTreeToLean(mkRewrite('foo', mkHole())).source).toBe('  rw [foo]\n  sorry');
    expect(proofTreeToLean(mkRewrite('foo', mkHole(), true)).source).toBe('  rw [← foo]\n  sorry');
  });

  test('unfold then continuation', () => {
    resetProofIds();
    expect(proofTreeToLean(mkUnfold('double', mkExact('rfl'))).source).toBe('  unfold double\n  exact rfl');
  });

  test('simp with and without lemmas', () => {
    resetProofIds();
    expect(proofTreeToLean(mkSimp([], [], mkHole())).source).toBe('  simp\n  sorry');
    expect(proofTreeToLean(mkSimp(['a', 'b'], [], mkHole())).source).toBe('  simp [a, b]\n  sorry');
  });

  // A multi-premise `apply` opens BRANCHES, and branches print as bullets —
  // the same form `constructor` uses. Printed flat (`apply foo` / `exact h1` /
  // `exact h2`) the structure is gone: a flat tactic sequence cannot say "these
  // two chains prove two different goals", so re-parsing collapses them.
  test('apply with two subgoal children prints them as bullets', () => {
    resetProofIds();
    const tree = mkApply('foo', [mkExact('h1'), mkExact('h2')]);
    const out = proofTreeToLean(tree);
    expect(out.source).toBe('  apply foo\n  ·\n    exact h1\n  ·\n    exact h2');
  });

  test('apply with named subgoals prints `case <tag> =>` blocks', () => {
    resetProofIds();
    const tree = mkApply('divPos', [mkHole(), mkHole()], false, ['ha', 'hb']);
    expect(proofTreeToLean(tree).source).toBe(
      '  apply divPos\n  case ha =>\n    sorry\n  case hb =>\n    sorry',
    );
  });

  test('a single-child apply still chains (the common case)', () => {
    resetProofIds();
    expect(proofTreeToLean(mkApply('foo', [mkExact('h1')])).source).toBe('  apply foo\n  exact h1');
  });

  test('have flat expression', () => {
    resetProofIds();
    const tree = mkHave('h', 'Nat.le_refl n', mkExact('h'));
    expect(proofTreeToLean(tree).source).toBe('  have h := Nat.le_refl n\n  exact h');
  });

  test('have with interactive subtree → have : T := by <subtree>', () => {
    resetProofIds();
    const tree = mkHave('h', '', mkExact('h'), 'n = n', mkExact('rfl'));
    const out = proofTreeToLean(tree);
    expect(out.source).toBe('  have h : n = n := by\n    exact rfl\n  exact h');
  });

  test('suffices with by-proof and continuation', () => {
    resetProofIds();
    const tree = mkSuffices('h', 'P n', mkExact('done'), mkExact('from_h'));
    expect(proofTreeToLean(tree).source).toBe('  suffices h : P n by\n    exact from_h\n  exact done');
  });

  test('induction with zero/succ cases produces a with-block', () => {
    resetProofIds();
    const zero = mkCase('zero', mkExact('rfl'), 'zero', []);
    const succ = mkCase('succ', mkExact('by simp'), 'succ', ['k', 'ih']);
    const tree = mkIntros(['n'], mkInduction('n', [zero, succ]));
    const out = proofTreeToLean(tree);
    expect(out.source).toBe(
      [
        '  intro n',
        '  induction n with',
        '  | zero =>',
        '    exact rfl',
        '  | succ k ih =>',
        '    exact by simp',
      ].join('\n'),
    );
  });

  test('cases tactic uses `cases` keyword', () => {
    resetProofIds();
    const tree = mkInduction('x', [mkCase('a', mkHole(), 'a', [])], true);
    expect(proofTreeToLean(tree).source.startsWith('  cases x with')).toBe(true);
  });

  test('node ranges are absolute when baseLine is given', () => {
    resetProofIds();
    const inner = mkExact('rfl');
    const tree = mkIntros(['n'], inner);
    const out = proofTreeToLean(tree, /* baseLine */ 10, /* baseDepth */ 1);
    // first tactic sits on line 10, the exact on line 11
    expect(out.nodeRanges.get(tree.id)!.startLine).toBe(10);
    expect(out.nodeRanges.get(inner.id)!.startLine).toBe(11);
  });

  describe('proofTreeToSource (write-back)', () => {
    test('omits a chaining tactic’s fabricated trailing hole', () => {
      resetProofIds();
      // `simp` then a hole continuation → for analysis prints `simp\n  sorry`,
      // but for source it should be just `simp`.
      const tree = mkSimp(['x'], [], mkHole());
      expect(proofTreeToLean(tree).source).toBe('  simp [x]\n  sorry');
      expect(proofTreeToSource(tree, 1)).toBe('  simp [x]');
    });

    test('keeps a standalone hole as sorry', () => {
      resetProofIds();
      expect(proofTreeToSource(mkHole(), 1)).toBe('  sorry');
    });

    test('omits trailing hole inside an induction case body', () => {
      resetProofIds();
      const zero = mkCase('zero', mkSimp([], [], mkHole()), 'zero', []);
      const tree = mkInduction('n', [zero]);
      expect(proofTreeToSource(tree, 1)).toBe('  induction n with\n  | zero =>\n    simp');
    });
  });

  test('every emitted node has a recorded range', () => {
    resetProofIds();
    const zero = mkCase('zero', mkExact('rfl'), 'zero', []);
    const tree = mkIntros(['n'], mkInduction('n', [zero]));
    const out = proofTreeToLean(tree);
    // intros, induction, case, exact → 4 ranges
    expect(out.nodeRanges.size).toBe(4);
  });
});
