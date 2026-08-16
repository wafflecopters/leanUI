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

  test('findFirstHole descends into a have proof subtree (hoisted obligation)', async () => {
    const { findFirstHole } = await import('../proof-tree/tactic-to-tree');
    resetProofIds();
    const tree = leanTacticsToTree(
      ['have h1 : 0 < e := by', '  sorry', 'have h := f h1', 'sorry'].join('\n'),
    ) as any;
    // The FIRST hole in proof order is inside h1's by-block, not the trailing one.
    const hole = findFirstHole(tree)!;
    expect(hole.id).toBe(tree.proofTree.id);
  });

  // REGRESSION: `apply <lemma>` used to accept only a single continuation, so a
  // multi-premise apply's branches parsed back as stray `exact ·` steps — the
  // proof structure was destroyed by every save/reload cycle.
  test('apply branches parse as subgoals, not as `exact ·` steps', () => {
    const tree = leanTacticsToTree('apply divPos\n·\n  exact h1\n·\n  exact h2');
    expect(tree.tag).toBe('apply');
    const apply = tree as { tag: 'apply'; children: readonly { tag: string }[] };
    expect(apply.children).toHaveLength(2);
    expect(apply.children.every((c) => c.tag === 'exact')).toBe(true);
  });

  test('case-tagged apply branches keep their goal names', () => {
    const tree = leanTacticsToTree('apply divPos\ncase ha =>\n  sorry\ncase hb =>\n  sorry');
    expect((tree as { childTags?: string[] }).childTags).toEqual(['ha', 'hb']);
  });

  // REGRESSION: the Compute suggestion emits `conv in (pat) => simp`, which
  // fell through to the raw-exact fallback — a TERMINAL node. The hole it
  // replaced vanished, so the goal chain stopped dead after the step instead
  // of continuing to the rewritten goal (e.g. `0 < 1` after `0 < 2 + -1`).
  test('conv-scoped simp is a chaining simp step, not a terminal exact', () => {
    resetProofIds();
    const tree = leanTacticsToTree('conv in (2 + -1) => simp') as any;
    expect(tree.tag).toBe('simp');
    expect(tree.convPattern).toBe('2 + -1');
    expect(tree.child.tag).toBe('hole');
  });

  test('conv-scoped simp keeps its continuation and lemma list', () => {
    resetProofIds();
    const tree = leanTacticsToTree('  conv in (f x) => simp only [foo, bar]\n  exact h') as any;
    expect(tree.tag).toBe('simp');
    expect(tree.convPattern).toBe('f x');
    expect(tree.only).toBe(true);
    expect(tree.lemmas).toEqual(['foo', 'bar']);
    expect(tree.child.tag).toBe('exact');
  });

  // REGRESSION: a term-proved have with a TYPE ANNOTATION printed back as the
  // weaker inferred form (`have h2 := e`), silently rewriting the user's proof —
  // and a seeded preset proof — on its first round-trip. The annotation states
  // what the step establishes, which is the reason for writing it that way.
  test('a typed have keeps its annotation when the proof is a term', () => {
    resetProofIds();
    const src = '  have h2 : 0 < \u03b5 / 2 := divTwoPos \u03b5 epsPos\n  sorry';
    expect(roundTrip(src)).toBe(src);
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
      ['conv-scoped simp', '  conv in (2 + -1) => simp\n  sorry'],
      ['typed have with a term proof', '  have h : 0 < e := divTwoPos e hp\n  sorry'],
      [
        'the seeded limitAdd prefix (nested cases under a have)',
        [
          '  constructor',
          '  intro \u03b5 epsPos',
          '  have h2 : 0 < \u03b5 / 2 := divTwoPos \u03b5 epsPos',
          '  have hF := limF.eps_delta (\u03b5 / 2) h2',
          '  cases hF with',
          '  | mk deltaF fProof =>',
          '    have hG := limG.eps_delta (\u03b5 / 2) h2',
          '    cases hG with',
          '    | mk deltaG gProof =>',
          '      sorry',
        ].join('\n'),
      ],
      ['conv-scoped simp only with lemmas', '  conv in (f x) => simp only [foo]\n  sorry'],
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
      ['apply with a single continuation', '  apply divTwoPos\n  sorry'],
      [
        'apply with two subgoal bullets (a multi-premise lemma)',
        ['  apply divPos', '  ·', '    sorry', '  ·', '    sorry'].join('\n'),
      ],
      [
        'apply with case-tagged subgoals',
        ['  apply divPos', '  case ha =>', '    sorry', '  case hb =>', '    sorry'].join('\n'),
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

describe('wrapped tactics are ONE tactic', () => {
  test('a have whose term is on the next line keeps its proof', () => {
    // Lean's own style breaks a long `have h : T :=` before the term. Treating
    // the term as its own tactic line dropped the proof AND swallowed every
    // later tactic into the resulting hole: quotMulDescends read as unproved
    // in the editor while Lean considered it fine.
    const tree = leanTacticsToTree([
      'unfold CosetEq',
      'have hprod : G.mul a b ∈ N.members :=',
      '  N.mulMem _ hconj _ hcd',
      'rw [quotRegroup]',
      'exact hprod',
    ].join('\n'));
    const printed = proofTreeToSource(tree);
    expect(printed).toContain('N.mulMem _ hconj _ hcd');
    expect(printed).not.toContain('sorry');
    expect(printed).toContain('exact hprod');
  });

  test('an unbalanced bracket also continues the line', () => {
    const tree = leanTacticsToTree([
      'exact foo (bar',
      '  baz)',
      'exact done',
    ].join('\n'));
    const printed = proofTreeToSource(tree);
    expect(printed).toContain('foo (bar baz)');
    expect(printed).not.toContain('sorry');
  });

  test('`have … := by` is NOT a continuation — its body stays an indented block', () => {
    const tree = leanTacticsToTree([
      'have h : A = B := by',
      '  rfl',
      'exact h',
    ].join('\n'));
    const printed = proofTreeToSource(tree);
    expect(printed).toContain(':= by');
    expect(printed).toContain('rfl');
    expect(printed).toContain('exact h');
  });
});

describe('a deeper-indented line continues the tactic unless a block opened', () => {
  test('a multi-line show is ONE tactic', () => {
    const tree = leanTacticsToTree([
      'show rsub (rmul a b)',
      '    (rsub c d)',
      '  = rsub e f',
      'exact h',
    ].join('\n'));
    const printed = proofTreeToSource(tree);
    expect(printed).toContain('rsub e f');
    expect(printed).not.toContain('sorry');
  });

  test('a case block\'s body is NOT swallowed into its header', () => {
    const tree = leanTacticsToTree([
      'induction n with',
      '| zero =>',
      '  rfl',
      '| succ k ih =>',
      '  exact ih',
    ].join('\n'));
    const printed = proofTreeToSource(tree);
    expect(printed).toContain('rfl');
    expect(printed).toContain('exact ih');
    expect(printed).not.toContain('=> rfl');
  });

  test('a bullet body stays separate from the bullet', () => {
    const tree = leanTacticsToTree([
      'constructor',
      '· exact a',
      '· exact b',
    ].join('\n'));
    const printed = proofTreeToSource(tree);
    expect(printed).toContain('exact a');
    expect(printed).toContain('exact b');
  });
});

describe('comments are not tactics', () => {
  test('a full-line comment does not swallow the proof beneath it', () => {
    // This was severe: the comment fell into the terminal unrecognized-tactic
    // fallback, so the whole proof reprinted as nothing but the comment.
    const tree = leanTacticsToTree([
      '-- the expansion, written out',
      'intro x',
      'exact h',
    ].join('\n'));
    const printed = proofTreeToSource(tree);
    expect(printed).toContain('intro x');
    expect(printed).toContain('exact h');
    expect(printed).not.toContain('--');
  });

  test('a trailing comment is stripped from its tactic', () => {
    const tree = leanTacticsToTree('exact h -- because of the above');
    const printed = proofTreeToSource(tree);
    expect(printed).toContain('exact h');
    expect(printed).not.toContain('because');
  });

  test('a block comment, on one line and across lines', () => {
    const one = proofTreeToSource(leanTacticsToTree('/- aside -/ intro x\nexact h'));
    expect(one).toContain('intro x');
    expect(one).toContain('exact h');
    const many = proofTreeToSource(leanTacticsToTree(
      ['intro x', '/- a long', '   aside -/', 'exact h'].join('\n')));
    expect(many).toContain('intro x');
    expect(many).toContain('exact h');
    expect(many).not.toContain('aside');
  });

  test('a double dash inside a string is not a comment', () => {
    const tree = leanTacticsToTree('exact foo "a--b"');
    expect(proofTreeToSource(tree)).toContain('a--b');
  });
});

describe('let names an expression', () => {
  test('a let round-trips as a let, not as a have', () => {
    // `have` is opaque; `let` keeps the body, which is what makes the name
    // usable with lemmas about the expression it abbreviates.
    const tree = leanTacticsToTree(['let delta := min(a, b)', 'exact delta'].join('\n'));
    const printed = proofTreeToSource(tree);
    expect(printed).toContain('let delta := min(a, b)');
    expect(printed).not.toContain('have delta');
    expect(printed).toContain('exact delta');
  });

  test('a typed let keeps its annotation', () => {
    const tree = leanTacticsToTree('let d : Real := min(a, b)\nexact d');
    expect(proofTreeToSource(tree)).toContain('let d : Real := min(a, b)');
  });

  test('a have is still a have', () => {
    const tree = leanTacticsToTree('have h : 0 < e := pos\nexact h');
    const printed = proofTreeToSource(tree);
    expect(printed).toContain('have h : 0 < e := pos');
    expect(printed).not.toContain('let ');
  });
});

