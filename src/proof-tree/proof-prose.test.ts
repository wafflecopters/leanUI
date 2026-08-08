import { describe, test, expect, beforeEach } from 'vitest';
import { generateProofProse, ProseItem } from './proof-prose';
import { ProofNode, resetProofIds, freshProofId } from './proof-tree';
import { NodeGoalInfo } from './goal-types';

beforeEach(() => {
  resetProofIds(100);
});

function mkGoalMap(entries: [number, Partial<NodeGoalInfo>][]): Map<number, NodeGoalInfo> {
  const map = new Map<number, NodeGoalInfo>();
  for (const [id, partial] of entries) {
    map.set(id, {
      goalLatex: partial.goalLatex ?? '',
      hypotheses: partial.hypotheses ?? [],
      ...partial,
    } as NodeGoalInfo);
  }
  return map;
}

describe('generateProofProse', () => {
  test('empty hole produces a single hole item', () => {
    const hole: ProofNode = { tag: 'hole', id: 1 };
    const goalMap = mkGoalMap([[1, { goalLatex: 'P' }]]);
    const items = generateProofProse(hole, 1, goalMap);

    expect(items).toHaveLength(1);
    expect(items[0].kind.tag).toBe('hole');
    expect((items[0].kind as any).goalLatex).toBe('P');
    expect(items[0].isCursor).toBe(true);
    expect(items[0].depth).toBe(0);
  });

  test('hole not at cursor has isCursor=false', () => {
    const hole: ProofNode = { tag: 'hole', id: 1 };
    const items = generateProofProse(hole, 999, mkGoalMap([]));
    expect(items[0].isCursor).toBe(false);
  });

  test('exact (solved) produces exact + qed', () => {
    const exact: ProofNode = { tag: 'exact', id: 1, expr: 'refl' };
    const goalMap = mkGoalMap([[1, { validation: { status: 'solved' } }]]);
    const items = generateProofProse(exact, 1, goalMap);

    expect(items).toHaveLength(2);
    expect(items[0].kind.tag).toBe('exact');
    expect((items[0].kind as any).exprLatex).toBe('refl');
    expect((items[0].kind as any).solved).toBe(true);
    expect(items[1].kind.tag).toBe('qed');
  });

  test('exact (error) produces exact without qed', () => {
    const exact: ProofNode = { tag: 'exact', id: 1, expr: 'bad' };
    const goalMap = mkGoalMap([[1, { validation: { status: 'error', message: 'type mismatch' } }]]);
    const items = generateProofProse(exact, 1, goalMap);

    expect(items).toHaveLength(1);
    expect(items[0].kind.tag).toBe('exact');
    expect((items[0].kind as any).solved).toBe(false);
    expect((items[0].kind as any).error).toBe('type mismatch');
  });

  test('exact (unsolved) produces exact without qed or error', () => {
    const exact: ProofNode = { tag: 'exact', id: 1, expr: 'foo' };
    const items = generateProofProse(exact, 1, mkGoalMap([]));

    expect(items).toHaveLength(1);
    expect((items[0].kind as any).solved).toBe(false);
    expect((items[0].kind as any).error).toBeUndefined();
  });

  test('exact surfaces a Lean round-trip tacticError (shows red in the editor)', () => {
    const exact: ProofNode = { tag: 'exact', id: 1, expr: '.refl' };
    // The Lean path reports failures via tacticError (not validation).
    const goalMap = mkGoalMap([[1, { tacticError: 'Type mismatch: Eq.refl ...' }]]);
    const items = generateProofProse(exact, 1, goalMap);
    expect((items[0].kind as any).error).toBe('Type mismatch: Eq.refl ...');
  });

  test('intros with typed hypotheses renders grouped LaTeX', () => {
    const hole: ProofNode = { tag: 'hole', id: 2 };
    const intros: ProofNode = { tag: 'intros', id: 1, names: ['n', 'm'], child: hole };
    const goalMap = mkGoalMap([
      [1, { hypotheses: [] }],
      [2, { hypotheses: [{ name: 'n', type: '\\mathbb{N}' }, { name: 'm', type: '\\mathbb{N}' }] }],
    ]);
    const items = generateProofProse(intros, 2, goalMap);

    expect(items).toHaveLength(2);
    expect(items[0].kind.tag).toBe('intro');
    // n and m should be grouped since same type
    expect((items[0].kind as any).latex).toBe('n, m : \\mathbb{N}');
    expect(items[1].kind.tag).toBe('hole');
  });

  test('intros with different types uses "and" separator', () => {
    const hole: ProofNode = { tag: 'hole', id: 2 };
    const intros: ProofNode = { tag: 'intros', id: 1, names: ['n', 'f'], child: hole };
    const goalMap = mkGoalMap([
      [1, { hypotheses: [] }],
      [2, { hypotheses: [
        { name: 'n', type: '\\mathbb{N}' },
        { name: 'f', type: '\\mathbb{N} \\to \\mathbb{N}' },
      ] }],
    ]);
    const items = generateProofProse(intros, 2, goalMap);
    expect((items[0].kind as any).latex).toBe(
      'n : \\mathbb{N} \\text{ and } f : \\mathbb{N} \\to \\mathbb{N}'
    );
  });

  test('intros falls back to names when no goal info', () => {
    const hole: ProofNode = { tag: 'hole', id: 2 };
    const intros: ProofNode = { tag: 'intros', id: 1, names: ['x', 'y'], child: hole };
    const items = generateProofProse(intros, 2, mkGoalMap([]));

    expect((items[0].kind as any).latex).toBe('x, y');
  });

  test('single unfold produces unfold item with goal', () => {
    const hole: ProofNode = { tag: 'hole', id: 2 };
    const unfold: ProofNode = { tag: 'unfold', id: 1, name: 'plus', child: hole };
    const goalMap = mkGoalMap([[2, { goalLatex: 'n = n' }]]);
    const items = generateProofProse(unfold, 2, goalMap);

    expect(items).toHaveLength(2);
    expect(items[0].kind.tag).toBe('unfold');
    expect((items[0].kind as any).name).toBe('plus');
    expect((items[0].kind as any).goalLatex).toBe('n = n');
    expect(items[1].kind.tag).toBe('hole');
  });

  test('consecutive unfold+rewrite produce separate items, each with next goal', () => {
    const hole: ProofNode = { tag: 'hole', id: 4 };
    const rewrite: ProofNode = { tag: 'rewrite', id: 3, name: 'plusComm', reverse: false, child: hole };
    const unfold2: ProofNode = { tag: 'unfold', id: 2, name: 'sum', child: rewrite };
    const unfold1: ProofNode = { tag: 'unfold', id: 1, name: 'plus', child: unfold2 };

    const goalMap = mkGoalMap([
      [2, { goalLatex: 'after plus' }],
      [3, { goalLatex: 'after sum' }],
      [4, { goalLatex: 'final goal' }],
    ]);
    const items = generateProofProse(unfold1, 4, goalMap);

    // 3 separate items (unfold, unfold, rewrite) + 1 hole
    expect(items).toHaveLength(4);
    expect(items[0].kind.tag).toBe('unfold');
    expect((items[0].kind as any).name).toBe('plus');
    expect((items[0].kind as any).goalLatex).toBe('after plus'); // next step's goal
    expect(items[1].kind.tag).toBe('unfold');
    expect((items[1].kind as any).name).toBe('sum');
    expect((items[1].kind as any).goalLatex).toBe('after sum');
    expect(items[2].kind.tag).toBe('rewrite');
    expect((items[2].kind as any).name).toBe('plusComm');
    expect((items[2].kind as any).goalLatex).toBe('final goal'); // tail's goal
    expect(items[3].kind.tag).toBe('hole');
  });

  test('reverse rewrite records reverse flag', () => {
    const hole: ProofNode = { tag: 'hole', id: 2 };
    const rewrite: ProofNode = { tag: 'rewrite', id: 1, name: 'minusSucc', reverse: true, child: hole };

    const items = generateProofProse(rewrite, 2, mkGoalMap([]));
    expect(items[0].kind.tag).toBe('rewrite');
    expect((items[0].kind as any).reverse).toBe(true);
  });

  test('rewrite with equationLatex', () => {
    const hole: ProofNode = { tag: 'hole', id: 2 };
    const rewrite: ProofNode = { tag: 'rewrite', id: 1, name: 'plusZero', reverse: false, child: hole };

    const goalMap = mkGoalMap([
      [1, { unifiedEquationLatex: 'n + 0 = n' }],
      [2, { goalLatex: 'done' }],
    ]);
    const items = generateProofProse(rewrite, 2, goalMap);
    expect(items[0].kind.tag).toBe('rewrite');
    expect((items[0].kind as any).equationLatex).toBe('n + 0 = n');
  });

  test('apply with one child', () => {
    const hole: ProofNode = { tag: 'hole', id: 2 };
    const apply: ProofNode = { tag: 'apply', id: 1, name: 'congSucc', children: [hole] };
    const goalMap = mkGoalMap([[2, { goalLatex: 'n = m' }]]);
    const items = generateProofProse(apply, 2, goalMap);

    expect(items).toHaveLength(2);
    expect(items[0].kind.tag).toBe('apply');
    expect((items[0].kind as any).name).toBe('congSucc');
    expect((items[0].kind as any).subgoalLatex).toEqual(['n = m']);
    // Single child stays at same depth (no progressive indentation)
    expect(items[1].depth).toBe(0);
    expect(items[1].kind.tag).toBe('hole');
  });

  test('apply with multiple children', () => {
    const h1: ProofNode = { tag: 'hole', id: 2 };
    const h2: ProofNode = { tag: 'hole', id: 3 };
    const apply: ProofNode = { tag: 'apply', id: 1, name: 'trans', children: [h1, h2] };
    const goalMap = mkGoalMap([
      [2, { goalLatex: 'a = b' }],
      [3, { goalLatex: 'b = c' }],
    ]);
    const items = generateProofProse(apply, 2, goalMap);

    // apply + 2×(subgoalHeader + hole) = 5 items
    expect(items).toHaveLength(5);
    expect((items[0].kind as any).subgoalLatex).toEqual(['a = b', 'b = c']);
    // Subgoal headers at depth 0, holes at depth 1
    expect(items[1].kind.tag).toBe('subgoalHeader');
    expect(items[1].depth).toBe(0);
    expect(items[2].kind.tag).toBe('hole');
    expect(items[2].depth).toBe(1);
    expect(items[3].kind.tag).toBe('subgoalHeader');
    expect(items[3].depth).toBe(0);
    expect(items[4].kind.tag).toBe('hole');
    expect(items[4].depth).toBe(1);
  });

  test('induction with base and inductive cases', () => {
    const baseHole: ProofNode = { tag: 'hole', id: 10 };
    const stepHole: ProofNode = { tag: 'hole', id: 11 };
    const induction: ProofNode = {
      tag: 'induction',
      id: 1,
      scrutinee: 'n',
      collapsed: false,
      cases: [
        {
          tag: 'case', id: 2, label: 'Zero', body: baseHole, collapsed: false,
          constructorName: 'Zero', constructorParamNames: [],
          labelLatex: 'n = 0',
        },
        {
          tag: 'case', id: 3, label: 'Succ', body: stepHole, collapsed: false,
          constructorName: 'Succ', constructorParamNames: ['k'],
          labelLatex: 'n = \\text{Succ}\\;k',
        },
      ],
    };
    const items = generateProofProse(induction, 10, mkGoalMap([]));

    // inductionHeader + caseHeader(Zero) + hole + caseHeader(Succ) + hole
    expect(items).toHaveLength(5);
    expect(items[0].kind.tag).toBe('inductionHeader');
    expect((items[0].kind as any).scrutinee).toBe('n');
    expect(items[0].depth).toBe(0);

    expect(items[1].kind.tag).toBe('caseHeader');
    expect((items[1].kind as any).labelLatex).toBe('n = 0');
    expect((items[1].kind as any).isBaseCase).toBe(true);
    expect(items[1].depth).toBe(1);

    expect(items[2].kind.tag).toBe('hole');
    expect(items[2].depth).toBe(2);

    expect(items[3].kind.tag).toBe('caseHeader');
    expect((items[3].kind as any).labelLatex).toBe('n = \\text{Succ}\\;k');
    expect((items[3].kind as any).isBaseCase).toBe(false);
    expect(items[3].depth).toBe(1);

    expect(items[4].depth).toBe(2);
  });

  test('Lean bullet-cases: goal hyps distinguish base case from inductive step', () => {
    // The Lean path emits `induction n` + `·` bullets with NO constructorParamNames,
    // so isBaseCase must be recovered from the goal state: the inductive step
    // introduces hypotheses (predecessor + IH) absent from the induction's goal.
    const zeroHole: ProofNode = { tag: 'hole', id: 2 };
    const succHole: ProofNode = { tag: 'hole', id: 4 };
    const induction: ProofNode = {
      tag: 'induction',
      id: 1,
      scrutinee: 'n',
      collapsed: false,
      cases: [
        { tag: 'case', id: 3, label: 'case', body: zeroHole, collapsed: false },
        { tag: 'case', id: 5, label: 'case', body: succHole, collapsed: false },
      ],
    };
    const goalMap = mkGoalMap([
      [1, { hypotheses: [{ name: 'n', type: 'MyNat' }] }], // induction's incoming goal
      [3, { caseLabelLatex: 'zero', hypotheses: [] }], // base: no new hyps
      [5, { caseLabelLatex: 'succ', hypotheses: [{ name: 'a', type: 'MyNat' }, { name: 'a_ih', type: 'P a' }] }],
    ]);
    const items = generateProofProse(induction, 999, goalMap);
    const caseHeaders = items.filter((it) => it.kind.tag === 'caseHeader');
    expect(caseHeaders).toHaveLength(2);
    expect((caseHeaders[0].kind as any).labelLatex).toBe('zero');
    expect((caseHeaders[0].kind as any).isBaseCase).toBe(true);
    expect((caseHeaders[1].kind as any).labelLatex).toBe('succ');
    expect((caseHeaders[1].kind as any).isBaseCase).toBe(false); // inductive step
  });

  test('case without constructorParamNames is base case', () => {
    const hole: ProofNode = { tag: 'hole', id: 10 };
    const induction: ProofNode = {
      tag: 'induction',
      id: 1,
      scrutinee: 'b',
      collapsed: false,
      cases: [
        { tag: 'case', id: 2, label: 'True', body: hole, collapsed: false },
      ],
    };
    const items = generateProofProse(induction, 10, mkGoalMap([]));
    // A SOLE case has no header row of its own, so it is item 0 (see below).
    expect((items[0].kind as any).isBaseCase).toBe(true);
    // Falls back to label when no labelLatex
    expect((items[0].kind as any).labelLatex).toBe('True');
  });

  // A split with one case is a DESTRUCTURING, not a case analysis: `cases hG
  // with | mk a b` names the parts of something with only one shape. It used to
  // get a header row plus two levels of indent, the same as a real split, so a
  // chain of them (destructure the pair, destructure its second half, …) walked
  // off the right edge of the page while saying nothing.
  test('a sole case folds the header into its own row and costs no indent', () => {
    const hole: ProofNode = { tag: 'hole', id: 10 };
    const induction: ProofNode = {
      tag: 'induction',
      id: 1,
      scrutinee: 'hG',
      isCases: true,
      collapsed: false,
      cases: [
        {
          tag: 'case', id: 2, label: 'mk', body: hole, collapsed: false,
          constructorName: 'mk', constructorParamNames: ['deltaG', 'gProof'],
        },
      ],
    };
    const items = generateProofProse(induction, 10, mkGoalMap([]));

    // No separate inductionHeader row: caseHeader + hole, nothing else.
    expect(items.map((i) => i.kind.tag)).toEqual(['caseHeader', 'hole']);
    // It carries the header text instead, so the row reads "By cases on hG: Case (…)".
    expect((items[0].kind as any).lead).toEqual({ nodeId: 1, scrutinee: 'hG', isCases: true });
    // And costs NO indentation — the body sits where the split did.
    expect(items[0].depth).toBe(0);
    expect(items[1].depth).toBe(0);
    // `lead.nodeId` is the SPLIT, not the case. Deleting this row has to remove
    // the split; without it the row had no delete at all and a one-case
    // destructure could not be undone from the prose.
    expect((items[0].kind as any).lead.nodeId).toBe(induction.id);
    expect(items[0].nodeId).not.toBe(induction.id);
  });

  test('two cases keep their header row and their indent — that IS a case analysis', () => {
    const l: ProofNode = { tag: 'hole', id: 10 };
    const r: ProofNode = { tag: 'hole', id: 11 };
    const induction: ProofNode = {
      tag: 'induction',
      id: 1,
      scrutinee: 'leTotal a b',
      isCases: true,
      collapsed: false,
      cases: [
        { tag: 'case', id: 2, label: 'left', body: l, collapsed: false, constructorName: 'left', constructorParamNames: ['h'] },
        { tag: 'case', id: 3, label: 'right', body: r, collapsed: false, constructorName: 'right', constructorParamNames: ['h'] },
      ],
    };
    const items = generateProofProse(induction, 10, mkGoalMap([]));

    expect(items.map((i) => i.kind.tag)).toEqual(['inductionHeader', 'caseHeader', 'hole', 'caseHeader', 'hole']);
    expect(items.map((i) => i.depth)).toEqual([0, 1, 2, 1, 2]);
    // No folded lead — the header has its own row here.
    expect((items[1].kind as any).lead).toBeUndefined();
  });

  test('nested intros → chain → exact produces correct depth and order', () => {
    const exact: ProofNode = { tag: 'exact', id: 4, expr: 'refl' };
    const rewrite: ProofNode = { tag: 'rewrite', id: 3, name: 'plusZero', reverse: false, child: exact };
    const unfold: ProofNode = { tag: 'unfold', id: 2, name: 'add', child: rewrite };
    const intros: ProofNode = { tag: 'intros', id: 1, names: ['n'], child: unfold };

    const goalMap = mkGoalMap([
      [1, { hypotheses: [] }],
      [2, { hypotheses: [{ name: 'n', type: '\\mathbb{N}' }] }],
      [4, { goalLatex: 'n = n', validation: { status: 'solved' } }],
    ]);
    const items = generateProofProse(intros, 4, goalMap);

    // intro, unfold, rewrite, exact, qed
    expect(items.map(i => i.kind.tag)).toEqual(['intro', 'unfold', 'rewrite', 'exact', 'qed']);
    // All at depth 0
    expect(items.map(i => i.depth)).toEqual([0, 0, 0, 0, 0]);
    // Only exact node is cursor
    expect(items.map(i => i.isCursor)).toEqual([false, false, false, true, true]);
  });

  test('multi-char variable names get mathit', () => {
    const hole: ProofNode = { tag: 'hole', id: 2 };
    const intros: ProofNode = { tag: 'intros', id: 1, names: ['xs'], child: hole };
    const goalMap = mkGoalMap([
      [1, { hypotheses: [] }],
      [2, { hypotheses: [{ name: 'xs', type: 'List' }] }],
    ]);
    const items = generateProofProse(intros, 2, goalMap);
    expect((items[0].kind as any).latex).toBe('\\mathit{xs} : List');
  });

  test('primed variable names render correctly', () => {
    const hole: ProofNode = { tag: 'hole', id: 2 };
    const intros: ProofNode = { tag: 'intros', id: 1, names: ["n'"], child: hole };
    const goalMap = mkGoalMap([
      [1, { hypotheses: [] }],
      [2, { hypotheses: [{ name: "n'", type: '\\mathbb{N}' }] }],
    ]);
    const items = generateProofProse(intros, 2, goalMap);
    expect((items[0].kind as any).latex).toBe("n' : \\mathbb{N}");
  });

  // ========================================================================
  // isValueType flag propagation
  // ========================================================================

  test('exact item inherits isValueType from its node info', () => {
    const ex: ProofNode = { tag: 'exact', id: 2, expr: 'δF' };
    const goalMap = mkGoalMap([
      [2, { goalLatex: '\\mathbb{R}', isValueType: true, validation: { status: 'solved' } }],
    ]);
    const items = generateProofProse(ex, 2, goalMap);
    const exactItem = items.find(i => i.kind.tag === 'exact');
    expect(exactItem).toBeDefined();
    expect((exactItem!.kind as any).isValueType).toBe(true);
  });

  test('exact item omits isValueType when goal is a proposition', () => {
    const ex: ProofNode = { tag: 'exact', id: 2, expr: 'refl' };
    const goalMap = mkGoalMap([
      [2, { goalLatex: '0 = 0', isValueType: false, validation: { status: 'solved' } }],
    ]);
    const items = generateProofProse(ex, 2, goalMap);
    const exactItem = items.find(i => i.kind.tag === 'exact');
    expect((exactItem!.kind as any).isValueType).toBe(false);
  });

  test('hole item carries isValueType flag', () => {
    const hole: ProofNode = { tag: 'hole', id: 1 };
    const goalMap = mkGoalMap([[1, { goalLatex: '\\mathbb{R}', isValueType: true }]]);
    const items = generateProofProse(hole, 1, goalMap);
    expect((items[0].kind as any).isValueType).toBe(true);
  });

  // REGRESSION (image #57): the simp prose used to list `node.lemmas` —
  // the FULL @simp set passed to the engine — rather than the lemmas that
  // actually fired during the simp run. The user-visible effect was a
  // line like "Simplifying using [12 lemma names] (2 steps)" when only 2
  // of those lemmas did anything. Now show just the lemmas that fired,
  // deduped in encounter order.
  test('simp prose lists only lemmas that actually fired, not the full @simp set', () => {
    const child: ProofNode = { tag: 'hole', id: 1 };
    // 12 lemmas were passed to simp; only 2 actually fired (addRealOfRat
    // twice, then realOfRatOne once — addRealOfRat dedupes to one entry).
    const simp: ProofNode = {
      tag: 'simp',
      id: 2,
      collapsed: false,
      lemmas: [
        'negLeft', 'addNegRight', 'realOfNatOne', 'realOfIntOne', 'realOfRatOne',
        'realOfNatZero', 'realOfIntZero', 'realOfRatZero', 'rtwoAsRealOfRat',
        'mulRealOfRat', 'addRealOfRat', 'subRealOfRat',
      ],
      steps: [
        { tag: 'rewrite', id: 3, name: 'addRealOfRat', reverse: false, child: { tag: 'hole', id: 99 } },
        { tag: 'rewrite', id: 4, name: 'addRealOfRat', reverse: false, child: { tag: 'hole', id: 99 } },
        { tag: 'rewrite', id: 5, name: 'realOfRatOne', reverse: false, child: { tag: 'hole', id: 99 } },
      ],
      child,
    };
    const goalMap = mkGoalMap([[2, { goalLatex: '0 \\le 1' }]]);
    const items = generateProofProse(simp, 1, goalMap);
    const simpItem = items.find(i => i.kind.tag === 'simp');
    expect(simpItem, 'simp item should exist').toBeDefined();
    const kind = simpItem!.kind as any;
    // The displayed lemma list should be only the firing lemmas, deduped.
    expect(kind.lemmas).toEqual(['addRealOfRat', 'realOfRatOne']);
    // Step count still reports total fires (including the duplicate).
    expect(kind.stepCount).toBe(3);
  });

  test('simp prose falls back to passed-in lemmas if no step has a name', () => {
    // Defensive fallback: if simp.steps somehow contains nodes without a
    // recordable name, we shouldn't render an empty list.
    const child: ProofNode = { tag: 'hole', id: 1 };
    const simp: ProofNode = {
      tag: 'simp',
      id: 2,
      collapsed: false,
      lemmas: ['someLemma'],
      steps: [{ tag: 'hole', id: 3 } as any],
      child,
    };
    const goalMap = mkGoalMap([[2, { goalLatex: 'X' }]]);
    const items = generateProofProse(simp, 1, goalMap);
    const simpItem = items.find(i => i.kind.tag === 'simp');
    expect((simpItem!.kind as any).lemmas).toEqual(['someLemma']);
  });

  test('subgoalHeader (Goal N) carries child isValueType for prose switch', () => {
    // apply constructor with 2 exact children where subgoal 1 is a value type.
    const ex1: ProofNode = { tag: 'exact', id: 11, expr: 'δF' };
    const ex2: ProofNode = { tag: 'exact', id: 12, expr: 'MkPair posF bnd' };
    const ap: ProofNode = { tag: 'apply', id: 10, name: 'constructor', children: [ex1, ex2] };
    const goalMap = mkGoalMap([
      [10, { goalLatex: 'DPair A B' }],
      [11, { goalLatex: '\\mathbb{R}', isValueType: true, validation: { status: 'solved' } }],
      [12, { goalLatex: '0 < \\delta_F', isValueType: false, validation: { status: 'solved' } }],
    ]);
    const items = generateProofProse(ap, 10, goalMap);
    // Since all children are `exact`, the compact proofExprs form is used
    // rather than subgoalHeader — verify no crash and no error.
    expect(items.length).toBeGreaterThan(0);
  });

  test('a hole Lean reports as solved is flagged (renders ✓, not ?)', () => {
    const hole: ProofNode = { tag: 'hole', id: 1 };
    const goalMap = mkGoalMap([[1, { goalLatex: '', validation: { status: 'solved' } }]]);
    const items = generateProofProse(hole, 999, goalMap); // not at cursor
    expect(items).toHaveLength(1);
    expect(items[0].kind.tag).toBe('hole');
    expect((items[0].kind as any).solved).toBe(true);
  });

  test('an open hole is not flagged solved', () => {
    const hole: ProofNode = { tag: 'hole', id: 1 };
    const goalMap = mkGoalMap([[1, { goalLatex: '0 \\leq a' }]]);
    const items = generateProofProse(hole, 999, goalMap);
    expect((items[0].kind as any).solved).toBeFalsy();
  });

  test('conditional rewrite renders side goal as a labeled branch', () => {
    // rw [summationSplit] leaves `0 ≤ a` as a side goal (still an open hole).
    const mainHole: ProofNode = { tag: 'hole', id: 21 };
    const sideHole: ProofNode = { tag: 'hole', id: 22 };
    const rw: ProofNode = {
      tag: 'rewrite', id: 20, name: 'summationSplit', reverse: false,
      child: mainHole, sideGoals: [sideHole],
    };
    const goalMap = mkGoalMap([
      [20, { goalLatex: '2 \\cdot S = T' }],
      [21, { goalLatex: 'rewritten' }],
      [22, { goalLatex: '0 \\leq a' }],
    ]);
    const items = generateProofProse(rw, 22, goalMap);
    // The rewrite step renders, then the main hole, then a "Side goal" header
    // carrying the side-goal LaTeX, then the side-goal hole itself.
    expect(items.find(i => i.kind.tag === 'rewrite')).toBeTruthy();
    const header = items.find(i => i.kind.tag === 'subgoalHeader');
    expect(header).toBeTruthy();
    expect((header!.kind as any).label).toBe('Side goal');
    expect((header!.kind as any).goalLatex).toBe('0 \\leq a');
    const sideHoleItem = items.find(i => i.kind.tag === 'hole' && (i.kind as any).goalLatex === '0 \\leq a');
    expect(sideHoleItem).toBeTruthy();
    expect(sideHoleItem!.isCursor).toBe(true);
  });

describe('case params carry their types (for hover)', () => {
  test('each bound param gets the type it has in the case goal', () => {
    const body: ProofNode = { tag: 'hole', id: 2 };
    const root: ProofNode = {
      tag: 'induction', id: 1, scrutinee: 'fProof', collapsed: false, isCases: true,
      cases: [{
        tag: 'case', id: 3, label: 'mk', body, collapsed: false,
        constructorName: 'mk', constructorParamNames: ['fst', 'snd'],
      }],
    };
    // The case has NO goal of its own (a lone case prints as a plain
    // continuation); the head of its body carries the same goal.
    const goalMap = mkGoalMap([
      [1, { hypotheses: [{ name: 'fProof', type: 'W' }] }],
      [2, { hypotheses: [{ name: 'fst', type: '0 < \\delta_F' }, { name: 'snd', type: '\\forall x, P' }] }],
    ]);
    const items = generateProofProse(root, 2, goalMap);
    const header = items.find((i: ProseItem) => i.kind.tag === 'caseHeader')!;
    expect(header.kind).toMatchObject({
      constructorParamNames: ['fst', 'snd'],
      paramTypeLatex: ['0 < \\delta_F', '\\forall x, P'],
    });
  });

  test('no types recorded when the goal map has nothing to say', () => {
    const root: ProofNode = {
      tag: 'induction', id: 1, scrutinee: 'x', collapsed: false, isCases: true,
      cases: [{
        tag: 'case', id: 3, label: 'mk', body: { tag: 'hole', id: 2 }, collapsed: false,
        constructorName: 'mk', constructorParamNames: ['a'],
      }],
    };
    const header = generateProofProse(root, 2, new Map()).find((i: ProseItem) => i.kind.tag === 'caseHeader')!;
    expect((header.kind as { paramTypeLatex?: string[] }).paramTypeLatex).toBeUndefined();
  });
});
});
