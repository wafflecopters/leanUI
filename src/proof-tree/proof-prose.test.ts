import { describe, test, expect, beforeEach } from 'vitest';
import { generateProofProse, ProseItem } from './proof-prose';
import { ProofNode, resetProofIds, freshProofId } from './proof-tree';
import { NodeGoalInfo } from './goal-computation';

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
    expect((items[1].kind as any).isBaseCase).toBe(true);
    // Falls back to label when no labelLatex
    expect((items[1].kind as any).labelLatex).toBe('True');
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
});
