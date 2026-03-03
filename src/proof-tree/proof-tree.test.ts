import { describe, test, expect, beforeEach } from 'vitest';
import {
  resetProofIds, freshProofId,
  mkHole, mkIntros, mkInduction, mkCase, mkExact,
  createInitialState,
  findNode, findCase, isCursorInSubtree, linearize,
  replaceNode, updateCase,
  applyIntros, applyInduction, applyExact,
  addCase, removeCase, toggleCollapse, toggleInductionCollapse,
  moveCursorUp, moveCursorDown,
  editIntroName, addIntroName, removeIntroName,
  editScrutinee, editExact, editCaseLabel,
  clearNode,
  createHistory, pushState, updateCurrent, undo, redo,
  ProofTreeState,
} from './proof-tree';

beforeEach(() => resetProofIds());

// ============================================================================
// 1. Construction
// ============================================================================

describe('construction', () => {
  test('mkHole creates hole with unique id', () => {
    const h1 = mkHole();
    const h2 = mkHole();
    expect(h1.tag).toBe('hole');
    expect(h1.id).not.toBe(h2.id);
  });

  test('mkIntros creates intros node with names and child', () => {
    const child = mkHole();
    const intros = mkIntros(['n', 'm'], child);
    expect(intros.tag).toBe('intros');
    expect(intros.names).toEqual(['n', 'm']);
    expect(intros.child).toBe(child);
  });

  test('mkInduction creates induction with scrutinee and cases', () => {
    const c1 = mkCase('Zero', mkHole());
    const c2 = mkCase('Succ k', mkHole());
    const ind = mkInduction('n', [c1, c2]);
    expect(ind.tag).toBe('induction');
    expect(ind.scrutinee).toBe('n');
    expect(ind.cases).toHaveLength(2);
    expect(ind.collapsed).toBe(false);
  });

  test('mkExact creates exact node with expression', () => {
    const exact = mkExact('refl');
    expect(exact.tag).toBe('exact');
    expect(exact.expr).toBe('refl');
  });

  test('mkCase creates case node with label and body', () => {
    const body = mkHole();
    const c = mkCase('Zero', body);
    expect(c.tag).toBe('case');
    expect(c.label).toBe('Zero');
    expect(c.body).toBe(body);
    expect(c.collapsed).toBe(false);
  });

  test('createInitialState creates hole root with cursor on it', () => {
    const state = createInitialState();
    expect(state.root.tag).toBe('hole');
    expect(state.cursor.nodeId).toBe(state.root.id);
  });

  test('each freshProofId is unique', () => {
    const ids = [freshProofId(), freshProofId(), freshProofId()];
    expect(new Set(ids).size).toBe(3);
  });

  test('resetProofIds resets counter', () => {
    freshProofId(); freshProofId();
    resetProofIds();
    const id = freshProofId();
    expect(id).toBe(1);
  });
});

// ============================================================================
// 2. Tree Queries — findNode, findCase
// ============================================================================

describe('findNode', () => {
  test('finds root node', () => {
    const root = mkHole();
    expect(findNode(root, root.id)).toBe(root);
  });

  test('finds intros child', () => {
    const child = mkHole();
    const root = mkIntros(['n'], child);
    expect(findNode(root, child.id)).toBe(child);
  });

  test('finds node inside induction case body', () => {
    const inner = mkHole();
    const c = mkCase('Zero', inner);
    const ind = mkInduction('n', [c]);
    expect(findNode(ind, inner.id)).toBe(inner);
  });

  test('returns null for case node id (case is not a ProofNode)', () => {
    const c = mkCase('Zero', mkHole());
    const ind = mkInduction('n', [c]);
    expect(findNode(ind, c.id)).toBeNull();
  });

  test('returns null for nonexistent id', () => {
    const root = mkHole();
    expect(findNode(root, 9999)).toBeNull();
  });
});

describe('findCase', () => {
  test('finds case by id in induction', () => {
    const c1 = mkCase('Zero', mkHole());
    const c2 = mkCase('Succ k', mkHole());
    const ind = mkInduction('n', [c1, c2]);
    expect(findCase(ind, c1.id)).toBe(c1);
    expect(findCase(ind, c2.id)).toBe(c2);
  });

  test('finds case in nested structure', () => {
    const innerCase = mkCase('Zero', mkHole());
    const innerInd = mkInduction('m', [innerCase]);
    const outerCase = mkCase('A', innerInd);
    const outerInd = mkInduction('n', [outerCase]);
    expect(findCase(outerInd, innerCase.id)).toBe(innerCase);
  });

  test('returns null for non-case id', () => {
    const body = mkHole();
    const c = mkCase('Zero', body);
    const ind = mkInduction('n', [c]);
    expect(findCase(ind, body.id)).toBeNull();
  });

  test('returns null in hole', () => {
    expect(findCase(mkHole(), 1)).toBeNull();
  });
});

describe('isCursorInSubtree', () => {
  test('returns true for root node itself', () => {
    const h = mkHole();
    expect(isCursorInSubtree(h, h.id)).toBe(true);
  });

  test('returns true for nested child', () => {
    const inner = mkHole();
    const root = mkIntros(['n'], inner);
    expect(isCursorInSubtree(root, inner.id)).toBe(true);
  });

  test('returns true for case id inside induction', () => {
    const c = mkCase('Zero', mkHole());
    const ind = mkInduction('n', [c]);
    expect(isCursorInSubtree(ind, c.id)).toBe(true);
  });

  test('returns false for unrelated id', () => {
    const root = mkHole();
    expect(isCursorInSubtree(root, 9999)).toBe(false);
  });
});

// ============================================================================
// 3. Linearization
// ============================================================================

describe('linearize', () => {
  test('single hole produces one entry', () => {
    const root = mkHole();
    const entries = linearize(root);
    expect(entries).toHaveLength(1);
    expect(entries[0]).toEqual({ kind: 'node', id: root.id, depth: 0 });
  });

  test('intros with hole child produces two entries', () => {
    const child = mkHole();
    const root = mkIntros(['n'], child);
    const entries = linearize(root);
    expect(entries).toHaveLength(2);
    expect(entries[0].id).toBe(root.id);
    expect(entries[0].depth).toBe(0);
    expect(entries[1].id).toBe(child.id);
    expect(entries[1].depth).toBe(1);
  });

  test('induction with two cases produces correct DFS order', () => {
    const body1 = mkHole();
    const body2 = mkHole();
    const c1 = mkCase('Zero', body1);
    const c2 = mkCase('Succ k', body2);
    const ind = mkInduction('n', [c1, c2]);
    const entries = linearize(ind);
    // induction, case1, body1, case2, body2
    expect(entries.map(e => e.id)).toEqual([ind.id, c1.id, body1.id, c2.id, body2.id]);
    expect(entries.map(e => e.depth)).toEqual([0, 1, 2, 1, 2]);
  });

  test('collapsed induction hides all cases', () => {
    const c1 = mkCase('Zero', mkHole());
    const c2 = mkCase('Succ k', mkHole());
    const ind: typeof mkInduction extends (...a: any) => infer R ? R : never =
      { ...mkInduction('n', [c1, c2]), collapsed: true };
    const entries = linearize(ind);
    expect(entries).toHaveLength(1);
    expect(entries[0].id).toBe(ind.id);
  });

  test('collapsed case shows header but hides body', () => {
    const body1 = mkHole();
    const body2 = mkHole();
    const c1: CaseNodeType = { ...mkCase('Zero', body1), collapsed: true };
    const c2 = mkCase('Succ k', body2);
    const ind = mkInduction('n', [c1, c2]);
    const entries = linearize(ind);
    // induction, case1 (no body1), case2, body2
    expect(entries.map(e => e.id)).toEqual([ind.id, c1.id, c2.id, body2.id]);
  });

  test('nested intros inside case body', () => {
    const innerHole = mkHole();
    const introsInCase = mkIntros(['m'], innerHole);
    const c = mkCase('Zero', introsInCase);
    const ind = mkInduction('n', [c]);
    const entries = linearize(ind);
    expect(entries.map(e => e.id)).toEqual([ind.id, c.id, introsInCase.id, innerHole.id]);
    expect(entries.map(e => e.depth)).toEqual([0, 1, 2, 3]);
  });
});

// Helper type alias for collapsed case construction
type CaseNodeType = ReturnType<typeof mkCase>;

// ============================================================================
// 4. Cursor Navigation
// ============================================================================

describe('cursor navigation', () => {
  test('moveCursorDown moves to next linear entry', () => {
    const child = mkHole();
    const root = mkIntros(['n'], child);
    const state: ProofTreeState = { root, cursor: { nodeId: root.id } };
    const moved = moveCursorDown(state);
    expect(moved.cursor.nodeId).toBe(child.id);
  });

  test('moveCursorUp moves to previous linear entry', () => {
    const child = mkHole();
    const root = mkIntros(['n'], child);
    const state: ProofTreeState = { root, cursor: { nodeId: child.id } };
    const moved = moveCursorUp(state);
    expect(moved.cursor.nodeId).toBe(root.id);
  });

  test('moveCursorDown at bottom is no-op', () => {
    const child = mkHole();
    const root = mkIntros(['n'], child);
    const state: ProofTreeState = { root, cursor: { nodeId: child.id } };
    const moved = moveCursorDown(state);
    expect(moved).toBe(state);
  });

  test('moveCursorUp at top is no-op', () => {
    const root = mkHole();
    const state: ProofTreeState = { root, cursor: { nodeId: root.id } };
    const moved = moveCursorUp(state);
    expect(moved).toBe(state);
  });

  test('navigation through full induction tree', () => {
    const body1 = mkHole();
    const body2 = mkHole();
    const c1 = mkCase('Zero', body1);
    const c2 = mkCase('Succ k', body2);
    const ind = mkInduction('n', [c1, c2]);
    let state: ProofTreeState = { root: ind, cursor: { nodeId: ind.id } };

    state = moveCursorDown(state);
    expect(state.cursor.nodeId).toBe(c1.id);

    state = moveCursorDown(state);
    expect(state.cursor.nodeId).toBe(body1.id);

    state = moveCursorDown(state);
    expect(state.cursor.nodeId).toBe(c2.id);

    state = moveCursorDown(state);
    expect(state.cursor.nodeId).toBe(body2.id);
  });

  test('navigation skips collapsed case body', () => {
    const body1 = mkHole();
    const body2 = mkHole();
    const c1: CaseNodeType = { ...mkCase('Zero', body1), collapsed: true };
    const c2 = mkCase('Succ k', body2);
    const ind = mkInduction('n', [c1, c2]);
    let state: ProofTreeState = { root: ind, cursor: { nodeId: ind.id } };

    state = moveCursorDown(state);
    expect(state.cursor.nodeId).toBe(c1.id);

    // Skips body1 because c1 is collapsed
    state = moveCursorDown(state);
    expect(state.cursor.nodeId).toBe(c2.id);

    state = moveCursorDown(state);
    expect(state.cursor.nodeId).toBe(body2.id);
  });
});

// ============================================================================
// 5. Tactic Application
// ============================================================================

describe('applyIntros', () => {
  test('replaces hole with intros node, cursor moves to child hole', () => {
    const state = createInitialState();
    const result = applyIntros(state, ['i', 'f', 'n']);
    expect(result).not.toBeNull();
    expect(result!.root.tag).toBe('intros');
    const intros = result!.root as { tag: 'intros'; names: readonly string[]; child: any };
    expect(intros.names).toEqual(['i', 'f', 'n']);
    expect(intros.child.tag).toBe('hole');
    expect(result!.cursor.nodeId).toBe(intros.child.id);
  });

  test('returns null if cursor is not on a hole', () => {
    const exact = mkExact('refl');
    const state: ProofTreeState = { root: exact, cursor: { nodeId: exact.id } };
    expect(applyIntros(state, ['n'])).toBeNull();
  });

  test('returns null if cursor is on nonexistent node', () => {
    const state = createInitialState();
    const modified: ProofTreeState = { ...state, cursor: { nodeId: 9999 } };
    expect(applyIntros(modified, ['n'])).toBeNull();
  });

  test('preserves rest of tree when applied in nested position', () => {
    // intros → hole  →  intros → intros → hole
    const state = createInitialState();
    const after1 = applyIntros(state, ['n'])!;
    const after2 = applyIntros(after1, ['m'])!;
    expect(after2.root.tag).toBe('intros');
    const outer = after2.root as { tag: 'intros'; child: any };
    expect(outer.child.tag).toBe('intros');
    expect(outer.child.child.tag).toBe('hole');
  });
});

describe('applyInduction', () => {
  test('replaces hole with induction, creates cases with holes', () => {
    const state = createInitialState();
    const result = applyInduction(state, 'n', ['Zero', 'Succ k']);
    expect(result).not.toBeNull();
    expect(result!.root.tag).toBe('induction');
    const ind = result!.root as any;
    expect(ind.scrutinee).toBe('n');
    expect(ind.cases).toHaveLength(2);
    expect(ind.cases[0].label).toBe('Zero');
    expect(ind.cases[0].body.tag).toBe('hole');
    expect(ind.cases[1].label).toBe('Succ k');
    expect(ind.cases[1].body.tag).toBe('hole');
  });

  test('cursor moves to first case body', () => {
    const state = createInitialState();
    const result = applyInduction(state, 'n', ['Zero', 'Succ k'])!;
    const ind = result.root as any;
    expect(result.cursor.nodeId).toBe(ind.cases[0].body.id);
  });

  test('returns null if cursor is not on a hole', () => {
    const exact = mkExact('refl');
    const state: ProofTreeState = { root: exact, cursor: { nodeId: exact.id } };
    expect(applyInduction(state, 'n', ['Zero'])).toBeNull();
  });

  test('with empty case labels creates induction with no cases', () => {
    const state = createInitialState();
    const result = applyInduction(state, 'n', []);
    expect(result).not.toBeNull();
    const ind = result!.root as any;
    expect(ind.cases).toHaveLength(0);
    // Cursor falls back to induction node itself
    expect(result!.cursor.nodeId).toBe(ind.id);
  });
});

describe('applyExact', () => {
  test('replaces hole with exact node', () => {
    const state = createInitialState();
    const result = applyExact(state, 'refl');
    expect(result).not.toBeNull();
    expect(result!.root.tag).toBe('exact');
    expect((result!.root as any).expr).toBe('refl');
  });

  test('cursor stays on exact node', () => {
    const state = createInitialState();
    const result = applyExact(state, 'refl')!;
    expect(result.cursor.nodeId).toBe(result.root.id);
  });

  test('returns null if cursor is not on a hole', () => {
    const exact = mkExact('existing');
    const state: ProofTreeState = { root: exact, cursor: { nodeId: exact.id } };
    expect(applyExact(state, 'new')).toBeNull();
  });
});

// ============================================================================
// 6. Case Operations
// ============================================================================

describe('case operations', () => {
  function makeInductionState(): ProofTreeState {
    const body1 = mkHole();
    const body2 = mkHole();
    const c1 = mkCase('Zero', body1);
    const c2 = mkCase('Succ k', body2);
    const ind = mkInduction('n', [c1, c2]);
    return { root: ind, cursor: { nodeId: body1.id } };
  }

  test('addCase appends new case to induction', () => {
    const state = makeInductionState();
    const result = addCase(state, state.root.id, 'NewCase');
    expect(result).not.toBeNull();
    const ind = result!.root as any;
    expect(ind.cases).toHaveLength(3);
    expect(ind.cases[2].label).toBe('NewCase');
  });

  test('addCase cursor moves to new case body', () => {
    const state = makeInductionState();
    const result = addCase(state, state.root.id, 'NewCase')!;
    const ind = result.root as any;
    expect(result.cursor.nodeId).toBe(ind.cases[2].body.id);
  });

  test('addCase returns null for non-induction node', () => {
    const state = createInitialState();
    expect(addCase(state, state.root.id, 'X')).toBeNull();
  });

  test('removeCase removes case at index', () => {
    const state = makeInductionState();
    const result = removeCase(state, state.root.id, 0);
    expect(result).not.toBeNull();
    const ind = result!.root as any;
    expect(ind.cases).toHaveLength(1);
    expect(ind.cases[0].label).toBe('Succ k');
  });

  test('removeCase blocks removal of last case', () => {
    const body = mkHole();
    const c = mkCase('Only', body);
    const ind = mkInduction('n', [c]);
    const state: ProofTreeState = { root: ind, cursor: { nodeId: body.id } };
    expect(removeCase(state, ind.id, 0)).toBeNull();
  });

  test('removeCase fixes cursor when cursor was in removed case', () => {
    const state = makeInductionState();
    // Cursor is on first case body. Remove first case.
    const result = removeCase(state, state.root.id, 0)!;
    const ind = result.root as any;
    // Cursor should move to remaining case's body
    expect(result.cursor.nodeId).toBe(ind.cases[0].body.id);
  });

  test('removeCase returns null for invalid index', () => {
    const state = makeInductionState();
    expect(removeCase(state, state.root.id, -1)).toBeNull();
    expect(removeCase(state, state.root.id, 5)).toBeNull();
  });

  test('toggleCollapse toggles case collapsed state', () => {
    const body = mkHole();
    const c = mkCase('Zero', body);
    const ind = mkInduction('n', [c]);
    const state: ProofTreeState = { root: ind, cursor: { nodeId: ind.id } };

    const toggled = toggleCollapse(state, c.id);
    const toggledCase = findCase(toggled.root, c.id)!;
    expect(toggledCase.collapsed).toBe(true);

    const unToggled = toggleCollapse(toggled, c.id);
    const unToggledCase = findCase(unToggled.root, c.id)!;
    expect(unToggledCase.collapsed).toBe(false);
  });

  test('toggleCollapse moves cursor to case header when collapsing hides cursor', () => {
    const body = mkHole();
    const c = mkCase('Zero', body);
    const ind = mkInduction('n', [c]);
    const state: ProofTreeState = { root: ind, cursor: { nodeId: body.id } };

    const toggled = toggleCollapse(state, c.id);
    expect(toggled.cursor.nodeId).toBe(c.id);
  });

  test('toggleInductionCollapse toggles induction collapsed state', () => {
    const state = makeInductionState();
    const result = toggleInductionCollapse(state, state.root.id)!;
    expect((result.root as any).collapsed).toBe(true);

    const result2 = toggleInductionCollapse(result, result.root.id)!;
    expect((result2.root as any).collapsed).toBe(false);
  });

  test('toggleInductionCollapse moves cursor when collapsing hides it', () => {
    const state = makeInductionState(); // cursor on first case body
    const result = toggleInductionCollapse(state, state.root.id)!;
    expect(result.cursor.nodeId).toBe(state.root.id);
  });

  test('toggleInductionCollapse returns null for non-induction node', () => {
    const state = createInitialState();
    expect(toggleInductionCollapse(state, state.root.id)).toBeNull();
  });
});

// ============================================================================
// 7. Editing
// ============================================================================

describe('editing', () => {
  test('editIntroName changes a specific name', () => {
    const child = mkHole();
    const intros = mkIntros(['a', 'b', 'c'], child);
    const state: ProofTreeState = { root: intros, cursor: { nodeId: intros.id } };
    const result = editIntroName(state, intros.id, 1, 'x')!;
    expect((result.root as any).names).toEqual(['a', 'x', 'c']);
  });

  test('editIntroName returns null for wrong node type', () => {
    const state = createInitialState();
    expect(editIntroName(state, state.root.id, 0, 'x')).toBeNull();
  });

  test('editIntroName returns null for out-of-bounds index', () => {
    const intros = mkIntros(['a'], mkHole());
    const state: ProofTreeState = { root: intros, cursor: { nodeId: intros.id } };
    expect(editIntroName(state, intros.id, 5, 'x')).toBeNull();
    expect(editIntroName(state, intros.id, -1, 'x')).toBeNull();
  });

  test('addIntroName appends a name', () => {
    const intros = mkIntros(['a', 'b'], mkHole());
    const state: ProofTreeState = { root: intros, cursor: { nodeId: intros.id } };
    const result = addIntroName(state, intros.id, 'c')!;
    expect((result.root as any).names).toEqual(['a', 'b', 'c']);
  });

  test('removeIntroName removes name at index', () => {
    const intros = mkIntros(['a', 'b', 'c'], mkHole());
    const state: ProofTreeState = { root: intros, cursor: { nodeId: intros.id } };
    const result = removeIntroName(state, intros.id, 1)!;
    expect((result.root as any).names).toEqual(['a', 'c']);
  });

  test('removeIntroName blocks removal of last name', () => {
    const intros = mkIntros(['a'], mkHole());
    const state: ProofTreeState = { root: intros, cursor: { nodeId: intros.id } };
    expect(removeIntroName(state, intros.id, 0)).toBeNull();
  });

  test('editScrutinee changes scrutinee string', () => {
    const ind = mkInduction('n', [mkCase('Zero', mkHole())]);
    const state: ProofTreeState = { root: ind, cursor: { nodeId: ind.id } };
    const result = editScrutinee(state, ind.id, 'm')!;
    expect((result.root as any).scrutinee).toBe('m');
  });

  test('editExact changes expression string', () => {
    const exact = mkExact('refl');
    const state: ProofTreeState = { root: exact, cursor: { nodeId: exact.id } };
    const result = editExact(state, exact.id, 'congSucc IH')!;
    expect((result.root as any).expr).toBe('congSucc IH');
  });

  test('editCaseLabel changes case label', () => {
    const c = mkCase('Zero', mkHole());
    const ind = mkInduction('n', [c]);
    const state: ProofTreeState = { root: ind, cursor: { nodeId: ind.id } };
    const result = editCaseLabel(state, c.id, 'Base');
    const updatedCase = findCase(result.root, c.id)!;
    expect(updatedCase.label).toBe('Base');
  });
});

// ============================================================================
// 8. Clear / Revert
// ============================================================================

describe('clearNode', () => {
  test('reverts intros to hole', () => {
    const child = mkHole();
    const intros = mkIntros(['n'], child);
    const state: ProofTreeState = { root: intros, cursor: { nodeId: intros.id } };
    const result = clearNode(state, intros.id)!;
    expect(result.root.tag).toBe('hole');
    expect(result.cursor.nodeId).toBe(result.root.id);
  });

  test('reverts induction to hole', () => {
    const ind = mkInduction('n', [mkCase('Zero', mkHole())]);
    const state: ProofTreeState = { root: ind, cursor: { nodeId: ind.id } };
    const result = clearNode(state, ind.id)!;
    expect(result.root.tag).toBe('hole');
  });

  test('reverts exact to hole', () => {
    const exact = mkExact('refl');
    const state: ProofTreeState = { root: exact, cursor: { nodeId: exact.id } };
    const result = clearNode(state, exact.id)!;
    expect(result.root.tag).toBe('hole');
  });

  test('returns null for already-a-hole', () => {
    const state = createInitialState();
    expect(clearNode(state, state.root.id)).toBeNull();
  });

  test('returns null for nonexistent node', () => {
    const state = createInitialState();
    expect(clearNode(state, 9999)).toBeNull();
  });

  test('clearing nested node preserves parent structure', () => {
    const innerHole = mkHole();
    const introsInner = mkIntros(['m'], innerHole);
    const c = mkCase('Zero', introsInner);
    const ind = mkInduction('n', [c]);
    const state: ProofTreeState = { root: ind, cursor: { nodeId: introsInner.id } };

    const result = clearNode(state, introsInner.id)!;
    // Induction still exists, but inner intros is now a hole
    expect(result.root.tag).toBe('induction');
    const updatedCase = (result.root as any).cases[0];
    expect(updatedCase.body.tag).toBe('hole');
  });
});

// ============================================================================
// 9. History
// ============================================================================

describe('history', () => {
  test('createHistory has empty undo/redo stacks', () => {
    const state = createInitialState();
    const hist = createHistory(state);
    expect(hist.undoStack).toHaveLength(0);
    expect(hist.redoStack).toHaveLength(0);
    expect(hist.current).toBe(state);
  });

  test('pushState adds to undo stack', () => {
    const s1 = createInitialState();
    const hist = createHistory(s1);
    const s2 = applyIntros(s1, ['n'])!;
    const hist2 = pushState(hist, s2);
    expect(hist2.undoStack).toHaveLength(1);
    expect(hist2.undoStack[0]).toBe(s1);
    expect(hist2.current).toBe(s2);
  });

  test('pushState clears redo stack', () => {
    const s1 = createInitialState();
    const s2 = applyIntros(s1, ['n'])!;
    const s3 = applyIntros(s2, ['m'])!;

    let hist = createHistory(s1);
    hist = pushState(hist, s2);
    hist = pushState(hist, s3);
    hist = undo(hist); // now at s2 with redo=[s3]
    expect(hist.redoStack).toHaveLength(1);

    // Push new state — redo should be cleared
    const s4 = applyExact(hist.current, 'refl')!;
    hist = pushState(hist, s4);
    expect(hist.redoStack).toHaveLength(0);
  });

  test('undo restores previous state', () => {
    const s1 = createInitialState();
    const s2 = applyIntros(s1, ['n'])!;
    let hist = createHistory(s1);
    hist = pushState(hist, s2);
    hist = undo(hist);
    expect(hist.current).toBe(s1);
  });

  test('undo pushes current onto redo stack', () => {
    const s1 = createInitialState();
    const s2 = applyIntros(s1, ['n'])!;
    let hist = createHistory(s1);
    hist = pushState(hist, s2);
    hist = undo(hist);
    expect(hist.redoStack).toHaveLength(1);
    expect(hist.redoStack[0]).toBe(s2);
  });

  test('undo at empty stack is no-op', () => {
    const state = createInitialState();
    const hist = createHistory(state);
    const result = undo(hist);
    expect(result).toBe(hist);
  });

  test('redo restores next state', () => {
    const s1 = createInitialState();
    const s2 = applyIntros(s1, ['n'])!;
    let hist = createHistory(s1);
    hist = pushState(hist, s2);
    hist = undo(hist);
    hist = redo(hist);
    expect(hist.current).toBe(s2);
  });

  test('redo pushes current onto undo stack', () => {
    const s1 = createInitialState();
    const s2 = applyIntros(s1, ['n'])!;
    let hist = createHistory(s1);
    hist = pushState(hist, s2);
    hist = undo(hist);
    hist = redo(hist);
    expect(hist.undoStack).toHaveLength(1);
    expect(hist.undoStack[0]).toBe(s1);
  });

  test('redo at empty stack is no-op', () => {
    const state = createInitialState();
    const hist = createHistory(state);
    const result = redo(hist);
    expect(result).toBe(hist);
  });

  test('updateCurrent changes current without affecting stacks', () => {
    const s1 = createInitialState();
    let hist = createHistory(s1);
    const s2 = moveCursorDown(s1); // no-op for single hole, but produces new ref
    hist = updateCurrent(hist, s2);
    expect(hist.current).toBe(s2);
    expect(hist.undoStack).toHaveLength(0);
    expect(hist.redoStack).toHaveLength(0);
  });

  test('undo restores cursor position from time of push', () => {
    const s1 = createInitialState(); // cursor on hole

    // Apply intros → cursor moves to child hole
    const s2 = applyIntros(s1, ['n'])!;
    let hist = createHistory(s1);
    hist = pushState(hist, s2);

    // Move cursor (via updateCurrent, not pushState)
    const introsNode = s2.root;
    const s2moved: ProofTreeState = { ...s2, cursor: { nodeId: introsNode.id } };
    hist = updateCurrent(hist, s2moved);

    // Undo: should restore s1 (with cursor on original hole), not s2moved
    hist = undo(hist);
    expect(hist.current).toBe(s1);
    expect(hist.current.cursor.nodeId).toBe(s1.root.id);
  });
});

// ============================================================================
// 10. Full Workflow
// ============================================================================

describe('full workflow', () => {
  test('intros → induction → exact in first case', () => {
    // Start with a hole
    let state = createInitialState();

    // Apply intros
    state = applyIntros(state, ['i', 'f', 'n'])!;
    expect(state.root.tag).toBe('intros');
    const intros = state.root as any;
    expect(intros.names).toEqual(['i', 'f', 'n']);

    // Apply induction at child hole
    state = applyInduction(state, 'n', ['n = 0', "n = k'"])!;
    const childInd = intros.child; // still points to old tree
    // Check the new tree
    expect((state.root as any).child.tag).toBe('induction');
    const ind = (state.root as any).child;
    expect(ind.cases).toHaveLength(2);
    expect(ind.cases[0].label).toBe('n = 0');
    expect(ind.cases[1].label).toBe("n = k'");

    // Apply exact in first case
    state = applyExact(state, 'refl')!;
    const updatedInd = (state.root as any).child;
    expect(updatedInd.cases[0].body.tag).toBe('exact');
    expect(updatedInd.cases[0].body.expr).toBe('refl');

    // Second case is still a hole
    expect(updatedInd.cases[1].body.tag).toBe('hole');
  });

  test('undo/redo through full workflow', () => {
    const s0 = createInitialState();
    let hist = createHistory(s0);

    // Step 1: intros
    const s1 = applyIntros(s0, ['n'])!;
    hist = pushState(hist, s1);

    // Step 2: induction
    const s2 = applyInduction(s1, 'n', ['Zero', 'Succ k'])!;
    hist = pushState(hist, s2);

    // Step 3: exact in first case
    const s3 = applyExact(s2, 'refl')!;
    hist = pushState(hist, s3);

    // Verify final state
    expect(hist.current.root.tag).toBe('intros');
    expect(hist.undoStack).toHaveLength(3);

    // Undo exact
    hist = undo(hist);
    expect(hist.current).toBe(s2);
    expect((hist.current.root as any).child.cases[0].body.tag).toBe('hole');

    // Undo induction
    hist = undo(hist);
    expect(hist.current).toBe(s1);
    expect((hist.current.root as any).child.tag).toBe('hole');

    // Undo intros
    hist = undo(hist);
    expect(hist.current).toBe(s0);
    expect(hist.current.root.tag).toBe('hole');

    // Redo all
    hist = redo(hist);
    expect(hist.current).toBe(s1);
    hist = redo(hist);
    expect(hist.current).toBe(s2);
    hist = redo(hist);
    expect(hist.current).toBe(s3);

    // Back at step 3
    expect(hist.undoStack).toHaveLength(3);
    expect(hist.redoStack).toHaveLength(0);
  });

  test('undo after clearing a node', () => {
    const s0 = createInitialState();
    const s1 = applyIntros(s0, ['n'])!;
    let hist = createHistory(s0);
    hist = pushState(hist, s1);

    // Clear intros → back to hole
    const s2 = clearNode(s1, s1.root.id)!;
    hist = pushState(hist, s2);
    expect(hist.current.root.tag).toBe('hole');

    // Undo clear → back to intros
    hist = undo(hist);
    expect(hist.current).toBe(s1);
    expect(hist.current.root.tag).toBe('intros');
  });
});
