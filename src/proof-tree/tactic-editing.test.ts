import { beforeEach, describe, expect, test } from 'vitest';
import { createInitialState, mkApply, mkCase, mkDestructure, mkExact, mkHave, mkHole, mkInduction, mkIntros, mkRewrite, mkSimp, resetProofIds } from './proof-tree';
import { buildHaveTacticCommands, proofTreeToTacticCommands } from './tactic-command-bridge';
import { tacticCommandsToProofTree } from './tactic-to-tree';
import {
  addInductionCaseInProofTree,
  applyManualProofTreeTactic,
  applySuggestionToProofTreeState,
  clearProofTreeNode,
  commitHaveExprSourceInProofTree,
  commitProofTreeBinderRename,
  convertMathEditorSourceToUnicode,
  renameHaveBindingInProofTree,
  renameCaseParamInProofTree,
  renameIntroTokenInProofTree,
  removeInductionCaseInProofTree,
  rewriteBinderReferencesInSubtree,
  type ProofTreeManualTacticMode,
  toggleCaseCollapseInProofTree,
  toggleInductionCollapseInProofTree,
  toggleSimpCollapseInProofTree,
  updateHaveExprInProofTree,
} from './tactic-editing';

beforeEach(() => resetProofIds());

describe('applySuggestionToProofTreeState', () => {
  test('uses edited intro names through the shared action helper', () => {
    const state = createInitialState();
    const next = applySuggestionToProofTreeState(state, {
      id: 'intro-vars',
      label: 'Given x',
      description: 'Introduce the hypotheses',
      proposedNames: ['x'],
    }, {
      editingSuggestionId: 'intro-vars',
      editingNames: ['α', 'β'],
    });

    expect(next).not.toBeNull();
    expect(next?.root.tag).toBe('intros');
    if (!next || next.root.tag !== 'intros') return;
    expect(next.root.names).toEqual(['α', 'β']);
  });

  test('apply suggestions reuse the shared apply-command bridge for subgoal counts', () => {
    const state = createInitialState();
    const next = applySuggestionToProofTreeState(state, {
      id: 'apply-def-sym',
      label: 'apply sym',
      description: 'Apply sym',
      numSubgoals: 2,
    }, {});

    expect(next).not.toBeNull();
    expect(next?.root.tag).toBe('apply');
    if (!next || next.root.tag !== 'apply') return;
    expect(next.root.name).toBe('sym');
    expect(next.root.children).toHaveLength(2);
  });

  test('rewrite suggestions preserve structured-editor targeting metadata', () => {
    const state = createInitialState();
    const next = applySuggestionToProofTreeState(state, {
      id: 'rewrite-mulOneRight',
      label: 'rewrite← mulOneRight',
      description: 'Reverse rewrite',
      rewriteName: 'mulOneRight',
      reverse: true,
      occurrences: [1],
      targetHead: 'two',
    } as any, {});

    expect(next).not.toBeNull();
    expect(next?.root.tag).toBe('rewrite');
    if (!next || next.root.tag !== 'rewrite') return;
    expect(next.root.reverse).toBe(true);
    expect(next.root.occurrences).toEqual([1]);
    expect(next.root.targetHead).toBe('two');
  });

  test('hypothesis projection suggestions use shared tactic commands directly', () => {
    const state = createInitialState();
    const next = applySuggestionToProofTreeState(state, {
      id: 'hyp-proj-hLim-eps_delta',
      label: 'Use eps_delta',
      description: 'Introduce a helper hypothesis',
      tacticCommands: buildHaveTacticCommands('h', 'Limit.eps_delta hLim _ _'),
    }, {});

    expect(next).not.toBeNull();
    expect(next?.root.tag).toBe('have');
    if (!next || next.root.tag !== 'have') return;
    expect(next.root.name).toBe('h');
    // Verbatim, and no longer wrapped in parentheses: the TT round-trip used to
    // parse the argument into a term and re-print it, which added parens around
    // every application. An argument is Lean source now and passes through.
    expect(next.root.expr).toBe('Limit.eps_delta hLim _ _');
  });

});

describe('applyManualProofTreeTactic', () => {
  test('manual apply uses shared subgoal-count callback', () => {
    const state = createInitialState();
    const tacticMode: ProofTreeManualTacticMode = { tactic: 'apply' };
    const next = applyManualProofTreeTactic(state, tacticMode, 'zeroLeOne', {
      computeApplySubgoalCount: () => 0,
    });

    expect(next).not.toBeNull();
    expect(next?.root.tag).toBe('apply');
    if (!next || next.root.tag !== 'apply') return;
    expect(next.root.children).toHaveLength(0);
  });

  test('manual have input goes through the shared command bridge', () => {
    const state = createInitialState();
    const tacticMode: ProofTreeManualTacticMode = { tactic: 'have' };
    const next = applyManualProofTreeTactic(state, tacticMode, 'h := refl', {});

    expect(next).not.toBeNull();
    expect(next?.root.tag).toBe('have');
    if (!next || next.root.tag !== 'have') return;
    expect(next.root.name).toBe('h');
    expect(next.root.expr).toBe('refl');
    expect(next.root.child.tag).toBe('hole');
  });

  // REGRESSION (image #37): typing `-1` into the structured editor's exact
  // input must produce a proof node whose stored expr is "-1", not "?".
  // The flow: parseExpr("-1") → RatLit(-1, 1) → surfaceTermToString → string
  // stored on the ExactNode. Previously surfaceTermToString didn't handle
  // RatLit and returned '?', producing "Type definition not found: ?" on
  // validation.
  test('manual exact "-1" stores expr as "-1" (not "?")', () => {
    const state = createInitialState();
    const tacticMode: ProofTreeManualTacticMode = { tactic: 'exact' };
    const next = applyManualProofTreeTactic(state, tacticMode, '-1', {});
    expect(next).not.toBeNull();
    expect(next?.root.tag).toBe('exact');
    if (!next || next.root.tag !== 'exact') return;
    expect(next.root.expr).toBe('-1');
  });
});

describe('have editing helpers', () => {
  test('updateHaveExprInProofTree rewrites the targeted have expression', () => {
    const child = mkHole();
    const state = {
      root: mkHave('h', 'oldProof', child),
      cursor: { nodeId: child.id },
    };

    const next = updateHaveExprInProofTree(state, state.root.id, 'newProof');
    expect(next).not.toBeNull();
    expect(next?.root.tag).toBe('have');
    if (!next || next.root.tag !== 'have') return;
    expect(next.root.expr).toBe('newProof');
  });

  test('renameHaveBindingInProofTree updates downstream exact references', () => {
    const state = {
      root: mkHave('h', 'refl', mkExact('h')),
      cursor: { nodeId: 0 },
    };

    const next = renameHaveBindingInProofTree(state, state.root.id, 'k');
    expect(next).not.toBeNull();
    expect(next?.root.tag).toBe('have');
    if (!next || next.root.tag !== 'have') return;
    expect(next.root.name).toBe('k');
    expect(next.root.child.tag).toBe('exact');
    if (next.root.child.tag === 'exact') {
      expect(next.root.child.expr).toBe('k');
    }
  });

  test('commitHaveExprSourceInProofTree normalizes math-editor source and rejects no-op edits', () => {
    const child = mkHole();
    const state = {
      root: mkHave('h', 'α', child),
      cursor: { nodeId: child.id },
    };

    const noChange = commitHaveExprSourceInProofTree(state, state.root.id, '\\alpha');
    expect(noChange).toBeNull();

    const next = commitHaveExprSourceInProofTree(state, state.root.id, '\\beta');
    expect(next?.root.tag).toBe('have');
    if (!next || next.root.tag !== 'have') return;
    expect(next.root.expr).toBe('β');
    expect(convertMathEditorSourceToUnicode('\\delta')).toBe('δ');
  });


});

describe('hypothesis suggestion helpers', () => {

  test('hypothesis exact/apply suggestions reuse the shared bridge helpers', () => {
    const state = createInitialState();

    const exactNext = applySuggestionToProofTreeState(state, {
      id: 'exact-hyp-h',
      label: 'exact h',
      description: 'Use the hypothesis directly',
    }, {});
    expect(exactNext?.root.tag).toBe('exact');

    const applyNext = applySuggestionToProofTreeState(state, {
      id: 'apply-hyp-h',
      label: 'apply h',
      description: 'Apply the hypothesis',
      numSubgoals: 2,
    }, {});
    expect(applyNext?.root.tag).toBe('apply');
    if (applyNext?.root.tag === 'apply') {
      expect(applyNext.root.children).toHaveLength(2);
    }
  });
});

describe('shared structural editing helpers', () => {
  test('clearProofTreeNode replaces non-hole nodes with a fresh hole', () => {
    const state = {
      root: mkExact('refl'),
      cursor: { nodeId: 0 },
    };

    const next = clearProofTreeNode(state, state.root.id);
    expect(next).not.toBeNull();
    expect(next?.root.tag).toBe('hole');
    if (!next || next.root.tag !== 'hole') return;
    expect(next.cursor.nodeId).toBe(next.root.id);
    expect(next.root.id).not.toBe(state.root.id);
  });

  test('renameIntroTokenInProofTree rewrites the targeted intro binder', () => {
    const child = mkHole();
    const root = mkIntros(['x', 'y'], child);
    const state = {
      root,
      cursor: { nodeId: child.id },
    };

    const next = renameIntroTokenInProofTree(state, root.id, 1, 'z');
    expect(next?.root.tag).toBe('intros');
    if (!next || next.root.tag !== 'intros') return;
    expect(next.root.names).toEqual(['x', 'z']);
  });

  test('renameCaseParamInProofTree rewrites constructor-param labels through the shared helper', () => {
    const caseNode = mkCase('n = Succ k', mkHole(), 'Succ', ['k']);
    const root = mkInduction('n', [caseNode]);
    const state = {
      root,
      cursor: { nodeId: caseNode.body.id },
    };

    const next = renameCaseParamInProofTree(state, caseNode.id, 0, 'j');
    expect(next?.root.tag).toBe('induction');
    if (!next || next.root.tag !== 'induction') return;
    expect(next.root.cases[0].constructorParamNames).toEqual(['j']);
    expect(next.root.cases[0].label).toBe('n = Succ j');
    expect(next.root.cases[0].body.id).toBe(caseNode.body.id);
  });

  test('commitProofTreeBinderRename normalizes latex-style binder names across rename targets', () => {
    const haveState = {
      root: mkHave('h', 'proof', mkExact('h')),
      cursor: { nodeId: 0 },
    };
    const renamedHave = commitProofTreeBinderRename(haveState, {
      tag: 'have',
      nodeId: haveState.root.id,
    }, '\\delta_f');
    expect(renamedHave?.root.tag).toBe('have');
    if (!renamedHave || renamedHave.root.tag !== 'have') return;
    expect(renamedHave.root.name).toBe('δ_f');
    expect(renamedHave.root.child.tag).toBe('exact');
    if (renamedHave.root.child.tag !== 'exact') return;
    expect(renamedHave.root.child.expr).toBe('δ_f');

    const introChild = mkHole();
    const introRoot = mkIntros(['x'], introChild);
    const renamedIntro = commitProofTreeBinderRename({
      root: introRoot,
      cursor: { nodeId: introChild.id },
    }, {
      tag: 'introToken',
      nodeId: introRoot.id,
      nameIndex: 0,
    }, '\\alpha');
    expect(renamedIntro?.root.tag).toBe('intros');
    if (!renamedIntro || renamedIntro.root.tag !== 'intros') return;
    expect(renamedIntro.root.names).toEqual(['α']);

    const caseNode = mkCase('n = Succ k', mkHole(), 'Succ', ['k']);
    const inductionRoot = mkInduction('n', [caseNode]);
    const renamedCase = commitProofTreeBinderRename({
      root: inductionRoot,
      cursor: { nodeId: caseNode.body.id },
    }, {
      tag: 'caseParam',
      nodeId: caseNode.id,
      paramIndex: 0,
    }, '\\beta');
    expect(renamedCase?.root.tag).toBe('induction');
    if (!renamedCase || renamedCase.root.tag !== 'induction') return;
    expect(renamedCase.root.cases[0].constructorParamNames).toEqual(['β']);
    expect(renamedCase.root.cases[0].label).toBe('n = Succ β');
  });

  test('commitProofTreeBinderRename rejects empty or unchanged binder names', () => {
    const child = mkHole();
    const root = mkIntros(['x'], child);
    const state = {
      root,
      cursor: { nodeId: child.id },
    };

    expect(commitProofTreeBinderRename(state, {
      tag: 'introToken',
      nodeId: root.id,
      nameIndex: 0,
    }, '   ')).toBeNull();

    expect(commitProofTreeBinderRename(state, {
      tag: 'introToken',
      nodeId: root.id,
      nameIndex: 0,
    }, 'x')).toBeNull();
  });

  test('induction case helpers share add/remove behavior', () => {
    const firstCase = mkCase('n = Zero', mkHole(), 'Zero', []);
    const root = mkInduction('n', [firstCase]);
    const state = {
      root,
      cursor: { nodeId: firstCase.body.id },
    };

    const added = addInductionCaseInProofTree(state, root.id, 'new case');
    expect(added?.root.tag).toBe('induction');
    if (!added || added.root.tag !== 'induction') return;
    expect(added.root.cases).toHaveLength(2);
    expect(added.root.cases[0].body.id).toBe(firstCase.body.id);

    const removed = removeInductionCaseInProofTree(added, added.root.id, 1);
    expect(removed?.root.tag).toBe('induction');
    if (!removed || removed.root.tag !== 'induction') return;
    expect(removed.root.cases).toHaveLength(1);
    expect(removed.root.cases[0].body.id).toBe(firstCase.body.id);
  });

  test('induction case helpers reject invalid targets through the shared layer', () => {
    const state = createInitialState();
    expect(addInductionCaseInProofTree(state, state.root.id, 'new case')).toBeNull();

    const onlyCase = mkCase('n = Zero', mkHole(), 'Zero', []);
    const inductionState = {
      root: mkInduction('n', [onlyCase]),
      cursor: { nodeId: onlyCase.body.id },
    };
    expect(removeInductionCaseInProofTree(inductionState, inductionState.root.id, 0)).toBeNull();
    expect(removeInductionCaseInProofTree(inductionState, inductionState.root.id, 4)).toBeNull();
  });

  test('collapse helpers preserve cursor behavior through the shared wrapper layer', () => {
    const firstCase = mkCase('n = Zero', mkHole(), 'Zero', []);
    const secondCase = mkCase('n = Succ k', mkHole(), 'Succ', ['k']);
    const inductionRoot = mkInduction('n', [firstCase, secondCase]);
    const inductionState = {
      root: inductionRoot,
      cursor: { nodeId: secondCase.body.id },
    };

    const collapsedInduction = toggleInductionCollapseInProofTree(inductionState, inductionRoot.id);
    expect(collapsedInduction?.root.tag).toBe('induction');
    if (!collapsedInduction || collapsedInduction.root.tag !== 'induction') return;
    expect(collapsedInduction.root.collapsed).toBe(true);
    expect(collapsedInduction.cursor.nodeId).toBe(inductionRoot.id);

    const caseState = {
      root: inductionRoot,
      cursor: { nodeId: firstCase.body.id },
    };
    const collapsedCase = toggleCaseCollapseInProofTree(caseState, firstCase.id);
    expect(collapsedCase.root.tag).toBe('induction');
    if (collapsedCase.root.tag !== 'induction') return;
    expect(collapsedCase.root.cases[0].collapsed).toBe(true);
    expect(collapsedCase.cursor.nodeId).toBe(firstCase.id);

    const simpStep = mkExact('step');
    const simpChild = mkHole();
    const simpRoot = { ...mkSimp(['foo'], [simpStep], simpChild), collapsed: false as const };
    const simpState = {
      root: simpRoot,
      cursor: { nodeId: simpStep.id },
    };
    const collapsedSimp = toggleSimpCollapseInProofTree(simpState, simpRoot.id);
    expect(collapsedSimp?.root.tag).toBe('simp');
    if (!collapsedSimp || collapsedSimp.root.tag !== 'simp') return;
    expect(collapsedSimp.root.collapsed).toBe(true);
    expect(collapsedSimp.cursor.nodeId).toBe(simpRoot.id);
  });

});

describe('binder rename propagates to references in scope', () => {
  test('the reference walker covers every field that can name a hypothesis', () => {
    // One tree exercising every reference-carrying field: destructure scrutinee,
    // induction scrutinee, rewrite lemma + side goals, apply target, simp
    // lemma list, have typeExpr and expr, exact expr.
    const tree = mkDestructure('h1', ['p', 'q'],
      mkInduction('leTotal h1 x', [
        mkCase('?', mkRewrite('h1',
          mkApply('h1', [
            mkSimp(['h1', 'mulComm'], [], mkHave('h2', 'symm h1', mkHole(), 'x < h1')),
          ]),
          false, undefined, undefined, undefined, undefined, [mkExact('h1')])),
      ], true));

    const out = rewriteBinderReferencesInSubtree(tree, 'h1', 'hle');
    expect(out.tag).toBe('destructure');
    if (out.tag !== 'destructure') return;
    expect(out.scrutinee).toBe('hle');
    const ind = out.child;
    expect(ind.tag).toBe('induction');
    if (ind.tag !== 'induction') return;
    expect(ind.scrutinee).toBe('leTotal hle x');
    const rw = ind.cases[0].body;
    expect(rw.tag).toBe('rewrite');
    if (rw.tag !== 'rewrite') return;
    expect(rw.name).toBe('hle');
    expect(rw.sideGoals?.[0].tag).toBe('exact');
    if (rw.sideGoals?.[0].tag === 'exact') expect(rw.sideGoals[0].expr).toBe('hle');
    const app = rw.child;
    expect(app.tag).toBe('apply');
    if (app.tag !== 'apply') return;
    expect(app.name).toBe('hle');
    const simp = app.children[0];
    expect(simp.tag).toBe('simp');
    if (simp.tag !== 'simp') return;
    expect(simp.lemmas).toEqual(['hle', 'mulComm']);
    const have = simp.child;
    expect(have.tag).toBe('have');
    if (have.tag !== 'have') return;
    expect(have.expr).toBe('symm hle');
    expect(have.typeExpr).toBe('x < hle');
  });

  test('caseParam rename rewrites references in that case body only (cases leTotal repro)', () => {
    // The user's repro: `cases leTotal deltaF deltaG` binds `a` in the left
    // case; a later have references it. Renaming the case param must follow.
    const leftBody = mkHave('h3', 'ltLeTrans |x - x0| deltaF deltaG h1 a', mkHole());
    const rightBody = mkHave('h4', 'gtOfNot a h1', mkHole());
    const left = mkCase('leTotal deltaF deltaG = inl a', leftBody, 'inl', ['a']);
    const right = mkCase('leTotal deltaF deltaG = inr a', rightBody, 'inr', ['a']);
    const root = mkInduction('leTotal deltaF deltaG', [left, right], true);
    const state = { root, cursor: { nodeId: leftBody.id } };

    const next = commitProofTreeBinderRename(state, {
      tag: 'caseParam', nodeId: left.id, paramIndex: 0,
    }, 'hle');
    expect(next?.root.tag).toBe('induction');
    if (!next || next.root.tag !== 'induction') return;
    expect(next.root.cases[0].constructorParamNames).toEqual(['hle']);
    const newLeftBody = next.root.cases[0].body;
    expect(newLeftBody.tag).toBe('have');
    if (newLeftBody.tag !== 'have') return;
    expect(newLeftBody.expr).toBe('ltLeTrans |x - x0| deltaF deltaG h1 hle');
    // The sibling case binds its OWN `a` — a rename must not leak into it.
    expect(next.root.cases[1].constructorParamNames).toEqual(['a']);
    const newRightBody = next.root.cases[1].body;
    expect(newRightBody.tag).toBe('have');
    if (newRightBody.tag !== 'have') return;
    expect(newRightBody.expr).toBe('gtOfNot a h1');
  });

  test('introToken rename rewrites descendant exprs and scrutinees', () => {
    const root = mkIntros(['ε', 'hpos'],
      mkHave('h1', 'divPos ε hpos', mkExact('h1')));
    const next = commitProofTreeBinderRename({ root, cursor: { nodeId: root.id } }, {
      tag: 'introToken', nodeId: root.id, nameIndex: 1,
    }, 'εpos');
    expect(next?.root.tag).toBe('intros');
    if (!next || next.root.tag !== 'intros') return;
    expect(next.root.names).toEqual(['ε', 'εpos']);
    const have = next.root.child;
    expect(have.tag).toBe('have');
    if (have.tag !== 'have') return;
    expect(have.expr).toBe('divPos ε εpos');

    // An intro'd name referenced by a cases/induction SCRUTINEE follows too.
    const root2 = mkIntros(['deltaF'],
      mkInduction('leTotal deltaF deltaG', [mkCase('?', mkHole())], true));
    const next2 = commitProofTreeBinderRename({ root: root2, cursor: { nodeId: root2.id } }, {
      tag: 'introToken', nodeId: root2.id, nameIndex: 0,
    }, 'δF');
    expect(next2?.root.tag).toBe('intros');
    if (!next2 || next2.root.tag !== 'intros') return;
    const ind = next2.root.child;
    expect(ind.tag).toBe('induction');
    if (ind.tag !== 'induction') return;
    expect(ind.scrutinee).toBe('leTotal δF deltaG');
  });

  test('destructureName rename rewrites descendant exprs and a later destructure scrutinee', () => {
    const inner = mkDestructure('hDeltaF', ['dPos', 'dBound'],
      mkHave('h2', 'ltTrans deltaF dPos', mkHole()));
    const root = mkDestructure('hF', ['deltaF', 'hDeltaF'], inner);
    const state = { root, cursor: { nodeId: root.id } };

    // Renaming the second bound name reaches the LATER destructure's scrutinee.
    const next = commitProofTreeBinderRename(state, {
      tag: 'destructureName', nodeId: root.id, nameIndex: 1,
    }, 'hdf');
    expect(next?.root.tag).toBe('destructure');
    if (!next || next.root.tag !== 'destructure') return;
    expect(next.root.names).toEqual(['deltaF', 'hdf']);
    expect(next.root.scrutinee).toBe('hF');
    const newInner = next.root.child;
    expect(newInner.tag).toBe('destructure');
    if (newInner.tag !== 'destructure') return;
    expect(newInner.scrutinee).toBe('hdf');

    // Renaming the first bound name reaches a descendant have expr.
    const next2 = commitProofTreeBinderRename(state, {
      tag: 'destructureName', nodeId: root.id, nameIndex: 0,
    }, 'δF');
    expect(next2?.root.tag).toBe('destructure');
    if (!next2 || next2.root.tag !== 'destructure') return;
    const inner2 = next2.root.child;
    expect(inner2.tag).toBe('destructure');
    if (inner2.tag !== 'destructure') return;
    const have2 = inner2.child;
    expect(have2.tag).toBe('have');
    if (have2.tag !== 'have') return;
    expect(have2.expr).toBe('ltTrans δF dPos');
  });

  test('destructureName rename leaves the node\'s OWN scrutinee alone', () => {
    // `obtain ⟨a, b⟩ := a` shadows: the scrutinee `a` is the OUTER a, evaluated
    // before the new names bind, so renaming the bound `a` must not touch it.
    const root = mkDestructure('a', ['a', 'b'], mkExact('a'));
    const next = commitProofTreeBinderRename({ root, cursor: { nodeId: root.id } }, {
      tag: 'destructureName', nodeId: root.id, nameIndex: 0,
    }, 'c');
    expect(next?.root.tag).toBe('destructure');
    if (!next || next.root.tag !== 'destructure') return;
    expect(next.root.scrutinee).toBe('a');
    expect(next.root.names).toEqual(['c', 'b']);
    if (next.root.child.tag === 'exact') expect(next.root.child.expr).toBe('c');
  });

  test('reference rewriting respects word boundaries (a does not hit radd or a1)', () => {
    const root = mkIntros(['a'], mkExact('radd a1 (a) a'));
    const next = commitProofTreeBinderRename({ root, cursor: { nodeId: root.id } }, {
      tag: 'introToken', nodeId: root.id, nameIndex: 0,
    }, 'c');
    expect(next?.root.tag).toBe('intros');
    if (!next || next.root.tag !== 'intros') return;
    expect(next.root.names).toEqual(['c']);
    const child = next.root.child;
    expect(child.tag).toBe('exact');
    if (child.tag !== 'exact') return;
    expect(child.expr).toBe('radd a1 (c) c');
  });
});

describe('tray input normalization (latex → unicode)', () => {
  test('intros \\epsilon introduces ε, not a literal backslash name', async () => {
    const { applyManualProofTreeTactic } = await import('./tactic-editing');
    const { createInitialState, findNode } = await import('./proof-tree');
    const state = createInitialState();
    const next = applyManualProofTreeTactic(state, { tactic: 'intros' } as any, '\\epsilon hpos', {} as any);
    expect(next).not.toBeNull();
    const root = next!.root as any;
    expect(root.tag).toBe('intros');
    expect(root.names).toEqual(['ε', 'hpos']);
    expect(findNode(next!.root, next!.cursor.nodeId)).toBeTruthy();
  });
});

describe('obtain command replay', () => {
  // The command bridge EMITS `obtain` for destructure nodes; the replay side
  // dropped unknown commands silently, so a destructure vanished on any
  // command round-trip.
  test('obtain survives proofTreeToTacticCommands → tacticCommandsToProofTree', () => {
    const tree = mkDestructure('fProof', ['dfPos', 'fFn'], mkHole());
    const cmds = proofTreeToTacticCommands(tree);
    expect(cmds[0]).toEqual({ name: 'obtain', args: ['⟨dfPos, fFn⟩ := fProof'] });
    const back = tacticCommandsToProofTree(cmds);
    expect(back.tag).toBe('destructure');
    if (back.tag !== 'destructure') return;
    expect(back.scrutinee).toBe('fProof');
    expect(back.names).toEqual(['dfPos', 'fFn']);
    expect(back.child.tag).toBe('hole');
  });
});
