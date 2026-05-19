import { mkConstTT, mkPiTT } from '../compiler/surface';
import { createDefinitionsMap } from '../compiler/term';
import { beforeEach, describe, expect, test } from 'vitest';
import type { InductiveInfo } from './goal-computation';
import { createInitialState, mkCase, mkExact, mkHave, mkHole, mkInduction, mkIntros, mkSimp, resetProofIds } from './proof-tree';
import { buildProjectionApplicationSource, buildHaveTacticCommands } from './tactic-command-bridge';
import {
  addInductionCaseInProofTree,
  applyManualProofTreeTactic,
  applySuggestionToProofTreeState,
  clearProofTreeNode,
  hoistTermBuilderSlotToHave,
  insertHaveFromTermBuilder,
  renameHaveBindingInProofTree,
  renameCaseParamInProofTree,
  renameIntroTokenInProofTree,
  removeInductionCaseInProofTree,
  type ProofTreeManualTacticMode,
  toggleCaseCollapseInProofTree,
  toggleInductionCollapseInProofTree,
  toggleSimpCollapseInProofTree,
  updateHaveExprInProofTree,
} from './tactic-editing';

beforeEach(() => resetProofIds());

const natInfo: InductiveInfo = {
  name: 'Nat',
  constructors: [
    { name: 'Zero', type: mkConstTT('Nat') },
    { name: 'Succ', type: mkPiTT(mkConstTT('Nat'), mkConstTT('Nat'), 'n') },
  ],
};

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
    expect(next.root.expr).toBe('(Limit.eps_delta hLim _ _)');
  });

  test('hypothesis destructure suggestions share the command bridge and preserve cases metadata', () => {
    const state = createInitialState();
    const destructCtx = {
      hypotheses: [{ name: 'n', rawType: mkConstTT('Nat'), type: 'Nat' }],
      goal: '?',
    } as any;
    const next = applySuggestionToProofTreeState(state, {
      id: 'induction-n',
      label: 'Destructure n',
      labelLatex: '\\text{cases } n',
      description: 'Destructure the hypothesis',
    }, {
      typedContext: destructCtx,
      inductiveMap: new Map([['Nat', natInfo]]),
    });

    expect(next?.root.tag).toBe('induction');
    if (!next || next.root.tag !== 'induction') return;
    expect(next.root.isCases).toBe(true);
    expect(next.root.cases.map(c => c.constructorName)).toEqual(['Zero', 'Succ']);
    expect(next.root.cases[1].constructorParamNames).toEqual(['n1']);
  });
});

describe('applyManualProofTreeTactic', () => {
  test('manual apply uses shared subgoal-count callback', () => {
    const state = createInitialState();
    const tacticMode: ProofTreeManualTacticMode = { tactic: 'apply' };
    const next = applyManualProofTreeTactic(state, tacticMode, 'zeroLeOne', {
      kernelType: {} as any,
      definitions: {} as any,
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

  test('hoistTermBuilderSlotToHave inserts a new interactive have and rewrites the parent expr', () => {
    const currentHave = mkHave('main', 'foo (old)', mkHole());
    const state = {
      root: currentHave,
      cursor: { nodeId: currentHave.id },
    };

    const next = hoistTermBuilderSlotToHave(state, currentHave.id, {
      fnName: 'foo',
      fnDisplayName: 'foo',
      slots: [{
        index: 0,
        name: 'x',
        type: { tag: 'Const', name: 'Nat' } as any,
        typeLatex: 'Nat',
        implicit: false,
        metaId: '?m',
        value: { tag: 'Const', name: 'old' } as any,
        sourceExpr: 'old',
      }],
      slotSuggestions: new Map(),
      engine: {} as any,
      goalCtx: [],
    }, 0);

    expect(next).not.toBeNull();
    expect(next?.root.tag).toBe('have');
    if (!next || next.root.tag !== 'have') return;
    expect(next.root.name).toBe('hx');
    expect(next.root.expr).toBe('?');
    expect(next.root.proofTree?.tag).toBe('hole');
    expect(next.root.child.tag).toBe('have');
    if (next.root.child.tag === 'have') {
      expect(next.root.child.expr).toBe('foo (hx)');
    }
  });
});

describe('hypothesis suggestion helpers', () => {
  test('projection helper builds source with placeholders for remaining explicit args', () => {
    const definitions = createDefinitionsMap();
    definitions.terms.set('Limit.eps_delta', {
      name: 'Limit.eps_delta',
      namedArgMap: new Map([['R', 0]]),
      type: {
        tag: 'Binder',
        name: 'R',
        binderKind: { tag: 'BPi' },
        domain: { tag: 'Sort', level: { tag: 'ULit', n: 0 } },
        body: {
          tag: 'Binder',
          name: 'limitProof',
          binderKind: { tag: 'BPi' },
          domain: { tag: 'Const', name: 'Limit' },
          body: {
            tag: 'Binder',
            name: 'eps',
            binderKind: { tag: 'BPi' },
            domain: { tag: 'Const', name: 'Carrier' },
            body: {
              tag: 'Binder',
              name: 'epsPos',
              binderKind: { tag: 'BPi' },
              domain: { tag: 'Const', name: 'Rlt' },
              body: { tag: 'Const', name: 'Sigma' },
            },
          },
        },
      } as any,
    });

    expect(buildProjectionApplicationSource('Limit.eps_delta', 'hLim', definitions))
      .toBe('Limit.eps_delta hLim ? ?');
  });

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

    const removed = removeInductionCaseInProofTree(added, added.root.id, 1);
    expect(removed?.root.tag).toBe('induction');
    if (!removed || removed.root.tag !== 'induction') return;
    expect(removed.root.cases).toHaveLength(1);
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

  test('insertHaveFromTermBuilder commits a shared have command from filled slots', () => {
    const state = createInitialState();
    const next = insertHaveFromTermBuilder(state, {
      fnName: 'pairNat',
      fnDisplayName: 'pairNat',
      slots: [{
        index: 0,
        name: 'x',
        type: { tag: 'Const', name: 'Nat' } as any,
        typeLatex: 'Nat',
        implicit: false,
        metaId: '?m0',
        value: { tag: 'Const', name: 'n' } as any,
        sourceExpr: 'n',
      }],
      slotSuggestions: new Map(),
      engine: {} as any,
      goalCtx: [],
    });

    expect(next?.root.tag).toBe('have');
    if (!next || next.root.tag !== 'have') return;
    expect(next.root.name).toBe('h');
    expect(next.root.expr).toBe('(pairNat n)');
  });
});
