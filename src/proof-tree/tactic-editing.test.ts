import { mkConstTT } from '../compiler/surface';
import { createDefinitionsMap } from '../compiler/term';
import { beforeEach, describe, expect, test } from 'vitest';
import { createInitialState, resetProofIds } from './proof-tree';
import {
  applyManualProofTreeTactic,
  applyHypothesisSuggestionToProofTreeState,
  applySuggestionToProofTreeState,
  buildProjectionApplicationSource,
  type ProofTreeManualTacticMode,
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

  test('hypothesis projection suggestion now goes through shared pure helper', () => {
    const state = createInitialState();
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

    const next = applyHypothesisSuggestionToProofTreeState(state, {
      id: 'hyp-proj-0',
      label: 'Use projection',
      description: 'Introduce a helper hypothesis',
      applyCtorName: 'Limit.eps_delta',
    }, 'hLim', { definitions });

    expect(next).not.toBeNull();
    expect(next?.root.tag).toBe('have');
    if (!next || next.root.tag !== 'have') return;
    expect(next.root.expr).toBe('(Limit.eps_delta hLim _ _)');
  });

  test('hypothesis exact/apply/destruct suggestions reuse the shared bridge helpers', () => {
    const state = createInitialState();

    const exactNext = applyHypothesisSuggestionToProofTreeState(state, {
      id: 'hyp-exact-0',
      label: 'exact h',
      description: 'Use the hypothesis directly',
    }, 'h', {});
    expect(exactNext?.root.tag).toBe('exact');

    const applyNext = applyHypothesisSuggestionToProofTreeState(state, {
      id: 'hyp-apply-0',
      label: 'apply h',
      description: 'Apply the hypothesis',
      numSubgoals: 2,
    }, 'h', {});
    expect(applyNext?.root.tag).toBe('apply');
    if (applyNext?.root.tag === 'apply') {
      expect(applyNext.root.children).toHaveLength(2);
    }

    const destructCtx = {
      hypotheses: [{ name: 'n', rawType: mkConstTT('Nat'), type: 'Nat' }],
      goal: '?',
    } as any;
    const destructNext = applyHypothesisSuggestionToProofTreeState(state, {
      id: 'hyp-destruct-0',
      label: 'cases n',
      description: 'Destructure the hypothesis',
    }, 'n', { typedContext: destructCtx });
    expect(destructNext?.root.tag).toBe('induction');
  });
});
