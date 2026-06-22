import { describe, expect, test } from 'vitest';
import { enrichInductionCaseNames } from './enrichInductionCases';
import type { ProofNode } from '../proof-tree/proof-tree';
import type { NodeGoalInfo } from '../proof-tree/goal-computation';

function mkGoalMap(entries: [number, Partial<NodeGoalInfo>][]): Map<number, NodeGoalInfo> {
  const m = new Map<number, NodeGoalInfo>();
  for (const [id, p] of entries) {
    m.set(id, { goalLatex: p.goalLatex ?? '', hypotheses: p.hypotheses ?? [], ...p } as NodeGoalInfo);
  }
  return m;
}

// `induction n` with two bullet cases (no constructor names yet).
function bulletInduction(): ProofNode {
  return {
    tag: 'induction',
    id: 1,
    scrutinee: 'n',
    collapsed: false,
    cases: [
      { tag: 'case', id: 3, label: 'case', body: { tag: 'hole', id: 2 }, collapsed: false },
      { tag: 'case', id: 5, label: 'case', body: { tag: 'hole', id: 4 }, collapsed: false },
    ],
  };
}

describe('enrichInductionCaseNames', () => {
  test('fills constructor names + dagger-free params from the goal map', () => {
    const goalMap = mkGoalMap([
      [1, { hypotheses: [{ name: 'n', type: 'MyNat' }] }], // induction's incoming goal
      [3, { caseLabelLatex: 'zero', hypotheses: [] }],
      // succ introduces predecessor + IH, with Lean's inaccessible daggers.
      [5, { caseLabelLatex: 'succ', hypotheses: [{ name: 'a✝', type: 'MyNat' }, { name: 'a_ih✝', type: 'P a' }] }],
    ]);
    const { root, changed } = enrichInductionCaseNames(bulletInduction(), goalMap);
    expect(changed).toBe(true);
    const ind = root as Extract<ProofNode, { tag: 'induction' }>;
    expect(ind.cases[0].constructorName).toBe('zero');
    expect(ind.cases[0].constructorParamNames).toEqual([]);
    expect(ind.cases[1].constructorName).toBe('succ');
    // Daggers stripped; ctor arg in the label, IH kept separate (not in the label).
    expect(ind.cases[1].constructorParamNames).toEqual(['a']);
    expect(ind.cases[1].ihNames).toEqual(['a_ih']);
  });

  test('is idempotent — already-named cases are left alone (no oscillation)', () => {
    const goalMap = mkGoalMap([
      [1, { hypotheses: [{ name: 'n', type: 'MyNat' }] }],
      [3, { caseLabelLatex: 'zero', hypotheses: [] }],
      [5, { caseLabelLatex: 'succ', hypotheses: [{ name: 'a', type: 'MyNat' }, { name: 'a_ih', type: 'P a' }] }],
    ]);
    const once = enrichInductionCaseNames(bulletInduction(), goalMap);
    const twice = enrichInductionCaseNames(once.root, goalMap);
    expect(twice.changed).toBe(false);
    expect(twice.root).toBe(once.root); // unchanged identity
  });

  test('no change when the goal map has no case info yet', () => {
    const { root, changed } = enrichInductionCaseNames(bulletInduction(), mkGoalMap([]));
    expect(changed).toBe(false);
    expect(root).toBe(root);
  });

  test('uniquifies params that collide after dagger stripping', () => {
    const goalMap = mkGoalMap([
      [1, { hypotheses: [] }],
      [3, { caseLabelLatex: 'zero', hypotheses: [] }],
      [5, { caseLabelLatex: 'succ', hypotheses: [{ name: 'a✝', type: 'T' }, { name: 'a✝¹', type: 'T' }] }],
    ]);
    const { root } = enrichInductionCaseNames(bulletInduction(), goalMap);
    const ind = root as Extract<ProofNode, { tag: 'induction' }>;
    expect(ind.cases[1].constructorParamNames).toEqual(['a', 'a1']);
  });
});
