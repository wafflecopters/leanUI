import { describe, expect, test } from 'vitest';
import { enrichInductionCaseNames } from './enrichInductionCases';
import type { ProofNode } from '../proof-tree/proof-tree';
import type { NodeGoalInfo } from '../proof-tree/goal-types';

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

describe('composed case tags (cases under an outer named goal)', () => {
  // REGRESSION: `constructor` on `Limit` leaves a goal tagged `eps_delta`;
  // `cases hF` inside it reports the COMPOSED tag `eps_delta.mk`. A `with |`
  // alternative must be the constructor's own tag — Lean rejects the composed
  // form with "Invalid alternative name `eps_delta.mk`: Expected `mk`".
  test('uses only the last tag component as the constructor name', () => {
    const goalMap = mkGoalMap([
      [1, { hypotheses: [{ name: 'hF', type: '∃ δ, W δ' }] }],
      [3, { caseLabelLatex: 'eps_delta.mk', hypotheses: [
        { name: 'fst✝', type: 'ℝ' },
        { name: 'snd✝', type: 'W fst✝' },
      ] }],
    ]);
    const one: ProofNode = {
      tag: 'induction',
      id: 1,
      scrutinee: 'hF',
      collapsed: false,
      isCases: true,
      cases: [{ tag: 'case', id: 3, label: 'case', body: { tag: 'hole', id: 2 }, collapsed: false }],
    } as ProofNode;
    const { root, changed } = enrichInductionCaseNames(one, goalMap);
    expect(changed).toBe(true);
    const ind = root as Extract<ProofNode, { tag: 'induction' }>;
    expect(ind.cases[0].constructorName).toBe('mk');
    expect(ind.cases[0].constructorParamNames).toEqual(['fst', 'snd']);
  });
});

describe('shadowing avoidance', () => {
  // The SECOND `cases` on a DPair introduces `fst✝/snd✝` again; cleaning the
  // daggers to `fst/snd` would shadow the first pair and strand the proof
  // (the witness needs BOTH deltas: `rmin fst fst1`).
  test('cleaned names never shadow hypotheses already in scope', () => {
    const goalMap = mkGoalMap([
      [1, { hypotheses: [
        { name: 'hG', type: '∃ δ, W δ' },
        { name: 'fst', type: 'ℝ' },
        { name: 'snd', type: 'W fst' },
      ] }],
      [3, { caseLabelLatex: 'mk', hypotheses: [
        { name: 'fst', type: 'ℝ' },
        { name: 'snd', type: 'W fst' },
        { name: 'fst✝', type: 'ℝ' },
        { name: 'snd✝', type: 'V fst✝' },
      ] }],
    ]);
    const one: ProofNode = {
      tag: 'induction',
      id: 1,
      scrutinee: 'hG',
      collapsed: false,
      isCases: true,
      cases: [{ tag: 'case', id: 3, label: 'case', body: { tag: 'hole', id: 2 }, collapsed: false }],
    } as ProofNode;
    const { root } = enrichInductionCaseNames(one, goalMap);
    const ind = root as Extract<ProofNode, { tag: 'induction' }>;
    expect(ind.cases[0].constructorParamNames).toEqual(['fst1', 'snd1']);
  });

  // REGRESSION: a LONE unnamed case prints as a plain continuation, not a `·`
  // bullet (a bullet focuses one goal, hiding the rest from validation), so the
  // case node has no source range and Lean reports nothing AT it — the tag is on
  // the head of its body instead. Reading only the case's own id left
  // `cases fProof` on a one-constructor structure permanently unnamed, with its
  // fields stuck as inaccessible `fst✝`/`snd✝` that the proof cannot refer to.
  test('a case with no goal of its own is named from the head of its body', () => {
    const lone: ProofNode = {
      tag: 'induction',
      id: 1,
      scrutinee: 'fProof',
      collapsed: false,
      isCases: true,
      cases: [{ tag: 'case', id: 3, label: '?', body: { tag: 'hole', id: 2 }, collapsed: false }],
    };
    const goalMap = mkGoalMap([
      [1, { hypotheses: [{ name: 'fProof', type: 'EpsDeltaWitness f x0 L (ε / 2) deltaF' }] }],
      // Nothing at id 3 — the case itself. The body carries Lean's composed tag.
      [2, {
        caseLabelLatex: 'eps_delta.mk.mk.mk',
        hypotheses: [
          { name: 'fProof', type: 'EpsDeltaWitness f x0 L (ε / 2) deltaF' },
          { name: 'fst✝', type: '0 < deltaF' },
          { name: 'snd✝', type: '∀ x, …' },
        ],
      }],
    ]);
    const { root, changed } = enrichInductionCaseNames(lone, goalMap);
    expect(changed).toBe(true);
    const ind = root as Extract<ProofNode, { tag: 'induction' }>;
    // Composed tag → the constructor's OWN name, which is what `| mk … =>` wants.
    expect(ind.cases[0].constructorName).toBe('mk');
    expect(ind.cases[0].constructorParamNames).toEqual(['fst', 'snd']);
    // And the display label, so the prose stops reading "Case (case)".
    expect(ind.cases[0].label).toBe('mk');
  });
});
