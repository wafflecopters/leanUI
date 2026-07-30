import { describe, expect, test } from 'vitest';
import { mapLeanGoalsToNodes } from './leanGoalMapping';
import type { LeanGoal, LeanGoalState, LeanMessage } from './types';
import type { NodeRange } from './proofTreeToLean';

const range = (line: number): NodeRange => ({ startLine: line, startCol: 2, endLine: line, endCol: 10 });

const goalAt = (line: number, target: string, hyps: { names: string[]; type: string }[] = [], kase?: string): LeanGoal => ({
  startLine: line,
  startCol: 2,
  endLine: line,
  endCol: 10,
  goals: [
    {
      ...(kase ? { case: kase } : {}),
      hyps: hyps.map((h) => ({ names: h.names, type: { t: 'text', s: h.type } })),
      targetTagged: { t: 'text', s: target },
      plain: target,
    },
  ],
});

describe('mapLeanGoalsToNodes', () => {
  test('maps a goal to the node whose range starts at the same position', () => {
    const nodeRanges = new Map([[1, range(5)]]);
    const goals = [goalAt(5, 'n + 0 = n', [{ names: ['n'], type: 'Nat' }])];
    const m = mapLeanGoalsToNodes({ nodeRanges, holeNodeIds: new Set(), goals, messages: [] });
    const info = m.get(1)!;
    expect(info.goalLatex).toContain('n');
    expect(info.hypotheses).toHaveLength(1);
    expect(info.hypotheses[0].name).toBe('n');
  });

  test('expands multi-name hypotheses into one TypedHypothesis each', () => {
    const nodeRanges = new Map([[1, range(3)]]);
    const goals = [goalAt(3, 'g', [{ names: ['a', 'b'], type: 'Nat' }])];
    const m = mapLeanGoalsToNodes({ nodeRanges, holeNodeIds: new Set(), goals, messages: [] });
    expect(m.get(1)!.hypotheses.map((h) => h.name)).toEqual(['a', 'b']);
  });

  test('carries the case label', () => {
    const nodeRanges = new Map([[7, range(9)]]);
    const goals = [goalAt(9, '0 + b = b', [{ names: ['b'], type: 'Nat' }], 'zero')];
    const m = mapLeanGoalsToNodes({ nodeRanges, holeNodeIds: new Set(), goals, messages: [] });
    expect(m.get(7)!.caseLabelLatex).toBe('zero');
  });

  test('a hole with no remaining goal is marked solved', () => {
    const nodeRanges = new Map([[1, range(4)]]);
    const m = mapLeanGoalsToNodes({ nodeRanges, holeNodeIds: new Set([1]), goals: [], messages: [] });
    expect(m.get(1)!.validation).toEqual({ status: 'solved' });
  });

  test('attaches a tactic error when Lean reports an error on the node line', () => {
    const nodeRanges = new Map([[1, range(5)]]);
    const err: LeanMessage = { severity: 'error', startLine: 5, startCol: 2, endLine: 5, endCol: 8, text: 'rw failed' };
    const goals = [goalAt(5, 'g')];
    const m = mapLeanGoalsToNodes({ nodeRanges, holeNodeIds: new Set(), goals, messages: [err] });
    expect(m.get(1)!.tacticError).toBe('rw failed');
  });

  test('error on a non-hole node with no goal still records the error', () => {
    const nodeRanges = new Map([[2, range(6)]]);
    const err: LeanMessage = { severity: 'error', startLine: 6, startCol: 2, endLine: 6, endCol: 8, text: 'boom' };
    const m = mapLeanGoalsToNodes({ nodeRanges, holeNodeIds: new Set(), goals: [], messages: [err] });
    expect(m.get(2)!.tacticError).toBe('boom');
  });

  test('innermost (smallest) matching goal range wins', () => {
    const nodeRanges = new Map([[1, range(5)]]);
    const wide: LeanGoal = { startLine: 5, startCol: 2, endLine: 9, endCol: 0, goals: [{ hyps: [], targetTagged: { t: 'text', s: 'WIDE' }, plain: 'WIDE' }] };
    const narrow = goalAt(5, 'NARROW');
    const m = mapLeanGoalsToNodes({ nodeRanges, holeNodeIds: new Set(), goals: [wide, narrow], messages: [] });
    expect(m.get(1)!.goalLatex).toContain('NARROW');
  });

  test('nodes with no goal and no error are omitted', () => {
    const nodeRanges = new Map([[1, range(5)]]);
    const m = mapLeanGoalsToNodes({ nodeRanges, holeNodeIds: new Set(), goals: [], messages: [] });
    expect(m.has(1)).toBe(false);
  });
});

// A goal that supplies a VALUE reads differently from one that states a claim.
// `apply ltLeTrans` leaves `⊢ ℝ` — not something to prove, the midpoint to
// choose — and Lean says which goal that is: its case tag is the name of the
// metavariable the siblings are waiting on.
describe('value goals (choose a term, not prove a claim)', () => {
  const state = (target: string, caseTag?: string): LeanGoalState => ({
    ...(caseTag ? { case: caseTag } : {}),
    hyps: [],
    targetTagged: { t: 'text' as const, s: target },
    plain: `⊢ ${target}`,
  });

  /** All three ltLeTrans goals reported at one hole, as Lean reports them. */
  const goalsAt = (line: number, states: ReturnType<typeof state>[]) => [
    { startLine: line, startCol: 2, endLine: line, endCol: 8, goals: states },
  ];

  test('the goal the siblings depend on is flagged as a value', () => {
    const ranges = new Map([[1, { startLine: 10, startCol: 2, endLine: 10, endCol: 8 }]]);
    const map = mapLeanGoalsToNodes({
      nodeRanges: ranges,
      holeNodeIds: new Set([1]),
      goals: goalsAt(10, [state('ℝ', 'hb.b'), state('0 < ?hb.b', 'hb.hab')]),
      messages: [],
    });
    expect(map.get(1)?.isValueType).toBe(true);
  });

  test('a goal nothing depends on is an ordinary claim', () => {
    const ranges = new Map([[1, { startLine: 10, startCol: 2, endLine: 10, endCol: 8 }]]);
    const map = mapLeanGoalsToNodes({
      nodeRanges: ranges,
      holeNodeIds: new Set([1]),
      goals: goalsAt(10, [state('0 < ?hb.b', 'hb.hab'), state('ℝ', 'hb.b')]),
      messages: [],
    });
    expect(map.get(1)?.isValueType).toBeUndefined();
  });

  test('an untagged goal is never a value goal', () => {
    const ranges = new Map([[1, { startLine: 10, startCol: 2, endLine: 10, endCol: 8 }]]);
    const map = mapLeanGoalsToNodes({
      nodeRanges: ranges,
      holeNodeIds: new Set([1]),
      goals: goalsAt(10, [state('ℝ'), state('0 < ?hb.b', 'hb.hab')]),
      messages: [],
    });
    expect(map.get(1)?.isValueType).toBeUndefined();
  });

  // REGRESSION: the pending-metavar heuristic dies the moment the value is
  // SUPPLIED — `exact 1` assigns ?hb.b, siblings stop mentioning it, and the
  // permanent rendering said "We must show ℝ" again. The extractor now records
  // the dependency at the split itself (`valueCaseTags`), which never goes stale.
  test('an explicit valueCaseTag marks the goal even with no pending metavar anywhere', () => {
    const ranges = new Map([[1, { startLine: 10, startCol: 2, endLine: 10, endCol: 8 }]]);
    const map = mapLeanGoalsToNodes({
      nodeRanges: ranges,
      holeNodeIds: new Set([1]),
      goals: [{ ...goalsAt(10, [state('ℝ', 'hb.b'), state('0 ≤ 1', 'hb.hab')])[0], valueCaseTags: ['hb.b'] }],
      messages: [],
    });
    expect(map.get(1)?.isValueType).toBe(true);
  });

  // A from-scratch preset states its claims in Type — every goal is non-Prop
  // there, so non-Prop-ness alone must NOT flag a goal as a value to choose.
  // Only the sibling-dependency record (valueCaseTags) does.
  test('a non-Prop goal with no dependency tag stays an ordinary claim', () => {
    const ranges = new Map([[1, { startLine: 10, startCol: 2, endLine: 10, endCol: 8 }]]);
    const map = mapLeanGoalsToNodes({
      nodeRanges: ranges,
      holeNodeIds: new Set([1]),
      goals: goalsAt(10, [{ ...state('0 < ε / 2', 'h1'), isProp: false }]),
      messages: [],
    });
    expect(map.get(1)?.isValueType).toBeUndefined();
  });

  // Lean CLEARS a goal's case tag once its `case b => …` block focuses it, so
  // the focused goal state is tagless and nothing in Lean's output connects it
  // back to `valueCaseTags`. The TREE remembers which branch the node proves.
  test('a tagless focused goal is matched to its branch via the tree', () => {
    const ranges = new Map([[13, { startLine: 10, startCol: 6, endLine: 10, endCol: 13 }]]);
    const map = mapLeanGoalsToNodes({
      nodeRanges: ranges,
      holeNodeIds: new Set(),
      goals: [
        {
          startLine: 10,
          startCol: 6,
          endLine: 10,
          endCol: 13,
          valueCaseTags: ['b'],
          goals: [state('ℝ')], // no `case` — Lean cleared it on focus
        },
      ],
      messages: [],
      branchTags: new Map([[13, 'b']]),
    });
    expect(map.get(13)?.isValueType).toBe(true);
  });

  test('a metavariable mentioned in a DIFFERENT branch still counts', () => {
    // Lean reports the remaining goals at each branch, so the value goal's own
    // position may list only itself — the dependency shows up elsewhere.
    const ranges = new Map([
      [1, { startLine: 10, startCol: 2, endLine: 10, endCol: 8 }],
      [2, { startLine: 20, startCol: 2, endLine: 20, endCol: 8 }],
    ]);
    const map = mapLeanGoalsToNodes({
      nodeRanges: ranges,
      holeNodeIds: new Set([1, 2]),
      goals: [
        ...goalsAt(10, [state('0 < ?hb.b', 'hb.hab')]),
        ...goalsAt(20, [state('ℝ', 'hb.b')]),
      ],
      messages: [],
    });
    expect(map.get(2)?.isValueType).toBe(true);
  });
});
