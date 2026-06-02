import { describe, expect, test } from 'vitest';
import { mapLeanGoalsToNodes } from './leanGoalMapping';
import type { LeanGoal, LeanMessage } from './types';
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
