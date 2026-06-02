import { describe, expect, test } from 'vitest';
import { groupGoalsByDeclaration, declKey } from './declProofSteps';
import type { LeanDeclaration, LeanGoal } from './types';

const decl = (name: string, line: number, kind: LeanDeclaration['kind'] = 'theorem'): LeanDeclaration => ({
  name,
  kind,
  prettyType: '',
  line,
  col: 0,
});

const goal = (startLine: number): LeanGoal => ({
  startLine,
  startCol: 2,
  endLine: startLine,
  endCol: 5,
  goals: [{ hyps: [], targetTagged: { t: 'text', s: `g${startLine}` }, plain: `g${startLine}` }],
});

describe('groupGoalsByDeclaration', () => {
  test('assigns each goal to the declaration whose span contains it', () => {
    const decls = [decl('first', 1), decl('second', 10)];
    const goals = [goal(2), goal(5), goal(12)];
    const m = groupGoalsByDeclaration(decls, goals);
    expect(m.get(declKey(decls[0]))!.map((s) => s.startLine)).toEqual([2, 5]);
    expect(m.get(declKey(decls[1]))!.map((s) => s.startLine)).toEqual([12]);
  });

  test('the last declaration owns everything after its start', () => {
    const decls = [decl('only', 3)];
    const m = groupGoalsByDeclaration(decls, [goal(4), goal(99)]);
    expect(m.get(declKey(decls[0]))!).toHaveLength(2);
  });

  test('goals before the first declaration are dropped', () => {
    const decls = [decl('d', 5)];
    const m = groupGoalsByDeclaration(decls, [goal(1), goal(6)]);
    expect(m.get(declKey(decls[0]))!.map((s) => s.startLine)).toEqual([6]);
  });

  test('handles unsorted declaration input by sorting on position', () => {
    const decls = [decl('late', 20), decl('early', 1)];
    const goals = [goal(2), goal(25)];
    const m = groupGoalsByDeclaration(decls, goals);
    expect(m.get(declKey(decls[1]))!.map((s) => s.startLine)).toEqual([2]); // early
    expect(m.get(declKey(decls[0]))!.map((s) => s.startLine)).toEqual([25]); // late
  });

  test('steps within a declaration are sorted by position', () => {
    const decls = [decl('d', 1)];
    const m = groupGoalsByDeclaration(decls, [goal(8), goal(3), goal(5)]);
    expect(m.get(declKey(decls[0]))!.map((s) => s.startLine)).toEqual([3, 5, 8]);
  });

  test('empty declarations → empty map', () => {
    expect(groupGoalsByDeclaration([], [goal(1)]).size).toBe(0);
  });
});
