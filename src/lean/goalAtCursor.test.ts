import { describe, expect, test } from 'vitest';
import { pickGoalAtCursor } from './goalAtCursor';
import type { LeanGoal, LeanGoalState } from './types';

// Minimal goal-state from a plain string (the picker only cares about ranges).
const gs = (plain: string): LeanGoalState => ({
  hyps: [],
  targetTagged: { t: 'text', s: plain },
  plain,
});

const g = (sl: number, sc: number, el: number, ec: number, goals: string[]): LeanGoal => ({
  startLine: sl,
  startCol: sc,
  endLine: el,
  endCol: ec,
  goals: goals.map(gs),
});

describe('pickGoalAtCursor', () => {
  test('returns null when no range contains the cursor', () => {
    const goals = [g(6, 2, 6, 5, ['⊢ a'])];
    expect(pickGoalAtCursor(goals, 1, 0)).toBeNull();
  });

  test('picks the single containing range', () => {
    const goals = [g(6, 2, 6, 5, ['⊢ a'])];
    expect(pickGoalAtCursor(goals, 6, 3)?.goals.map((s) => s.plain)).toEqual(['⊢ a']);
  });

  test('innermost (smallest) range wins when nested', () => {
    const outer = g(9, 2, 11, 35, ['⊢ outer']);
    const inner = g(11, 4, 11, 35, ['⊢ inner']);
    expect(pickGoalAtCursor([outer, inner], 11, 10)?.goals.map((s) => s.plain)).toEqual(['⊢ inner']);
    expect(pickGoalAtCursor([outer, inner], 9, 3)?.goals.map((s) => s.plain)).toEqual(['⊢ outer']);
  });

  test('boundary columns are inclusive', () => {
    const goals = [g(6, 2, 6, 5, ['⊢ a'])];
    expect(pickGoalAtCursor(goals, 6, 2)).not.toBeNull();
    expect(pickGoalAtCursor(goals, 6, 5)).not.toBeNull();
    expect(pickGoalAtCursor(goals, 6, 1)).toBeNull();
    expect(pickGoalAtCursor(goals, 6, 6)).toBeNull();
  });

  test('multi-line range contains interior lines regardless of column', () => {
    const goals = [g(9, 2, 11, 35, ['⊢ x'])];
    expect(pickGoalAtCursor(goals, 10, 0)).not.toBeNull();
  });
});
