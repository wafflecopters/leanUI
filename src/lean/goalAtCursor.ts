import type { LeanGoal } from './types';

/**
 * Pick the goal state to show for the cursor — the Lean InfoView behavior.
 *
 * Goal ranges use Lean's convention: 1-based line, 0-based column. The cursor is
 * given in the SAME convention (callers translate Monaco's 1-based column down by
 * one before calling).
 *
 * When several tactic ranges contain the cursor (nested tactic blocks), the
 * smallest (innermost) wins — that's the most specific goal at that point.
 * Returns null when the cursor isn't inside any tactic range.
 */
export function pickGoalAtCursor(goals: LeanGoal[], line: number, col: number): LeanGoal | null {
  let best: LeanGoal | null = null;
  let bestSpan = Number.POSITIVE_INFINITY;
  for (const g of goals) {
    if (!containsPos(g, line, col)) continue;
    const span = rangeSpan(g);
    if (span < bestSpan) {
      best = g;
      bestSpan = span;
    }
  }
  return best;
}

function containsPos(g: LeanGoal, line: number, col: number): boolean {
  const afterStart = line > g.startLine || (line === g.startLine && col >= g.startCol);
  const beforeEnd = line < g.endLine || (line === g.endLine && col <= g.endCol);
  return afterStart && beforeEnd;
}

/** A monotonic measure of range size for "smallest range wins" comparisons. */
function rangeSpan(g: LeanGoal): number {
  const LINE_WEIGHT = 100_000;
  return (g.endLine - g.startLine) * LINE_WEIGHT + (g.endCol - g.startCol);
}
