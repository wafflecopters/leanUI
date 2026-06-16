/**
 * Build an `InteractiveGoal` (clickable subterms) from a Lean tagged goal target.
 *
 * `InteractiveGoalView` makes any DOM element whose id starts with `goal-`
 * clickable, reporting that id as the selected `GoalPath`. So we render the goal
 * to LaTeX with each tagged subexpression wrapped in `\htmlId{goal-<pos>}{…}`,
 * and build a `subtermMap` keyed by those ids. The path id encodes the Lean
 * `SubExpr.Pos`, which the suggestion provider uses to scope discovery (conv).
 */
import { codeWithInfosToMathRow } from './codeWithInfos';
import { renderStaticLatex } from '../math-editor/render';
import { mkGroup, mkRow, type MathNode, type MathRow } from '../math-editor/types';
import type { TaggedText } from './types';
import type { InteractiveGoal, SubtermInfo } from '../proof-tree/interactive-goal';

/** Prefix InteractiveGoalView recognizes as a clickable subterm id. */
const GOAL_PREFIX = 'goal-';

/** Encode/decode a Lean SubExpr.Pos in a goal- htmlId (positions contain `/`). */
export function goalIdForPos(pos: string): string {
  return `${GOAL_PREFIX}${pos.replace(/\//g, '_')}`;
}
export function posForGoalId(id: string): string | null {
  if (!id.startsWith(GOAL_PREFIX)) return null;
  return id.slice(GOAL_PREFIX.length).replace(/_/g, '/');
}

/**
 * Convert a tagged goal target into a MathRow whose subterm Groups carry
 * `goal-<pos>` htmlIds, plus the subterm map. We reuse codeWithInfosToMathRow's
 * structural recognition by converting WITHOUT its own subexpr wrappers, then
 * re-walking the tagged tree to wrap tagged spans with goal- ids. Simpler: build
 * the MathRow with wrapSubterms but relabel the Group htmlIds.
 */
export function taggedToInteractiveGoal(target: TaggedText): InteractiveGoal {
  const subtermMap = new Map<string, SubtermInfo>();

  // Walk the converted MathRow; for each Group whose htmlId is a subexpr id,
  // relabel to a goal- id and register it in the map.
  const relabel = (nodes: readonly MathNode[]): MathNode[] =>
    nodes.map((n) => {
      if (n.tag === 'Group') {
        const pos = n.htmlId.startsWith('subexpr:') ? n.htmlId.slice('subexpr:'.length) : n.htmlId;
        const goalId = goalIdForPos(pos);
        subtermMap.set(goalId, {
          htmlId: goalId,
          // We have no TTerm; downstream Lean suggestions key off the path string.
          term: { tag: 'Hole' } as unknown as SubtermInfo['term'],
          isAppOfConst: false,
        });
        return mkGroup(goalId, relabel(n.children));
      }
      return n;
    });

  const row: MathRow = codeWithInfosToMathRow(target, { wrapSubterms: true });
  const relabeled = mkRow(relabel(row.children));
  const latex = renderStaticLatex(relabeled);

  return { latex, binders: [], subtermMap, contextVarTypes: new Map() };
}
