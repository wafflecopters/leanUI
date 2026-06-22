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
/** Plain text of a tagged subtree (concatenated leaves), trimmed. */
export function taggedText(tt: TaggedText): string {
  switch (tt.t) {
    case 'text':
      return tt.s;
    case 'append':
      return tt.kids.map(taggedText).join('');
    case 'tag':
      return taggedText(tt.child);
  }
}

/**
 * Map each subexpression's `goal-<pos>` id to its plain text, so the suggestion
 * layer knows WHAT was clicked (e.g. a bare variable `n` → offer induction n).
 */
export function subtermTextMap(target: TaggedText): Map<string, string> {
  const out = new Map<string, string>();
  const walk = (tt: TaggedText) => {
    if (tt.t === 'tag') {
      out.set(goalIdForPos(tt.pos), taggedText(tt).trim());
      walk(tt.child);
    } else if (tt.t === 'append') {
      tt.kids.forEach(walk);
    }
  };
  walk(target);
  return out;
}

export function taggedToInteractiveGoal(target: TaggedText): InteractiveGoal {
  const subtermMap = new Map<string, SubtermInfo>();

  // Walk the converted MathRow, relabeling every Group's subexpr htmlId to a
  // clickable goal- id — recursing through ALL compound-node slots (Frac, Sup,
  // Sub, SubSup, BigOp below/above/body, Accent, Delimiter), not just Group
  // children, so subterms inside ∑ bounds / fractions / sub-superscripts are
  // clickable too.
  const relabelRow = (row: MathRow): MathRow => mkRow(relabel(row.children));
  const relabel = (nodes: readonly MathNode[]): MathNode[] =>
    nodes.map((n): MathNode => {
      switch (n.tag) {
        case 'Group': {
          const pos = n.htmlId.startsWith('subexpr:') ? n.htmlId.slice('subexpr:'.length) : n.htmlId;
          const goalId = goalIdForPos(pos);
          subtermMap.set(goalId, {
            htmlId: goalId,
            term: { tag: 'Hole' } as unknown as SubtermInfo['term'],
            isAppOfConst: false,
          });
          return mkGroup(goalId, relabel(n.children));
        }
        case 'Frac':
          return { ...n, numer: relabelRow(n.numer), denom: relabelRow(n.denom) };
        case 'Sup':
          return { ...n, base: relabelRow(n.base), sup: relabelRow(n.sup) };
        case 'Sub':
          return { ...n, base: relabelRow(n.base), sub: relabelRow(n.sub) };
        case 'SubSup':
          return { ...n, base: relabelRow(n.base), sub: relabelRow(n.sub), sup: relabelRow(n.sup) };
        case 'BigOp':
          return {
            ...n,
            below: n.below ? relabelRow(n.below) : null,
            above: n.above ? relabelRow(n.above) : null,
            body: relabelRow(n.body),
          };
        case 'Accent':
          return { ...n, body: relabelRow(n.body) };
        case 'Delimiter':
          return { ...n, inner: relabelRow(n.inner) };
        default:
          return n;
      }
    });

  const row: MathRow = codeWithInfosToMathRow(target, { wrapSubterms: true });
  const relabeled = mkRow(relabel(row.children));
  const latex = renderStaticLatex(relabeled);

  return { latex, binders: [], subtermMap, contextVarTypes: new Map() };
}
