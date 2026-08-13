import { ProofNodeId } from './proof-tree';
import { ProseItem, ProseItemKind } from './proof-prose';

export interface ProseGoalLead {
  readonly goalLatex: string;
  readonly lead: string;
  readonly inline: boolean;
}

function isStructuralBoundary(kind: ProseItemKind): boolean {
  return kind.tag === 'caseHeader' || kind.tag === 'inductionHeader';
}

function stopsInteractiveGoalSearch(kind: ProseItemKind): boolean {
  return kind.tag === 'hole' || kind.tag === 'qed' || kind.tag === 'exact';
}

export function proseItemShowsVisibleGoal(kind: ProseItemKind): boolean {
  switch (kind.tag) {
    case 'unfold':
    case 'rewrite':
    case 'simp':
    case 'intro':
    case 'have':
    case 'suffices':
    case 'subgoalHeader':
      return !!kind.goalLatex;
    case 'apply':
      return (kind.subgoalLatex?.length ?? 0) <= 1 && !!kind.subgoalLatex?.[0];
    case 'calcChain':
      return true;
    default:
      return false;
  }
}

export function proseItemCanAnchorInteractiveGoal(kind: ProseItemKind): boolean {
  switch (kind.tag) {
    case 'unfold':
    case 'rewrite':
    case 'simp':
      return true;
    case 'intro':
      return !!kind.goalLatex;
    case 'apply':
      return true;
    default:
      return false;
  }
}

export function findLastInteractiveGoalStepIndex(items: readonly ProseItem[]): number {
  const holeIdx = items.findIndex((item) => item.isCursor && item.kind.tag === 'hole');
  if (holeIdx < 0) return -1;

  for (let idx = holeIdx - 1; idx >= 0; idx--) {
    const kind = items[idx].kind;
    if (proseItemCanAnchorInteractiveGoal(kind)) return idx;
    if (isStructuralBoundary(kind) || stopsInteractiveGoalSearch(kind)) break;
  }

  return -1;
}

export function findNextHoleNodeId(items: readonly ProseItem[], startIndex: number): ProofNodeId | undefined {
  for (let idx = startIndex + 1; idx < items.length; idx++) {
    const kind = items[idx].kind;
    if (kind.tag === 'hole') return items[idx].nodeId;
    if (isStructuralBoundary(kind)) break;
  }
  return undefined;
}

/**
 * Approximate the RENDERED glyph count of a latex string.
 *
 * The inline-vs-display decision must depend on what the READER sees. Raw
 * latex length counts invisible markup — every subexpression is wrapped in
 * `\htmlId{subexpr:...}{...}` for click-targeting, so a goal as small as `ℝ`
 * is 31 characters of latex and would never qualify as inline. Strip the
 * wrappers and count each remaining command (`\varepsilon`, `\mathbb`) as one
 * glyph, which is what it renders as.
 */
export function visibleLatexLength(latex: string): number {
  return latex
    .replace(/\\htmlId\{[^{}]*\}/g, '')
    .replace(/\\[a-zA-Z]+/g, 'X')
    .replace(/[{}]/g, '')
    .replace(/\s+/g, '')
    .length;
}

export function buildProseGoalLead(
  goalLatex: string | undefined,
  isValueType?: boolean,
  inlineThreshold = 30,
  /** Force display mode (the row being edited expands for room to work). */
  expand = false,
): ProseGoalLead | null {
  if (!goalLatex) return null;
  return {
    goalLatex,
    // A data goal is a value to PICK, not a proposition to prove — say so.
    lead: isValueType ? 'We must choose a value of type' : 'We must show',
    inline: !expand && visibleLatexLength(goalLatex) <= inlineThreshold,
  };
}

/**
 * Where to put a hover tooltip so it stays on screen.
 *
 * Centring the tooltip on its anchor is right until the content is a long
 * formula and the anchor sits near an edge: the induction hypothesis' type is
 * wider than the window, so half of it — including the whole `∀ ws ∈ List(G),
 * |ws|` prefix — was clipped away, and the tooltip appeared to START at `< |r|`.
 * Clamp the ideal centred position into the viewport instead.
 */
export function clampTooltipLeft(
  anchorCenter: number,
  tooltipWidth: number,
  viewportWidth: number,
  margin = 8,
): number {
  const ideal = anchorCenter - tooltipWidth / 2;
  // When the tooltip is wider than the viewport there is no non-negative
  // placement; pin it to the left margin so the START of the formula is what
  // survives, which is the part that says what the statement is about.
  const rightMost = Math.max(margin, viewportWidth - tooltipWidth - margin);
  return Math.min(Math.max(ideal, margin), rightMost);
}

/** Above the anchor when it fits, otherwise below it. */
export function tooltipTop(
  anchorTop: number,
  anchorBottom: number,
  tooltipHeight: number,
  gap = 6,
): number {
  const above = anchorTop - tooltipHeight - gap;
  return above >= gap ? above : anchorBottom + gap;
}
