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

export function buildProseGoalLead(
  goalLatex: string | undefined,
  isValueType?: boolean,
  inlineThreshold = 30,
): ProseGoalLead | null {
  if (!goalLatex) return null;
  return {
    goalLatex,
    lead: isValueType ? 'We need a value of type' : 'We must show',
    inline: goalLatex.length <= inlineThreshold,
  };
}
