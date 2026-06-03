/**
 * Map Lean InfoTree goal-states back onto proof-tree nodes.
 *
 * This is the second half of the WYSIWYG-on-Lean seam (the first being
 * `proofTreeToLean`). After the printed tactic block is elaborated by Lean, we
 * have goal states keyed by source range; here we match each proof node (by its
 * recorded range) to the goal state Lean reported there, producing the same
 * `Map<ProofNodeId, NodeGoalInfo>` the UI's prose/rendering already consume —
 * i.e. a drop-in replacement for the TT `replayEntireTree`.
 *
 * Goal text comes from Lean's tagged pretty-print, rendered to LaTeX through the
 * math editor's own renderer, so the visual output matches the rest of the UI.
 */
import type { ProofNodeId } from '../proof-tree/proof-tree';
import type { NodeGoalInfo, TypedHypothesis } from '../proof-tree/goal-computation';
import type { LeanGoal, LeanGoalState, LeanMessage } from './types';
import type { NodeRange } from './proofTreeToLean';
import { taggedToLatex } from './codeWithInfos';

/** Does goal `g` start at the same position as node range `r`? */
function sameStart(g: LeanGoal, r: NodeRange): boolean {
  return g.startLine === r.startLine && g.startCol === r.startCol;
}

/** The smallest-range goal whose start matches the node's tactic head. */
function goalForRange(goals: LeanGoal[], r: NodeRange): LeanGoal | null {
  let best: LeanGoal | null = null;
  let bestSpan = Number.POSITIVE_INFINITY;
  for (const g of goals) {
    if (!sameStart(g, r)) continue;
    const span = (g.endLine - g.startLine) * 100_000 + (g.endCol - g.startCol);
    if (span < bestSpan) {
      best = g;
      bestSpan = span;
    }
  }
  return best;
}

function hypsToTyped(state: LeanGoalState): TypedHypothesis[] {
  const out: TypedHypothesis[] = [];
  for (const h of state.hyps) {
    const type = taggedToLatex(h.type, '');
    for (const name of h.names) {
      out.push({ name, type });
    }
  }
  return out;
}

/** Build a NodeGoalInfo from a single Lean goal state. */
function nodeGoalInfoFromState(state: LeanGoalState): NodeGoalInfo {
  return {
    goalLatex: taggedToLatex(state.targetTagged, state.plain),
    hypotheses: hypsToTyped(state),
    ...(state.case ? { caseLabelLatex: state.case } : {}),
  };
}

export interface LeanGoalMappingInput {
  nodeRanges: Map<ProofNodeId, NodeRange>;
  holeNodeIds: Set<ProofNodeId>;
  goals: LeanGoal[];
  messages: LeanMessage[];
}

/**
 * Produce the per-node goal map the proof UI consumes, from Lean's analysis of
 * the printed tactic block. Each node that has a goal state at its range gets a
 * `NodeGoalInfo`; hole nodes with no remaining goal are treated as solved.
 */
export function mapLeanGoalsToNodes(input: LeanGoalMappingInput): Map<ProofNodeId, NodeGoalInfo> {
  const { nodeRanges, holeNodeIds, goals, messages } = input;
  const result = new Map<ProofNodeId, NodeGoalInfo>();

  // Index errors by start line for cheap per-node lookup.
  const errorByLine = new Map<number, LeanMessage>();
  for (const m of messages) {
    if (m.severity === 'error' && !errorByLine.has(m.startLine)) {
      errorByLine.set(m.startLine, m);
    }
  }

  for (const [nodeId, range] of nodeRanges) {
    const g = goalForRange(goals, range);
    const err = errorByLine.get(range.startLine);
    const isHole = holeNodeIds.has(nodeId);

    // A `sorry` that lands where the previous tactic already closed the goal
    // produces "no goals to be solved" — that's SOLVED, not a real error. Treat
    // such a hole as solved rather than surfacing the error.
    const isNoGoalsError = err !== undefined && /no goals/i.test(err.text);
    if (isHole && isNoGoalsError) {
      result.set(nodeId, { goalLatex: '', hypotheses: [], validation: { status: 'solved' } });
      continue;
    }

    if (g && g.goals.length > 0) {
      const info = nodeGoalInfoFromState(g.goals[0]);
      result.set(nodeId, err ? { ...info, tacticError: err.text } : info);
      continue;
    }

    // No goal at this range. For a hole that means the proof is complete here
    // (Lean reports a `sorry` warning, not an open goal we must show).
    if (isHole) {
      result.set(nodeId, { goalLatex: '', hypotheses: [], validation: { status: 'solved' } });
      continue;
    }

    if (err) {
      result.set(nodeId, { goalLatex: '', hypotheses: [], tacticError: err.text });
    }
  }

  return result;
}
