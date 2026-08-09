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
import type { ProofNode, ProofNodeId } from '../proof-tree/proof-tree';
import { rewriteSideGoals } from '../proof-tree/proof-tree';
import type { NodeGoalInfo, TypedHypothesis } from '../proof-tree/goal-types';
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

/**
 * The goals that SUPPLY A VALUE rather than state something to prove.
 *
 * `apply ltLeTrans` on `0 < 2` leaves three goals:
 *
 *     case hb.hab  ⊢ 0 < ?hb.b
 *     case hb.hbc  ⊢ ?hb.b ≤ 2
 *     case hb.b    ⊢ ℝ          ← this one is the midpoint you have to choose
 *
 * The third isn't a claim, it's a blank: you pick a real number and the other
 * two goals become concrete. Lean says exactly which goal that is — its case tag
 * (`hb.b`) is the NAME of the metavariable (`?hb.b`) the siblings are waiting
 * on. So: a goal whose tag appears as `?<tag>` anywhere in the proof is a value
 * goal, and the prose can say "We need a value of type ℝ" instead of the
 * baffling "We must show ℝ".
 *
 * Generic — it reads Lean's own dependency structure, with no knowledge of any
 * particular type or lemma.
 */
function valueGoalTags(goals: readonly LeanGoal[]): Set<string> {
  const tags = new Set<string>();
  // Authoritative: the extractor records, at each tactic's goal split, which
  // goals' metavariables occur in sibling goals' types. Computed at the split
  // itself, so it stays true after the user supplies the value (when the
  // `?tag` mentions below disappear from the pretty-printed text). NOTE this
  // is deliberately NOT `isProp`: from-scratch presets state their claims in
  // Type, where every goal is non-Prop — dependency structure is the signal
  // that generalizes.
  for (const g of goals) {
    for (const t of g.valueCaseTags ?? []) tags.add(t);
  }
  // Fallback for output from an extractor built before `valueCaseTags`:
  // pending `?tag` mentions in the plain goal text.
  const pending = new Set<string>();
  for (const g of goals) {
    for (const state of g.goals) {
      for (const m of state.plain.matchAll(/\?([A-Za-z_][A-Za-z0-9_.'!]*)/g)) pending.add(m[1]);
    }
  }
  for (const g of goals) {
    for (const state of g.goals) {
      if (state.case && pending.has(state.case)) tags.add(state.case);
    }
  }
  return tags;
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

/**
 * Branch tags by branch-head node id: for every `apply` printed with
 * case-tagged children (`case b => …`), the head node of each branch mapped to
 * its tag. Lean CLEARS a goal's case tag once the `case` block focuses it, so
 * the goal state AT the branch head is tagless — the TREE is what remembers
 * which branch a node proves, and that memory survives supplying the value.
 */
export function collectBranchTags(root: ProofNode): Map<ProofNodeId, string> {
  const tags = new Map<ProofNodeId, string>();
  const visit = (n: ProofNode): void => {
    switch (n.tag) {
      case 'hole':
      case 'exact':
        return;
      case 'intros':
      case 'destructure':
      case 'unfold':
      case 'fold':
        return visit(n.child);
      case 'rewrite':
        visit(n.child);
        for (const sg of rewriteSideGoals(n)) visit(sg);
        return;
      case 'simp':
        return visit(n.child);
      case 'have':
        if (n.proofTree) visit(n.proofTree);
        return visit(n.child);
      case 'suffices':
        if (n.byProof) visit(n.byProof);
        return visit(n.child);
      case 'apply':
        if (n.childTags && n.childTags.length === n.children.length) {
          n.children.forEach((c, i) => tags.set(c.id, n.childTags![i]));
        }
        for (const c of n.children) visit(c);
        return;
      case 'induction':
        for (const c of n.cases) visit(c.body);
        return;
    }
  };
  visit(root);
  return tags;
}

/** Build a NodeGoalInfo from a single Lean goal state. */
function nodeGoalInfoFromState(
  state: LeanGoalState,
  valueTags: ReadonlySet<string>,
  branchTag?: string,
): NodeGoalInfo {
  // A goal is a value to CHOOSE (not a claim to prove) when its metavariable
  // is what sibling goals talk about — see valueGoalTags. The state's own tag
  // when Lean kept one, else the tree's memory of which branch this node
  // proves. `state.isProp` is NOT the signal: in a from-scratch preset that
  // states claims in Type, every goal is non-Prop, and "prove 0 < ε" must
  // still read as a claim.
  const tag = state.case ?? branchTag;
  const isValue = !!tag && valueTags.has(tag);
  return {
    goalLatex: taggedToLatex(state.targetTagged, state.plain),
    hypotheses: hypsToTyped(state),
    ...(state.case ? { caseLabelLatex: state.case } : {}),
    ...(isValue ? { isValueType: true } : {}),
  };
}

export interface LeanGoalMappingInput {
  nodeRanges: Map<ProofNodeId, NodeRange>;
  holeNodeIds: Set<ProofNodeId>;
  goals: LeanGoal[];
  messages: LeanMessage[];
  /** Branch tags by branch-head node (see collectBranchTags) — how a tagless
   *  focused goal inside a `case` block is matched to `valueCaseTags`. */
  branchTags?: ReadonlyMap<ProofNodeId, string>;
}

/**
 * Produce the per-node goal map the proof UI consumes, from Lean's analysis of
 * the printed tactic block. Each node that has a goal state at its range gets a
 * `NodeGoalInfo`; hole nodes with no remaining goal are treated as solved.
 */
export function mapLeanGoalsToNodes(input: LeanGoalMappingInput): Map<ProofNodeId, NodeGoalInfo> {
  const { nodeRanges, holeNodeIds, goals, messages, branchTags } = input;
  const result = new Map<ProofNodeId, NodeGoalInfo>();
  const valueTags = valueGoalTags(goals);

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
      const info = nodeGoalInfoFromState(g.goals[0], valueTags, branchTags?.get(nodeId));
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
