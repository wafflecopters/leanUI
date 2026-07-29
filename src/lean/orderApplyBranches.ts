/**
 * Put the branch you have to fill in FIRST.
 *
 * `apply ltLeTrans` on `0 < 2` leaves three goals, and Lean orders them the way
 * the lemma's arguments happen to be written:
 *
 *     0 ≤ ?b        ?b ≤ 2        ℝ
 *
 * That's backwards for a person. The third one is the midpoint — a blank you
 * CHOOSE — and the first two are unanswerable until you've chosen it. Landing on
 * "we must show 0 ≤ ?b" with no idea where `?b` comes from is exactly the
 * confusion this fixes. Reordered, the proof reads the way it's thought:
 *
 *     pick b : ℝ,   then show 0 ≤ b,   then show b ≤ 2
 *
 * Lean lets us: `case <tag> =>` selects a goal BY NAME, so the branches may be
 * written in any order (verified against the real toolchain, including the
 * dotted tags nested applies produce). We reorder once, after the round-trip
 * tells us the tags, and record them so the printed proof is stable.
 *
 * Idempotent and self-correcting: once the order matches nothing changes, and if
 * Lean later reports different tags (the surrounding proof was restructured)
 * they're refreshed.
 */
import type { ProofNode, ProofNodeId } from '../proof-tree/proof-tree';
import type { NodeGoalInfo } from '../proof-tree/goal-computation';
import { orderedSubgoalTags } from './leanSuggestions';

export interface OrderApplyBranchesInput {
  root: ProofNode;
  /** Lean's per-node goal info — supplies each branch's `case` tag. */
  goalMap: Map<ProofNodeId, NodeGoalInfo>;
  /** Plain-text target per node — supplies the "does it mention a
   *  metavariable" signal that separates witnesses from obligations. */
  goalTexts: Map<ProofNodeId, string>;
  /** Cursor position; moved onto the new first branch when it was sitting on a
   *  branch of a node we reordered and no work had been done there yet. */
  cursorId: ProofNodeId;
}

export interface OrderApplyBranchesResult {
  root: ProofNode;
  cursorId: ProofNodeId;
  changed: boolean;
}

export function orderApplyBranches(input: OrderApplyBranchesInput): OrderApplyBranchesResult {
  const { goalMap, goalTexts } = input;
  let changed = false;
  let cursorId = input.cursorId;

  const walk = (node: ProofNode): ProofNode => {
    switch (node.tag) {
      case 'hole':
      case 'exact':
        return node;
      case 'intros':
      case 'unfold':
      case 'fold': {
        const child = walk(node.child);
        return child === node.child ? node : { ...node, child };
      }
      case 'rewrite': {
        const child = walk(node.child);
        const sides = node.sideGoals?.map(walk);
        const sidesChanged = !!sides && sides.some((s, i) => s !== node.sideGoals![i]);
        if (child === node.child && !sidesChanged) return node;
        return { ...node, child, ...(sides ? { sideGoals: sides } : {}) };
      }
      case 'have': {
        const proofTree = node.proofTree ? walk(node.proofTree) : undefined;
        const child = walk(node.child);
        if (proofTree === node.proofTree && child === node.child) return node;
        return { ...node, proofTree, child };
      }
      case 'suffices': {
        const byProof = node.byProof ? walk(node.byProof) : undefined;
        const child = walk(node.child);
        if (byProof === node.byProof && child === node.child) return node;
        return { ...node, byProof, child };
      }
      case 'induction': {
        let any = false;
        const cases = node.cases.map((c) => {
          const body = walk(c.body);
          if (body === c.body) return c;
          any = true;
          return { ...c, body };
        });
        return any ? { ...node, cases } : node;
      }
      case 'simp': {
        const child = walk(node.child);
        return child === node.child ? node : { ...node, child };
      }
      case 'apply': {
        const children = node.children.map(walk);
        const anyChild = children.some((c, i) => c !== node.children[i]);
        const base = anyChild ? { ...node, children } : node;
        if (children.length < 2) return base;

        // Every branch must have a Lean tag and a goal; without both we can't
        // say which is the witness, so leave the proof exactly as written.
        const tagged = children.map((c) => ({
          child: c,
          tag: goalMap.get(c.id)?.caseLabelLatex,
          target: goalTexts.get(c.id) ?? '',
        }));
        if (tagged.some((t) => !t.tag)) return base;

        const desired = orderedSubgoalTags(tagged.map((t) => ({ tag: t.tag, target: t.target })));
        if (!desired) return base;

        const byTag = new Map(tagged.map((t) => [t.tag!, t] as const));
        const ordered = desired.map((tag) => byTag.get(tag)).filter((t): t is typeof tagged[number] => !!t);
        if (ordered.length !== children.length) return base;

        const sameOrder = ordered.every((t, i) => t.child === children[i]);
        const hasTags = (base.childTags?.length ?? 0) > 0;
        const tagsCorrect =
          base.childTags?.length === desired.length && desired.every((t, i) => base.childTags![i] === t);
        // Rewrite only when it earns it: the order is wrong, or the recorded
        // `case` selectors have gone stale (they'd no longer match a goal, and
        // the proof would stop compiling). A correctly ordered node written
        // with plain bullets is left exactly as the user wrote it.
        if (sameOrder && (!hasTags || tagsCorrect)) return base;

        // The cursor is following the user, not the tree: right after the apply
        // it should land on the choice everything else waits on. But only while
        // that choice is still OPEN — once the witness has been supplied, the
        // cursor must be free to move on, or every refresh drags it back to a
        // branch that's already done.
        const first = ordered[0].child;
        if (first.tag === 'hole' && first.id !== cursorId) {
          const at = children.find((c) => c.id === cursorId);
          if (at?.tag === 'hole') cursorId = first.id;
        }
        changed = true;
        return { ...base, children: ordered.map((t) => t.child), childTags: desired };
      }
    }
  };

  return { root: walk(input.root), cursorId, changed };
}
