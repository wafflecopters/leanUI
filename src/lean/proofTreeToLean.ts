/**
 * ProofNode tree → Lean tactic source (the keystone of the WYSIWYG-on-Lean seam).
 *
 * The structured proof editor's `ProofNode` tree is serialized to a Lean `by`
 * tactic block. We record, for every node, the source range of the tactic it
 * produced, so that after Lean elaborates the block we can map each InfoTree
 * goal-state (keyed by source range) back onto its `ProofNodeId` — feeding the
 * existing goal-rendering / prose pipeline. This replaces the in-process TT
 * `replayEntireTree` with a real Lean round-trip.
 *
 * Holes become `sorry` so the block always elaborates (Lean reports the goal at
 * each `sorry`, which is exactly the open goal the UI needs to show).
 *
 * Positions are 1-based line, 0-based column (Lean's convention), matching the
 * extractor and `goalAtCursor`.
 */
import type {
  ProofNode,
  ProofNodeId,
  CaseNode,
} from '../proof-tree/proof-tree';

export interface NodeRange {
  startLine: number;
  startCol: number;
  endLine: number;
  endCol: number;
}

export interface ProofTreeLean {
  /** The full Lean tactic block (no leading `by`; caller wraps in a decl). */
  source: string;
  /** Per-node source range of the tactic head, for mapping InfoTree goals back. */
  nodeRanges: Map<ProofNodeId, NodeRange>;
  /** Node ids that emitted a `sorry` (open goals / holes). */
  holeNodeIds: Set<ProofNodeId>;
}

const INDENT = '  ';

/** Emitter that accumulates lines while tracking the current cursor position. */
class Emitter {
  lines: string[] = [];
  ranges = new Map<ProofNodeId, NodeRange>();
  holes = new Set<ProofNodeId>();

  /** Emit one tactic line at the given indent depth, recording its node range. */
  emit(depth: number, text: string, nodeId?: ProofNodeId): void {
    const indent = INDENT.repeat(depth);
    const line = indent + text;
    const lineNo = this.lines.length + 1; // 1-based
    this.lines.push(line);
    if (nodeId !== undefined) {
      this.ranges.set(nodeId, {
        startLine: lineNo,
        startCol: indent.length,
        endLine: lineNo,
        endCol: line.length,
      });
    }
  }

  /** Emit a tactic and continuation text on the same line (e.g. `| zero => exact h`). */
  emitInline(depth: number, head: string, nodeId: ProofNodeId, tail: string): void {
    const indent = INDENT.repeat(depth);
    const line = indent + head + tail;
    const lineNo = this.lines.length + 1;
    this.lines.push(line);
    this.ranges.set(nodeId, {
      startLine: lineNo,
      startCol: indent.length,
      endLine: lineNo,
      endCol: line.length,
    });
  }
}

/** Escape/normalize an identifier list for `intro`. */
function introNames(names: readonly string[]): string {
  const cleaned = names.map((n) => n.trim()).filter((n) => n.length > 0);
  return cleaned.length > 0 ? cleaned.join(' ') : '_';
}

function rewriteTerm(node: { name: string; reverse: boolean }): string {
  return node.reverse ? `← ${node.name}` : node.name;
}

function emitNode(em: Emitter, node: ProofNode, depth: number): void {
  switch (node.tag) {
    case 'hole': {
      em.emit(depth, 'sorry', node.id);
      em.holes.add(node.id);
      return;
    }
    case 'intros': {
      em.emit(depth, `intro ${introNames(node.names)}`, node.id);
      emitNode(em, node.child, depth);
      return;
    }
    case 'exact': {
      const expr = node.expr.trim() || 'sorry';
      em.emit(depth, `exact ${expr}`, node.id);
      return;
    }
    case 'unfold': {
      em.emit(depth, `unfold ${node.name}`, node.id);
      emitNode(em, node.child, depth);
      return;
    }
    case 'fold': {
      // `fold` is not a core tactic; emit as a no-op comment so the block still
      // elaborates and the node keeps a range. (Lean-native fold handled later.)
      em.emit(depth, `-- fold ${node.name}`, node.id);
      emitNode(em, node.child, depth);
      return;
    }
    case 'rewrite': {
      em.emit(depth, `rw [${rewriteTerm(node)}]`, node.id);
      emitNode(em, node.child, depth);
      return;
    }
    case 'simp': {
      const lemmas = node.lemmas.filter((l) => l.trim().length > 0);
      em.emit(depth, lemmas.length ? `simp [${lemmas.join(', ')}]` : 'simp', node.id);
      emitNode(em, node.child, depth);
      return;
    }
    case 'apply': {
      em.emit(depth, `apply ${node.name}`, node.id);
      // Each child proves one subgoal; emit them in order at the same depth.
      // Lean focuses subgoals sequentially after `apply`.
      for (const child of node.children) {
        emitNode(em, child, depth);
      }
      return;
    }
    case 'have': {
      if (node.proofTree) {
        // Interactive subtree proves the have's type.
        const type = node.typeExpr?.trim();
        em.emit(depth, type ? `have ${node.name} : ${type} := by` : `have ${node.name} := by`, node.id);
        emitNode(em, node.proofTree, depth + 1);
      } else {
        const expr = node.expr.trim() || 'sorry';
        em.emit(depth, `have ${node.name} := ${expr}`, node.id);
      }
      emitNode(em, node.child, depth);
      return;
    }
    case 'suffices': {
      const type = node.typeExpr.trim();
      em.emit(depth, `suffices ${node.name} : ${type} by`, node.id);
      if (node.byProof) emitNode(em, node.byProof, depth + 1);
      else em.emit(depth + 1, 'sorry');
      emitNode(em, node.child, depth);
      return;
    }
    case 'induction': {
      const kw = node.isCases ? 'cases' : 'induction';
      em.emit(depth, `${kw} ${node.scrutinee} with`, node.id);
      for (const c of node.cases) {
        emitCase(em, c, depth);
      }
      return;
    }
  }
}

function emitCase(em: Emitter, c: CaseNode, depth: number): void {
  // `| ctor params =>` then the case body indented one level deeper.
  const ctor = c.constructorName ?? c.label;
  const params = c.constructorParamNames && c.constructorParamNames.length > 0
    ? ' ' + c.constructorParamNames.join(' ')
    : '';
  const header = `| ${ctor}${params} =>`;
  // Record the case header range under the case node id.
  em.emit(depth, header, c.id);
  emitNode(em, c.body, depth + 1);
}

/**
 * Serialize a proof tree to a Lean tactic block.
 *
 * `baseLine` is the 1-based line where the block's FIRST tactic will sit in the
 * final file (so recorded ranges are absolute and match what Lean reports).
 * `baseDepth` is the indent depth of that first tactic.
 */
export function proofTreeToLean(root: ProofNode, baseLine = 1, baseDepth = 1): ProofTreeLean {
  const em = new Emitter();
  emitNode(em, root, baseDepth);
  // Shift recorded line numbers so the first emitted line is `baseLine`.
  const lineShift = baseLine - 1;
  if (lineShift !== 0) {
    for (const [id, r] of em.ranges) {
      em.ranges.set(id, {
        startLine: r.startLine + lineShift,
        startCol: r.startCol,
        endLine: r.endLine + lineShift,
        endCol: r.endCol,
      });
    }
  }
  return { source: em.lines.join('\n'), nodeRanges: em.ranges, holeNodeIds: em.holes };
}
