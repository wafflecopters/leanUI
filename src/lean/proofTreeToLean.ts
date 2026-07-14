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
  /** Write-back mode: drop a chaining tactic's lone-hole continuation. */
  omitTrailingHoles = false;
  /** When set, a hole with this id emits `holeOverrideTactic` instead of `sorry`. */
  holeOverrideId?: ProofNodeId;
  holeOverrideTactic = '';

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

/** Emit a chaining tactic's continuation child, honoring omitTrailingHoles. */
function emitChild(em: Emitter, child: ProofNode, depth: number): void {
  if (em.omitTrailingHoles && child.tag === 'hole') return;
  emitNode(em, child, depth);
}

function emitNode(em: Emitter, node: ProofNode, depth: number): void {
  switch (node.tag) {
    case 'hole': {
      if (em.holeOverrideId === node.id) {
        // Suggestion discovery: emit a discovery tactic (exact?/apply?/…) here
        // instead of `sorry`, so Lean reports its `Try this:` at this range.
        em.emit(depth, em.holeOverrideTactic, node.id);
        return;
      }
      em.emit(depth, 'sorry', node.id);
      em.holes.add(node.id);
      return;
    }
    case 'intros': {
      em.emit(depth, `intro ${introNames(node.names)}`, node.id);
      emitChild(em, node.child, depth);
      return;
    }
    case 'exact': {
      const expr = node.expr.trim() || 'sorry';
      // `raw` exact carries a whole tactic (omega/rfl/decide/…) — print verbatim.
      em.emit(depth, node.raw ? expr : `exact ${expr}`, node.id);
      return;
    }
    case 'unfold': {
      em.emit(depth, `unfold ${node.name}`, node.id);
      emitChild(em, node.child, depth);
      return;
    }
    case 'fold': {
      // `fold` is not a core tactic; emit as a no-op comment so the block still
      // elaborates and the node keeps a range. (Lean-native fold handled later.)
      em.emit(depth, `-- fold ${node.name}`, node.id);
      emitChild(em, node.child, depth);
      return;
    }
    case 'rewrite': {
      // Subterm-scoped rewrite → `conv in (pat) => rw [...]`; else plain `rw`.
      const rw = `rw [${rewriteTerm(node)}]`;
      const head = node.convPattern ? `conv in (${node.convPattern}) => ${rw}` : rw;
      const sides = node.sideGoals ?? [];
      // A conditional rewrite leaves side goals (the lemma's premises). Lean
      // focuses the rewritten goal first, then the side goals — emit `·` bullet
      // branches so each is a visible, separately-provable obligation. (conv
      // rewrites don't take this path; they never leave side goals.)
      if (sides.length > 0 && !node.convPattern) {
        em.emit(depth, head, node.id);
        emitBullet(em, node.child, depth); // main (rewritten) goal first
        for (const sg of sides) emitBullet(em, sg, depth);
        return;
      }
      em.emit(depth, head, node.id);
      emitChild(em, node.child, depth);
      return;
    }
    case 'simp': {
      const lemmas = node.lemmas.filter((l) => l.trim().length > 0);
      const kw = node.only ? 'simp only' : 'simp';
      em.emit(depth, lemmas.length ? `${kw} [${lemmas.join(', ')}]` : kw, node.id);
      emitChild(em, node.child, depth);
      return;
    }
    case 'apply': {
      // `raw` apply carries a whole tactic (e.g. `constructor`) — print verbatim.
      em.emit(depth, node.raw ? node.name : `apply ${node.name}`, node.id);
      // Each child proves one subgoal. A LONE child follows the chaining-tactic
      // convention (write-back drops a trailing hole, so a goal-closing
      // `constructor` doesn't write a stray `sorry`). MULTIPLE children of a
      // RAW apply print as `·` bullets — unambiguous to parse back (a flat
      // tactic sequence can't express "these N chains are N subgoals") and how
      // a Lean author writes a multi-goal constructor (DPair: body + witness).
      if (node.children.length === 1) {
        emitChild(em, node.children[0], depth);
      } else if (node.raw && node.childTags && node.childTags.length === node.children.length) {
        // Tagged children print as `case <tag> =>` blocks — Lean selects goals
        // BY NAME, so the proof can present them in a different order than
        // Lean produced them (witness before dependent body).
        node.children.forEach((child, i) => {
          em.emit(depth, `case ${node.childTags![i]} =>`);
          emitNode(em, child, depth + 1);
        });
      } else if (node.raw) {
        for (const child of node.children) emitBullet(em, child, depth);
      } else {
        for (const child of node.children) {
          emitNode(em, child, depth);
        }
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
      emitChild(em, node.child, depth);
      return;
    }
    case 'suffices': {
      const type = node.typeExpr.trim();
      em.emit(depth, `suffices ${node.name} : ${type} by`, node.id);
      if (node.byProof) emitNode(em, node.byProof, depth + 1);
      else em.emit(depth + 1, 'sorry');
      emitChild(em, node.child, depth);
      return;
    }
    case 'induction': {
      const kw = node.isCases ? 'cases' : 'induction';
      // Use a `with`/`| ctor =>` block only when EVERY case has a real Lean
      // constructor name (a valid identifier). Otherwise the TT engine produced
      // display-only labels like "n = 0" — invalid as Lean case tags — so emit a
      // bare `induction n` + `·` bullets (Lean focuses cases in order), keeping
      // the source valid.
      const named = node.cases.length > 0 && node.cases.every((c) => isLeanCtorName(c.constructorName));
      if (named) {
        em.emit(depth, `${kw} ${node.scrutinee} with`, node.id);
        for (const c of node.cases) emitNamedCase(em, c, depth);
      } else {
        em.emit(depth, `${kw} ${node.scrutinee}`, node.id);
        for (const c of node.cases) emitBulletCase(em, c, depth);
      }
      return;
    }
  }
}

/** A valid Lean constructor identifier (letters/digits/_/., not a display label). */
function isLeanCtorName(name: string | undefined): name is string {
  return name !== undefined && /^[A-Za-z_][A-Za-z0-9_.]*$/.test(name);
}

function emitNamedCase(em: Emitter, c: CaseNode, depth: number): void {
  // Bind constructor args AND induction hypotheses (`| succ a a_ih =>`), so Lean
  // doesn't auto-generate inaccessible (✝) names for the IH.
  const names = [...(c.constructorParamNames ?? []), ...(c.ihNames ?? [])];
  const params = names.length > 0 ? ' ' + names.join(' ') : '';
  em.emit(depth, `| ${c.constructorName}${params} =>`, c.id);
  emitNode(em, c.body, depth + 1);
}

function emitBulletCase(em: Emitter, c: CaseNode, depth: number): void {
  // `·` focuses the next goal; the body goes on following indented lines.
  em.emit(depth, '·', c.id);
  emitNode(em, c.body, depth + 1);
}

/** Emit a `·`-bulleted branch (focuses the next goal). Used for a conditional
 *  rewrite's main + side-goal branches. Bodies always render their holes as
 *  `sorry` — even in write-back — since an un-bulleted side goal would be an
 *  unsolved obligation Lean rejects. */
function emitBullet(em: Emitter, body: ProofNode, depth: number): void {
  em.emit(depth, '·');
  emitNode(em, body, depth + 1);
}

/**
 * Serialize a proof tree to a Lean tactic block.
 *
 * `baseLine` is the 1-based line where the block's FIRST tactic will sit in the
 * final file (so recorded ranges are absolute and match what Lean reports).
 * `baseDepth` is the indent depth of that first tactic.
 */
export function proofTreeToLean(
  root: ProofNode,
  baseLine = 1,
  baseDepth = 1,
  opts?: { holeOverrideId?: ProofNodeId; holeOverrideTactic?: string },
): ProofTreeLean {
  const em = new Emitter();
  if (opts?.holeOverrideId !== undefined) {
    em.holeOverrideId = opts.holeOverrideId;
    em.holeOverrideTactic = opts.holeOverrideTactic ?? 'sorry';
  }
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

/**
 * Print a proof tree as Lean source for WRITE-BACK into the user's file.
 *
 * Unlike `proofTreeToLean` (which renders every hole as `sorry` so Lean reports
 * a goal there), this omits trailing-hole continuations of chaining tactics: a
 * goal-closing tactic like `simp` that the parser gave a fabricated `sorry`
 * child would otherwise write `simp\n  sorry` — which Lean rejects as "no goals
 * to be solved". A standalone unfinished hole still becomes `sorry` so the user
 * keeps a visible obligation.
 */
export function proofTreeToSource(root: ProofNode, baseDepth = 1): string {
  const em = new Emitter();
  em.omitTrailingHoles = true;
  emitNode(em, root, baseDepth);
  return em.lines.join('\n');
}
