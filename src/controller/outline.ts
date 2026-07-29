/**
 * The proof tree, flattened to printable data.
 *
 * The React editor renders a `ProofNode` tree directly as prose. Nothing else
 * can: a test can't assert on prose, a REPL can't print it, an agent can't read
 * it. `proofOutline` turns the same tree into plain nested records — one line
 * per step, branch names, per-node status from Lean's goal map — so every
 * consumer sees the same shape of the proof.
 *
 * Pure: tree + goal map in, data out.
 */
import {
  rewriteSideGoals,
  type CaseNode,
  type ProofNode,
  type ProofNodeId,
} from '../proof-tree/proof-tree';
import type { NodeGoalInfo } from '../proof-tree/goal-computation';
import type { NodeStatus, OutlineNode } from './types';

/** The one-line rendering of a step — what the REPL prints, near enough to the
 *  Lean tactic that it reads as the proof it is. */
export function nodeLabel(node: ProofNode): string {
  switch (node.tag) {
    case 'hole':
      return '?';
    case 'intros':
      return `${node.names.length === 1 ? 'intro' : 'intros'} ${node.names.join(' ')}`.trim();
    case 'induction':
      return `${node.isCases ? 'cases' : 'induction'} ${node.scrutinee}`;
    case 'exact':
      return node.raw ? node.expr : `exact ${node.expr}`;
    case 'unfold':
      return `unfold ${node.name}`;
    case 'fold':
      return `fold ${node.name}`;
    case 'rewrite': {
      const term = node.reverse ? `← ${node.name}` : node.name;
      return node.convPattern ? `conv in (${node.convPattern}) => rw [${term}]` : `rw [${term}]`;
    }
    case 'apply':
      return node.raw ? node.name : `apply ${node.name}`;
    case 'simp': {
      const simp = node.lemmas.length
        ? `simp${node.only ? ' only' : ''} [${node.lemmas.join(', ')}]`
        : `simp${node.only ? ' only' : ''}`;
      return node.convPattern ? `conv in (${node.convPattern}) => ${simp}` : simp;
    }
    case 'have':
      return node.typeExpr ? `have ${node.name} : ${node.typeExpr}` : `have ${node.name} := ${node.expr}`;
    case 'suffices':
      return `suffices ${node.name} : ${node.typeExpr}`;
  }
}

/**
 * A node's status, as Lean sees it.
 *
 * `unknown` matters and is not a synonym for solved: it means no round-trip has
 * reported on this node yet. Calling that "solved" is how a proof silently
 * claims to be finished before Lean has looked at it.
 */
function statusOf(node: ProofNode, info: NodeGoalInfo | undefined): NodeStatus {
  if (info?.tacticError) return 'error';
  if (info?.validation?.status === 'error') return 'error';
  if (node.tag !== 'hole') return info ? 'solved' : 'unknown';
  if (!info) return 'unknown';
  if (info.validation?.status === 'solved') return 'solved';
  return info.goalLatex ? 'open' : 'unknown';
}

interface BuildContext {
  goalMap: Map<ProofNodeId, NodeGoalInfo>;
  cursorId: ProofNodeId;
  /** Plain-text goals by node, when the caller has them (the LaTeX in
   *  NodeGoalInfo is for rendering, not for reading). */
  goalTexts?: Map<ProofNodeId, string>;
}

function build(node: ProofNode, ctx: BuildContext, branch?: string): OutlineNode {
  const info = ctx.goalMap.get(node.id);
  const out: OutlineNode = {
    id: node.id,
    tag: node.tag,
    label: nodeLabel(node),
    ...(branch ? { branch } : {}),
    status: statusOf(node, info),
    ...(ctx.goalTexts?.get(node.id) ? { goalText: ctx.goalTexts.get(node.id) } : {}),
    ...(info?.tacticError ? { error: info.tacticError } : {}),
    isCursor: node.id === ctx.cursorId,
    children: [],
  };

  const kids: OutlineNode[] = [];
  const push = (child: ProofNode, label?: string) => kids.push(build(child, ctx, label));

  switch (node.tag) {
    case 'hole':
    case 'exact':
      break;
    case 'intros':
    case 'unfold':
    case 'fold':
      push(node.child);
      break;
    case 'rewrite': {
      push(node.child);
      const sides = rewriteSideGoals(node);
      sides.forEach((sg, i) =>
        push(sg, sides.length > 1 ? `side goal ${i + 1}` : 'side goal'),
      );
      break;
    }
    case 'have':
      if (node.proofTree) push(node.proofTree, `proof of ${node.name}`);
      push(node.child);
      break;
    case 'suffices':
      if (node.byProof) push(node.byProof, `given ${node.name}`);
      push(node.child);
      break;
    case 'apply':
      node.children.forEach((c, i) =>
        push(c, node.childTags?.[i] ?? (node.children.length > 1 ? `goal ${i + 1}` : undefined)),
      );
      break;
    case 'induction':
      for (const c of node.cases as readonly CaseNode[]) push(c.body, `case ${c.label}`);
      break;
    case 'simp':
      // simp's discovered steps are read-only detail, not proof obligations.
      push(node.child);
      break;
  }
  out.children = kids;
  return out;
}

export function proofOutline(
  root: ProofNode,
  cursorId: ProofNodeId,
  goalMap: Map<ProofNodeId, NodeGoalInfo>,
  goalTexts?: Map<ProofNodeId, string>,
): OutlineNode {
  return build(root, { goalMap, cursorId, goalTexts });
}

/** Depth-first walk of an outline. */
export function walkOutline(node: OutlineNode, visit: (n: OutlineNode, depth: number) => void, depth = 0): void {
  visit(node, depth);
  for (const c of node.children) walkOutline(c, visit, depth + 1);
}

/** Every hole with an open Lean goal, in proof order — the "what's left" list. */
export function openHoles(outline: OutlineNode): OutlineNode[] {
  const out: OutlineNode[] = [];
  walkOutline(outline, (n) => {
    if (n.tag === 'hole' && n.status === 'open') out.push(n);
  });
  return out;
}

/** Render an outline as an indented listing — the REPL's proof view. */
export function formatOutline(outline: OutlineNode): string {
  const lines: string[] = [];
  walkOutline(outline, (n, depth) => {
    const mark = n.isCursor ? '▶' : ' ';
    const badge =
      n.status === 'error' ? ' ✗' : n.status === 'open' ? ' ○' : n.status === 'solved' ? ' ✓' : '';
    const branch = n.branch ? `${n.branch}: ` : '';
    const goal = n.goalText ? `    ⊢ ${n.goalText}` : '';
    lines.push(`${mark} ${'  '.repeat(depth)}${branch}${n.label}${badge}${goal}`);
    if (n.error) lines.push(`  ${'  '.repeat(depth)}  ✗ ${n.error}`);
  });
  return lines.join('\n');
}
