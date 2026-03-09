/**
 * Proof Prose Generator — converts a proof tree + goal map into
 * natural-language mathematical prose items.
 *
 * Pure function with zero React or tactic-engine dependencies.
 * Consumes a proof tree and precomputed NodeGoalInfo map,
 * produces a flat array of ProseItems for rendering.
 */

import { ProofNode, ProofNodeId, CaseNode } from './proof-tree';
import { NodeGoalInfo, TypedHypothesis } from './goal-computation';

// ============================================================================
// Data Model
// ============================================================================

export interface ProseItem {
  readonly nodeId: ProofNodeId;
  readonly depth: number;
  readonly kind: ProseItemKind;
  readonly isCursor: boolean;
}

export type ProseItemKind =
  | { tag: 'intro'; latex: string }
  | { tag: 'chain'; steps: ChainStep[]; goalLatex?: string }
  | { tag: 'apply'; name: string; subgoalLatex?: string[] }
  | { tag: 'inductionHeader'; scrutinee: string }
  | { tag: 'caseHeader'; labelLatex: string; isBaseCase: boolean }
  | { tag: 'exact'; exprLatex: string; solved: boolean; error?: string }
  | { tag: 'hole'; goalLatex?: string }
  | { tag: 'qed' };

/** A single step in an unfold/rewrite chain. */
export interface ChainStep {
  readonly nodeId: ProofNodeId;
  readonly type: 'unfold' | 'rewrite';
  readonly name: string;
  readonly reverse?: boolean;
}

// ============================================================================
// Hypothesis Grouping
// ============================================================================

interface HypGroup {
  readonly names: string[];
  readonly typeLatex: string;
}

/**
 * Group hypotheses by type for concise rendering.
 * E.g., [n:N, m:N, f:N->N] → [{names:["n","m"], type:"N"}, {names:["f"], type:"N->N"}]
 */
function groupHypotheses(hyps: readonly TypedHypothesis[]): HypGroup[] {
  const groups: HypGroup[] = [];
  for (const h of hyps) {
    const last = groups[groups.length - 1];
    if (last && last.typeLatex === h.type) {
      last.names.push(h.name);
    } else {
      groups.push({ names: [h.name], typeLatex: h.type });
    }
  }
  return groups;
}

/**
 * Render grouped hypotheses as a LaTeX "Let" clause.
 * E.g., "n, m \\in \\mathbb{N} \\text{ and } f : \\mathbb{N} \\to \\mathbb{N}"
 */
function renderIntroLatex(
  parentHyps: readonly TypedHypothesis[],
  childHyps: readonly TypedHypothesis[],
): string {
  // New hypotheses are the ones added by intros (child has more than parent)
  const newHyps = childHyps.slice(parentHyps.length);
  if (newHyps.length === 0) return '';

  const groups = groupHypotheses(newHyps);
  const parts = groups.map(g => {
    const names = g.names.map(n => texName(n)).join(', ');
    return `${names} : ${g.typeLatex}`;
  });

  if (parts.length === 1) return parts[0];
  return parts.slice(0, -1).join(', ') + ' \\text{ and } ' + parts[parts.length - 1];
}

/** Render a variable name for LaTeX (italicize single chars, textify multi-char). */
function texName(name: string): string {
  if (name.length === 1) return name;
  // Check if it's a common pattern like n' (primed variable)
  if (name.length === 2 && name[1] === "'") return `${name[0]}'`;
  return `\\mathit{${name}}`;
}

// ============================================================================
// Chain Detection
// ============================================================================

function isChainNode(node: ProofNode): node is (ProofNode & { tag: 'unfold' | 'rewrite' }) {
  return node.tag === 'unfold' || node.tag === 'rewrite';
}

/**
 * Collect a chain of consecutive unfold/rewrite nodes.
 * Returns the chain steps and the first non-chain child.
 */
function collectChain(node: ProofNode): { steps: ChainStep[]; tail: ProofNode } {
  const steps: ChainStep[] = [];
  let current = node;
  while (isChainNode(current)) {
    if (current.tag === 'unfold') {
      steps.push({ nodeId: current.id, type: 'unfold', name: current.name });
    } else {
      steps.push({ nodeId: current.id, type: 'rewrite', name: current.name, reverse: current.reverse });
    }
    current = current.child;
  }
  return { steps, tail: current };
}

// ============================================================================
// Prose Generation
// ============================================================================

export function generateProofProse(
  root: ProofNode,
  cursorId: ProofNodeId,
  goalMap: Map<ProofNodeId, NodeGoalInfo>,
): ProseItem[] {
  const items: ProseItem[] = [];

  function emit(nodeId: ProofNodeId, depth: number, kind: ProseItemKind): void {
    items.push({ nodeId, depth, kind, isCursor: nodeId === cursorId });
  }

  function walk(node: ProofNode, depth: number): void {
    const info = goalMap.get(node.id);

    switch (node.tag) {
      case 'hole': {
        emit(node.id, depth, { tag: 'hole', goalLatex: info?.goalLatex });
        break;
      }

      case 'exact': {
        const solved = info?.validation?.status === 'solved';
        const error = info?.validation?.status === 'error' ? info.validation.message : undefined;
        emit(node.id, depth, { tag: 'exact', exprLatex: node.expr, solved, error });
        if (solved) {
          emit(node.id, depth, { tag: 'qed' });
        }
        break;
      }

      case 'intros': {
        // Get child's hypotheses to see what was introduced
        const childInfo = goalMap.get(node.child.id);
        const parentHyps = info?.hypotheses ?? [];
        const childHyps = childInfo?.hypotheses ?? [];
        const latex = renderIntroLatex(parentHyps, childHyps);
        emit(node.id, depth, { tag: 'intro', latex: latex || node.names.join(', ') });
        walk(node.child, depth);
        break;
      }

      case 'unfold':
      case 'rewrite': {
        // Collect chain of consecutive unfold/rewrite
        const { steps, tail } = collectChain(node);
        const tailInfo = goalMap.get(tail.id);
        emit(node.id, depth, {
          tag: 'chain',
          steps,
          goalLatex: tailInfo?.goalLatex,
        });
        walk(tail, depth);
        break;
      }

      case 'apply': {
        // Collect subgoal LaTeX from children
        const subgoalLatex = node.children.map(child => {
          const childInfo = goalMap.get(child.id);
          return childInfo?.goalLatex ?? '?';
        });
        emit(node.id, depth, { tag: 'apply', name: node.name, subgoalLatex });
        // Walk each child at increased depth
        for (const child of node.children) {
          walk(child, depth + 1);
        }
        break;
      }

      case 'induction': {
        emit(node.id, depth, { tag: 'inductionHeader', scrutinee: node.scrutinee });
        for (let i = 0; i < node.cases.length; i++) {
          const c = node.cases[i];
          const isBaseCase = !c.constructorParamNames || c.constructorParamNames.length === 0;
          emit(c.id, depth + 1, {
            tag: 'caseHeader',
            labelLatex: c.labelLatex ?? c.label,
            isBaseCase,
          });
          walk(c.body, depth + 2);
        }
        break;
      }
    }
  }

  walk(root, 0);
  return items;
}
