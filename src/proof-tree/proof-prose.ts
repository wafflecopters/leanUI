/**
 * Proof Prose Generator — converts a proof tree + goal map into
 * natural-language mathematical prose items.
 *
 * Pure function with zero React or tactic-engine dependencies.
 * Consumes a proof tree and precomputed NodeGoalInfo map,
 * produces a flat array of ProseItems for rendering.
 */

import { ProofNode, ProofNodeId, CaseNode, ExactNode } from './proof-tree';
import { NodeGoalInfo, TypedHypothesis } from './goal-computation';
import { TTerm } from '../compiler/surface';

/** Walk a byProof subtree to extract the proof expression string.
 *  Typically this is a single `exact` node, possibly under intros. */
function extractByExpr(node?: ProofNode): string | undefined {
  if (!node) return undefined;
  switch (node.tag) {
    case 'exact': return node.expr;
    case 'intros': return extractByExpr(node.child);
    case 'have': return extractByExpr(node.child);
    default: return undefined;
  }
}

// ============================================================================
// Data Model
// ============================================================================

export interface ProseItem {
  readonly nodeId: ProofNodeId;
  readonly depth: number;
  readonly kind: ProseItemKind;
  readonly isCursor: boolean;
}

/** A single clickable variable token in an intro line. */
export interface IntroToken {
  readonly name: string;        // e.g., "n"
  readonly nameLatex: string;   // e.g., "n" or "\\mathit{ih}"
  readonly nameIndex: number;   // index into IntrosNode.names (for editIntroName)
  readonly typeLatex: string;   // shared type LaTeX for the group
  readonly rawType?: TTerm;     // for extractTypeHead → induction check
}

/** A group of variables sharing the same type in an intro line. */
export interface IntroGroup {
  readonly tokens: readonly IntroToken[];
  readonly typeLatex: string;
}

export type ProseItemKind =
  | { tag: 'intro'; latex: string; goalLatex?: string; groups?: readonly IntroGroup[] }
  | { tag: 'unfold'; name: string; occurrence?: number; preGoalLatex?: string; goalLatex?: string; error?: string }
  | { tag: 'fold'; name: string; occurrence?: number; preGoalLatex?: string; goalLatex?: string; error?: string }
  | { tag: 'rewrite'; name: string; reverse?: boolean; occurrences?: readonly number[]; equationLatex?: string; preGoalLatex?: string; goalLatex?: string; error?: string }
  | { tag: 'apply'; name: string; preGoalLatex?: string; subgoalLatex?: string[]; appliedArgsLatex?: string[]; error?: string }
  | { tag: 'inductionHeader'; scrutinee: string }
  | { tag: 'caseHeader'; labelLatex: string; isBaseCase: boolean; constructorParamNames?: readonly string[]; constructorName?: string; scrutinee?: string }
  | { tag: 'exact'; exprLatex: string; solved: boolean; goalLatex?: string; error?: string; proofExprLatex?: string }
  | { tag: 'hole'; goalLatex?: string }
  | { tag: 'simp'; lemmas: readonly string[]; stepCount: number; preGoalLatex?: string; goalLatex?: string }
  | { tag: 'have'; name: string; expr: string; typeLatex?: string; proofExprLatex?: string; preGoalLatex?: string; goalLatex?: string }
  | { tag: 'suffices'; name: string; goalLatex?: string; byExprLatex?: string }
  | { tag: 'subgoalHeader'; label: string; goalLatex?: string }
  | { tag: 'qed' };

/** A single step in an unfold/rewrite chain. */
export interface ChainStep {
  readonly nodeId: ProofNodeId;
  readonly type: 'unfold' | 'fold' | 'rewrite';
  readonly name: string;
  readonly reverse?: boolean;
  /** For unfold/fold: 1-based occurrence index (if targeting a specific occurrence). */
  readonly occurrence?: number;
  /** For rewrite: 1-based occurrence indices (if targeting specific occurrences). */
  readonly occurrences?: readonly number[];
  /** For rewrite steps: the unified equation rendered as LaTeX (e.g., "a + 0 = a"). */
  readonly equationLatex?: string;
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

/**
 * Build structured intro groups with per-variable metadata for clickable tokens.
 * Each group contains variables sharing the same type, with rawType for induction checks.
 */
function buildIntroGroups(
  parentHyps: readonly TypedHypothesis[],
  childHyps: readonly TypedHypothesis[],
): IntroGroup[] {
  const newHyps = childHyps.slice(parentHyps.length);
  if (newHyps.length === 0) return [];

  const groups = groupHypotheses(newHyps);
  let nameIdx = 0;
  return groups.map(g => ({
    tokens: g.names.map(name => {
      const hyp = newHyps[nameIdx];
      const token: IntroToken = {
        name,
        nameLatex: texName(name),
        nameIndex: nameIdx,
        typeLatex: g.typeLatex,
        rawType: hyp?.rawType,
      };
      nameIdx++;
      return token;
    }),
    typeLatex: g.typeLatex,
  }));
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

function isChainNode(node: ProofNode): node is (ProofNode & { tag: 'unfold' | 'fold' | 'rewrite' }) {
  return node.tag === 'unfold' || node.tag === 'fold' || node.tag === 'rewrite';
}

/**
 * Collect a chain of consecutive unfold/rewrite nodes.
 * Returns the chain steps and the first non-chain child.
 * Attaches unified equation LaTeX from the goal map when available.
 */
function collectChain(
  node: ProofNode,
  goalMap: Map<ProofNodeId, NodeGoalInfo>,
): { steps: ChainStep[]; tail: ProofNode } {
  const steps: ChainStep[] = [];
  let current = node;
  while (isChainNode(current)) {
    const nodeInfo = goalMap.get(current.id);
    if (current.tag === 'unfold') {
      steps.push({ nodeId: current.id, type: 'unfold', name: current.name, occurrence: current.occurrence });
    } else if (current.tag === 'fold') {
      steps.push({ nodeId: current.id, type: 'fold', name: current.name, occurrence: current.occurrence });
    } else {
      steps.push({
        nodeId: current.id,
        type: 'rewrite',
        name: current.name,
        reverse: current.reverse,
        occurrences: current.occurrences,
        equationLatex: nodeInfo?.unifiedEquationLatex,
      });
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

  /** Walk a proof branch with a labeled header, indented content. */
  function walkBranch(parentId: ProofNodeId, label: string, goalLatex: string | undefined, body: ProofNode, depth: number): void {
    emit(parentId, depth, { tag: 'subgoalHeader', label, goalLatex });
    walk(body, depth + 1);
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
        emit(node.id, depth, { tag: 'exact', exprLatex: node.expr, solved, goalLatex: info?.goalLatex, error, proofExprLatex: info?.proofExprLatex });
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
        const groups = buildIntroGroups(parentHyps, childHyps);
        const childGoalLatex = childInfo?.goalLatex;
        emit(node.id, depth, {
          tag: 'intro',
          latex: latex || node.names.join(', '),
          goalLatex: childGoalLatex,
          groups: groups.length > 0 ? groups : undefined,
        });
        walk(node.child, depth);
        break;
      }

      case 'unfold':
      case 'fold':
      case 'rewrite': {
        // Collect chain of consecutive unfold/fold/rewrite, emit each as its own item.
        // Each step shows the goal AFTER that step (= the next node's goal).
        // The first step also carries preGoalLatex (the goal before the chain).
        const { steps, tail } = collectChain(node, goalMap);
        const tailInfo = goalMap.get(tail.id);
        for (let si = 0; si < steps.length; si++) {
          const step = steps[si];
          // Goal after this step = next step's node goal, or the tail's goal
          const nextGoalLatex = si + 1 < steps.length
            ? goalMap.get(steps[si + 1].nodeId)?.goalLatex
            : tailInfo?.goalLatex;
          // Pre-goal: only the first step needs it (subsequent steps' pre-goal
          // was already shown as the previous step's post-goal)
          const preGoalLatex = si === 0
            ? goalMap.get(steps[0].nodeId)?.goalLatex
            : undefined;
          const stepError = goalMap.get(step.nodeId)?.tacticError;
          if (step.type === 'unfold') {
            emit(step.nodeId, depth, { tag: 'unfold', name: step.name, occurrence: step.occurrence, preGoalLatex, goalLatex: nextGoalLatex, error: stepError });
          } else if (step.type === 'fold') {
            emit(step.nodeId, depth, { tag: 'fold', name: step.name, occurrence: step.occurrence, preGoalLatex, goalLatex: nextGoalLatex, error: stepError });
          } else {
            emit(step.nodeId, depth, {
              tag: 'rewrite',
              name: step.name,
              reverse: step.reverse,
              occurrences: step.occurrences,
              equationLatex: step.equationLatex,
              preGoalLatex,
              goalLatex: nextGoalLatex,
              error: stepError,
            });
          }
        }
        walk(tail, depth);
        break;
      }

      case 'apply': {
        // Collect subgoal LaTeX from children
        const subgoalLatex = node.children.map(child => {
          const childInfo = goalMap.get(child.id);
          return childInfo?.goalLatex ?? '?';
        });
        emit(node.id, depth, { tag: 'apply', name: node.name, preGoalLatex: info?.goalLatex, subgoalLatex, appliedArgsLatex: info?.appliedArgsLatex, error: info?.tacticError });
        if (node.children.length > 1) {
          // Multiple subgoals: use labeled branches with indentation
          for (let i = 0; i < node.children.length; i++) {
            const child = node.children[i];
            const childGoal = goalMap.get(child.id)?.goalLatex;
            walkBranch(node.id, `Goal ${i + 1}`, childGoal, child, depth);
          }
        } else {
          // Single subgoal: stay at same depth to avoid progressive indentation
          for (const child of node.children) {
            walk(child, depth);
          }
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
            constructorParamNames: c.constructorParamNames,
            constructorName: c.constructorName,
            scrutinee: node.scrutinee,
          });
          walk(c.body, depth + 2);
        }
        break;
      }

      case 'have': {
        const childInfo = goalMap.get(node.child.id);
        const childGoalLatex = childInfo?.goalLatex;
        // Find the hypothesis type from the child's context (last entry with this name)
        const hypType = childInfo?.hypotheses.find(h => h.name === node.name)?.type;
        emit(node.id, depth, {
          tag: 'have',
          name: node.name,
          expr: node.expr,
          typeLatex: hypType,
          proofExprLatex: info?.proofExprLatex,
          preGoalLatex: info?.goalLatex,
          goalLatex: childGoalLatex,
        });
        walk(node.child, depth);
        break;
      }

      case 'suffices': {
        const childInfo = goalMap.get(node.child.id);
        // The child's goalLatex IS the suffices type, rendered through the math pipeline
        const childGoalLatex = childInfo?.goalLatex;
        emit(node.id, depth, {
          tag: 'suffices',
          name: node.name,
          goalLatex: childGoalLatex,
          byExprLatex: info?.sufficesByLatex,
        });
        // Suffices replaces the goal — the continuation flows at the same depth (not a fork)
        walk(node.child, depth);
        break;
      }

      case 'simp': {
        const childGoalLatex = goalMap.get(node.child.id)?.goalLatex;
        emit(node.id, depth, {
          tag: 'simp',
          lemmas: node.lemmas,
          stepCount: node.steps.length,
          preGoalLatex: info?.goalLatex,
          goalLatex: childGoalLatex,
        });
        // Steps are already replayed by the engine; just recurse into child
        walk(node.child, depth);
        break;
      }
    }
  }

  walk(root, 0);
  return items;
}
