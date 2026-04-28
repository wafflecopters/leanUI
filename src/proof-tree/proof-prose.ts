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
  | { tag: 'apply'; name: string; preGoalLatex?: string; subgoalLatex?: string[]; appliedArgsLatex?: string[]; error?: string; proofExprs?: readonly string[] }
  | { tag: 'inductionHeader'; scrutinee: string; scrutineeLatex?: string; isCases?: boolean }
  | { tag: 'caseHeader'; labelLatex: string; isBaseCase: boolean; constructorParamNames?: readonly string[]; constructorName?: string; scrutinee?: string; isCases?: boolean }
  | { tag: 'exact'; exprLatex: string; solved: boolean; goalLatex?: string; error?: string; proofExprLatex?: string; isValueType?: boolean }
  | { tag: 'hole'; goalLatex?: string; isValueType?: boolean }
  | { tag: 'simp'; lemmas: readonly string[]; stepCount: number; preGoalLatex?: string; goalLatex?: string }
  | { tag: 'have'; name: string; expr: string; typeLatex?: string; proofExprLatex?: string; preGoalLatex?: string; goalLatex?: string; error?: string; hasProofTree?: boolean }
  | { tag: 'suffices'; name: string; goalLatex?: string; byExprLatex?: string }
  | { tag: 'subgoalHeader'; label: string; goalLatex?: string; isValueType?: boolean }
  | { tag: 'calcChain'; preGoalLatex?: string; steps: readonly CalcChainStep[] }
  | { tag: 'qed' };

/** A single step in a calc-style equational chain. */
export interface CalcChainStep {
  readonly nodeId: ProofNodeId;
  /** Goal equation AFTER this rewrite step (the new LHS = RHS). */
  readonly goalLatex?: string;
  /** The rewrite equation used (e.g., "a + 0 = a"). */
  readonly equationLatex?: string;
  /** Lemma name for the justification. */
  readonly lemmaName: string;
  /** Error from the tactic engine. */
  readonly error?: string;
}

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

/** Map Unicode Greek → LaTeX. */
const GREEK_LATEX: Record<string, string> = {
  'α': '\\alpha', 'β': '\\beta', 'γ': '\\gamma', 'δ': '\\delta',
  'ε': '\\varepsilon', 'ζ': '\\zeta', 'η': '\\eta', 'θ': '\\theta',
  'λ': '\\lambda', 'μ': '\\mu', 'π': '\\pi', 'σ': '\\sigma',
  'φ': '\\varphi', 'ψ': '\\psi', 'ω': '\\omega',
};

/** Render a variable name for LaTeX (italicize single chars, subscript digits, textify multi-char). */
function texName(name: string): string {
  // Single Greek letter: δ → \delta
  if (name.length === 1 && GREEK_LATEX[name]) return GREEK_LATEX[name];
  // Greek + digits: δ1 → \delta_{1}
  if (name.length >= 2 && GREEK_LATEX[name[0]] && /^\d+$/.test(name.slice(1))) {
    return `${GREEK_LATEX[name[0]]}_{${name.slice(1)}}`;
  }
  if (name.length === 1) return name;
  if (name.length === 2 && name[1] === "'") return `${name[0]}'`;
  // Single letter + digits: subscript (x0 → x_{0}, n12 → n_{12})
  if (/^[a-zA-Z]\d+$/.test(name)) return `{${name[0]}}_{${name.slice(1)}}`;
  // Multi-letter: upright text (escape underscores so KaTeX doesn't read them as subscript)
  return `\\mathit{${name.replace(/_/g, '\\_')}}`;
}

/** A synthetic induction inserted by nested-pattern desugaring —
 *  scrutinee is a fresh `_nested*` var and there is exactly one case. */
function isSyntheticNestedInduction(node: ProofNode): boolean {
  return node.tag === 'induction'
    && node.scrutinee.startsWith('_nested')
    && node.cases.length === 1;
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
  function walkBranch(parentId: ProofNodeId, label: string, goalLatex: string | undefined, body: ProofNode, depth: number, isValueType?: boolean): void {
    emit(parentId, depth, { tag: 'subgoalHeader', label, goalLatex, isValueType });
    walk(body, depth + 1);
  }

  function walk(node: ProofNode, depth: number): void {
    const info = goalMap.get(node.id);

    switch (node.tag) {
      case 'hole': {
        emit(node.id, depth, { tag: 'hole', goalLatex: info?.goalLatex, isValueType: info?.isValueType });
        break;
      }

      case 'exact': {
        const solved = info?.validation?.status === 'solved';
        const error = info?.validation?.status === 'error' ? info.validation.message : undefined;
        emit(node.id, depth, { tag: 'exact', exprLatex: node.expr, solved, goalLatex: info?.goalLatex, error, proofExprLatex: info?.proofExprLatex, isValueType: info?.isValueType });
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
        const { steps, tail } = collectChain(node, goalMap);
        const tailInfo = goalMap.get(tail.id);

        // Count consecutive rewrite-only steps for calc chain rendering
        const rewriteOnlySteps = steps.filter(s => s.type === 'rewrite');
        const hasNonRewrite = steps.some(s => s.type !== 'rewrite');

        // If we have 2+ consecutive rewrites with no unfold/fold mixed in,
        // emit a calc-style equational chain instead of individual items
        if (rewriteOnlySteps.length >= 2 && !hasNonRewrite) {
          const preGoalLatex = goalMap.get(steps[0].nodeId)?.goalLatex;
          const calcSteps: CalcChainStep[] = steps.map((step, si) => {
            const nextGoalLatex = si + 1 < steps.length
              ? goalMap.get(steps[si + 1].nodeId)?.goalLatex
              : tailInfo?.goalLatex;
            const stepError = goalMap.get(step.nodeId)?.tacticError;
            // Extract lemma name from the rewrite name — strip leading parens first
            const lemmaName = step.name.replace(/^\(+/, '').trim().split(/[\s(]/)[0];
            return {
              nodeId: step.nodeId,
              goalLatex: nextGoalLatex,
              equationLatex: step.equationLatex,
              lemmaName,
              error: stepError,
            };
          });
          // Emit the calc chain using the first step's nodeId (for cursor/click)
          emit(steps[0].nodeId, depth, { tag: 'calcChain', preGoalLatex, steps: calcSteps });
        } else {
          // Mixed chain or single step — emit individual items (existing behavior)
          for (let si = 0; si < steps.length; si++) {
            const step = steps[si];
            const nextGoalLatex = si + 1 < steps.length
              ? goalMap.get(steps[si + 1].nodeId)?.goalLatex
              : tailInfo?.goalLatex;
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

        // Compact form: when ALL children are simple `exact` nodes, collect
        // their proof expressions and embed them directly in the apply item.
        // The component renders these as a tight numbered list instead of
        // separate "Goal N: We must show TYPE / The result follows from PROOF"
        // sections — e.g., "(i) δF  (ii) MkPair(posF, ...)" instead of
        // "Goal 1: We must show ℝ / The result follows from δF".
        const allChildrenExact = node.children.length > 1 &&
          node.children.every(c => c.tag === 'exact');
        if (allChildrenExact) {
          const proofExprs = node.children.map(child => {
            const childInfo = goalMap.get(child.id);
            return childInfo?.proofExprLatex ?? (child as ExactNode).expr;
          });
          emit(node.id, depth, {
            tag: 'apply', name: node.name,
            preGoalLatex: info?.goalLatex, subgoalLatex,
            appliedArgsLatex: info?.appliedArgsLatex,
            error: info?.tacticError,
            proofExprs,
          });
          // Check if all children solved successfully → emit qed
          const allSolved = node.children.every(child => {
            const v = goalMap.get(child.id)?.validation;
            return v?.status === 'solved';
          });
          if (allSolved) {
            emit(node.id, depth, { tag: 'qed' });
          }
          break;
        }

        emit(node.id, depth, { tag: 'apply', name: node.name, preGoalLatex: info?.goalLatex, subgoalLatex, appliedArgsLatex: info?.appliedArgsLatex, error: info?.tacticError });
        if (node.children.length > 1) {
          // Multiple subgoals: use labeled branches with indentation
          for (let i = 0; i < node.children.length; i++) {
            const child = node.children[i];
            const childInfo = goalMap.get(child.id);
            walkBranch(node.id, `Goal ${i + 1}`, childInfo?.goalLatex, child, depth, childInfo?.isValueType);
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
        // Synthetic induction inserted by nested-pattern desugaring:
        // `cases _nested10 with | MkPair posF boundF => ...`
        // Hide it entirely — the outer case header already shows the user's
        // original nested pattern, so walking the single case body at the
        // current depth collapses the two levels back into one.
        if (isSyntheticNestedInduction(node)) {
          walk(node.cases[0].body, depth);
          break;
        }
        emit(node.id, depth, { tag: 'inductionHeader', scrutinee: node.scrutinee, scrutineeLatex: info?.scrutineeLatex, isCases: node.isCases });
        for (let i = 0; i < node.cases.length; i++) {
          const c = node.cases[i];
          const isBaseCase = !c.constructorParamNames || c.constructorParamNames.length === 0;
          // Prefer the registry-aware label computed by goal-computation
          // (so nested `@syntax` like `MkDPair → witness ...` applies).
          const registryLabel = goalMap.get(c.id)?.caseLabelLatex;
          emit(c.id, depth + 1, {
            tag: 'caseHeader',
            labelLatex: registryLabel ?? c.labelLatex ?? c.label,
            isBaseCase,
            constructorParamNames: c.constructorParamNames,
            constructorName: c.constructorName,
            scrutinee: node.scrutinee,
            isCases: node.isCases,
          });
          walk(c.body, depth + 2);
        }
        break;
      }

      case 'have': {
        const childInfo = goalMap.get(node.child.id);
        const childGoalLatex = childInfo?.goalLatex;
        // Find the hypothesis type from the child's context (last entry with this name)
        let hypType = childInfo?.hypotheses.find(h => h.name === node.name)?.type;
        // If child doesn't have the hypothesis, try the proofTree's goal (which IS the type)
        if (!hypType && node.proofTree) {
          const ptInfo = goalMap.get(node.proofTree.id);
          if (ptInfo?.goalLatex) hypType = ptInfo.goalLatex;
        }
        emit(node.id, depth, {
          tag: 'have',
          name: node.name,
          expr: node.expr,
          typeLatex: hypType,
          proofExprLatex: info?.proofExprLatex,
          preGoalLatex: info?.goalLatex,
          goalLatex: childGoalLatex,
          error: info?.tacticError,
          hasProofTree: !!node.proofTree,
        });
        // Walk the proofTree subtree (emits prose items for the interactive proof)
        if (node.proofTree) {
          walk(node.proofTree, depth + 1);
        }
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
