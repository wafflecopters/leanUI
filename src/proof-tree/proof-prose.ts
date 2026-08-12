/**
 * Proof Prose Generator — converts a proof tree + goal map into
 * natural-language mathematical prose items.
 *
 * Pure function with zero React or tactic-engine dependencies.
 * Consumes a proof tree and precomputed NodeGoalInfo map,
 * produces a flat array of ProseItems for rendering.
 */

import { ProofNode, ProofNodeId, CaseNode, ExactNode } from './proof-tree';
import { NodeGoalInfo, TypedHypothesis } from './goal-types';
import { renderNameLatex } from './name-latex';
import { splitAnonTuple } from './prose-row-helpers';

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
}

/** A group of variables sharing the same type in an intro line. */
export interface IntroGroup {
  readonly tokens: readonly IntroToken[];
  readonly typeLatex: string;
  /** Lean says this group states CONDITIONS (Props), not data — the prose
   *  folds it into the binder: "Let x ∈ ℝ with 0 < x", names de-emphasized. */
  readonly isProp?: boolean;
}

export type ProseItemKind =
  | { tag: 'intro'; latex: string; goalLatex?: string; groups?: readonly IntroGroup[] }
  | { tag: 'unfold'; name: string; occurrence?: number; preGoalLatex?: string; goalLatex?: string; error?: string }
  | { tag: 'fold'; name: string; occurrence?: number; preGoalLatex?: string; goalLatex?: string; error?: string }
  | { tag: 'rewrite'; name: string; reverse?: boolean; occurrences?: readonly number[]; equationLatex?: string; preGoalLatex?: string; goalLatex?: string; error?: string }
  | { tag: 'apply'; name: string; preGoalLatex?: string; subgoalLatex?: string[]; appliedArgsLatex?: string[]; error?: string; proofExprs?: readonly string[]; repeatedGoal?: boolean }
  | {
      tag: 'inductionHeader';
      scrutinee: string;
      scrutineeLatex?: string;
      isCases?: boolean;
      /** What each branch MEANS — the type of the single hypothesis it
       *  introduces (`δF ≤ δG` / `δG ≤ δF`). Present only when every case has
       *  one, so the header can read "Either A or B." like a paper. */
      caseMeanings?: readonly string[];
    }
  | {
      tag: 'caseHeader';
      labelLatex: string;
      isBaseCase: boolean;
      constructorParamNames?: readonly string[];
      /** Rendered type per param, positionally — what a hover shows. */
      paramTypeLatex?: readonly string[];
      constructorName?: string;
      scrutinee?: string;
      isCases?: boolean;
      /** The type of the one hypothesis this case introduces — what the case
       *  MEANS. A paper writes "Case δF ≤ δG:", not "Case (left (a)):". */
      meaningLatex?: string;
      /** The hypothesis's name, kept as a de-emphasized clickable handle. */
      meaningName?: string;
      /** Per bound name (destructures): is it a CONDITION — a fact worth
       *  stating inline ("dfPos : 0 < δ_F") — rather than data like δ_F : ℝ?
       *  Prop-likeness: genuinely Prop, OR the type depends on a name the
       *  PROOF introduced (initial declaration binders don't count). */
      paramIsCondition?: readonly boolean[];
      /** Fused have+destructure: `have hF := J` immediately unpacked by
       *  `obtain ⟨a, b⟩ := hF` reads as ONE sentence — "Choose a and b since
       *  J." — the way a paper introduces a witness. Holds J's latex. */
      chooseSinceLatex?: string;
      /** An `obtain ⟨a, b⟩ := e` row: no constructor to name, so the pattern
       *  renders as the anonymous constructor the proof actually writes. */
      anonymous?: boolean;
      /** Set when this is the split's ONLY case, which makes the split a
       *  destructuring rather than a case analysis: the "By cases on x" header
       *  gets no row of its own and is folded into this one, so the pair reads
       *  as a single line at a single indent level. */
      lead?: {
        /** The induction node this row stands in for — what deleting it removes. */
        nodeId: ProofNodeId;
        scrutinee: string;
        scrutineeLatex?: string;
        isCases?: boolean;
      };
    }
  | {
      tag: 'exact';
      exprLatex: string;
      solved: boolean;
      goalLatex?: string;
      error?: string;
      proofExprLatex?: string;
      isValueType?: boolean;
      repeatedGoal?: boolean;
      /** For ⟨tuple⟩ exacts: each component's INSTANTIATED type when the
       *  component is a hypothesis in scope — what a hover shows. */
      componentTypes?: readonly (string | null)[];
    }
  | { tag: 'hole'; goalLatex?: string; isValueType?: boolean; solved?: boolean; repeatedGoal?: boolean }
  | { tag: 'simp'; lemmas: readonly string[]; stepCount: number; preGoalLatex?: string; goalLatex?: string; error?: string }
  | { tag: 'have'; name: string; expr: string; typeLatex?: string; proofExprLatex?: string; preGoalLatex?: string; goalLatex?: string; error?: string; hasProofTree?: boolean }
  | { tag: 'suffices'; name: string; goalLatex?: string; byExprLatex?: string }
  | {
      tag: 'subgoalHeader';
      label: string;
      goalLatex?: string;
      isValueType?: boolean;
      /** The ONLY remaining obligation after value branches folded away —
       *  reads "It remains to show …", with no "Goal N:" tag. */
      remaining?: boolean;
    }
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
  readonly isProp?: boolean;
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
      groups.push({ names: [h.name], typeLatex: h.type, ...(h.isProp !== undefined ? { isProp: h.isProp } : {}) });
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
 * Each group contains the variables sharing one type.
 */
function buildIntroGroups(
  parentHyps: readonly TypedHypothesis[],
  childHyps: readonly TypedHypothesis[],
): IntroGroup[] {
  // Inaccessible (daggered) hypotheses are Lean's internal bookkeeping — e.g.
  // `cases (term)` asserts its major premise as `x✝` — and are NOT something
  // the sentence introduced. Never render them as bindings.
  const newHyps = childHyps.slice(parentHyps.length).filter((h) => !h.name.includes('✝'));
  if (newHyps.length === 0) return [];

  const stepNames = new Set(newHyps.map((h) => h.name));
  const condition = (h: TypedHypothesis): boolean =>
    h.isProp === true || (h.dependsOn ?? []).some((n) => stepNames.has(n) );
  const groups = groupHypotheses(newHyps.map((h) => ({ ...h, isProp: condition(h) })));
  let nameIdx = 0;
  return groups.map(g => ({
    tokens: g.names.map(name => {
      const hyp = newHyps[nameIdx];
      const token: IntroToken = {
        name,
        nameLatex: texName(name),
        nameIndex: nameIdx,
        typeLatex: g.typeLatex,
      };
      nameIdx++;
      return token;
    }),
    typeLatex: g.typeLatex,
    ...(g.isProp !== undefined ? { isProp: g.isProp } : {}),
  }));
}

/** Render a variable name for LaTeX (italicize single chars, subscript digits, textify multi-char). */
function texName(name: string): string {
  // Upright for multi-char names — math italic renders `epsPos` as the
  // product e·p·s·P·o·s. Same convention as the editor's texNameForProse,
  // so a name looks identical in a Let-row and in a case pattern.
  return renderNameLatex(name, 'textsf');
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
  // A conditional rewrite (with side goals) is NOT a plain chain step — it
  // renders as its own item with branches, so it must terminate the chain.
  if (node.tag === 'rewrite' && node.sideGoals && node.sideGoals.length > 0) return false;
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

  // Names present before the first tactic ran — the declaration's own binders.
  // A dependency on anything OUTSIDE this set marks a fact the proof built.
  const initialNames = new Set((goalMap.get(root.id)?.hypotheses ?? []).map((h) => h.name));

  /** Walk a proof branch with a labeled header, indented content. */
  function walkBranch(parentId: ProofNodeId, label: string, goalLatex: string | undefined, body: ProofNode, depth: number, isValueType?: boolean, remaining?: boolean): void {
    emit(parentId, depth, { tag: 'subgoalHeader', label, goalLatex, isValueType, ...(remaining ? { remaining: true } : {}) });
    walk(body, depth + 1);
  }

  function walk(node: ProofNode, depth: number): void {
    const info = goalMap.get(node.id);

    switch (node.tag) {
      case 'hole': {
        // A hole whose goal Lean reports as already closed (e.g. the
        // continuation after a `simp` that solved the goal) is DONE, not an open
        // obligation — flag it so the view shows ✓ rather than a stray `?`.
        emit(node.id, depth, { tag: 'hole', goalLatex: info?.goalLatex, isValueType: info?.isValueType, solved: info?.validation?.status === 'solved' });
        break;
      }

      case 'exact': {
        const solved = info?.validation?.status === 'solved';
        // Error from the TT validator (validation) OR the Lean round-trip
        // (tacticError) — so a failing `exact` shows red in the structured editor.
        const error = (info?.validation?.status === 'error' ? info.validation.message : undefined) ?? info?.tacticError;
        // Tuple components that are hypotheses in scope carry their
        // instantiated types, so the witness row can show "h : [] spans W"
        // on hover — Lean's answer, not a lookup of the general statement.
        const parts = splitAnonTuple(node.expr);
        const hypTypes = new Map((info?.hypotheses ?? []).map((h) => [h.name, h.type]));
        const componentTypes = parts?.map((c) => hypTypes.get(c.trim()) ?? null);
        emit(node.id, depth, {
          tag: 'exact', exprLatex: node.expr, solved, goalLatex: info?.goalLatex, error,
          proofExprLatex: info?.proofExprLatex, isValueType: info?.isValueType,
          ...(componentTypes?.some((t) => t !== null) ? { componentTypes } : {}),
        });
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
        // A CONDITIONAL rewrite leaves side goals (the lemma's premises). Render
        // it as a single step, then the rewritten goal continues inline, and
        // each side goal becomes a labeled branch — so the obligation (e.g.
        // `0 ≤ a` from summationSplit's `i ≤ n`) is visible right here rather
        // than surfacing later. (Not flattened into a calc chain.)
        if (node.tag === 'rewrite' && node.sideGoals && node.sideGoals.length > 0) {
          const childInfo = goalMap.get(node.child.id);
          emit(node.id, depth, {
            tag: 'rewrite',
            name: node.name,
            reverse: node.reverse,
            occurrences: node.occurrences,
            equationLatex: info?.unifiedEquationLatex,
            preGoalLatex: info?.goalLatex,
            goalLatex: childInfo?.goalLatex,
            error: info?.tacticError,
          });
          walk(node.child, depth); // rewritten (main) goal continues inline
          const many = node.sideGoals.length > 1;
          node.sideGoals.forEach((sg, i) => {
            const sgInfo = goalMap.get(sg.id);
            walkBranch(node.id, many ? `Side goal ${i + 1}` : 'Side goal', sgInfo?.goalLatex, sg, depth, sgInfo?.isValueType);
          });
          break;
        }
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
        // A 0-subgoal apply (e.g., `apply zeroLeOne` on `0 ≤ 1`) closes the
        // goal outright. Emit a qed marker so the prose shows the ∎ box,
        // matching what an exact-closing goal does (lines 262-264).
        if (node.children.length === 0 && info?.validation?.status === 'solved') {
          emit(node.id, depth, { tag: 'qed' });
        }
        if (node.children.length > 1) {
          // A VALUE branch already answered by a one-line exact is a CHOICE,
          // not a subgoal: it folds to "Take ⟨v⟩." with no Goal-N scaffolding
          // ("Goal 1: We must choose a value of type ℝ. By δ_F." was the
          // reviewer's #5). The remaining branches renumber; when only one is
          // left it reads "It remains to show …".
          const folded: boolean[] = node.children.map((child) => {
            const ci = goalMap.get(child.id);
            return ci?.isValueType === true && child.tag === 'exact';
          });
          const kept = folded.filter((f) => !f).length;
          let shown = 0;
          for (let i = 0; i < node.children.length; i++) {
            const child = node.children[i];
            const childInfo = goalMap.get(child.id);
            if (folded[i]) {
              // The choice itself, one line, no goal restatement.
              const c = child as ExactNode;
              emit(child.id, depth + 1, {
                tag: 'exact',
                exprLatex: c.expr,
                solved: true,
                isValueType: true,
                proofExprLatex: childInfo?.proofExprLatex,
              });
              continue;
            }
            shown++;
            walkBranch(
              node.id,
              kept === 1 ? '' : `Goal ${shown}`,
              childInfo?.goalLatex,
              child,
              depth,
              childInfo?.isValueType,
              kept === 1,
            );
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
        // A split with ONE case is a destructuring — `cases hG with | mk a b`
        // names the parts of something that only has one shape. Giving it a
        // header row and two levels of indent, the way a real case analysis
        // gets, marched a chain of them off the right edge of the page for no
        // information. So a sole case folds its header into its own row and
        // costs no indentation; a genuine split (2+ branches) keeps both.
        const soleCase = node.cases.length === 1;
        // What each branch MEANS: when a `cases` branch introduces exactly one
        // hypothesis, its TYPE is the sentence a paper would write ("Case
        // δF ≤ δG:"), and the header can read "Either A or B." — the
        // constructor name (`left`) is plumbing. Only when EVERY branch has a
        // single-hypothesis meaning; mixed splits keep the constructor form.
        const parentNames = new Set((info?.hypotheses ?? []).map((h) => h.name));
        const meanings = node.cases.map((c) => {
          const ci = goalMap.get(c.id) ?? goalMap.get(c.body.id);
          const fresh = (ci?.hypotheses ?? []).filter((h) => !parentNames.has(h.name));
          return fresh.length === 1 && fresh[0].type ? { name: fresh[0].name, type: fresh[0].type } : null;
        });
        const meaningful =
          !soleCase && node.isCases === true && node.cases.length >= 2 && meanings.every((m) => m !== null);
        if (!soleCase) {
          emit(node.id, depth, {
            tag: 'inductionHeader',
            scrutinee: node.scrutinee,
            scrutineeLatex: info?.scrutineeLatex,
            isCases: node.isCases,
            ...(meaningful ? { caseMeanings: meanings.map((m) => m!.type) } : {}),
          });
        }
        for (let i = 0; i < node.cases.length; i++) {
          const c = node.cases[i];
          let isBaseCase = !c.constructorParamNames || c.constructorParamNames.length === 0;
          // The Lean path produces bullet-cases with no recorded constructor
          // params, so the heuristic above would call every case a "base case".
          // Recover the distinction generically (no hard-coded constructor names)
          // from the goal state: a case that introduces hypotheses NOT present in
          // the induction's incoming goal (the constructor's recursive args / the
          // induction hypothesis) is the inductive step, not a base case.
          // A LONE unnamed case prints as a plain continuation and so has no
          // goal of its own; the head of its body carries the same goal.
          const caseInfo = goalMap.get(c.id) ?? goalMap.get(c.body.id);
          if (isBaseCase) {
            const parentHyps = new Set((info?.hypotheses ?? []).map((h) => h.name));
            const caseHyps = caseInfo?.hypotheses ?? [];
            if (caseHyps.some((h) => !parentHyps.has(h.name))) isBaseCase = false;
          }
          // Prefer the registry-aware label computed by goal-computation
          // (so nested `@syntax` like `MkDPair → witness ...` applies).
          const registryLabel = caseInfo?.caseLabelLatex;
          // The type of each bound param, so hovering a name can show it. The
          // names are the ones the case binds, so they resolve in its own goal.
          const caseHypTypes = new Map((caseInfo?.hypotheses ?? []).map((h) => [h.name, h.type]));
          const paramTypeLatex = c.constructorParamNames?.map((n) => caseHypTypes.get(n) ?? '');
          emit(c.id, soleCase ? depth : depth + 1, {
            tag: 'caseHeader',
            labelLatex: registryLabel ?? c.labelLatex ?? c.label,
            isBaseCase,
            constructorParamNames: c.constructorParamNames,
            ...(paramTypeLatex?.some((t) => t) ? { paramTypeLatex } : {}),
            constructorName: c.constructorName,
            scrutinee: node.scrutinee,
            isCases: node.isCases,
            ...(meaningful ? { meaningLatex: meanings[i]!.type, meaningName: meanings[i]!.name } : {}),
            ...(soleCase
              ? { lead: { nodeId: node.id, scrutinee: node.scrutinee, scrutineeLatex: info?.scrutineeLatex, isCases: node.isCases } }
              : {}),
          });
          walk(c.body, soleCase ? depth : depth + 2);
        }
        break;
      }

      // `obtain ⟨a, b, c⟩ := e` — bound names, no branch, so no indent. Same
      // row shape as a sole case (which is the same thing said with `cases`).
      case 'destructure': {
        const childInfo = goalMap.get(node.child.id);
        const byName = new Map((childInfo?.hypotheses ?? []).map((h) => [h.name, h]));
        const nameTypeLatex = node.names.map((n) => byName.get(n)?.type ?? '');
        // A bound name is a CONDITION when its type is Prop, or depends on a
        // name the PROOF introduced. `dfPos : 0 < δ_F` depends on δ_F (proof-
        // introduced) → condition; `δ_F : ℝ` depends only on the declaration's
        // own binders → data. Works for Type-valued relations, where isProp
        // alone says no to everything.
        const isCondition = node.names.map((n) => {
          const h = byName.get(n);
          if (!h) return false;
          return h.isProp === true || (h.dependsOn ?? []).some((d) => !initialNames.has(d));
        });
        emit(node.id, depth, {
          tag: 'caseHeader',
          labelLatex: '',
          isBaseCase: false,
          isCases: true,
          anonymous: true,
          constructorParamNames: node.names,
          ...(isCondition.some(Boolean) ? { paramIsCondition: isCondition } : {}),
          ...(nameTypeLatex.some((t) => t) ? { paramTypeLatex: nameTypeLatex } : {}),
          lead: {
            nodeId: node.id,
            scrutinee: node.scrutinee,
            scrutineeLatex: info?.scrutineeLatex,
            isCases: true,
          },
        });
        walk(node.child, depth);
        break;
      }

      case 'have': {
        // `have hF := J` immediately unpacked by `obtain ⟨…⟩ := hF`: the pair
        // is the mathematician's "Choose δ_F and fProof … since J" — one
        // sentence, not an Observe + a Write. Only when the have has no
        // proof subtree and the destructure consumes exactly its name.
        if (!node.proofTree && node.child.tag === 'destructure' && node.child.scrutinee === node.name
            && info?.proofExprLatex) {
          const d = node.child;
          const dInfo = goalMap.get(d.child.id);
          const byName = new Map((dInfo?.hypotheses ?? []).map((h) => [h.name, h]));
          const types = d.names.map((n) => byName.get(n)?.type ?? '');
          const conds = d.names.map((n) => {
            const h = byName.get(n);
            if (!h) return false;
            return h.isProp === true || (h.dependsOn ?? []).some((dep) => !initialNames.has(dep));
          });
          emit(d.id, depth, {
            tag: 'caseHeader',
            labelLatex: '',
            isBaseCase: false,
            isCases: true,
            anonymous: true,
            constructorParamNames: d.names,
            ...(conds.some(Boolean) ? { paramIsCondition: conds } : {}),
            ...(types.some(Boolean) ? { paramTypeLatex: types } : {}),
            chooseSinceLatex: info.proofExprLatex,
            lead: { nodeId: d.id, scrutinee: node.name, isCases: true },
          });
          walk(d.child, depth);
          break;
        }
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
        // Show only the lemmas that ACTUALLY fired during this simp run, not
        // every lemma in the @simp set that was offered to the engine. The
        // engine receives the full set (often dozens of lemmas) but only a
        // handful do useful work on any one goal — listing all of them is
        // noisy and misleading ("Simplifying using [12 lemmas] (2 steps)"
        // when only 2 lemmas actually fired). Dedupe in encounter order so
        // a lemma that fires twice shows up once.
        const firedLemmas: string[] = [];
        const seen = new Set<string>();
        for (const step of node.steps) {
          const name = (step.tag === 'rewrite' || step.tag === 'unfold') ? step.name : null;
          if (name && !seen.has(name)) { seen.add(name); firedLemmas.push(name); }
        }
        emit(node.id, depth, {
          tag: 'simp',
          // Fall back to the passed-in `lemmas` if no step recorded a name —
          // shouldn't happen in practice, but keeps the prose readable.
          lemmas: firedLemmas.length > 0 ? firedLemmas : node.lemmas,
          stepCount: node.steps.length,
          preGoalLatex: info?.goalLatex,
          goalLatex: childGoalLatex,
          error: info?.tacticError,
        });
        // Steps are already replayed by the engine; just recurse into child
        walk(node.child, depth);
        break;
      }
    }
  }

  walk(root, 0);
  return markRepeatedGoals(items);
}

/** The goal LaTeX an item DISPLAYS, if any — used to spot repetition. */
function displayedGoal(kind: ProseItemKind): string | undefined {
  switch (kind.tag) {
    case 'intro':
    case 'unfold':
    case 'fold':
    case 'rewrite':
    case 'simp':
    case 'have':
    case 'subgoalHeader':
    case 'hole':
    case 'exact':
      return kind.goalLatex;
    case 'apply':
      // A 1-subgoal apply displays that subgoal inline ("It remains to show
      // S"); a 0- or many-subgoal apply displays its INCOMING goal ("We must
      // show G. This holds by construction: …").
      return kind.subgoalLatex?.length === 1 ? kind.subgoalLatex[0] : kind.preGoalLatex;
    default:
      return undefined;
  }
}

/**
 * Flag "We must show G" rows whose G is EXACTLY a goal already on screen, so
 * the renderer can say "the claim above" instead of repeating a display
 * equation. A paper states a claim once; the repeat came from case splits
 * (each branch re-showing the goal the split didn't change) and cost a third
 * of the proof's height.
 *
 * "Already on screen" means ANYWHERE earlier in the document, not just the
 * previous row: the second case of a split still matches the goal shown
 * before the split even when the first branch displayed other goals in
 * between. (The plain last-row compare missed exactly that, and limitAdd
 * displayed the same ∃δ-bundle three times.) When the identical formula did
 * appear above — even in a sibling branch — "the claim above" is what a
 * paper says; symmetric cases read "similarly", not twice at full width.
 *
 * Only hole/exact/apply rows are flagged — a transform step's goal genuinely
 * changed, so equality there is information.
 */
function markRepeatedGoals(items: ProseItem[]): ProseItem[] {
  const seen = new Set<string>();
  return items.map((item) => {
    const g = displayedGoal(item.kind);
    if (!g) return item;
    const repeated = seen.has(g);
    seen.add(g);
    const flaggable = item.kind.tag === 'hole' || item.kind.tag === 'exact' || item.kind.tag === 'apply';
    if (!repeated || !flaggable) return item;
    return { ...item, kind: { ...item.kind, repeatedGoal: true } };
  });
}
