import { normalizeBinderNameInput } from './name-latex';
import { parseHaveInput } from './haveInput';
import type { TypedProofContext } from './goal-types';
import type { ProofNodeId, ProofTreeState } from './proof-tree';
import {
  applyInduction,
  applySimp,
  clearNode,
  editIntroName,
  findCase,
  findNode,
  mkExact,
  isCursorInSubtree,
  mkHave,
  mkHole,
  mkRewrite,
  mkSimp,
  replaceNode,
  toggleInductionCollapse,
  toggleSimpCollapse,
  updateCase,
} from './proof-tree';
import type { RewriteSuggestion, TacticSuggestion } from './suggestion-types';
import {
  applyTacticCommandsAtCursor,
  buildCaseBranchFromCaseNode,
  buildApplyTacticCommands,
  buildHaveTacticCommands,
  buildInductionTacticCommands,
  rebuildInductionNodeFromCaseBranches,
} from './tactic-command-bridge';

export type ProofTreeManualTacticMode =
  | { tactic: 'intros' }
  | { tactic: 'induction' }
  | { tactic: 'cases' }
  | { tactic: 'exact' }
  | { tactic: 'unfold' }
  | { tactic: 'fold' }
  | { tactic: 'rewrite' }
  | { tactic: 'rewrite_rev' }
  | { tactic: 'apply' }
  | { tactic: 'simp' }
  | { tactic: 'have' };

export interface ProofTreeSuggestionContext {
  readonly typedContext?: TypedProofContext | null;
  readonly editingNames?: readonly string[] | null;
  readonly editingSuggestionId?: string | null;
}

export interface ProofTreeManualTacticContext {
  readonly typedContext?: TypedProofContext | null;
  /** How many subgoals `apply <name>` opens — answered from the lemma's type in
   *  the Lean declaration list (`src/lean/rewriteCandidates.ts`). */
  readonly computeApplySubgoalCount?: (
    root: ProofTreeState['root'],
    cursorNodeId: number,
    name: string,
  ) => number;
  /** How many SIDE GOALS `rw [name]` leaves (the lemma's premises). When > 0 the
   *  rewrite is created with that many side-goal holes, so a conditional
   *  rewrite's obligations are visible immediately. */
  readonly computeRewriteSideGoalCount?: (name: string) => number;
  /** How many branches a split on `scrutinee` opens — one per constructor of
   *  its type, answered from the extractor's facts (`src/lean/caseBranches.ts`).
   *  `null` means nothing in scope knows; the caller opens a single branch
   *  rather than inventing a shape. */
  readonly computeCaseBranchCount?: (scrutinee: string) => number | null;
}

export type ProofTreeBinderRenameTarget =
  | { tag: 'have'; nodeId: ProofNodeId }
  | { tag: 'introToken'; nodeId: ProofNodeId; nameIndex: number }
  | { tag: 'caseParam'; nodeId: ProofNodeId; paramIndex: number };

function splitNames(value: string): string[] {
  return value.split(/[\s,]+/).filter(Boolean);
}

const LATEX_TO_UNICODE: Record<string, string> = {
  '\\alpha': 'α', '\\beta': 'β', '\\gamma': 'γ', '\\delta': 'δ',
  '\\epsilon': 'ε', '\\varepsilon': 'ε', '\\zeta': 'ζ', '\\eta': 'η',
  '\\theta': 'θ', '\\lambda': 'λ', '\\mu': 'μ', '\\pi': 'π',
  '\\sigma': 'σ', '\\varphi': 'φ', '\\psi': 'ψ', '\\omega': 'ω',
};

export function convertMathEditorSourceToUnicode(source: string): string {
  return source.replace(/\\[a-zA-Z]+/g, match => LATEX_TO_UNICODE[match] ?? match);
}

/**
 * Open a `cases`/`induction` on a scrutinee.
 *
 * The TT path looked the scrutinee's type up in an in-process inductive map to
 * name the constructor cases up front. On Lean the names come from the goal
 * round-trip instead (`enrichInductionCases` renames the placeholder cases once
 * Lean reports them), so this starts with placeholder branches.
 *
 * How MANY branches comes from `ctx.computeCaseBranchCount` — one per
 * constructor of the scrutinee's type. This used to be two, always, labelled
 * `n = 0` and `n = k'`: Nat's shape written into a layer that is supposed to
 * work for any type. That is right for Nat, leaves a stray empty branch on a
 * one-constructor structure, and silently loses branches on anything wider.
 * When nothing knows the type we open ONE branch — an honest "I don't know yet"
 * that the round-trip corrects — rather than guessing a shape.
 */
function applyInductionFromContext(
  state: ProofTreeState,
  scrutinee: string,
  tacticName: 'induction' | 'cases',
  ctx?: ProofTreeManualTacticContext,
): ProofTreeState | null {
  const branches = ctx?.computeCaseBranchCount?.(scrutinee) ?? 1;
  const labels = Array.from({ length: Math.max(1, branches) }, () => '?');
  return applyInduction(state, scrutinee, labels, tacticName);
}

function inferInductionSuggestionTacticName(
  suggestion: Pick<TacticSuggestion, 'label' | 'labelLatex'>,
): 'induction' | 'cases' {
  const label = suggestion.label.toLowerCase();
  if (label.startsWith('destructure ') || label.startsWith('cases ')) {
    return 'cases';
  }
  if (suggestion.labelLatex?.includes('\\text{cases }')) {
    return 'cases';
  }
  return 'induction';
}

function findInductionAndCase(
  root: ProofTreeState['root'],
  caseId: ProofNodeId,
): { node: Extract<ProofTreeState['root'], { tag: 'induction' }>; caseIndex: number } | null {
  switch (root.tag) {
    case 'induction': {
      const caseIndex = root.cases.findIndex(c => c.id === caseId);
      if (caseIndex >= 0) return { node: root, caseIndex };
      for (const c of root.cases) {
        const nested = findInductionAndCase(c.body, caseId);
        if (nested) return nested;
      }
      return null;
    }
    case 'intros':
    case 'destructure':
    case 'unfold':
    case 'fold':
    case 'rewrite':
      return findInductionAndCase(root.child, caseId);
    case 'apply':
      for (const child of root.children) {
        const nested = findInductionAndCase(child, caseId);
        if (nested) return nested;
      }
      return null;
    case 'simp':
      for (const step of root.steps) {
        const nested = findInductionAndCase(step, caseId);
        if (nested) return nested;
      }
      return findInductionAndCase(root.child, caseId);
    case 'have':
      if (root.proofTree) {
        const nested = findInductionAndCase(root.proofTree, caseId);
        if (nested) return nested;
      }
      return findInductionAndCase(root.child, caseId);
    case 'suffices':
      if (root.byProof) {
        const nested = findInductionAndCase(root.byProof, caseId);
        if (nested) return nested;
      }
      return findInductionAndCase(root.child, caseId);
    case 'exact':
    case 'hole':
      return null;
  }
}

function escapeRegExp(s: string): string {
  return s.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
}

function replaceHaveNodeAtId(
  root: ProofTreeState['root'],
  haveNodeId: ProofNodeId,
  updater: (node: Extract<ProofTreeState['root'], { tag: 'have' }>) => ProofTreeState['root'],
): ProofTreeState['root'] | null {
  if (root.id === haveNodeId && root.tag === 'have') {
    return updater(root);
  }

  switch (root.tag) {
    case 'intros':
    case 'destructure':
    case 'unfold':
    case 'fold':
    case 'rewrite': {
      const newChild = replaceHaveNodeAtId(root.child, haveNodeId, updater);
      return newChild ? { ...root, child: newChild } : null;
    }
    case 'apply': {
      for (let i = 0; i < root.children.length; i++) {
        const newChild = replaceHaveNodeAtId(root.children[i], haveNodeId, updater);
        if (newChild) {
          const newChildren = [...root.children];
          newChildren[i] = newChild;
          return { ...root, children: newChildren };
        }
      }
      return null;
    }
    case 'induction': {
      for (let i = 0; i < root.cases.length; i++) {
        const c = root.cases[i];
        const newBody = replaceHaveNodeAtId(c.body, haveNodeId, updater);
        if (newBody) {
          const newCases = [...root.cases];
          newCases[i] = { ...c, body: newBody };
          return { ...root, cases: newCases };
        }
      }
      return null;
    }
    case 'simp': {
      for (let i = 0; i < root.steps.length; i++) {
        const newStep = replaceHaveNodeAtId(root.steps[i], haveNodeId, updater);
        if (newStep) {
          const newSteps = [...root.steps];
          newSteps[i] = newStep;
          return { ...root, steps: newSteps };
        }
      }
      const newChild = replaceHaveNodeAtId(root.child, haveNodeId, updater);
      return newChild ? { ...root, child: newChild } : null;
    }
    case 'suffices': {
      if (root.byProof) {
        const newBy = replaceHaveNodeAtId(root.byProof, haveNodeId, updater);
        if (newBy) return { ...root, byProof: newBy };
      }
      const newChild = replaceHaveNodeAtId(root.child, haveNodeId, updater);
      return newChild ? { ...root, child: newChild } : null;
    }
    case 'have': {
      if (root.proofTree) {
        const newProof = replaceHaveNodeAtId(root.proofTree, haveNodeId, updater);
        if (newProof) return { ...root, proofTree: newProof };
      }
      const newChild = replaceHaveNodeAtId(root.child, haveNodeId, updater);
      return newChild ? { ...root, child: newChild } : null;
    }
    case 'exact':
    case 'hole':
      return null;
  }
}

function rewriteHaveReferenceSubtree(
  node: ProofTreeState['root'],
  oldName: string,
  newName: string,
): ProofTreeState['root'] {
  const replaceNameInExpr = (expr: string): string =>
    expr.replace(new RegExp(`(?<=^|[\\s()])${escapeRegExp(oldName)}(?=$|[\\s()])`, 'g'), newName);

  switch (node.tag) {
    case 'exact':
      return { ...node, expr: replaceNameInExpr(node.expr) };
    case 'have':
      return {
        ...node,
        expr: replaceNameInExpr(node.expr),
        child: rewriteHaveReferenceSubtree(node.child, oldName, newName),
        proofTree: node.proofTree ? rewriteHaveReferenceSubtree(node.proofTree, oldName, newName) : undefined,
      };
    case 'intros':
    case 'destructure':
    case 'unfold':
    case 'fold':
    case 'rewrite':
      return { ...node, child: rewriteHaveReferenceSubtree(node.child, oldName, newName) };
    case 'simp':
      return {
        ...node,
        steps: node.steps.map(step => rewriteHaveReferenceSubtree(step, oldName, newName)),
        child: rewriteHaveReferenceSubtree(node.child, oldName, newName),
      };
    case 'apply':
      return { ...node, children: node.children.map(child => rewriteHaveReferenceSubtree(child, oldName, newName)) };
    case 'induction':
      return { ...node, cases: node.cases.map(c => ({ ...c, body: rewriteHaveReferenceSubtree(c.body, oldName, newName) })) };
    case 'suffices':
      return {
        ...node,
        child: rewriteHaveReferenceSubtree(node.child, oldName, newName),
        byProof: node.byProof ? rewriteHaveReferenceSubtree(node.byProof, oldName, newName) : undefined,
      };
    case 'hole':
      return node;
  }
}

export function updateHaveExprInProofTree(
  state: ProofTreeState,
  haveNodeId: ProofNodeId,
  newExpr: string,
): ProofTreeState | null {
  const newRoot = replaceHaveNodeAtId(state.root, haveNodeId, node => ({ ...node, expr: newExpr }));
  return newRoot ? { ...state, root: newRoot } : null;
}

export function commitHaveExprSourceInProofTree(
  state: ProofTreeState,
  haveNodeId: ProofNodeId,
  rawExpr: string,
): ProofTreeState | null {
  const newExpr = convertMathEditorSourceToUnicode(rawExpr.trim());
  if (!newExpr) return null;
  const node = findNode(state.root, haveNodeId);
  if (!node || node.tag !== 'have' || node.expr === newExpr) return null;
  return updateHaveExprInProofTree(state, haveNodeId, newExpr);
}

export function renameHaveBindingInProofTree(
  state: ProofTreeState,
  haveNodeId: ProofNodeId,
  newName: string,
): ProofTreeState | null {
  const haveNode = findNode(state.root, haveNodeId);
  if (!haveNode || haveNode.tag !== 'have') return null;
  const oldName = haveNode.name;

  const newRoot = replaceHaveNodeAtId(state.root, haveNodeId, node => ({
    ...node,
    name: newName,
    child: rewriteHaveReferenceSubtree(node.child, oldName, newName),
  }));
  return newRoot ? { ...state, root: newRoot } : null;
}

export function commitProofTreeBinderRename(
  state: ProofTreeState,
  target: ProofTreeBinderRenameTarget,
  rawName: string,
): ProofTreeState | null {
  const newName = normalizeBinderNameInput(rawName.trim());
  if (!newName) return null;

  switch (target.tag) {
    case 'have': {
      const node = findNode(state.root, target.nodeId);
      if (!node || node.tag !== 'have' || node.name === newName) return null;
      return renameHaveBindingInProofTree(state, target.nodeId, newName);
    }
    case 'introToken': {
      const node = findNode(state.root, target.nodeId);
      if (!node || node.tag !== 'intros') return null;
      if (target.nameIndex < 0 || target.nameIndex >= node.names.length) return null;
      if (node.names[target.nameIndex] === newName) return null;
      return renameIntroTokenInProofTree(state, target.nodeId, target.nameIndex, newName);
    }
    case 'caseParam': {
      const induction = findInductionAndCase(state.root, target.nodeId);
      if (!induction) return null;
      const params = induction.node.cases[induction.caseIndex]?.constructorParamNames;
      if (!params || target.paramIndex < 0 || target.paramIndex >= params.length) return null;
      if (params[target.paramIndex] === newName) return null;
      return renameCaseParamInProofTree(state, target.nodeId, target.paramIndex, newName);
    }
  }
}

export function clearProofTreeNode(
  state: ProofTreeState,
  nodeId: ProofNodeId,
): ProofTreeState | null {
  return clearNode(state, nodeId);
}

export function renameIntroTokenInProofTree(
  state: ProofTreeState,
  nodeId: ProofNodeId,
  nameIndex: number,
  newName: string,
): ProofTreeState | null {
  return editIntroName(state, nodeId, nameIndex, newName);
}

export function renameCaseParamInProofTree(
  state: ProofTreeState,
  caseId: ProofNodeId,
  paramIndex: number,
  newName: string,
): ProofTreeState | null {
  const induction = findInductionAndCase(state.root, caseId);
  if (!induction) return null;
  const { node, caseIndex } = induction;
  const branches = node.cases.map(buildCaseBranchFromCaseNode);
  const target = branches[caseIndex];
  if (!target || paramIndex < 0 || paramIndex >= target.params.length) return null;
  const param = target.params[paramIndex];
  if (param.tag !== 'var') return null;
  const nextBranches = [...branches];
  nextBranches[caseIndex] = {
    ...target,
    params: target.params.map((p, index) => index === paramIndex ? { tag: 'var', name: newName } : p),
  };
  const rebuilt = rebuildInductionNodeFromCaseBranches(node, nextBranches);
  return { root: replaceNode(state.root, node.id, rebuilt), cursor: state.cursor };
}

export function addInductionCaseInProofTree(
  state: ProofTreeState,
  inductionId: ProofNodeId,
  label: string,
): ProofTreeState | null {
  const node = findNode(state.root, inductionId);
  if (!node || node.tag !== 'induction') return null;
  const rebuilt = rebuildInductionNodeFromCaseBranches(node, [
    ...node.cases.map(buildCaseBranchFromCaseNode),
    { constructor: label, params: [], tactics: [] },
  ]);
  const newRoot = replaceNode(state.root, inductionId, rebuilt);
  const newCase = rebuilt.cases[rebuilt.cases.length - 1];
  return { root: newRoot, cursor: { nodeId: newCase.body.id } };
}

export function removeInductionCaseInProofTree(
  state: ProofTreeState,
  inductionId: ProofNodeId,
  caseIndex: number,
): ProofTreeState | null {
  const node = findNode(state.root, inductionId);
  if (!node || node.tag !== 'induction') return null;
  if (node.cases.length <= 1 || caseIndex < 0 || caseIndex >= node.cases.length) return null;
  const removedCase = node.cases[caseIndex];
  const rebuilt = rebuildInductionNodeFromCaseBranches(
    node,
    node.cases.map(buildCaseBranchFromCaseNode).filter((_, index) => index !== caseIndex),
  );
  const newRoot = replaceNode(state.root, inductionId, rebuilt);
  if (removedCase.id === state.cursor.nodeId || isCursorInSubtree(removedCase.body, state.cursor.nodeId)) {
    const fallbackIdx = Math.min(caseIndex, rebuilt.cases.length - 1);
    return { root: newRoot, cursor: { nodeId: rebuilt.cases[fallbackIdx].body.id } };
  }
  return { root: newRoot, cursor: state.cursor };
}

export function toggleCaseCollapseInProofTree(
  state: ProofTreeState,
  caseId: ProofNodeId,
): ProofTreeState {
  const caseNode = findCase(state.root, caseId);
  if (!caseNode) return state;
  const newCollapsed = !caseNode.collapsed;
  const newRoot = updateCase(state.root, caseId, c => ({ ...c, collapsed: newCollapsed }));
  let cursor = state.cursor;
  if (newCollapsed && isCursorInSubtree(caseNode.body, state.cursor.nodeId)) {
    cursor = { nodeId: caseId };
  }
  return { root: newRoot, cursor };
}

export function toggleSimpCollapseInProofTree(
  state: ProofTreeState,
  nodeId: ProofNodeId,
): ProofTreeState | null {
  return toggleSimpCollapse(state, nodeId);
}

export function toggleInductionCollapseInProofTree(
  state: ProofTreeState,
  nodeId: ProofNodeId,
): ProofTreeState | null {
  return toggleInductionCollapse(state, nodeId);
}

export function applySuggestionToProofTreeState(
  state: ProofTreeState,
  suggestion: TacticSuggestion,
  ctx: ProofTreeSuggestionContext,
): ProofTreeState | null {
  if (suggestion.tacticCommands && suggestion.tacticCommands.length > 0) {
    return applyTacticCommandsAtCursor(state, suggestion.tacticCommands);
  }

  if (suggestion.id === 'exact-refl') {
    return applyTacticCommandsAtCursor(state, [{ name: 'exact', args: ['refl'] }]);
  }

  if (suggestion.id.startsWith('unfold-')) {
    const name = suggestion.id.slice('unfold-'.length);
    return applyTacticCommandsAtCursor(state, [{ name: 'unfold', args: [name] }]);
  }

  if (suggestion.id.startsWith('induction-')) {
    const scrutinee = suggestion.id.slice('induction-'.length);
    return applyInductionFromContext(state, scrutinee, inferInductionSuggestionTacticName(suggestion), ctx);
  }

  if (suggestion.id.startsWith('fold-')) {
    const name = suggestion.foldName ?? suggestion.id.slice('fold-'.length);
    return applyTacticCommandsAtCursor(state, [{ name: 'fold', args: [name] }]);
  }

  if (suggestion.id.startsWith('exact-hyp-')) {
    const name = suggestion.id.slice('exact-hyp-'.length);
    return applyTacticCommandsAtCursor(state, [{ name: 'exact', args: [name] }]);
  }

  if (suggestion.id.startsWith('apply-hyp-')) {
    const name = suggestion.id.slice('apply-hyp-'.length);
    return applyTacticCommandsAtCursor(state, buildApplyTacticCommands(name, suggestion.numSubgoals ?? 1));
  }

  if (suggestion.id.startsWith('apply-def-')) {
    const name = suggestion.id.slice('apply-def-'.length);
    return applyTacticCommandsAtCursor(state, buildApplyTacticCommands(name, suggestion.numSubgoals ?? 1));
  }


  if (suggestion.id.startsWith('construct-')) {
    const ctorName = suggestion.applyCtorName ?? suggestion.id.slice('construct-'.length);
    return applyTacticCommandsAtCursor(state, buildApplyTacticCommands(ctorName, suggestion.numSubgoals ?? 1, true));
  }


  if (suggestion.id.startsWith('rewrite-') || suggestion.id.startsWith('simp-')) {
    const rw = suggestion as RewriteSuggestion;
    return applyTacticCommandsAtCursor(state, [{
      name: 'rewrite',
      args: [rw.rewriteName],
      rewriteOptions: {
        reverse: rw.reverse,
        occurrences: rw.occurrences,
        targetHead: rw.targetHead,
      },
    }]);
  }

  const names = ctx.editingSuggestionId === suggestion.id && ctx.editingNames
    ? [...ctx.editingNames]
    : [...(suggestion.proposedNames ?? [])];
  if (names.length === 0) return null;
  const introName = names.length === 1 ? 'intro' : 'intros';
  return applyTacticCommandsAtCursor(state, [{ name: introName, args: [...names] }]);
}

/**
 * Lean-backend rewrite: build the rewrite node directly so a CONDITIONAL lemma's
 * side goals (its premises) appear as visible bullet branches immediately.
 * Returns null when not applicable (no Lean side-goal counter, the lemma leaves
 * no side goals, or the cursor isn't a hole) — the caller then uses the normal
 * single-child rewrite path.
 */
function applyLeanRewriteWithSideGoals(
  state: ProofTreeState,
  name: string,
  reverse: boolean,
  ctx: ProofTreeManualTacticContext,
): ProofTreeState | null {
  if (!ctx.computeRewriteSideGoalCount) return null;
  const count = ctx.computeRewriteSideGoalCount(name);
  if (count <= 0) return null;
  const node = findNode(state.root, state.cursor.nodeId);
  if (!node || node.tag !== 'hole') return null;
  const mainHole = mkHole();
  const sideGoals = Array.from({ length: count }, () => mkHole());
  const rw = mkRewrite(name, mainHole, reverse, undefined, undefined, undefined, undefined, sideGoals);
  const newRoot = replaceNode(state.root, state.cursor.nodeId, rw);
  return { root: newRoot, cursor: { nodeId: mainHole.id } };
}

export function applyManualProofTreeTactic(
  state: ProofTreeState,
  tacticMode: ProofTreeManualTacticMode | null,
  value: string,
  ctx: ProofTreeManualTacticContext,
): ProofTreeState | null {
  if (!tacticMode) return null;

  // Tray inputs accept LaTeX-style names (`\epsilon`): normalize to unicode
  // (ε) — a valid identifier on both engines — before any tactic parses the
  // value. Without this, `intros \epsilon` sends a literal backslash to Lean.
  value = convertMathEditorSourceToUnicode(value);

  switch (tacticMode.tactic) {
    case 'intros': {
      const names = splitNames(value);
      if (names.length === 0) return null;
      const introName = names.length === 1 ? 'intro' : 'intros';
      return applyTacticCommandsAtCursor(state, [{ name: introName, args: [...names] }]);
    }

    case 'induction': {
      const scrutinee = value.trim();
      if (!scrutinee) return null;
      return applyInductionFromContext(state, scrutinee, 'induction', ctx);
    }

    // `cases` splits on an arbitrary EXPRESSION, not just a hypothesis name —
    // `cases leTotal a b` is how a proof does "either a ≤ b or b ≤ a", and
    // without this the only route to it was a suggestion pill happening to
    // offer it. How many branches it opens is measured afterwards (the session
    // trials it and expands the node), since only Lean knows.
    case 'cases': {
      const scrutinee = value.trim();
      if (!scrutinee) return null;
      return applyInductionFromContext(state, scrutinee, 'cases', ctx);
    }

    case 'exact': {
      const expr = value.trim();
      if (!expr) return null;
      // Keep the user's expression text VERBATIM: it is Lean source, and only
      // Lean parses Lean. (The deleted TT round-trip used to rewrite notation
      // into TT spellings — `ε / 2` → `div ε 2` — which real Lean rejects.)
      {
        const node = findNode(state.root, state.cursor.nodeId);
        if (!node || node.tag !== 'hole') return null;
        return {
          root: replaceNode(state.root, state.cursor.nodeId, mkExact(expr)),
          cursor: state.cursor,
        };
      }
      return applyTacticCommandsAtCursor(state, [{ name: 'exact', args: [expr] }]);
    }

    case 'unfold': {
      const name = value.trim();
      if (!name) return null;
      return applyTacticCommandsAtCursor(state, [{ name: 'unfold', args: [name] }]);
    }

    case 'fold': {
      const name = value.trim();
      if (!name) return null;
      return applyTacticCommandsAtCursor(state, [{ name: 'fold', args: [name] }]);
    }

    case 'rewrite': {
      const name = value.trim();
      if (!name) return null;
      const leanRw = applyLeanRewriteWithSideGoals(state, name, false, ctx);
      if (leanRw) return leanRw;
      return applyTacticCommandsAtCursor(state, [{ name: 'rewrite', args: [name] }]);
    }

    case 'rewrite_rev': {
      const name = value.trim();
      if (!name) return null;
      const leanRw = applyLeanRewriteWithSideGoals(state, name, true, ctx);
      if (leanRw) return leanRw;
      return applyTacticCommandsAtCursor(state, [{
        name: 'rewrite',
        args: [name],
        rewriteOptions: { reverse: true },
      }]);
    }

    case 'apply': {
      const name = value.trim();
      if (!name) return null;
      let numChildren = 1;
      // The TT counter needs kernelType+definitions; a Lean-backed counter
      // (which estimates from the lemma type) needs neither — so call whatever
      // counter is provided, as long as the TT one has its kernel inputs.
      if (ctx.computeApplySubgoalCount) {
        numChildren = ctx.computeApplySubgoalCount(state.root, state.cursor.nodeId, name);
      }
      return applyTacticCommandsAtCursor(state, buildApplyTacticCommands(name, numChildren));
    }

    case 'have': {
      const parsed = parseHaveInput(value);
      if (!parsed) return null;
      // A TYPED have (`h1 : 0 < ε / 2`) states an obligation and opens a goal
      // for it, with the rest of the proof continuing below — the shape an ε-δ
      // proof is written in, and what hoisting an obligation produces. The
      // cursor lands on the OBLIGATION: you stated it because you mean to prove
      // it.
      if (parsed.kind === 'typed') {
        const node = findNode(state.root, state.cursor.nodeId);
        if (!node || node.tag !== 'hole') return null;
        const obligation = mkHole();
        const rest = mkHole();
        const inserted = mkHave(parsed.name, '', rest, parsed.typeExpr, obligation);
        return {
          root: replaceNode(state.root, state.cursor.nodeId, inserted),
          cursor: { nodeId: obligation.id },
        };
      }
      // Keep the term-have's expression VERBATIM (see the exact case above).
      {
        const node = findNode(state.root, state.cursor.nodeId);
        if (!node || node.tag !== 'hole') return null;
        const rest = mkHole();
        const inserted = mkHave(parsed.name, parsed.expr, rest);
        return {
          root: replaceNode(state.root, state.cursor.nodeId, inserted),
          cursor: { nodeId: rest.id },
        };
      }
    }

    case 'simp': {
      const lemmaStr = value.trim();
      const lemmas = lemmaStr ? lemmaStr.split(/[\s,]+/).filter(Boolean) : [];
      // Insert a structural `simp [...]` node and let the Lean round-trip
      // check it. (The TT path ran an in-process simp engine here and recorded
      // the individual rewrite steps it fired; Lean reports the resulting goal
      // instead, which is the part the reader actually needs.)
      const child = mkHole();
      const newRoot = replaceNode(state.root, state.cursor.nodeId, mkSimp(lemmas, [], child));
      return { root: newRoot, cursor: { nodeId: child.id } };
    }
  }
}
