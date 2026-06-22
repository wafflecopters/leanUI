import { buildReverseRegistry } from '../math-editor/tt-to-math';
import { parseExpr } from '../parser/parser';
import { SyntaxRegistry } from '../math-editor/syntax-registry';
import { mkConstTT } from '../compiler/surface';
import { type DefinitionsMap } from '../compiler/term';
import { normalizeBinderNameInput } from './name-latex';
import { runSimp } from '../tactics/simp-tactic';
import {
  TypedProofContext,
  type InductiveMap,
  extractTypeHead,
  generateCaseInfos,
} from './goal-computation';
import type { ProofNodeId, ProofTreeState } from './proof-tree';
import {
  applyInduction,
  applySimp,
  clearNode,
  editIntroName,
  findCase,
  findNode,
  isCursorInSubtree,
  mkHave,
  mkHole,
  mkSimp,
  replaceNode,
  toggleInductionCollapse,
  toggleSimpCollapse,
  updateCase,
} from './proof-tree';
import {
  buildExprFromSlots,
  buildTermBuilderRuntime,
  clearTermBuilderSlotFromGoal,
  fillTermBuilderSlotFromGoal,
  kernelTermToSource,
  openTermBuilderFromSourceExpr,
  type TermBuilderKernelGoalRuntime,
  type TermBuilderState,
} from './term-builder';
import type { RewriteSuggestion, TacticSuggestion } from './tactic-suggestions';
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
  | { tactic: 'exact' }
  | { tactic: 'unfold' }
  | { tactic: 'fold' }
  | { tactic: 'rewrite' }
  | { tactic: 'rewrite_rev' }
  | { tactic: 'apply' }
  | { tactic: 'simp' }
  | { tactic: 'have' };

export interface ProofTreeSuggestionContext {
  readonly inductiveMap?: InductiveMap;
  readonly registry?: SyntaxRegistry;
  readonly typedContext?: TypedProofContext | null;
  readonly definitions?: DefinitionsMap;
  readonly editingNames?: readonly string[] | null;
  readonly editingSuggestionId?: string | null;
}

export interface ProofTreeManualTacticContext {
  readonly typedContext?: TypedProofContext | null;
  readonly inductiveMap?: InductiveMap;
  readonly registry?: SyntaxRegistry;
  readonly kernelType?: import('../compiler/kernel').TTKTerm;
  readonly definitions?: DefinitionsMap;
  readonly computeApplySubgoalCount?: (
    root: ProofTreeState['root'],
    cursorNodeId: number,
    kernelType: import('../compiler/kernel').TTKTerm,
    definitions: import('../compiler/term').DefinitionsMap,
    name: string,
  ) => number;
}

export type ProofTreeBinderRenameTarget =
  | { tag: 'have'; nodeId: ProofNodeId }
  | { tag: 'introToken'; nodeId: ProofNodeId; nameIndex: number }
  | { tag: 'caseParam'; nodeId: ProofNodeId; paramIndex: number };

export interface ProofTreeHaveTermBuilderEditResult {
  readonly state: ProofTreeState;
  readonly builderState: TermBuilderState;
}

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

function buildInductionTacticCommandsFromContext(
  scrutinee: string,
  ctx: Pick<ProofTreeManualTacticContext, 'typedContext' | 'inductiveMap' | 'registry'>,
  tacticName: 'induction' | 'cases',
) {
  const hyp = ctx.typedContext?.hypotheses.find(h => h.name === scrutinee);
  const rawType = hyp?.rawType;
  const headName = rawType ? extractTypeHead(rawType) : null;
  const indInfo = headName && ctx.inductiveMap ? ctx.inductiveMap.get(headName) : undefined;

  if (indInfo) {
    const rev = ctx.registry ? buildReverseRegistry(ctx.registry) : undefined;
    const ctxNames = ctx.typedContext?.hypotheses.map(h => h.name);
    const ctorInfos = generateCaseInfos(scrutinee, indInfo, rev, ctxNames);
    return buildInductionTacticCommands(scrutinee, ctorInfos, tacticName);
  }

  return null;
}

function applyInductionFromContext(
  state: ProofTreeState,
  scrutinee: string,
  ctx: Pick<ProofTreeManualTacticContext, 'typedContext' | 'inductiveMap' | 'registry'>,
  tacticName: 'induction' | 'cases',
): ProofTreeState | null {
  const commands = buildInductionTacticCommandsFromContext(scrutinee, ctx, tacticName);
  if (commands) {
    return applyTacticCommandsAtCursor(state, commands);
  }

  return applyInduction(state, scrutinee, [`${scrutinee} = 0`, `${scrutinee} = k'`]);
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

export function openHaveExprTermBuilder(
  sourceExpr: string,
  kernelGoal: TermBuilderKernelGoalRuntime | null | undefined,
  definitions?: DefinitionsMap,
) {
  const runtime = buildTermBuilderRuntime(kernelGoal, definitions);
  if (!runtime) return null;
  return openTermBuilderFromSourceExpr(sourceExpr, runtime);
}

export function fillHaveTermBuilderSlotInProofTree(
  state: ProofTreeState,
  haveNodeId: ProofNodeId,
  builderState: TermBuilderState,
  slotIndex: number,
  sourceExpr: string,
  kernelGoal: TermBuilderKernelGoalRuntime | null | undefined,
  definitions?: DefinitionsMap,
): ProofTreeHaveTermBuilderEditResult | null {
  const rebuilt = fillTermBuilderSlotFromGoal(
    builderState,
    slotIndex,
    convertMathEditorSourceToUnicode(sourceExpr),
    kernelGoal,
    definitions,
  );
  if (!rebuilt) return null;
  const nextState = rebuilt.expr
    ? (updateHaveExprInProofTree(state, haveNodeId, rebuilt.expr) ?? state)
    : state;
  return { state: nextState, builderState: rebuilt.builderState };
}

export function clearHaveTermBuilderSlotInProofTree(
  state: ProofTreeState,
  haveNodeId: ProofNodeId,
  builderState: TermBuilderState,
  slotIndex: number,
  kernelGoal: TermBuilderKernelGoalRuntime | null | undefined,
  definitions?: DefinitionsMap,
): ProofTreeHaveTermBuilderEditResult | null {
  const rebuilt = clearTermBuilderSlotFromGoal(
    builderState,
    slotIndex,
    kernelGoal,
    definitions,
  );
  if (!rebuilt) return null;
  const nextState = rebuilt.expr
    ? (updateHaveExprInProofTree(state, haveNodeId, rebuilt.expr) ?? state)
    : state;
  return { state: nextState, builderState: rebuilt.builderState };
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

function buildHoistedHaveName(builderState: TermBuilderState, slotIndex: number): string {
  const slot = builderState.slots[slotIndex];
  const baseName = (slot?.name && slot.name !== '_' && !slot.name.startsWith('_'))
    ? slot.name
    : `${slotIndex}`;
  return `h${baseName}`;
}

export function hoistTermBuilderSlotToHave(
  state: ProofTreeState,
  haveNodeId: ProofNodeId,
  builderState: TermBuilderState,
  slotIndex: number,
  definitions?: DefinitionsMap,
): ProofTreeState | null {
  const slot = builderState.slots[slotIndex];
  if (!slot) return null;

  const target = findNode(state.root, haveNodeId);
  if (!target) return null;

  const hoistName = buildHoistedHaveName(builderState, slotIndex);
  // Zonk the slot type before serializing so meta solutions (e.g. the
  // implicit `R` of `rdiv` / `rtwo` in `ε/2`) get folded in. Without this
  // step the source string ends up with literal `?` placeholders for any
  // meta that the term-builder created but didn't get to solve at slot
  // construction time — surfacing as `ε/?` in the hoisted have type.
  const zonkedSlotType = typeof builderState.engine.zonkTerm === 'function'
    ? builderState.engine.zonkTerm(slot.type, builderState.goalCtx.length)
    : slot.type;
  const typeSourceExpr = kernelTermToSource(zonkedSlotType, builderState.goalCtx, definitions);
  const proofHole = mkHole();
  const inserted = mkHave(hoistName, '?', target, typeSourceExpr, proofHole);
  let updated: ProofTreeState = {
    root: replaceNode(state.root, haveNodeId, inserted),
    cursor: state.cursor,
  };

  const newSlots = [...builderState.slots];
  newSlots[slotIndex] = {
    ...slot,
    value: { tag: 'Const', name: hoistName },
    sourceExpr: hoistName,
  };
  const expr = buildExprFromSlots(builderState.fnName, newSlots, builderState.goalCtx);
  if (!expr) return updated;

  return updateHaveExprInProofTree(updated, haveNodeId, expr) ?? updated;
}

export function clearProofTreeNode(
  state: ProofTreeState,
  nodeId: ProofNodeId,
): ProofTreeState | null {
  return clearNode(state, nodeId);
}

export function insertHaveFromTermBuilder(
  state: ProofTreeState,
  builderState: TermBuilderState,
  haveName = 'h',
): ProofTreeState | null {
  const expr = buildExprFromSlots(
    builderState.fnName,
    builderState.slots,
    builderState.goalCtx,
  );
  if (!expr) return null;
  return applyTacticCommandsAtCursor(state, buildHaveTacticCommands(haveName, expr));
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
    return applyTacticCommandsAtCursor(state, [{ name: 'exact', args: [mkConstTT('refl')] }]);
  }

  if (suggestion.id.startsWith('unfold-')) {
    const name = suggestion.id.slice('unfold-'.length);
    return applyTacticCommandsAtCursor(state, [{ name: 'unfold', args: [mkConstTT(name)] }]);
  }

  if (suggestion.id.startsWith('induction-')) {
    const scrutinee = suggestion.id.slice('induction-'.length);
    return applyInductionFromContext(state, scrutinee, ctx, inferInductionSuggestionTacticName(suggestion));
  }

  if (suggestion.id.startsWith('fold-')) {
    const name = suggestion.foldName ?? suggestion.id.slice('fold-'.length);
    return applyTacticCommandsAtCursor(state, [{ name: 'fold', args: [mkConstTT(name)] }]);
  }

  if (suggestion.id.startsWith('exact-hyp-')) {
    const name = suggestion.id.slice('exact-hyp-'.length);
    return applyTacticCommandsAtCursor(state, [{ name: 'exact', args: [mkConstTT(name)] }]);
  }

  if (suggestion.id.startsWith('apply-hyp-')) {
    const name = suggestion.id.slice('apply-hyp-'.length);
    return applyTacticCommandsAtCursor(state, buildApplyTacticCommands(name, suggestion.numSubgoals ?? 1));
  }

  if (suggestion.id.startsWith('apply-def-')) {
    const name = suggestion.id.slice('apply-def-'.length);
    return applyTacticCommandsAtCursor(state, buildApplyTacticCommands(name, suggestion.numSubgoals ?? 1));
  }

  if (suggestion.id.startsWith('simp-then-apply-def-')) {
    const defName = suggestion.id.slice('simp-then-apply-def-'.length);
    const numSubgoals = suggestion.numSubgoals ?? 1;
    const kernelGoal = ctx.typedContext?.kernelGoal;
    if (!kernelGoal) return null;
    const lemmas = [...(kernelGoal.definitions.simpLemmas ?? [])];
    const simpResult = runSimp(kernelGoal.engine, lemmas);
    if (!simpResult.success || simpResult.steps.length === 0) return null;
    const afterSimp = applySimp(state, lemmas, simpResult.proofNodes);
    if (!afterSimp) return null;
    return applyTacticCommandsAtCursor(afterSimp, buildApplyTacticCommands(defName, numSubgoals));
  }

  if (suggestion.id.startsWith('construct-')) {
    const ctorName = suggestion.applyCtorName ?? suggestion.id.slice('construct-'.length);
    return applyTacticCommandsAtCursor(state, buildApplyTacticCommands(ctorName, suggestion.numSubgoals ?? 1, true));
  }

  if (suggestion.id === 'simp-auto' || suggestion.id === 'compute') {
    // 'compute' is the norm_num variant of simp-auto: the suggestion was
    // surfaced because the clicked subterm was registered carrier-arithmetic
    // and evaluated to a closed Rat. Dispatch both to runSimp, but for
    // 'compute' augment the @simp set with @carrierBridge lemmas (the
    // alias-→-realOfRat bridges needed to normalize literals before
    // applying arithmetic homomorphism lemmas like addRealOfRat). This
    // keeps the tactic tree shape consistent — replay walks see a simp
    // node in either case — while letting Compute reach cases that
    // ordinary simp can't.
    const kernelGoal = ctx.typedContext?.kernelGoal;
    if (!kernelGoal) return null;
    const baseSimp = [...(kernelGoal.definitions.simpLemmas ?? [])];
    const lemmas = suggestion.id === 'compute' && kernelGoal.definitions.carrierBridges
      ? [...baseSimp, ...kernelGoal.definitions.carrierBridges]
      : baseSimp;
    const simpResult = runSimp(kernelGoal.engine, lemmas);
    if (!simpResult.success) return null;
    return applySimp(state, lemmas, simpResult.proofNodes);
  }

  if (suggestion.id.startsWith('rewrite-') || suggestion.id.startsWith('simp-')) {
    const rw = suggestion as RewriteSuggestion;
    return applyTacticCommandsAtCursor(state, [{
      name: 'rewrite',
      args: [mkConstTT(rw.rewriteName)],
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
  return applyTacticCommandsAtCursor(state, [{ name: introName, args: names.map(mkConstTT) }]);
}

export function applyManualProofTreeTactic(
  state: ProofTreeState,
  tacticMode: ProofTreeManualTacticMode | null,
  value: string,
  ctx: ProofTreeManualTacticContext,
): ProofTreeState | null {
  if (!tacticMode) return null;

  switch (tacticMode.tactic) {
    case 'intros': {
      const names = splitNames(value);
      if (names.length === 0) return null;
      const introName = names.length === 1 ? 'intro' : 'intros';
      return applyTacticCommandsAtCursor(state, [{ name: introName, args: names.map(mkConstTT) }]);
    }

    case 'induction': {
      const scrutinee = value.trim();
      if (!scrutinee) return null;
      return applyInductionFromContext(state, scrutinee, ctx, 'induction');
    }

    case 'exact': {
      const expr = value.trim();
      if (!expr) return null;
      return applyTacticCommandsAtCursor(state, [{ name: 'exact', args: [parseExpr(expr)] }]);
    }

    case 'unfold': {
      const name = value.trim();
      if (!name) return null;
      return applyTacticCommandsAtCursor(state, [{ name: 'unfold', args: [mkConstTT(name)] }]);
    }

    case 'fold': {
      const name = value.trim();
      if (!name) return null;
      return applyTacticCommandsAtCursor(state, [{ name: 'fold', args: [mkConstTT(name)] }]);
    }

    case 'rewrite': {
      const name = value.trim();
      if (!name) return null;
      return applyTacticCommandsAtCursor(state, [{ name: 'rewrite', args: [mkConstTT(name)] }]);
    }

    case 'rewrite_rev': {
      const name = value.trim();
      if (!name) return null;
      return applyTacticCommandsAtCursor(state, [{
        name: 'rewrite',
        args: [mkConstTT(name)],
        rewriteOptions: { reverse: true },
      }]);
    }

    case 'apply': {
      const name = value.trim();
      if (!name) return null;
      let numChildren = 1;
      if (ctx.kernelType && ctx.definitions && ctx.computeApplySubgoalCount) {
        numChildren = ctx.computeApplySubgoalCount(
          state.root,
          state.cursor.nodeId,
          ctx.kernelType,
          ctx.definitions,
          name,
        );
      }
      return applyTacticCommandsAtCursor(state, buildApplyTacticCommands(name, numChildren));
    }

    case 'have': {
      const trimmed = value.trim();
      const eqIdx = trimmed.indexOf(':=');
      if (eqIdx <= 0) return null;
      const haveName = trimmed.slice(0, eqIdx).trim().split(':')[0].trim();
      const haveExpr = trimmed.slice(eqIdx + 2).trim();
      if (!haveName || !haveExpr) return null;
      return applyTacticCommandsAtCursor(state, buildHaveTacticCommands(haveName, haveExpr));
    }

    case 'simp': {
      const lemmaStr = value.trim();
      const lemmas = lemmaStr ? lemmaStr.split(/[\s,]+/).filter(Boolean) : [];
      // Lean backend: no TT kernel engine — insert a structural `simp [...]` node
      // and let the Lean round-trip check/replay it (the engine path below only
      // runs for the in-process TT checker).
      if (!ctx.typedContext?.kernelGoal) {
        const child = mkHole();
        const newRoot = replaceNode(state.root, state.cursor.nodeId, mkSimp(lemmas, [], child));
        return { root: newRoot, cursor: { nodeId: child.id } };
      }
      const { engine, definitions } = ctx.typedContext.kernelGoal;
      const allLemmas = lemmas.length ? lemmas : [...(definitions.simpLemmas ?? [])];
      const simpResult = runSimp(engine, allLemmas);
      if (!simpResult.success) return null;
      return applySimp(state, allLemmas, simpResult.proofNodes);
    }
  }
}
