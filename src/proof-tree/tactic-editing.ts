import { buildReverseRegistry } from '../math-editor/tt-to-math';
import { parseExpr } from '../parser/parser';
import { SyntaxRegistry } from '../math-editor/syntax-registry';
import { mkConstTT } from '../compiler/surface';
import { type DefinitionsMap } from '../compiler/term';
import { runSimp } from '../tactics/simp-tactic';
import {
  TypedProofContext,
  type InductiveMap,
  extractTypeHead,
  generateCaseInfos,
} from './goal-computation';
import type { ProofNodeId, ProofTreeState } from './proof-tree';
import { applyInduction, applyInductionWithCtors, applySimp, findNode, mkHave, mkHole, replaceNode } from './proof-tree';
import { buildExprFromSlots, kernelTermToSource, type TermBuilderState } from './term-builder';
import type { RewriteSuggestion, TacticSuggestion } from './tactic-suggestions';
import {
  applyTacticCommandsAtCursor,
  buildApplyTacticCommands,
  buildHaveTacticCommands,
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

function splitNames(value: string): string[] {
  return value.split(/[\s,]+/).filter(Boolean);
}

function buildInductionResult(
  state: ProofTreeState,
  scrutinee: string,
  ctx: Pick<ProofTreeManualTacticContext, 'typedContext' | 'inductiveMap' | 'registry'>,
): ProofTreeState | null {
  const hyp = ctx.typedContext?.hypotheses.find(h => h.name === scrutinee);
  const rawType = hyp?.rawType;
  const headName = rawType ? extractTypeHead(rawType) : null;
  const indInfo = headName && ctx.inductiveMap ? ctx.inductiveMap.get(headName) : undefined;

  if (indInfo) {
    const rev = ctx.registry ? buildReverseRegistry(ctx.registry) : undefined;
    const ctxNames = ctx.typedContext?.hypotheses.map(h => h.name);
    const ctorInfos = generateCaseInfos(scrutinee, indInfo, rev, ctxNames);
    return applyInductionWithCtors(state, scrutinee, ctorInfos);
  }

  return applyInduction(state, scrutinee, [`${scrutinee} = 0`, `${scrutinee} = k'`]);
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
  const typeSourceExpr = kernelTermToSource(slot.type, builderState.goalCtx, definitions);
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
    return buildInductionResult(state, scrutinee, ctx);
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

  if (suggestion.id === 'simp-auto') {
    const kernelGoal = ctx.typedContext?.kernelGoal;
    if (!kernelGoal) return null;
    const lemmas = [...(kernelGoal.definitions.simpLemmas ?? [])];
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
      return buildInductionResult(state, scrutinee, ctx);
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
      if (!ctx.typedContext?.kernelGoal) return null;
      const { engine, definitions } = ctx.typedContext.kernelGoal;
      const lemmaStr = value.trim();
      const lemmas = lemmaStr
        ? lemmaStr.split(/[\s,]+/).filter(Boolean)
        : [...(definitions.simpLemmas ?? [])];
      const simpResult = runSimp(engine, lemmas);
      if (!simpResult.success) return null;
      return applySimp(state, lemmas, simpResult.proofNodes);
    }
  }
}
