import { buildReverseRegistry } from '../math-editor/tt-to-math';
import { parseExpr } from '../parser/parser';
import { SyntaxRegistry } from '../math-editor/syntax-registry';
import { mkConstTT, mkHoleTT, mkPropTT } from '../compiler/surface';
import { createNamedArgLookup, type DefinitionsMap } from '../compiler/term';
import { runSimp } from '../tactics/simp-tactic';
import type { InteractiveGoal } from './interactive-goal';
import {
  TypedProofContext,
  type InductiveMap,
  extractTypeHead,
  generateCaseInfos,
} from './goal-computation';
import type { ProofTreeState } from './proof-tree';
import { applyInduction, applyInductionWithCtors, applySimp } from './proof-tree';
import type { RewriteSuggestion, TacticSuggestion } from './tactic-suggestions';
import {
  applyTacticCommandsAtCursor,
  buildApplyTacticCommands,
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
  readonly interactiveGoal?: InteractiveGoal | null;
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

export function buildProjectionApplicationSource(
  projName: string,
  hypName: string,
  definitions: DefinitionsMap,
): string | null {
  const namedArgLookup = createNamedArgLookup(definitions);
  const namedArgMap = namedArgLookup(projName);
  const numImplicit = namedArgMap?.size ?? 0;
  const termDef = definitions.terms.get(projName);
  if (!termDef?.type) return null;

  let numExplicit = 0;
  let t = termDef.type;
  let idx = 0;
  while (t.tag === 'Binder' && t.binderKind.tag === 'BPi') {
    if (idx >= numImplicit) numExplicit++;
    t = t.body;
    idx++;
  }

  const holes = Array(Math.max(0, numExplicit - 1)).fill('?').join(' ');
  return holes ? `${projName} ${hypName} ${holes}` : `${projName} ${hypName}`;
}

export function applySuggestionToProofTreeState(
  state: ProofTreeState,
  suggestion: TacticSuggestion,
  ctx: ProofTreeSuggestionContext,
): ProofTreeState | null {
  if (suggestion.id === 'exact-refl') {
    return applyTacticCommandsAtCursor(state, [{ name: 'exact', args: [mkConstTT('refl')] }]);
  }

  if (suggestion.id.startsWith('unfold-')) {
    const name = suggestion.id.slice('unfold-'.length);
    return applyTacticCommandsAtCursor(state, [{ name: 'unfold', args: [mkConstTT(name)] }]);
  }

  if (suggestion.id.startsWith('induction-')) {
    const scrutinee = suggestion.id.slice('induction-'.length);
    const typeHead = ctx.interactiveGoal?.contextVarTypes.get(scrutinee);
    const indInfo = typeHead && ctx.inductiveMap ? ctx.inductiveMap.get(typeHead) : undefined;
    if (!indInfo) return null;
    const rev = ctx.registry ? buildReverseRegistry(ctx.registry) : undefined;
    const ctxNames = ctx.typedContext?.hypotheses.map(h => h.name);
    const ctorInfos = generateCaseInfos(scrutinee, indInfo, rev, ctxNames);
    return applyInductionWithCtors(state, scrutinee, ctorInfos);
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

export function applyHypothesisSuggestionToProofTreeState(
  state: ProofTreeState,
  suggestion: TacticSuggestion,
  hypName: string,
  ctx: Pick<ProofTreeSuggestionContext, 'typedContext' | 'inductiveMap' | 'registry' | 'definitions'>,
): ProofTreeState | null {
  if (suggestion.id.startsWith('hyp-exact-')) {
    return applySuggestionToProofTreeState(state, {
      ...suggestion,
      id: `exact-hyp-${hypName}`,
    }, {});
  }

  if (suggestion.id.startsWith('hyp-apply-')) {
    return applySuggestionToProofTreeState(state, {
      ...suggestion,
      id: `apply-hyp-${hypName}`,
    }, {});
  }

  if (suggestion.id.startsWith('hyp-proj-')) {
    const projName = suggestion.applyCtorName;
    if (!projName || !ctx.definitions) return null;
    const expr = buildProjectionApplicationSource(projName, hypName, ctx.definitions);
    if (!expr) return null;
    return applyManualProofTreeTactic(state, { tactic: 'have' }, `h := ${expr}`, {});
  }

  if (suggestion.id.startsWith('hyp-destruct-')) {
    return applyManualProofTreeTactic(state, { tactic: 'induction' }, hypName, {
      typedContext: ctx.typedContext,
      inductiveMap: ctx.inductiveMap,
      registry: ctx.registry,
    });
  }

  return null;
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
      return applyTacticCommandsAtCursor(state, [{
        name: 'have',
        args: [
          mkConstTT(haveName),
          mkHoleTT('_have_type', mkHoleTT('_have_type_type', mkPropTT())),
          parseExpr(haveExpr),
        ],
      }]);
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
