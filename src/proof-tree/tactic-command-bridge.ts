import { parseExpr } from '../parser/parser';
import {
  TacticCommand,
  type CaseBranch,
  mkConstTT,
  mkHoleTT,
  mkPropTT,
  allPatternVarNames,
  flatParamsToCasePatterns,
  type TTerm,
} from '../compiler/surface';
import { createNamedArgLookup, type DefinitionsMap } from '../compiler/term';
import type { CaseNode, InductionNode, ProofNode, ProofTreeState } from './proof-tree';
import { findNode, formatCaseLabelLatex, mkCase, replaceNode } from './proof-tree';
import { findFirstHole, tacticCommandsToProofTree } from './tactic-to-tree';

function parseSourceExpr(expr: string): TTerm {
  return parseExpr(expr);
}

function mkFocusCommand(tactics: readonly TacticCommand[]): TacticCommand {
  return { name: 'focus', args: [], focusedTactics: [...tactics] };
}

export function buildApplyTacticCommands(
  name: string,
  numChildren: number,
  isConstructor = false,
): TacticCommand[] {
  const head: TacticCommand = isConstructor
    ? { name: 'constructor', args: [] }
    : { name: 'apply', args: [mkConstTT(name)] };

  if (numChildren === 0) {
    return [{ ...head, focusedTactics: [] }];
  }

  return [
    head,
    ...Array.from({ length: numChildren }, () => mkFocusCommand([])),
  ];
}

export function buildHaveTacticCommands(
  name: string,
  expr: string,
): TacticCommand[] {
  const inferredTypeHole = mkHoleTT('_have_type', mkHoleTT('_have_type_type', mkPropTT()));
  return [{
    name: 'have',
    args: [mkConstTT(name), inferredTypeHole, parseSourceExpr(expr)],
  }];
}

export interface StructuredInductionCaseInfo {
  readonly constructorName: string;
  readonly paramNames: readonly string[];
}

export function buildCaseBranchFromCaseNode(node: CaseNode): CaseBranch {
  return {
    constructor: node.constructorName ?? node.label,
    params: node.casePatterns ? [...node.casePatterns] : flatParamsToCasePatterns(node.constructorParamNames ?? []),
    tactics: proofTreeToTacticCommands(node.body),
  };
}

export function buildInductionTacticCommands(
  scrutinee: string,
  caseInfos: readonly StructuredInductionCaseInfo[],
  tacticName: 'induction' | 'cases' = 'induction',
): TacticCommand[] {
  return [{
    name: tacticName,
    args: [parseSourceExpr(scrutinee)],
    caseBranches: caseInfos.map(info => ({
      constructor: info.constructorName,
      params: flatParamsToCasePatterns(info.paramNames),
      tactics: [],
    })),
  }];
}

export function rebuildInductionNodeFromCaseBranches(
  node: InductionNode,
  caseBranches: readonly CaseBranch[],
): InductionNode {
  const cases = caseBranches.map((branch, index) => {
    const prev = node.cases[index];
    const hasNestedPatterns = branch.params.some(param => param.tag === 'ctor');
    const constructorParamNames = hasNestedPatterns ? undefined : allPatternVarNames(branch.params);
    const label = constructorParamNames && constructorParamNames.length > 0
      ? `${node.scrutinee} = ${branch.constructor} ${constructorParamNames.join(' ')}`
      : `${node.scrutinee} = ${branch.constructor}`;
    const caseNode = mkCase(
      label,
      prev ? prev.body : tacticCommandsToProofTree(branch.tactics),
      branch.constructor,
      constructorParamNames,
      formatCaseLabelLatex(node.scrutinee, branch.constructor, constructorParamNames ?? []),
      hasNestedPatterns ? branch.params : undefined,
    );
    return prev
      ? { ...caseNode, id: prev.id, body: prev.body, collapsed: prev.collapsed }
      : caseNode;
  });
  return { ...node, cases };
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

export function applyTacticCommandsAtCursor(
  state: ProofTreeState,
  commands: readonly TacticCommand[],
): ProofTreeState | null {
  const node = findNode(state.root, state.cursor.nodeId);
  if (!node || node.tag !== 'hole') return null;

  const fragment = tacticCommandsToProofTree([...commands]);
  const newRoot = replaceNode(state.root, state.cursor.nodeId, fragment);
  const nextHole = findFirstHole(fragment);
  return {
    root: newRoot,
    cursor: { nodeId: nextHole ? nextHole.id : fragment.id },
  };
}

export function proofTreeToTacticCommands(node: ProofNode): TacticCommand[] {
  switch (node.tag) {
    case 'hole':
      return [];

    case 'intros': {
      const introName = node.names.length === 1 ? 'intro' : 'intros';
      const intro: TacticCommand = {
        name: introName,
        args: node.names.map(name => mkConstTT(name)),
      };
      return [intro, ...proofTreeToTacticCommands(node.child)];
    }

    case 'exact':
      return [{ name: 'exact', args: [parseSourceExpr(node.expr)] }];

    case 'unfold':
      return [
        { name: 'unfold', args: [mkConstTT(node.name)] },
        ...proofTreeToTacticCommands(node.child),
      ];

    case 'fold':
      return [
        { name: 'fold', args: [mkConstTT(node.name)] },
        ...proofTreeToTacticCommands(node.child),
      ];

    case 'rewrite': {
      const rewrite: TacticCommand = {
        name: 'rewrite',
        args: [parseSourceExpr(node.name)],
        rewriteOptions: {
          reverse: node.reverse,
          occurrences: node.occurrences,
          targetHead: node.targetHead,
          enhanced: node.enhanced,
        },
      };
      return [rewrite, ...proofTreeToTacticCommands(node.child)];
    }

    case 'apply': {
      const isConstructor = node.name === 'constructor';
      const head: TacticCommand = isConstructor
        ? { name: 'constructor', args: [] }
        : { name: 'apply', args: [parseSourceExpr(node.name)] };

      if (node.children.length === 0) {
        return [{ ...head, focusedTactics: [] }];
      }

      return [
        head,
        ...node.children.map(child => mkFocusCommand(proofTreeToTacticCommands(child))),
      ];
    }

    case 'induction': {
      const tacticName = node.isCases ? 'cases' : 'induction';
      const caseBranches = node.cases.map(c => ({
        constructor: c.constructorName ?? c.label,
        params: c.casePatterns ? [...c.casePatterns] : flatParamsToCasePatterns(c.constructorParamNames ?? []),
        tactics: proofTreeToTacticCommands(c.body),
      }));
      return [{
        name: tacticName,
        args: [parseSourceExpr(node.scrutinee)],
        caseBranches,
      }];
    }

    case 'have': {
      if (node.proofTree) {
        if (!node.typeExpr) {
          throw new Error('proofTreeToTacticCommands: interactive have proofs require typeExpr to serialize to source tactics');
        }
        return [
          {
            name: 'have',
            args: [mkConstTT(node.name), parseSourceExpr(node.typeExpr)],
            focusedTactics: proofTreeToTacticCommands(node.proofTree),
          },
          ...proofTreeToTacticCommands(node.child),
        ];
      }
      return [
        ...buildHaveTacticCommands(node.name, node.expr),
        ...proofTreeToTacticCommands(node.child),
      ];
    }

    case 'suffices': {
      const closing = node.byProof ? proofTreeToTacticCommands(node.byProof) : [];
      return [
        {
          name: 'suffices',
          args: [mkConstTT(node.name), parseSourceExpr(node.typeExpr)],
          focusedTactics: closing,
        },
        ...proofTreeToTacticCommands(node.child),
      ];
    }

    case 'simp':
      if (node.steps.length === 0) {
        return [
          {
            name: 'simp',
            args: node.lemmas.map(name => mkConstTT(name)),
          },
          ...proofTreeToTacticCommands(node.child),
        ];
      }
      return [
        ...node.steps.flatMap(step => proofTreeToTacticCommands(step)),
        ...proofTreeToTacticCommands(node.child),
      ];
  }
}
