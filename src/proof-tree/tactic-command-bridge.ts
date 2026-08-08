import {
  TacticCommand,
  type CaseBranch,
  allPatternVarNames,
  flatParamsToCasePatterns,
} from './tactic-command';
import type { CaseNode, InductionNode, ProofNode, ProofTreeState } from './proof-tree';
import { findNode, formatCaseLabelLatex, mkCase, replaceNode } from './proof-tree';
import { findFirstHole, tacticCommandsToProofTree } from './tactic-to-tree';

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
    : { name: 'apply', args: [name] };

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
  // Slot 1 is the have's TYPE: `_` means "infer it", which is what an untyped
  // `have h := e` asks for.
  return [{ name: 'have', args: [name, '_', expr] }];
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
    args: [scrutinee],
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

    case 'destructure':
      return [
        { name: 'obtain', args: [`\u27e8${node.names.join(', ')}\u27e9 := ${node.scrutinee}`] },
        ...proofTreeToTacticCommands(node.child),
      ];

    case 'intros': {
      const introName = node.names.length === 1 ? 'intro' : 'intros';
      const intro: TacticCommand = {
        name: introName,
        args: [...node.names],
      };
      return [intro, ...proofTreeToTacticCommands(node.child)];
    }

    case 'exact':
      return [{ name: 'exact', args: [node.expr] }];

    case 'unfold':
      return [
        { name: 'unfold', args: [node.name] },
        ...proofTreeToTacticCommands(node.child),
      ];

    case 'fold':
      return [
        { name: 'fold', args: [node.name] },
        ...proofTreeToTacticCommands(node.child),
      ];

    case 'rewrite': {
      const rewrite: TacticCommand = {
        name: 'rewrite',
        args: [node.name],
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
        : { name: 'apply', args: [node.name] };

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
        args: [node.scrutinee],
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
            args: [node.name, node.typeExpr],
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
          args: [node.name, node.typeExpr],
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
            args: [...node.lemmas],
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
