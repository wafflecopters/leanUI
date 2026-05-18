import { parseExpr } from '../parser/parser';
import {
  TacticCommand,
  mkConstTT,
  mkHoleTT,
  mkPropTT,
  flatParamsToCasePatterns,
  type TTerm,
} from '../compiler/surface';
import type { ProofNode, ProofTreeState } from './proof-tree';
import { findNode, replaceNode } from './proof-tree';
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
      const inferredTypeHole = mkHoleTT('_have_type', mkHoleTT('_have_type_type', mkPropTT()));
      return [
        {
          name: 'have',
          args: [mkConstTT(node.name), inferredTypeHole, parseSourceExpr(node.expr)],
        },
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
