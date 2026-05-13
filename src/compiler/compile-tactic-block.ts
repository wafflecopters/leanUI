import type { Tactic } from '../tactics/tactic';
import {
  createBranchParamNameMap,
  createBranchParamNameMapFromCurrentNames,
  renameCtxEntriesByCurrentNames,
  renameLastCtxEntries,
} from '../tactics/branch-context';
import { ReflexivityTactic } from '../tactics/reflexivity-tactic';
import { createRootInfoNode, type SourcePosition, TacticInfoTree, type TacticInfoNode } from '../tactics/info-tree';
import { extractGoalStates, engineToProofState } from '../tactics/proof-state';
import { elaborateTacticArg, tacticCommandToTactic, shouldKeepArgAsName } from '../tactics/elaborate-tactic-arg';
import { createInitialEngine, type TacticEngine } from '../tactics/tacticsEngine';
import type { ElabMap } from '../types/source-position';
import type { IndexPath, SourceMap } from '../types/source-position';
import { serializeIndexPath } from '../types/source-position';
import { desugarNestedCaseBranch } from './case-pattern-desugar';
import type { TTKContext, TTKTerm } from './kernel';
import type { TacticBlockElaborationResult } from './compile-term-simple-value';
import { allPatternVarNames, type CaseBranch, type TacticCommand, type TTacticBlock } from './surface';
import { createTCEnv, type DefinitionsMap, TCEnvError } from './term';

function indexPathToSourcePosition(
  indexPath: IndexPath | undefined,
  sourceMap: SourceMap,
): SourcePosition {
  if (!indexPath) return { line: 0, col: 0 };

  const serialized = serializeIndexPath(indexPath);
  let range = sourceMap.get(serialized);
  if (!range) {
    const namePathSerialized = serializeIndexPath([...indexPath, { kind: 'field', name: 'name' }]);
    range = sourceMap.get(namePathSerialized);
  }
  if (!range) return { line: 0, col: 0 };

  return {
    line: range.start.line,
    col: range.start.col,
    endLine: range.end.line,
    endCol: range.end.col,
  };
}

function createTacticNode(
  position: SourcePosition,
  goalsBefore: ReturnType<typeof extractGoalStates>,
  goalsAfter: ReturnType<typeof extractGoalStates>,
  tacticTag: string,
  error?: string,
): TacticInfoNode {
  return {
    position,
    goalsBefore,
    goalsAfter,
    tactic: { tag: tacticTag } as any,
    error,
    children: [],
  };
}

function elaborateFocusedTactics(
  focusedTactics: readonly TacticCommand[],
  goalCtx: TTKContext,
  definitions: DefinitionsMap,
  hasSorryRef: { current: boolean },
): Tactic[] {
  function elaborateOne(focusedCmd: TacticCommand, ctx: TTKContext): Tactic {
    const focusedElabArgs: Array<any> = focusedCmd.args.map((arg, i) => {
      if (shouldKeepArgAsName(focusedCmd.name, i, focusedCmd.args.length)) return arg;
      return elaborateTacticArg(arg, ctx, definitions);
    });

    const nestedFocused = focusedCmd.focusedTactics && focusedCmd.focusedTactics.length > 0
      ? focusedCmd.focusedTactics.map(ft => elaborateOne(ft, ctx))
      : undefined;
    const tactic = tacticCommandToTactic({
      name: focusedCmd.name,
      args: focusedElabArgs,
      focusedTactics: nestedFocused,
    });
    if (tactic === 'sorry') {
      hasSorryRef.current = true;
      return {
        name: 'sorry',
        apply: (engine) => ({ success: true, newEngine: engine }),
      } as Tactic;
    }
    return tactic;
  }

  return focusedTactics.map(ft => elaborateOne(ft, goalCtx));
}

function closeReflexiveGoals(engine: TacticEngine): TacticEngine {
  let current = engine;
  let changed = true;

  while (changed) {
    changed = false;
    for (let i = 0; i < current.goals.length; i++) {
      const focused = current.withUpdates({ focusIndex: i });
      const goal = focused.getFocusedGoal();
      const goalId = focused.getFocusedGoalId();
      if (!goal || !goalId) continue;
      const result = new ReflexivityTactic().apply(focused, goal, goalId);
      if (result.success) {
        current = result.newEngine;
        changed = true;
        break;
      }
    }
  }

  return current;
}

function applyCaseBranchesRecursive(
  engine: TacticEngine,
  caseBranches: readonly CaseBranch[],
  definitions: DefinitionsMap,
  outerParamNameMap: Map<string, string>,
  parentInfoNode: TacticInfoNode,
  hasSorryRef: { current: boolean },
  sourceMap: SourceMap,
): TacticEngine {
  for (const rawBranch of caseBranches) {
    const branch = desugarNestedCaseBranch(rawBranch);
    const branchGoalId = engine.goals.find(gid => {
      const meta = engine.metaVars.get(gid);
      return meta && meta.caseTag === branch.constructor;
    });

    if (!branchGoalId) {
      throw new Error(`Structured cases: no goal found for constructor '${branch.constructor}'`);
    }

    const branchGoalIndex = engine.goals.indexOf(branchGoalId);
    engine = engine.withUpdates({ focusIndex: branchGoalIndex });

    const branchGoal = engine.getFocusedGoal();
    const branchGoalId2 = engine.getFocusedGoalId();
    if (!branchGoal || !branchGoalId2) {
      throw new Error(`Structured cases: no focused goal available for constructor '${branch.constructor}'`);
    }

    const patternParamNames = allPatternVarNames(branch.params);
    const currentParamNames = branchGoal.branchParamNames;
    engine = currentParamNames && currentParamNames.length === patternParamNames.length
      ? renameCtxEntriesByCurrentNames(engine, currentParamNames, patternParamNames)
      : renameLastCtxEntries(engine, patternParamNames);
    const renamedGoal = engine.getFocusedGoal() ?? branchGoal;
    const paramNameMap = currentParamNames && currentParamNames.length === patternParamNames.length
      ? createBranchParamNameMapFromCurrentNames(
          renamedGoal.ctx,
          currentParamNames,
          patternParamNames,
          outerParamNameMap,
        )
      : createBranchParamNameMap(renamedGoal.ctx, patternParamNames, outerParamNameMap);

    for (const branchTactic of branch.tactics) {
      const branchGoalCurrent = engine.getFocusedGoal();
      const branchGoalIdCurrent = engine.getFocusedGoalId();
      if (!branchGoalCurrent || !branchGoalIdCurrent) {
        throw new Error(`Structured cases: no active goal while processing constructor '${branch.constructor}'`);
      }

      const branchElabArgs: Array<any> = branchTactic.args.map((arg, argIndex) => {
        if (shouldKeepArgAsName(branchTactic.name, argIndex, branchTactic.args.length)) {
          return arg;
        }
        return elaborateTacticArg(arg, branchGoalCurrent.ctx, definitions, 0, paramNameMap);
      });

      const branchFocused = branchTactic.focusedTactics && branchTactic.focusedTactics.length > 0
        ? elaborateFocusedTactics(branchTactic.focusedTactics, branchGoalCurrent.ctx, definitions, hasSorryRef)
        : undefined;

      const goalsBefore = extractGoalStates(engineToProofState(engine));
      const branchTacticObj = tacticCommandToTactic({
        name: branchTactic.name,
        args: branchElabArgs,
        focusedTactics: branchFocused,
      });

      if (branchTacticObj === 'sorry') {
        hasSorryRef.current = true;
        continue;
      }

      const branchResult = branchTacticObj.apply(engine, branchGoalCurrent, branchGoalIdCurrent);
      const position = indexPathToSourcePosition(branchTactic.indexPath, sourceMap);

      if (!branchResult.success) {
        parentInfoNode.children.push(
          createTacticNode(position, goalsBefore, goalsBefore, branchTactic.name, branchResult.error),
        );
        const errorMsg = `Structured cases (${branch.constructor}): tactic '${branchTactic.name}' failed: ${branchResult.error}`;
        if (branchTactic.indexPath) {
          const tacticEnv = createTCEnv({ definitions, indexPath: branchTactic.indexPath, options: { mode: 'check' } });
          throw TCEnvError.create(errorMsg, tacticEnv);
        }
        throw new Error(errorMsg);
      }

      engine = branchResult.newEngine;
      const goalsAfter = extractGoalStates(engineToProofState(engine));
      const branchNode = createTacticNode(position, goalsBefore, goalsAfter, branchTactic.name);
      parentInfoNode.children.push(branchNode);

      if ((branchTactic.name === 'cases' || branchTactic.name === 'induction') && branchTactic.caseBranches && branchTactic.caseBranches.length > 0) {
        engine = applyCaseBranchesRecursive(
          engine,
          branchTactic.caseBranches,
          definitions,
          paramNameMap,
          branchNode,
          hasSorryRef,
          sourceMap,
        );
      } else if ((branchTactic.name === 'cases' || branchTactic.name === 'induction') && branchTactic.caseBranches?.length === 0) {
        engine = closeReflexiveGoals(engine);
      }
    }
  }

  return engine;
}

export function elaborateTacticBlock(
  tacticBlock: TTacticBlock,
  expectedType: TTKTerm,
  definitions: DefinitionsMap,
  _elabMap: ElabMap,
  sourceMap: SourceMap,
  context: TTKContext = [],
  recursiveTermName?: string,
): TacticBlockElaborationResult {
  if (tacticBlock.tactics.length === 0) {
    throw new Error('Tactic proof has no tactics (unsolved goals)');
  }

  let engine = createInitialEngine(expectedType, context, definitions, '?goal0', recursiveTermName);
  const hasSorryRef = { current: false };
  const rootNode = createRootInfoNode(extractGoalStates(engineToProofState(engine)));

  for (const cmd of tacticBlock.tactics) {
    const goal = engine.getFocusedGoal();
    const goalId = engine.getFocusedGoalId();
    if (!goal || !goalId) {
      throw new Error('Tactic proof: no active goal');
    }

    const elabArgs: Array<any> = cmd.args.map((arg, argIndex) => {
      if (shouldKeepArgAsName(cmd.name, argIndex, cmd.args.length)) {
        return arg;
      }
      return elaborateTacticArg(arg, goal.ctx, definitions);
    });

    let focusedTactics: Tactic[] | undefined;
    if (cmd.focusedTactics && cmd.focusedTactics.length > 0) {
      const sufficesHypName = cmd.name === 'suffices' && cmd.args.length >= 1 && cmd.args[0].tag === 'Const'
        ? (cmd.args[0] as any).name as string
        : undefined;
      const focusedCtx = sufficesHypName
        ? [...goal.ctx, { name: sufficesHypName, type: { tag: 'Hole' as const, id: '_suffices_type' } }]
        : goal.ctx;
      focusedTactics = elaborateFocusedTactics(cmd.focusedTactics, focusedCtx, definitions, hasSorryRef);
    }

    const goalsBefore = extractGoalStates(engineToProofState(engine));
    const position = indexPathToSourcePosition(cmd.indexPath, sourceMap);
    const tactic = tacticCommandToTactic({ name: cmd.name, args: elabArgs, focusedTactics });

    if (tactic === 'sorry') {
      hasSorryRef.current = true;
      rootNode.children.push(createTacticNode(position, goalsBefore, goalsBefore, 'sorry'));
      continue;
    }

    const result = tactic.apply(engine, goal, goalId);
    if (!result.success) {
      rootNode.children.push(createTacticNode(position, goalsBefore, goalsBefore, cmd.name, result.error));
      const errorMsg = `Tactic '${tactic.name}' failed: ${result.error}`;
      if (cmd.indexPath) {
        const tacticEnv = createTCEnv({ definitions, indexPath: cmd.indexPath, options: { mode: 'check' } });
        throw TCEnvError.create(errorMsg, tacticEnv);
      }
      throw new Error(errorMsg);
    }

    engine = result.newEngine;
    const goalsAfter = extractGoalStates(engineToProofState(engine));
    const tacticNode = createTacticNode(position, goalsBefore, goalsAfter, cmd.name);
    rootNode.children.push(tacticNode);

    if ((cmd.name === 'cases' || cmd.name === 'induction') && cmd.caseBranches && cmd.caseBranches.length > 0) {
      engine = applyCaseBranchesRecursive(
        engine,
        cmd.caseBranches,
        definitions,
        new Map(),
        tacticNode,
        hasSorryRef,
        sourceMap,
      );
    } else if ((cmd.name === 'cases' || cmd.name === 'induction') && cmd.caseBranches?.length === 0) {
      engine = closeReflexiveGoals(engine);
    }
  }

  const remainingGoals = engine.getUnsolvedGoals();
  if (remainingGoals.length > 0 && !hasSorryRef.current) {
    throw new Error(`Tactic proof has unsolved goals: ${remainingGoals.length} remaining`);
  }

  rootNode.goalsAfter = extractGoalStates(engineToProofState(engine));
  return {
    term: engine.zonk(),
    infoTree: new TacticInfoTree(rootNode),
  };
}
