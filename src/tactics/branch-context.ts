import type { TTKContext } from '../compiler/kernel';
import type { MetaVar } from '../compiler/term';
import type { TacticEngine } from './tacticsEngine';

export function renameLastCtxEntries(
  engine: TacticEngine,
  userNames: readonly string[],
): TacticEngine {
  if (userNames.length === 0) return engine;
  const goalId = engine.getFocusedGoalId();
  const goal = engine.getFocusedGoal();
  if (!goalId || !goal) return engine;

  const startIdx = goal.ctx.length - userNames.length;
  if (startIdx < 0) return engine;

  const reserved = new Set<string>();
  for (let i = 0; i < startIdx; i++) {
    reserved.add(goal.ctx[i].name);
  }

  const renamedCtx = goal.ctx.map((entry, i) => {
    if (i < startIdx) return entry;
    let desired = userNames[i - startIdx];
    if (reserved.has(desired)) {
      let suffix = 1;
      while (reserved.has(desired + suffix)) suffix++;
      desired = desired + suffix;
    }
    reserved.add(desired);
    return { ...entry, name: desired };
  });

  const renamedGoal: MetaVar = { ...goal, ctx: renamedCtx };
  const newMetaVars = new Map(engine.metaVars);
  newMetaVars.set(goalId, renamedGoal);
  return engine.withUpdates({ metaVars: newMetaVars });
}

export function renameCtxEntriesByCurrentNames(
  engine: TacticEngine,
  currentNames: readonly string[],
  userNames: readonly string[],
): TacticEngine {
  if (currentNames.length === 0 || currentNames.length !== userNames.length) return engine;
  const goalId = engine.getFocusedGoalId();
  const goal = engine.getFocusedGoal();
  if (!goalId || !goal) return engine;

  const indices = currentNames.map(name => goal.ctx.findIndex(entry => entry.name === name));
  if (indices.some(index => index < 0)) return engine;

  const reserved = new Set<string>();
  for (let i = 0; i < goal.ctx.length; i++) {
    if (!indices.includes(i)) reserved.add(goal.ctx[i].name);
  }

  const renamedCtx = goal.ctx.map((entry, i) => {
    const renameIdx = indices.indexOf(i);
    if (renameIdx < 0) return entry;
    let desired = userNames[renameIdx];
    if (reserved.has(desired)) {
      let suffix = 1;
      while (reserved.has(desired + suffix)) suffix++;
      desired = desired + suffix;
    }
    reserved.add(desired);
    return { ...entry, name: desired };
  });

  const renamedGoal: MetaVar = { ...goal, ctx: renamedCtx, branchParamNames: userNames.slice() as string[] };
  const newMetaVars = new Map(engine.metaVars);
  newMetaVars.set(goalId, renamedGoal);
  return engine.withUpdates({ metaVars: newMetaVars });
}

export function createBranchParamNameMap(
  goalCtx: TTKContext,
  branchParamNames: readonly string[],
  outerParamNameMap?: Map<string, string>,
): Map<string, string> {
  const paramNameMap = new Map<string, string>(outerParamNameMap);
  const ctxNames = goalCtx.map(entry => entry.name);
  for (let i = 0; i < branchParamNames.length; i++) {
    const ctxIndex = ctxNames.length - branchParamNames.length + i;
    if (ctxIndex >= 0 && ctxIndex < ctxNames.length) {
      paramNameMap.set(branchParamNames[i], ctxNames[ctxIndex]);
    }
  }
  return paramNameMap;
}

export function createBranchParamNameMapFromCurrentNames(
  goalCtx: TTKContext,
  currentNames: readonly string[],
  branchParamNames: readonly string[],
  outerParamNameMap?: Map<string, string>,
): Map<string, string> {
  const paramNameMap = new Map<string, string>(outerParamNameMap);
  if (currentNames.length !== branchParamNames.length) return paramNameMap;
  for (let i = 0; i < currentNames.length; i++) {
    const ctxEntry = goalCtx.find(entry => entry.name === currentNames[i]);
    if (ctxEntry) {
      paramNameMap.set(branchParamNames[i], ctxEntry.name);
    }
  }
  return paramNameMap;
}
