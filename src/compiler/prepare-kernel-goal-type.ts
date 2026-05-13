import type { TTKContext, TTKTerm } from './kernel';
import { inferType } from './checker';
import { TCEnv, type DefinitionsMap } from './term';

export function prepareKernelGoalType(
  goalType: TTKTerm,
  context: TTKContext,
  definitions: DefinitionsMap,
): TTKTerm {
  const env = new TCEnv(
    context,
    definitions,
    new Map(),
    [],
    [],
    [],
    goalType,
    new Map(),
    { mode: 'check' },
  );

  try {
    const inferred = inferType(env);
    const solved = inferred.solveMetasAndConstraints({ liftMetasToFullContext: false });
    return solved.zonkTerm(inferred.elaboratedTerm ?? goalType);
  } catch {
    return goalType;
  }
}
