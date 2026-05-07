import { inferType } from './checker';
import { TTKContext, TTKTerm } from './kernel';
import { Constraint, DefinitionsMap, MetaVar, TCEnv } from './term';

interface CheckerInput {
  readonly term: TTKTerm;
  readonly context: TTKContext;
  readonly definitions: DefinitionsMap;
  readonly metaVars?: ReadonlyMap<string, MetaVar>;
  readonly constraints?: readonly Constraint[];
}

export function createTermCheckerEnv(input: CheckerInput): TCEnv<TTKTerm> {
  return new TCEnv(
    [...input.context],
    input.definitions,
    new Map(input.metaVars),
    [...(input.constraints ?? [])],
    [],
    [],
    input.term,
    new Map(),
    { mode: 'check' }
  );
}

export function inferTermInContext(input: CheckerInput): TCEnv<TTKTerm> {
  return inferType(createTermCheckerEnv(input));
}

export function inferTermTypeInContext(input: CheckerInput): TTKTerm {
  const inferredEnv = inferTermInContext(input);
  return inferredEnv.zonkTerm(inferredEnv.value);
}

export function elaborateTermInContext(input: CheckerInput): TTKTerm {
  try {
    const inferredEnv = inferTermInContext(input);
    const elaborated = inferredEnv.elaboratedTerm;
    if (!elaborated) {
      return input.term;
    }
    try {
      const solvedEnv = inferredEnv.solveMetasAndConstraints({ liftMetasToFullContext: false });
      return solvedEnv.zonkTerm(elaborated);
    } catch {
      return inferredEnv.zonkTerm(elaborated);
    }
  } catch {
    return input.term;
  }
}
