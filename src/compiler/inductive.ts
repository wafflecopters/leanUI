import { addDefinitionInTCEnv, addInductiveDefinitionInTCEnv, createTCEnv, DefinitionsMap, InductiveDefinition, postOrderTraverseTerm, TCEnv, TCEnvError } from "./term";
import { TTKTerm } from "../types/tt-kernel";
import { inferType } from "./checker";

function checkTermOnlyContainsValidConstructors(env: TCEnv<TTKTerm>): TCEnvError<unknown>[] {
  const errors: TCEnvError<unknown>[] = [];

  postOrderTraverseTerm(env.value, (term, indexPath) => {
    if (term.tag === 'Const' || term.tag === 'Var' || term.tag === 'Sort' || term.tag === 'App') {
      // Valid
    } else if (term.tag === 'Binder' && term.binderKind.tag === 'BPi') {
      // Valid
    } else {
      const msg = {
        Annot: 'Explicit annotation',
        Hole: 'Inferred type',
        Match: 'Pattern matching',
        Binder: undefined,
      }[term.tag] ?? (
          term.tag === 'Binder' ? term.binderKind.tag === 'BLam' ? 'Lambda Expression' : 'Let Expression' : undefined
        ) ?? 'Other syntax'
      errors.push(new TCEnvError(`Term contains syntax not allowed in an inductive type definition: ${msg}`, env.atIndexPath(indexPath)));
    }
  }, env.indexPath);

  return errors
}

function runAndAccumulateErrors<S, T>(
  env: TCEnv<S>,
  fn: (e: TCEnv<S>) => TCEnv<T>,
  errors: TCEnvError<unknown>[]
): TCEnv<T> | undefined {
  try {
    return fn(env);
  } catch (e) {
    if (e instanceof TCEnvError) {
      errors.push(e);
    } else {
      errors.push(new TCEnvError(e instanceof Error ? e.message : String(e), env));
    }
  }
}

export function checkInductiveDeclaration(
  name: string,
  type: TTKTerm,
  constructors: Array<{ name: string; type: TTKTerm }>,
  indexPositions: number[],
  definitions: DefinitionsMap,
): {
  success: false,
  errors: TCEnvError<unknown>[]
} | {
  success: true,
  newDefinitions: DefinitionsMap
} {
  const inductiveDefinition: InductiveDefinition = { name, type, constructors, indexPositions };
  const defEnv = createTCEnv(definitions).withValue(inductiveDefinition);

  const errors: TCEnvError<unknown>[] = [
    ...checkTermOnlyContainsValidConstructors(defEnv.inInductiveDefinitionType()),
    ...constructors.flatMap((_, index) =>
      checkTermOnlyContainsValidConstructors(
        defEnv
          .inInductiveDefinitionConstructors()
          .inInductiveDefinitionConstructor(index)
          .inInductiveDefinitionConstructorType(),
      )
    )
  ]

  if (errors.length > 0) {
    return { success: false, errors };
  }

  runAndAccumulateErrors(defEnv.inInductiveDefinitionType(), inferType, errors);

  if (errors.length > 0) {
    return { success: false, errors };
  }

  let ctorsEnv = addDefinitionInTCEnv(defEnv, name, type).inInductiveDefinitionConstructors();

  constructors.forEach((ctor, index) => {
    runAndAccumulateErrors(
      ctorsEnv.inInductiveDefinitionConstructor(index).inInductiveDefinitionConstructorType(),
      e => {
        const result = inferType(e)
        ctorsEnv = addDefinitionInTCEnv(ctorsEnv, ctor.name, ctor.type);
        return result
      },
      errors
    )
  })

  if (errors.length > 0) {
    return {
      success: false,
      errors
    }
  }

  const newEnv = addInductiveDefinitionInTCEnv(ctorsEnv, name, type, constructors, indexPositions);

  // TODO: ensure indices fit within the type
  // TODO: check for strict positivity

  return {
    success: true,
    newDefinitions: newEnv.definitions
  }
}
