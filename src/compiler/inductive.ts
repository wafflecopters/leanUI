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
  constructors.forEach((ctor, i) => checkNestedPiForNegativeOccurrences(name, ctor.name, ctorsEnv.inInductiveDefinitionConstructor(i).inInductiveDefinitionConstructorType(), 'strictly_positive', errors));

  if (errors.length > 0) {
    return { success: false, errors };
  }

  return {
    success: true,
    newDefinitions: newEnv.definitions
  }
}

/**
 * Polarity of an occurrence of a type variable.
 * - 'positive': Can appear here (target of arrows or direct argument)
 * - 'negative': Cannot appear here (source of arrow)
 * - 'strictly_positive': Can appear here and is not under any arrow on the left
 */
export type Polarity = 'strictly_positive' | 'positive' | 'negative';

/**
 * Check a nested Pi type for negative occurrences of the inductive type.
 *
 * For a Pi type (A -> B):
 * - In the domain A, polarity is FLIPPED
 * - In the body B, polarity stays the same
 *
 * When we find the inductive type at negative polarity, it's an error.
 */
function checkNestedPiForNegativeOccurrences(
  inductiveName: string,
  ctorName: string,
  env: TCEnv<TTKTerm>,
  polarity: Polarity,
  errorsAcc: TCEnvError<unknown>[]
): void {

  if (env.isConstTerm()) {
    if (env.value.name === inductiveName) {
      if (polarity !== 'strictly_positive') {
        const msg = polarity === 'negative' ? 'negative' : '(non-strict) positive'
        errorsAcc.push(new TCEnvError(
          `Constructor '${ctorName}' has ${msg} occurrence of '${inductiveName}'`,
          env
        ));
      }
    }
  } else if (env.isVarTerm() || env.isSortTerm() || env.isHoleTerm()) {
    // No occurrences of the inductive type
  } else if (env.isAppTerm()) {
    checkNestedPiForNegativeOccurrences(inductiveName, ctorName, env.inAppFn(), polarity, errorsAcc);
    checkNestedPiForNegativeOccurrences(inductiveName, ctorName, env.inAppArg(), polarity, errorsAcc);
  } else if (env.isBinderPiTerm()) {
    checkNestedPiForNegativeOccurrences(inductiveName, ctorName, env.inBinderPiDomain(), flipPolarity(polarity), errorsAcc);
    checkNestedPiForNegativeOccurrences(inductiveName, ctorName, env.inBinderPiBody(), polarity, errorsAcc);
  } else {
    throw new Error('Syntax has been checked already. This should not happen.');
  }
}

/**
 * Flip the polarity when entering the domain of a function type.
 */
function flipPolarity(p: Polarity): Polarity {
  switch (p) {
    case 'strictly_positive':
      return 'negative';
    case 'positive':
      return 'negative';
    case 'negative':
      return 'positive';
  }
}