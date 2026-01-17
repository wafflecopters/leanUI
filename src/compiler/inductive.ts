import { addDefinitionInTCEnv, addInductiveDefinitionInTCEnv, createTCEnv, DefinitionsMap, extractPiSpine, InductiveDefinition, postOrderTraverseTerm, TCEnv, TCEnvError } from "./term";
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
  constructors.forEach((_, i) => checkStrictPositivity(name, ctorsEnv.inInductiveDefinitionConstructor(i), errors));

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
 * Check that the inductive type occurs only in strictly positive positions.
 *
 * A strictly positive occurrence means the inductive type does NOT appear
 * in the domain (left side) of any function arrow, except as a direct argument.
 *
 * The key insight is:
 * - For `succ : Nat -> Nat`, the `Nat` argument is strictly positive ✓
 *   (It's a direct argument, not nested under any arrows in its type)
 * - For `bad : (Nat -> X) -> Bad`, the `Nat` is NEGATIVE ✗
 *   (It's in the domain of a function type that is itself an argument)
 *
 * We check the DOMAINS of the constructor's Pi binders. Within each domain,
 * any occurrence of the inductive type is problematic because it means
 * the inductive type appears in a negative position.
 *
 * Examples:
 * - `Nat → Nat` - Nat in argument position is strictly positive ✓
 * - `(Nat → A) → Nat` - Nat inside the argument type is NEGATIVE ✗
 * - `((Nat → A) → A) → Nat` - Nat is still negative (nested) ✗
 */
function checkStrictPositivity(
  inductiveName: string,
  env: TCEnv<{ name: string, type: TTKTerm }>,
  errors: TCEnvError<unknown>[]
): TCEnvError<unknown>[] {
  let traverseEnv = env.inInductiveDefinitionConstructorType();
  while (traverseEnv.isBinderPiTerm()) {
    checkDomainPositivity(inductiveName, env.value.name, traverseEnv.inBinderPiDomain(), errors);
    traverseEnv = traverseEnv.inBinderPiBody();
  }
  return errors;
}

/**
 * Check a constructor argument type for positivity violations.
 *
 * A direct occurrence of the inductive type is fine (strictly positive).
 * But if the inductive type appears in the domain of a nested function type,
 * that's a positivity violation.
 *
 * @param termPath - The path to the current term being checked (for error reporting)
 */
function checkDomainPositivity(
  inductiveName: string,
  ctorName: string,
  env: TCEnv<TTKTerm>,
  errors: TCEnvError<unknown>[]
): void {
  if (env.isConstTerm() || env.isVarTerm() || env.isSortTerm() || env.isHoleTerm()) {
    // Direct occurrences of constants/vars are fine
    // Even if it's the inductive type, this is strictly positive
  } else if (env.isAppTerm()) {
    checkDomainPositivity(inductiveName, ctorName, env.inAppFn(), errors);
    checkDomainPositivity(inductiveName, ctorName, env.inAppArg(), errors);
  } else if (env.isBinderTerm()) {
    checkNestedPiForNegativeOccurrences(
      inductiveName,
      ctorName,
      env,
      'strictly_positive',
      errors,
    );
    if (env.isBinderPiTerm()) {
    } else {
      throw new Error(`Syntax has been checked already. This should not happen. Binder-${env.value.binderKind.tag}`);
    }
  } else {
    throw new Error(`Syntax has been checked already. This should not happen. ${env.value.tag}`);
  }
}

/**
 * Check a nested Pi type for negative occurrences of the inductive type.
 *
 * For a Pi type (A -> B):
 * - In the domain A, polarity is FLIPPED
 * - In the body B, polarity stays the same
 *
 * When we find the inductive type at negative polarity, it's an error.
 *
 * @param termPath - The path to the current term being checked (for error reporting)
 */
function checkNestedPiForNegativeOccurrences(
  inductiveName: string,
  ctorName: string,
  env: TCEnv<TTKTerm>,
  polarity: Polarity,
  errors: TCEnvError<unknown>[]
): void {
  if (env.isVarTerm() || env.isSortTerm()) {
    // Valid
  } else if (env.isConstTerm()) {
    if (env.value.name === inductiveName) {
      const msg = polarity === 'negative' ? 'negative' : '(non-strict) positive';
      errors.push(new TCEnvError(`Constructor '${ctorName}' has a ${msg} occurrence of '${inductiveName}'.`, env));
    }
  } else if (env.isAppTerm()) {
    checkNestedPiForNegativeOccurrences(inductiveName, ctorName, env.inAppFn(), polarity, errors);
    checkNestedPiForNegativeOccurrences(inductiveName, ctorName, env.inAppArg(), polarity, errors);
  } else if (env.isBinderTerm()) {
    if (env.isBinderPiTerm()) {
      checkNestedPiForNegativeOccurrences(inductiveName, ctorName, env.inBinderPiDomain(), flipPolarity(polarity), errors);
      checkNestedPiForNegativeOccurrences(inductiveName, ctorName, env.inBinderPiBody(), polarity, errors);
    } else {
      throw new Error(`Syntax has been checked already. This should not happen. Binder-${env.value.binderKind.tag}`);
    }
  } else {
    throw new Error(`Syntax has been checked already. This should not happen. ${env.value.tag}`);
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