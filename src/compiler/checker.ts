// INFERENCE

import { subst, TTKTerm } from "../types/tt-kernel"
import { TCEnv, TCEnvError } from "./term";

function inferBinderType(env: TCEnv<TTKTerm & { tag: 'Binder' }>): TCEnv<TTKTerm> {
  if (env.isBinderPiTerm()) {
    const domResult = inferType(env.inBinderPiDomain())
    const bodyResult = inferType(env.inBinderPiBody())

    return env.withValue(maxSort(domResult.value, bodyResult.value, env))
  }
  debugger
  throw new TCEnvError<TTKTerm>(`Inference not implemented for binder type ${env.value.tag}`, env)
}

export function inferType(env: TCEnv<TTKTerm>): TCEnv<TTKTerm> {
  if (env.isConstTerm()) {
    return env.getTypeDefinitionAssert(env.value.name)
  } else if (env.isBinderTerm()) {
    return inferBinderType(env)
  } else if (env.isSortTerm()) {
    return env.withValue({ tag: 'Sort', level: env.value.level + 1 })
  } else if (env.isVarTerm()) {
    return env.getTypeAtIndexInSignatureAssert(env.value.index)
  } else if (env.isAppTerm()) {
    const fnTypeEnv = inferType(env.inAppFn())

    if (!fnTypeEnv.isBinderPiTerm()) {
      throw fnTypeEnv.expectedBinderPiError()
    }

    const argEnv = env.inAppArg()
    inferType(argEnv)
    checkType(argEnv, fnTypeEnv.value.domain);
    return env.mapValue(term => subst(0, term.arg, fnTypeEnv.value.body))
  }
  debugger
  throw new TCEnvError<TTKTerm>(`Inference not implemented for term type ${env.value.tag}`, env)
}

// CHECKING

export function checkType(env: TCEnv<TTKTerm>, expectedType: TTKTerm): TCEnv<TTKTerm> {
  if (env.isBinderLambdaTerm()) {
    // ────────────────────────────────────────────────────────────────
    // (LAM) - Lambda abstraction
    // 
    //   Γ ⊢ Π x : A, B
    //   Γ, x : A ⊢ t ⇐ B
    //   ───────────────────────────────
    //   Γ ⊢ λ x : A => t ⇐ Π x : A, B
    // ────────────────────────────────────────────────────────────────
    if (expectedType.tag !== 'Binder' || expectedType.binderKind.tag !== 'BPi') {
      throw env.expectedCheckTypeToBeBinderPiError(expectedType)
    }
    env.assertAreTypesDefinitionallyEqual(env.value.domain, expectedType.domain, 'Lambda domain mismatch')
    return checkType(env.inBinderLambdaBody(), expectedType.body);
  }

  // ────────────────────────────────────────────────────────────────
  // (CONV) - Type conversion
  // 
  //   Γ ⊢ t ⇒ T
  //   T ≃ T′
  //   ─────────────
  //   Γ ⊢ t ⇐ T′
  // ────────────────────────────────────────────────────────────────
  const inferResult = inferType(env);
  env.assertAreTypesDefinitionallyEqual(inferResult.value, expectedType, 'Type mismatch')
  return inferResult
}

// Helpers

function maxSort(lhs: TTKTerm, rhs: TTKTerm, env: TCEnv<unknown>): TTKTerm {
  if (lhs.tag === 'Sort' && rhs.tag === 'Sort') {
    return { tag: 'Sort', level: Math.max(lhs.level, rhs.level) }
  }
  debugger
  throw new TCEnvError(`Max sort not implemented for term types ${lhs.tag} and ${rhs.tag}`, env)
}
