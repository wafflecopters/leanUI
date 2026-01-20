// INFERENCE

import { TTKTerm, mkLMax, simplifyLevel, mkPi } from "./kernel";
import { subst } from "./subst";
import { assertIsPi, TCEnv, TCEnvError } from "./term";

function inferBinderType(env: TCEnv<TTKTerm & { tag: 'Binder' }>): TCEnv<TTKTerm> {
  if (env.isBinderPiTerm()) {
    // ────────────────────────────────────────────────────────────────
    // (PI) - Pi type
    //
    //   Γ ⊢ A ⇐ Type_i
    //   Γ, x : A ⊢ B ⇐ Type_j
    //   ─────────────────────────────
    //   Γ ⊢ Π x : A, B ⇒ Type_max(i,j)
    // ────────────────────────────────────────────────────────────────
    // Create fresh level metas for domain and body
    const { env: env1, sort: domainSort } = env.typeSortFresh();
    const domEnv = checkType(env1.atValueAndPathOfEnv(env).inBinderPiDomain(), domainSort);

    const { env: env2, sort: bodySort } = domEnv.typeSortFresh();
    const bodyEnv = checkType(env2.atValueAndPathOfEnv(env).inBinderPiBody(), bodySort);

    // Result is Sort(max(l_i, l_j)) where the levels come from the fresh metas
    const resultSort: TTKTerm = {
      tag: 'Sort',
      level: simplifyLevel(mkLMax(domainSort.level, bodySort.level))
    };
    return bodyEnv.withValue(resultSort);
  }

  if (env.isBinderLambdaTerm()) {
    // ────────────────────────────────────────────────────────────────
    // (LAM-INFER) - Lambda without expected type
    //
    //   Γ ⊢ A ⇐ Type
    //   Γ, x : A ⊢ t ⇒ B
    //   ─────────────────────────────
    //   Γ ⊢ λ x : A => t ⇒ Π x : A, B
    // ────────────────────────────────────────────────────────────────
    // Note: This requires the lambda to have a domain annotation.
    // If unannotated, we can't infer — must use checkType instead.
    if (env.lambdaDomainIsHole()) {
      throw TCEnvError.create('Cannot infer type of unannotated lambda', env);
    }
    const { env: env1, sort: domainSort } = env.typeSortFresh();
    const domEnv = checkType(env1.atValueAndPathOfEnv(env).inBinderLambdaDomain(), domainSort);
    const bodyEnv = inferType(domEnv.atValueAndPathOfEnv(env).inBinderLambdaBody());
    // Build Π(x : A). B where A is the domain and B is the inferred body type
    const piType = mkPi(env.value.domain, bodyEnv.value, env.value.name);
    return bodyEnv.withValue(piType);
  }

  debugger
  throw TCEnvError.create(`Inference not implemented for binder type ${env.value.binderKind.tag}`, env)
}

export function inferType(env: TCEnv<TTKTerm>): TCEnv<TTKTerm> {
  if (env.isVarTerm()) {
    // ────────────────────────────────────────────────────────────────
    // (VAR) - Variable
    //
    //   (x : T) ∈ Γ
    //   ─────────────
    //   Γ ⊢ x ⇒ T
    // ────────────────────────────────────────────────────────────────
    return env.getTypeAtIndexInContextAssert(env.value.index)
  }

  if (env.isConstTerm()) {
    // ────────────────────────────────────────────────────────────────
    // (CONST) - Constant
    //
    //   (c : T) ∈ Σ
    //   ─────────────
    //   Γ ⊢ c ⇒ T
    // ────────────────────────────────────────────────────────────────
    return env.getTypeDefinitionAssert(env.value.name)
  }

  if (env.isSortTerm()) {
    // ────────────────────────────────────────────────────────────────
    // (SORT) - Type/Sort
    //
    //   ─────────────────
    //   Γ ⊢ Type_i ⇒ Type_(i+1)
    // ────────────────────────────────────────────────────────────────
    return env.withSortOfSort();
  }

  if (env.isAppTerm()) {
    // ────────────────────────────────────────────────────────────────
    // (APP) - Application
    //
    //   Γ ⊢ f ⇒ Π x : A, B
    //   Γ ⊢ e ⇐ A
    //   ─────────────────────────
    //   Γ ⊢ f e ⇒ B[x := e]
    // ────────────────────────────────────────────────────────────────
    const fnTypeEnv = inferType(env.inAppFn()).ensurePi();
    const argEnv = checkType(fnTypeEnv.atValueAndPathOfEnv(env).inAppArg(), fnTypeEnv.value.domain);
    // Result type is B[x := e] where B is the body and e is the argument
    const resultType = subst(0, env.value.arg, fnTypeEnv.value.body);
    return argEnv.withValue(resultType);
  }

  if (env.isBinderTerm()) {
    return inferBinderType(env)
  }

  if (env.isHoleTerm()) {
    // ────────────────────────────────────────────────────────────────
    // (HOLE-INFER) - Hole in infer mode
    //
    // Can't infer the type of a hole — need expected type.
    // Create a meta for both the type and the term.
    // ────────────────────────────────────────────────────────────────
    const { env: envWithTypeMeta, metaTerm: typeMeta } = env.createMetaForType();
    return envWithTypeMeta.createMetaForHole(typeMeta);
  }

  if (env.isAnnotTerm()) {
    // ────────────────────────────────────────────────────────────────
    // (ANNOT) - Type annotation
    //
    //   Γ ⊢ T ⇐ Type
    //   Γ ⊢ t ⇐ T
    //   ─────────────────
    //   Γ ⊢ (t : T) ⇒ T
    // ────────────────────────────────────────────────────────────────
    const { env: env1, sort: typeSort } = env.typeSortFresh();
    const typeEnv = checkType(env1.atValueAndPathOfEnv(env).inAnnotType(), typeSort);
    // The checked type annotation becomes the expected type for the term
    const annotationType = env.value.type;  // Use the original annotation type
    const termEnv = checkType(typeEnv.atValueAndPathOfEnv(env).inAnnotTerm(), annotationType);
    return termEnv.withValue(annotationType);
  }

  debugger
  throw TCEnvError.create(`Inference not implemented for term type ${env.value.tag}`, env)
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
    assertIsPi(expectedType)

    return env
      .unifyTerms(env.value.domain, expectedType.domain)
      .then(e => checkType(e.inBinderLambdaBody(), expectedType.body))
  }

  if (env.isHoleTerm()) {
    // ────────────────────────────────────────────────────────────────
    // (HOLE) - Hole
    //
    //   ?m fresh
    //   Γ ⊢ ?m : T
    //   ─────────────
    //   Γ ⊢ _ ⇐ T
    // ────────────────────────────────────────────────────────────────
    return env.createMetaForHole(expectedType, 'Hole type mismatch')
  }

  // ────────────────────────────────────────────────────────────────
  // (CONV) - Type conversion
  //
  //   Γ ⊢ t ⇒ T
  //   T ≃ T′
  //   ─────────────
  //   Γ ⊢ t ⇐ T′
  // ────────────────────────────────────────────────────────────────
  const inferredEnv = inferType(env);
  // inferredEnv.value is the INFERRED TYPE, not the term
  // We unify the inferred type with the expected type
  const unifiedEnv = inferredEnv.unifyTerms(inferredEnv.value, expectedType);
  // Return with the original term (env.value), not the type
  return unifiedEnv.atValueAndPathOfEnv(env);
}

