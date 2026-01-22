// INFERENCE

import { TTKTerm, mkLMax, simplifyLevel, mkPi, prettyPrint } from "./kernel";
import { subst } from "./subst";
import { assertIsPi, TCEnv, TCEnvError } from "./term";

/**
 * Get a readable name for a function being applied.
 * Used to provide helpful error context like "while checking argument to 'Succ'".
 */
function getFunctionName(fn: TTKTerm, env: TCEnv<unknown>): string {
  // Unwrap applications to get the head
  let head = fn;
  while (head.tag === 'App') {
    head = head.fn;
  }

  if (head.tag === 'Const') {
    return `'${head.name}'`;
  }
  if (head.tag === 'Var') {
    const name = env.context[env.context.length - 1 - head.index]?.name;
    if (name) {
      return `'${name}'`;
    }
  }
  // Fallback: pretty print the function (truncated if too long)
  const printed = prettyPrint(fn, env.context.map(c => c.name).reverse());
  if (printed.length > 30) {
    return 'function';
  }
  return printed;
}

/**
 * Count the number of Pi binders in a type and extract their names.
 * Used to provide better error messages for under-applied functions.
 */
function countPiBindersWithNames(type: TTKTerm): { count: number; names: string[] } {
  const names: string[] = [];
  let current = type;
  while (current.tag === 'Binder' && current.binderKind.tag === 'BPi') {
    names.push(current.name);
    current = current.body;
  }
  return { count: names.length, names };
}

/**
 * Get a short description of a term for error messages.
 */
function getTermDescription(term: TTKTerm, env: TCEnv<unknown>): string {
  if (term.tag === 'Const') {
    return `'${term.name}'`;
  }
  if (term.tag === 'Var') {
    const name = env.context[env.context.length - 1 - term.index]?.name;
    if (name) {
      return `'${name}'`;
    }
    return 'variable';
  }
  if (term.tag === 'App') {
    return `application of ${getFunctionName(term.fn, env)}`;
  }
  if (term.tag === 'Binder') {
    if (term.binderKind.tag === 'BLam') return 'lambda';
    if (term.binderKind.tag === 'BPi') return 'Pi type';
    if (term.binderKind.tag === 'BLet') return 'let expression';
  }
  if (term.tag === 'Sort') return 'Type';
  if (term.tag === 'Hole') return 'hole';
  if (term.tag === 'Meta') return 'metavariable';
  if (term.tag === 'Annot') return 'annotated term';
  if (term.tag === 'Match') return 'match expression';
  return 'term';
}

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

    // IMPORTANT: Use env1's context (original), not domEnv's context.
    // Checking the domain may extend the context (if domain is itself a Pi),
    // but that extension should NOT leak into the body's context.
    // We only need domEnv for its metaVars/constraints/levelMetas.
    const { env: env2, sort: bodySort } = domEnv.typeSortFresh();
    const envForBody = env1.withMetasConstraintsLevelMetasFrom(env2);
    const bodyEnv = checkType(envForBody.atValueAndPathOfEnv(env).inBinderPiBody(), bodySort);

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

    // Check the argument against the expected domain type
    let argEnv: TCEnv<TTKTerm>;
    try {
      argEnv = checkType(fnTypeEnv.atValueAndPathOfEnv(env).inAppArg(), fnTypeEnv.value.domain);
    } catch (e) {
      if (e instanceof TCEnvError) {
        // Provide semantic error: what function, what it expects, what it got
        const fnName = getFunctionName(env.value.fn, env);
        const expectedType = env.prettyPrint(fnTypeEnv.value.domain);

        // Try to infer the argument's type to show what was actually provided
        let actualType: string | undefined;
        try {
          const argTypeEnv = inferType(env.inAppArg());
          actualType = env.prettyPrint(argTypeEnv.value);
        } catch {
          // Couldn't infer argument type - that's fine, we'll show a simpler message
        }

        const msg = actualType
          ? `${fnName} expects ${expectedType} but was applied to ${actualType}`
          : `${fnName} expects ${expectedType}`;
        throw e.wrappedBy(msg);
      }
      throw e;
    }

    // Result type is B[x := e] where B is the body and e is the argument
    // Use the ELABORATED argument for substitution (in case it was a Hole->Meta)
    const elaboratedArg = argEnv.value;
    const resultType = subst(0, elaboratedArg, fnTypeEnv.value.body);

    // Construct the elaborated App with the elaborated function and argument
    // The function's elaborated form is in fnTypeEnv.elaboratedTerm (if set)
    const elaboratedFn = fnTypeEnv.elaboratedTerm ?? env.value.fn;
    const elaboratedApp: TTKTerm = { tag: 'App', fn: elaboratedFn, arg: elaboratedArg };

    return argEnv.withValue(resultType).withElaboratedTerm(elaboratedApp);
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

    let lambdaEnv: typeof env | undefined = undefined

    try {
      lambdaEnv = env.unifyTerms(env.value.domain, expectedType.domain)
    } catch (e) {
      if (e instanceof TCEnvError) {
        debugger
        throw e.wrappedBy(`Lambda parameter '${env.value.name}' has type ${e.env.prettyPrint(env.value.domain)} but expected ${e.env.prettyPrint(expectedType.domain)}`);
      }
      throw e;
    }

    const bodyEnv = lambdaEnv.inBinderLambdaBody()
    const checkedBodyEnv = checkType(bodyEnv, expectedType.body)

    // Reconstruct the Lambda with the elaborated body
    const elaboratedLambda: TTKTerm = {
      tag: 'Binder',
      name: env.value.name,
      binderKind: env.value.binderKind,
      domain: env.value.domain,
      body: checkedBodyEnv.value  // Use the elaborated body
    };
    return checkedBodyEnv.withValue(elaboratedLambda);
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
  // inferredEnv.elaboratedTerm is the ELABORATED TERM (if set)
  // We unify the inferred type with the expected type
  try {
    const unifiedEnv = inferredEnv.unifyTerms(inferredEnv.value, expectedType);
    // Return with the elaborated term (if available), otherwise the original term
    const elaboratedTerm = inferredEnv.elaboratedTerm ?? env.value;
    return unifiedEnv.withValue(elaboratedTerm);
  } catch (e) {
    if (e instanceof TCEnvError) {
      const termDesc = getTermDescription(env.value, env);
      const inferredType = env.prettyPrint(inferredEnv.value);
      const expected = env.prettyPrint(expectedType);

      // Check if this is an under-application: inferred type is a Pi but expected type is not
      const inferredIsPi = inferredEnv.value.tag === 'Binder' && inferredEnv.value.binderKind.tag === 'BPi';
      const expectedIsPi = expectedType.tag === 'Binder' && expectedType.binderKind.tag === 'BPi';

      if (inferredIsPi && !expectedIsPi) {
        // Count how many arguments are still needed
        const { count, names } = countPiBindersWithNames(inferredEnv.value);
        const argList = names.map(n => `'${n}'`).join(', ');
        throw e.wrappedBy(
          `${termDesc} is missing required argument${count > 1 ? 's' : ''}: ${argList}. ` +
          `Expected ${expected} but got a function type.`
        );
      }

      throw e.wrappedBy(`${termDesc} has type ${inferredType} but expected ${expected}`);
    }
    throw e;
  }
}

