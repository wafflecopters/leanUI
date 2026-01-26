// INFERENCE

import { TTKTerm, mkLMax, simplifyLevel, mkPi, prettyPrint, mkLevelNum, levelContainsParam, mkLSucc, mkLOmega } from "./kernel";
import { subst } from "./subst";
import { assertIsPi, TCEnv, TCEnvError, getTermDefinition, DefinitionsMap, NamedArgMap } from "./term";

/**
 * Get the namedArgMap for a constructor by searching all inductive types.
 */
function getConstructorNamedArgMap(definitions: DefinitionsMap, ctorName: string): NamedArgMap | undefined {
  for (const inductive of definitions.inductiveTypes.values()) {
    for (const ctor of inductive.constructors) {
      if (ctor.name === ctorName) {
        return ctor.namedArgMap;
      }
    }
  }
  return undefined;
}

/**
 * Get the namedArgMap for an inductive type itself.
 */
function getInductiveNamedArgMap(definitions: DefinitionsMap, typeName: string): NamedArgMap | undefined {
  const inductive = definitions.inductiveTypes.get(typeName);
  return inductive?.namedArgMap;
}

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
    // However, if the level contains a level parameter (LParam), this means
    // the codomain level depends on a bound variable of type ULevel.
    // In that case, the Pi type must live in Type ω.
    // Example: (U : ULevel) -> Type U has type Type ω
    const rawLevel = simplifyLevel(mkLMax(domainSort.level, bodySort.level));
    // Substitute any solved level metas before checking for LParam
    const substitutedLevel = bodyEnv.substituteLevelMetasInLevel(rawLevel);
    const simplifiedLevel = simplifyLevel(substitutedLevel);
    const resultLevel = levelContainsParam(simplifiedLevel) ? mkLSucc(mkLOmega()) : simplifiedLevel;
    const resultSort: TTKTerm = {
      tag: 'Sort',
      level: resultLevel
    };

    // Build elaborated Pi term if domain or body was elaborated (Holes->Metas)
    // This allows zonking to substitute solved metas in the constructor type.
    const elaboratedDomain = domEnv.elaboratedTerm ?? env.value.domain;
    const elaboratedBody = bodyEnv.elaboratedTerm ?? env.value.body;
    const elaboratedPi: TTKTerm = {
      tag: 'Binder',
      name: env.value.name,
      binderKind: env.value.binderKind,
      domain: elaboratedDomain,
      body: elaboratedBody
    };
    return bodyEnv.withValue(resultSort).withElaboratedTerm(elaboratedPi);
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
    // Note: If domain is a Hole (unannotated lambda), checkType will
    // create a meta for it, which can be inferred from usage.
    const { env: env1, sort: domainSort } = env.typeSortFresh();
    const domEnv = checkType(env1.atValueAndPathOfEnv(env).inBinderLambdaDomain(), domainSort);

    // Use elaborated domain (Meta if it was a Hole) for both context extension and Pi type
    const elaboratedDomain = domEnv.elaboratedTerm ?? env.value.domain;

    // Infer body type with context extended by the ELABORATED domain (not the original Hole)
    const bodyEnv = inferType(domEnv.atValueAndPathOfEnv(env).inBinderLambdaBodyWithDomain(elaboratedDomain));

    // Build Π(x : A). B where A is the elaborated domain and B is the inferred body type
    const piType = mkPi(elaboratedDomain, bodyEnv.value, env.value.name);
    return bodyEnv.withValue(piType);
  }

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
    // (APP) - Application with implicit argument insertion
    //
    //   Γ ⊢ f ⇒ Π x : A, B
    //   (insert metas for implicit args if needed)
    //   Γ ⊢ e ⇐ A
    //   ─────────────────────────
    //   Γ ⊢ f e ⇒ B[x := e]
    // ────────────────────────────────────────────────────────────────

    // NOTE: Implicit argument insertion is handled by elaboration (elab.ts).
    // When a function has named parameters (namedArgMap), elaboration:
    // 1. Reorders named arguments to their correct positions
    // 2. Fills missing implicit positions with Holes
    // The checker's job is to convert those Holes to Metas with proper types.
    // We do NOT do implicit insertion here to avoid double-inserting.

    // Infer function type
    const fnInferredEnv = inferType(env.inAppFn());
    let fnTypeEnv = fnInferredEnv.ensurePi();
    let currentFnTerm = fnTypeEnv.elaboratedTerm ?? env.value.fn;

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
        let innerError: TCEnvError | undefined;
        try {
          const argTypeEnv = inferType(env.inAppArg());
          actualType = env.prettyPrint(argTypeEnv.value);
        } catch (e) {
          if (e instanceof TCEnvError) {
            innerError = e;
          } else {
            throw e;
          }
        }

        const msg = actualType
          ? `${fnName} expects ${expectedType} but was applied to ${actualType}`
          : `${fnName} expects ${expectedType}`;

        if (innerError) {
          throw innerError
        }

        throw e.wrappedBy(msg);
      }
      throw e;
    }

    // Result type is B[x := e] where B is the body and e is the argument
    // Use the ELABORATED argument for substitution (in case it was a Hole->Meta)
    const elaboratedArg = argEnv.elaboratedTerm ?? argEnv.value;
    const resultType = subst(0, elaboratedArg, fnTypeEnv.value.body);

    // Construct the elaborated App with the elaborated function (with implicits) and argument
    const elaboratedApp: TTKTerm = { tag: 'App', fn: currentFnTerm, arg: elaboratedArg };

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

  if (env.isULevelTerm()) {
    // ────────────────────────────────────────────────────────────────
    // (ULEVEL) - Universe level
    //
    //   ─────────────────
    //   Γ ⊢ ULevel ⇒ ULevel
    // ────────────────────────────────────────────────────────────────
    return env.withValue({ tag: 'Sort', level: mkLevelNum(1) });
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
  // (CONV) - Type conversion with implicit argument insertion
  //
  //   Γ ⊢ t ⇒ T
  //   T ≃ T′
  //   ─────────────
  //   Γ ⊢ t ⇐ T′
  //
  // Additionally, if T = Π{x:A}.B (implicit/named Pi) and T′ is not a Pi,
  // we insert a meta for the implicit argument:
  //   Γ ⊢ t ?m ⇐ T′   where ?m : A
  // ────────────────────────────────────────────────────────────────
  let inferredEnv = inferType(env);
  // inferredEnv.value is the INFERRED TYPE, not the term
  // inferredEnv.elaboratedTerm is the ELABORATED TERM (if set)
  let currentTerm = inferredEnv.elaboratedTerm ?? env.value;

  // Insert implicit arguments while needed
  // When inferred type is a Pi and we have namedArgMap info indicating the position is implicit,
  // and expected type is not a Pi, we insert metavariables for the implicit arguments
  // Get namedArgMap from the term if it's a Const
  const namedArgMap = env.value.tag === 'Const'
    ? getTermDefinition(env.definitions, env.value.name)?.namedArgMap ??
      getConstructorNamedArgMap(env.definitions, env.value.name) ??
      getInductiveNamedArgMap(env.definitions, env.value.name)
    : undefined;

  while (true) {
    const inferredIsPi = inferredEnv.value.tag === 'Binder' && inferredEnv.value.binderKind.tag === 'BPi';

    if (!inferredIsPi) {
      // Inferred type is not a Pi - stop
      break;
    }

    // Check if this binder is implicit (its name is in namedArgMap)
    const piBinder = inferredEnv.value as TTKTerm & { tag: 'Binder'; binderKind: { tag: 'BPi' } };
    const binderName = piBinder.name;
    const isImplicit = namedArgMap && namedArgMap.has(binderName);

    if (!isImplicit) {
      // This is an explicit argument - stop inserting implicits
      break;
    }

    // Insert an implicit argument: create a meta for the domain type
    // Special case: if domain is ULevel, create a level meta so it can participate
    // in level unification when the level appears inside Sort terms.
    let envWithMeta: typeof inferredEnv;
    let metaTerm: TTKTerm;
    if (piBinder.domain.tag === 'ULevel') {
      const result = inferredEnv.freshLevelMeta();
      envWithMeta = result.env;
      metaTerm = result.level;
    } else {
      const result = inferredEnv.createMetaWithType(piBinder.domain);
      envWithMeta = result.env;
      metaTerm = result.metaTerm;
    }

    // Apply the current term to the meta
    currentTerm = { tag: 'App', fn: currentTerm, arg: metaTerm };

    // New inferred type is the body with the meta substituted
    const newInferredType = subst(0, metaTerm, piBinder.body);
    inferredEnv = envWithMeta.withValue(newInferredType);
  }

  // Now try to unify the inferred type with the expected type
  // First, substitute any solved level metas in both types
  const inferredTypeWithLevels = inferredEnv.substituteLevelMetasInTerm(inferredEnv.value);
  const expectedTypeWithLevels = inferredEnv.substituteLevelMetasInTerm(expectedType);

  try {
    const unifiedEnv = inferredEnv.unifyTerms(inferredTypeWithLevels, expectedTypeWithLevels);
    // Return with the elaborated term (with implicit args inserted)
    // Set both value and elaboratedTerm to currentTerm since it has all elaboration applied
    return unifiedEnv.withValue(currentTerm).withElaboratedTerm(currentTerm);
  } catch (e) {
    if (e instanceof TCEnvError) {
      const termDesc = getTermDescription(env.value, env);
      const inferredType = env.prettyPrint(inferredEnv.value);
      const expected = env.prettyPrint(expectedType);

      // Check if this is an under-application: inferred type is a Pi but expected type is not
      const inferredIsPi = inferredEnv.value.tag === 'Binder' && inferredEnv.value.binderKind.tag === 'BPi';
      const expectedIsPi = expectedType.tag === 'Binder' && expectedType.binderKind.tag === 'BPi';

      if (inferredIsPi && !expectedIsPi) {
        // Count how many arguments are still needed (these are explicit args, not implicit)
        const { count, names } = countPiBindersWithNames(inferredEnv.value);
        const argList = names.map(n => `'${n}'`).join(', ');
        throw e.wrappedBy(
          `${termDesc} is missing required argument${count > 1 ? 's' : ''}: ${argList}. ` +
          `Expected ${expected} but got a function type.`
        );
      }

      // Check if a term is being used where a type is expected
      const expectedIsSort = expectedType.tag === 'Sort' ||
        (expectedType.tag === 'Meta') ||  // Meta could be a Sort
        (expectedType.tag === 'Hole');    // Hole could be a Sort
      const inferredIsSort = inferredEnv.value.tag === 'Sort';

      if (expectedIsSort && !inferredIsSort && expectedType.tag === 'Sort') {
        throw e.wrappedBy(
          `${termDesc} is a term of type ${inferredType}, but a type was expected here. ` +
          `Only types (values of sort Type) can appear in type position.`
        );
      }

      throw e.wrappedBy(`${termDesc} has type ${inferredType} but expected ${expected}`);
    }
    throw e;
  }
}

