// INFERENCE

import { TTKTerm, mkLMax, simplifyLevel, mkPi, prettyPrint, mkLevelNum, levelContainsParam, mkLSucc, mkLOmega, isDefinitionallyEqual, mkULevel } from "./kernel";
import { subst, shiftTerm, minFreeVarIndex, containsVarIndex } from "./subst";
import { assertIsPi, TCEnv, TCEnvError, getTermDefinition, DefinitionsMap, NamedArgMap, BinderPartSegment } from "./term";
import { IndexPath } from "../types/source-position";
import { unifyTerms } from "./unify";

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
    // Check for duplicate parameter name (shadowing)
    if (!env.options.allowDuplicatePiNames) {
      const piName = env.value.name;
      if (piName !== '_' && piName !== '') {
        if (env.context.some(entry => entry.name === piName)) {
          throw TCEnvError.create(
            `Duplicate parameter name '${piName}' in type signature`,
            env.atIndexPath([...env.indexPath, BinderPartSegment.Name])
          );
        }
      }
    }

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

    // Build elaborated lambda term (preserving the lambda wrapper).
    // This is critical: when CONV calls inferType on a lambda, it uses
    // elaboratedTerm as the kernel term. Without this, the bare body would
    // be used, losing the lambda binders and leaving dangling de Bruijn indices.
    const elaboratedLambda: TTKTerm = {
      tag: 'Binder',
      name: env.value.name,
      binderKind: env.value.binderKind,
      domain: elaboratedDomain,
      body: bodyEnv.elaboratedTerm ?? env.value.body
    };
    return bodyEnv.withValue(piType).withElaboratedTerm(elaboratedLambda);
  }

  if (env.isBinderLetTerm()) {
    // ────────────────────────────────────────────────────────────────
    // (LET) - Let binding with optional type inference (no generalisation)
    //
    //   Γ ⊢ A ⇐ Type_i            (type annotation, or Hole→Meta)
    //   Γ ⊢ v ⇐ A                 (value checked against A; solves Meta if inferred)
    //   Γ, x : A ⊢ body ⇒ B'      (infer body type in extended context)
    //   B = [x := v]B'            (substitute v for x if B' references x, else shift)
    //   ─────────────────────────────────────────────────────────────────
    //   Γ ⊢ let x : A := v in body ⇒ B
    //
    // When A is a Hole, checkType creates a Meta. Checking v against
    // that Meta infers v's type and solves the Meta. No generalisation.
    // ────────────────────────────────────────────────────────────────

    // 1. Check type annotation against Sort (Hole → Meta for inference)
    const { env: env1, sort: domainSort } = env.typeSortFresh();
    const domEnv = checkType(env1.atValueAndPathOfEnv(env).inBinderLetDomain(), domainSort);
    const elaboratedDomain = domEnv.elaboratedTerm ?? env.value.domain;

    // 2. Check value against the (possibly meta) type — this creates constraints
    const valEnv = checkType(domEnv.atValueAndPathOfEnv(env).inBinderLetValue(), elaboratedDomain);
    const elaboratedValue = valEnv.elaboratedTerm ?? env.value.binderKind.defVal;

    // 3. Solve constraints to resolve the domain type before entering the body
    //    This is crucial when the domain was a Hole — checking the value creates
    //    constraints that solve the meta, but we need those solutions available
    //    for the body (e.g., when applying a let-bound function).
    const solvedEnv = valEnv.solveMetasAndConstraints({ liftMetasToFullContext: false });
    const solvedDomain = solvedEnv.zonkTerm(elaboratedDomain);

    // 4. Infer body type with x : solvedDomain in context (pass let-value for ζ-reduction)
    const bodyEnv = inferType(solvedEnv.atValueAndPathOfEnv(env).inBinderLetBodyWithDomain(solvedDomain, elaboratedValue));

    // 5. Build elaborated let term with solved domain
    const elaboratedLet: TTKTerm = {
      tag: 'Binder',
      name: env.value.name,
      binderKind: { tag: 'BLet', defVal: elaboratedValue },
      domain: solvedDomain,
      body: bodyEnv.elaboratedTerm ?? env.value.body
    };

    // 6. Strengthen the body type by removing the let binding from scope
    //    The body type was inferred in context Γ,x. We need to convert it to context Γ.
    //    If the body type references x (index 0), we substitute the let value.
    //    Otherwise, we just shift by -1.
    const bodyType = bodyEnv.value;
    const minFreeVar = minFreeVarIndex(bodyType);
    let strengthenedBodyType: TTKTerm;
    if (minFreeVar === 0) {
      // Body type references the let-bound variable
      // Substitute the let value (elaboratedValue) for index 0 in the body type
      // Note: subst(0, v, t) replaces index 0 with v and shifts down
      strengthenedBodyType = subst(0, elaboratedValue, bodyType);
    } else {
      // Body type doesn't reference the let variable, just shift by -1
      strengthenedBodyType = shiftTerm(bodyType, -1, 0);
    }

    // Return strengthened body type (the type of the whole let expression)
    return bodyEnv.withValue(strengthenedBodyType).withElaboratedTerm(elaboratedLet);
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
    const varResult = env.getTypeAtIndexInContextAssert(env.value.index);
    env.recordTypeInfo(varResult.value);
    return varResult;
  }

  if (env.isConstTerm()) {
    // ────────────────────────────────────────────────────────────────
    // (CONST) - Constant
    //
    //   (c : T) ∈ Σ
    //   ─────────────
    //   Γ ⊢ c ⇒ T
    // ────────────────────────────────────────────────────────────────
    const constName = env.value.name;

    // Built-in universe level operations (USucc, UMax, UIMax).
    // These are represented as Const nodes in TTK but are not user-defined.
    if (constName === 'USucc') {
      const resultType = mkPi(mkULevel(), mkULevel(), '_');
      env.recordTypeInfo(resultType);
      return env.withValue(resultType);
    }
    if (constName === 'UMax' || constName === 'UIMax') {
      const resultType = mkPi(mkULevel(), mkPi(mkULevel(), mkULevel(), '_'), '_');
      env.recordTypeInfo(resultType);
      return env.withValue(resultType);
    }

    const constResult = env.getTypeDefinitionAssert(constName);
    env.recordTypeInfo(constResult.value);
    return constResult;
  }

  if (env.isSortTerm()) {
    // ────────────────────────────────────────────────────────────────
    // (SORT) - Type/Sort
    //
    //   ─────────────────
    //   Γ ⊢ Type_i ⇒ Type_(i+1)
    // ────────────────────────────────────────────────────────────────
    const sortResult = env.withSortOfSort();
    env.recordTypeInfo(sortResult.value);
    return sortResult;
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
    let fnTypeEnv: ReturnType<typeof fnInferredEnv.ensurePi>;
    try {
      fnTypeEnv = fnInferredEnv.ensurePi();
    } catch (e) {
      if (e instanceof TCEnvError) {
        const fnName = getFunctionName(env.value.fn, env);
        const fnType = env.prettyPrint(fnInferredEnv.value);
        throw e.wrappedBy(`${fnName} has type ${fnType} and cannot be applied as a function`);
      }
      throw e;
    }
    let currentFnTerm = fnTypeEnv.elaboratedTerm ?? env.value.fn;

    // Check the argument against the expected domain type
    // IMPORTANT: Use env's context (the original context), not fnTypeEnv's context.
    // When inferring the type of a lambda, the context is extended with the lambda parameter,
    // but the argument should be checked in the original context (without the lambda parameter).
    let argEnv: TCEnv<TTKTerm>;
    try {
      argEnv = checkType(env.withMetasConstraintsLevelMetasFrom(fnTypeEnv).inAppArg(), fnTypeEnv.value.domain);
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
        } catch (e) {
          if (!(e instanceof TCEnvError)) {
            throw e;
          }
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
    const elaboratedArg = argEnv.elaboratedTerm ?? argEnv.value;
    const resultType = subst(0, elaboratedArg, fnTypeEnv.value.body);

    // Construct the elaborated App with the elaborated function (with implicits) and argument
    const elaboratedApp: TTKTerm = { tag: 'App', fn: currentFnTerm, arg: elaboratedArg };

    const appResult = argEnv.withValue(resultType).withElaboratedTerm(elaboratedApp);
    // Record at the APP's indexPath (env.indexPath), using argEnv's metaVars for zonking
    argEnv.atIndexPath(env.indexPath).recordTypeInfo(resultType);
    return appResult;
  }

  if (env.isBinderTerm()) {
    const binderResult = inferBinderType(env);
    env.recordTypeInfo(binderResult.value);
    // Record the binder variable's type at the .name sub-path
    // so hovering on the binder name shows the domain type (e.g., "n : Nat").
    const nameIndexPath: IndexPath = [...env.indexPath, { kind: 'field', name: 'name' }];
    env.atIndexPath(nameIndexPath).recordTypeInfo(env.value.domain);
    return binderResult;
  }

  if (env.isHoleTerm()) {
    // ────────────────────────────────────────────────────────────────
    // (HOLE-INFER) - Hole in infer mode
    //
    // Can't infer the type of a hole — need expected type.
    // Create a meta for both the type and the term.
    // ────────────────────────────────────────────────────────────────
    const { env: envWithTypeMeta, metaTerm: typeMeta } = env.createMetaForType();
    const holeResult = envWithTypeMeta.createMetaForHole(typeMeta);
    env.recordTypeInfo(typeMeta);
    return holeResult;
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
    env.recordTypeInfo(annotationType);
    return termEnv.withValue(annotationType);
  }

  if (env.isULevelTerm()) {
    // ────────────────────────────────────────────────────────────────
    // (ULEVEL) - Universe level type
    //
    //   ─────────────────
    //   Γ ⊢ ULevel ⇒ Type 1
    // ────────────────────────────────────────────────────────────────
    const ulevelType: TTKTerm = { tag: 'Sort', level: mkLevelNum(1) };
    env.recordTypeInfo(ulevelType);
    return env.withValue(ulevelType);
  }

  if (env.value.tag === 'ULit') {
    // ────────────────────────────────────────────────────────────────
    // (ULIT) - Universe level literal
    //
    //   ─────────────────
    //   Γ ⊢ n ⇒ ULevel    (where n is a numeric level like 0, 1, 2, ...)
    // ────────────────────────────────────────────────────────────────
    const ulitType: TTKTerm = { tag: 'ULevel' };
    env.recordTypeInfo(ulitType);
    return env.withValue(ulitType);
  }

  if (env.value.tag === 'Meta') {
    // ────────────────────────────────────────────────────────────────
    // (META) - Metavariable
    //
    // Look up the meta's type from metaVars. Metas are created during
    // elaboration with a known type.
    // ────────────────────────────────────────────────────────────────
    const meta = env.metaVars.get(env.value.id);
    if (meta) {
      env.recordTypeInfo(meta.type);
      return env.withValue(meta.type);
    }
    // If meta not found, this is an internal error
    throw TCEnvError.create(`Unknown metavariable: ${env.value.id}`, env);
  }

  if (env.value.tag === 'NatLit') {
    // ────────────────────────────────────────────────────────────────
    // (NATLIT) - Natural number literal
    //
    // A NatLit infers as the inductive type registered with @impl=nat.
    // If exactly one is registered, use it directly. If none, error.
    // (Phase 3 will add @ofNat coercion for non-nat targets.)
    // ────────────────────────────────────────────────────────────────
    const reg = env.definitions.natImplByCtor;
    if (reg && reg.size > 0) {
      // Collect distinct NatImpls (each impl appears under both ctors)
      const impls = new Set<string>();
      for (const impl of reg.values()) impls.add(impl.inductiveName);
      if (impls.size === 1) {
        const indName = [...impls][0];
        const natType: TTKTerm = { tag: 'Const', name: indName };
        env.recordTypeInfo(natType);
        return env.withValue(natType);
      }
      throw TCEnvError.create(
        `Cannot infer type for numeric literal ${env.value.value}: multiple @impl=nat types in scope (${[...impls].join(', ')}). Add a type annotation.`,
        env,
      );
    }
    throw TCEnvError.create(
      `Cannot infer type for numeric literal ${env.value.value}: no @impl=nat type registered. Declare an inductive with @syntax @impl=nat or use a type annotation.`,
      env,
    );
  }

  throw TCEnvError.create(`Inference not implemented for term type ${env.value.tag}`, env)
}

// CHECKING

export function checkType(env: TCEnv<TTKTerm>, expectedType: TTKTerm): TCEnv<TTKTerm> {
  // (NATLIT-COERCE) — when checking a NatLit against a non-Nat target type,
  // look for a registered @ofNat coercion and rewrite as `App(coerce, ..., NatLit)`.
  // This is what makes `1 : Carrier R` work when realOfNat is registered
  // with `@syntax @ofNat`.
  if (env.value.tag === 'NatLit') {
    // Walk to the head of the expected type
    let head = expectedType;
    while (head.tag === 'App') head = head.fn;
    if (head.tag === 'Const') {
      const headName = head.name;
      // Skip coercion if the target IS a Nat-impl — that's the identity case
      const reg = env.definitions.natImplByCtor;
      const isNatImpl = reg && [...reg.values()].some(impl => impl.inductiveName === headName);
      if (!isNatImpl) {
        const coerceFn = env.definitions.ofNatByTargetHead?.get(headName);
        if (coerceFn) {
          // Build: App(...App(Const(coerceFn), ?meta1), ..., NatLit)
          // The function takes some args, then a Nat. Insert metas for the
          // pre-Nat args; let unification solve them from expectedType.
          const coerceDef = env.definitions.terms.get(coerceFn);
          if (coerceDef) {
            // Count Pi binders before the final (Nat) one
            let argCount = 0;
            let t = coerceDef.type;
            while (t.tag === 'Binder' && t.binderKind.tag === 'BPi') {
              argCount++;
              t = t.body;
            }
            // argCount includes the Nat arg — we want metas for argCount-1 pre-Nat args
            const numPreArgs = argCount - 1;
            let appTerm: TTKTerm = { tag: 'Const', name: coerceFn };
            for (let i = 0; i < numPreArgs; i++) {
              appTerm = { tag: 'App', fn: appTerm, arg: { tag: 'Hole', id: `_ofNat_arg${i}` } };
            }
            appTerm = { tag: 'App', fn: appTerm, arg: env.value };
            // Now check this synthesized application against expectedType.
            // The CONV rule handles the unification.
            return checkType(env.withValue(appTerm), expectedType);
          }
        }
      }
    }
  }

  // Only use the Lambda-specific rule when expectedType is a Pi.
  // If expectedType is a Meta or something else, fall through to CONV rule
  // which infers the lambda's type and unifies.
  const expectedIsPi = expectedType.tag === 'Binder' && expectedType.binderKind.tag === 'BPi';
  if (env.isBinderLambdaTerm() && expectedIsPi) {
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

    const bodyEnv = lambdaEnv.inBinderLambdaBodyWithDomain(expectedType.domain)
    const checkedBodyEnv = checkType(bodyEnv, expectedType.body)

    // Reconstruct the Lambda with the elaborated domain and body
    // Use expectedType.domain instead of env.value.domain because:
    // 1. If env.value.domain was a Hole (unannotated lambda), unification succeeded
    //    so expectedType.domain is the actual inferred type
    // 2. If env.value.domain was concrete, unification verified it matches expectedType.domain
    // Either way, using expectedType.domain gives us the concrete type, not a Hole
    const elaboratedLambda: TTKTerm = {
      tag: 'Binder',
      name: env.value.name,
      binderKind: env.value.binderKind,
      domain: expectedType.domain,  // Use expected type's domain (concrete, not a Hole)
      body: checkedBodyEnv.value
    };
    // Record the lambda's Pi type at the lambda's path (env.indexPath), not the body's path.
    // Use lambdaEnv for correct outer context (without the lambda variable).
    lambdaEnv.atIndexPath(env.indexPath).recordTypeInfo(expectedType, expectedType);
    // Also record the lambda parameter's type at the .name sub-path
    // so hovering on the parameter name shows its type (e.g., "x : A").
    const nameIndexPath: IndexPath = [...env.indexPath, { kind: 'field', name: 'name' }];
    lambdaEnv.atIndexPath(nameIndexPath).recordTypeInfo(expectedType.domain);
    // Return at the OUTER context depth (lambdaEnv), not the body's depth (checkedBodyEnv).
    // The lambda body extends the context by 1, but after checking the body we leave that scope.
    // Returning at the outer depth ensures that subsequent type comparisons (e.g., CONV rule
    // comparing return types) create constraints with correct de Bruijn indices relative to
    // the outer context. Metas and constraints from the body are preserved via
    // withMetasConstraintsLevelMetasFrom — body constraints store their own ctx at the inner depth.
    return lambdaEnv.withMetasConstraintsLevelMetasFrom(checkedBodyEnv).withValue(elaboratedLambda);
  }

  if (env.isBinderLetTerm()) {
    // ────────────────────────────────────────────────────────────────
    // (LET-CHECK) - Let binding in checking mode
    //
    //   Γ ⊢ A ⇐ Type_i
    //   Γ ⊢ v ⇐ A
    //   Γ, x : A ⊢ body ⇐ T        (check body against expected type)
    //   ─────────────────────────────
    //   Γ ⊢ let x : A := v in body ⇐ T
    //
    // Unlike CONV (which infers then unifies), this propagates the expected
    // type directly to the body, so holes inside the body know their goal type.
    // ────────────────────────────────────────────────────────────────

    // 1. Check type annotation
    const { env: env1, sort: domainSort } = env.typeSortFresh();
    const domEnv = checkType(env1.atValueAndPathOfEnv(env).inBinderLetDomain(), domainSort);
    const elaboratedDomain = domEnv.elaboratedTerm ?? env.value.domain;

    // 2. Check value against the domain type
    const valEnv = checkType(domEnv.atValueAndPathOfEnv(env).inBinderLetValue(), elaboratedDomain);
    const elaboratedValue = valEnv.elaboratedTerm ?? env.value.binderKind.defVal;

    // 3. Solve metas from value checking before entering body
    const solvedEnv = valEnv.solveMetasAndConstraints({ liftMetasToFullContext: false });
    const solvedDomain = solvedEnv.zonkTerm(elaboratedDomain);

    // 4. Check body against expected type (propagating the goal)
    // Shift expectedType by +1 because we're entering the let body scope:
    // Var(0) in the body context refers to the let variable, so all existing
    // free variables in expectedType need to be bumped up by 1.
    const shiftedExpectedType = shiftTerm(expectedType, 1, 0);
    const bodyEnv = checkType(
      solvedEnv.atValueAndPathOfEnv(env).inBinderLetBodyWithDomain(solvedDomain),
      shiftedExpectedType
    );

    // 5. Build elaborated let term
    const elaboratedLet: TTKTerm = {
      tag: 'Binder',
      name: env.value.name,
      binderKind: { tag: 'BLet', defVal: elaboratedValue },
      domain: solvedDomain,
      body: bodyEnv.elaboratedTerm ?? env.value.body
    };

    // Record type info for the let expression and its name
    env.recordTypeInfo(expectedType, expectedType);
    const nameIndexPath: IndexPath = [...env.indexPath, { kind: 'field', name: 'name' }];
    env.atIndexPath(nameIndexPath).recordTypeInfo(solvedDomain);

    return env.withMetasConstraintsLevelMetasFrom(bodyEnv).withValue(elaboratedLet);
  }

  if (env.isHoleTerm()) {
    // ────────────────────────────────────────────────────────────────
    // (HOLE) - Hole
    //
    //   ?m fresh
    //   Γ ⊢ ?m : T
    //   ─────────────
    //   Γ ⊢ _ ⇐ T
    env.recordTypeInfo(expectedType, expectedType);
    return env.createMetaForHole(expectedType, 'Hole type mismatch');
  }

  // ────────────────────────────────────────────────────────────────
  // (APP-IMPLICIT-EXTRACT) - Extract implicit args from expected type for App chains
  //
  // When checking an application (e.g., MkDPair b refl) against an expected type,
  // if the head is a Const with implicit parameters, try to extract those implicit
  // arguments from the expected type BEFORE the normal CONV flow.
  // This enables: MkDPair b refl : DPair Nat (\n => Equal b (plus a n))
  // without needing explicit {fn := ...}
  //
  // Algorithm:
  // 1. Decompose App chain to get head Const and explicit args
  // 2. Get the Const's type and collect leading implicit parameters
  // 3. Apply the type to the explicit args to get the result type
  // 4. Unify result type with expected type in pattern mode
  // 5. Extract solutions for implicit parameters from substitutions
  // 6. Build new term with implicits applied: ((...(Const impl1) impl2) ... arg1) arg2 ...
  // 7. Check the new term
  // ────────────────────────────────────────────────────────────────

  // Helper: decompose App chain into head and args
  function getAppChainHeadAndArgs(term: TTKTerm): { head: TTKTerm; args: TTKTerm[] } | null {
    const args: TTKTerm[] = [];
    let current = term;
    while (current.tag === 'App') {
      args.unshift(current.arg);
      current = current.fn;
    }
    if (current.tag === 'Const') {
      return { head: current, args };
    }
    return null;
  }

  const appChain = getAppChainHeadAndArgs(env.value);

  if (appChain) {
    const constName = (appChain.head as { tag: 'Const'; name: string }).name;
    const explicitArgs = appChain.args;

    // Get named arg map to know which parameters are implicit
    const namedArgMap2 = getTermDefinition(env.definitions, constName)?.namedArgMap ??
      getConstructorNamedArgMap(env.definitions, constName) ??
      getInductiveNamedArgMap(env.definitions, constName);

    if (namedArgMap2 && namedArgMap2.size > 0) {
      // This Const has implicit parameters - try to extract them from expected type
      const constTypeResult = env.getTypeDefinitionAssert(constName);
      let currentType = constTypeResult.value;

      // Collect implicit Pi binders
      const implicitParams: Array<{ name: string; domain: TTKTerm }> = [];

      while (currentType.tag === 'Binder' && currentType.binderKind.tag === 'BPi') {
        const binderName = currentType.name;
        if (namedArgMap2.has(binderName)) {
          implicitParams.push({ name: binderName, domain: currentType.domain });
          currentType = currentType.body;
        } else {
          break;  // Hit first explicit parameter
        }
      }

      // Only attempt extraction if:
      // 1. We have implicit params
      // 2. We have at least one explicit arg (otherwise it's just a bare constructor reference)
      // 3. The expected type is NOT a Sort/Type (we're checking a term, not a type)
      // 4. The first N args are Holes (elaboration inserted them for implicits)
      const expectedIsSort = expectedType.tag === 'Sort' ||
        (expectedType.tag === 'ULevel') ||
        (expectedType.tag === 'Meta' && expectedType.id.startsWith('?l'));

      const numImplicits = implicitParams.length;

      // Check if we have enough args and if the first N are Holes
      const hasEnoughArgs = explicitArgs.length >= numImplicits;
      const firstArgsAreHoles = hasEnoughArgs &&
        explicitArgs.slice(0, numImplicits).every(arg => arg.tag === 'Hole');

      // ADDITIONAL SAFETY: Only run for constructors, not for arbitrary functions
      // This prevents interfering with normal function application
      const isConstructor = !!getConstructorNamedArgMap(env.definitions, constName);

      // WHITELIST: Only run for specific constructors known to need this feature
      // This prevents interfering with other constructors that work fine with normal implicit handling
      const isWhitelisted = constName === 'MkDPair' || constName === 'MkSigma';

      if (implicitParams.length > 0 && hasEnoughArgs && !expectedIsSort && firstArgsAreHoles && isConstructor && isWhitelisted) {
        try {

          // The first N args should be for the N implicit parameters
          // (elaboration inserts Holes for them)
          // The remaining args are the actual explicit arguments
          const actualExplicitArgs = explicitArgs.slice(numImplicits);

          // Get result type after applying all args (both implicit and explicit)
          // Start from currentType which is after the implicit Pis
          let resultType = currentType;
          for (let i = 0; i < actualExplicitArgs.length; i++) {
            if (resultType.tag === 'Binder' && resultType.binderKind.tag === 'BPi') {
              // Move past this Pi (we don't substitute because we're in pattern mode)
              resultType = resultType.body;
            } else {
              // No more Pis - can't extract
              throw new Error('Not enough Pis for explicit args');
            }
          }

          // Extract implicit arguments by directly matching the App spine structure.
          //
          // For record constructors, the result type is always of the form
          // `InductiveName Var(n-1) ... Var(0)` where each Var refers to a
          // binder position. We extract implicits by pairing result type spine
          // args (Vars) with expected type spine args (concrete terms).
          //
          // This AVOIDS using unifyTerms which would incorrectly apply substitutions
          // across de Bruijn namespace boundaries — result type Vars refer to MkDPair's
          // binders while expected type Vars refer to the typing context.
          const resultSpine = getAppChainHeadAndArgs(resultType);
          const expectedSpine = getAppChainHeadAndArgs(expectedType);

          if (!resultSpine || !expectedSpine) {
            throw new Error('Could not extract App spines');
          }

          // Verify same head constructor and same number of args
          if (resultSpine.head.tag !== 'Const' || expectedSpine.head.tag !== 'Const' ||
              (resultSpine.head as any).name !== (expectedSpine.head as any).name ||
              resultSpine.args.length !== expectedSpine.args.length) {
            throw new Error('Mismatched spine structure');
          }

          const implicitArgs: (TTKTerm | undefined)[] = new Array(implicitParams.length);
          const numExplicitPis = actualExplicitArgs.length;
          const numImplicitParams = implicitParams.length;

          // Map each Var in the result spine to its corresponding expected spine arg
          for (let i = 0; i < resultSpine.args.length; i++) {
            const resultArg = resultSpine.args[i];
            if (resultArg.tag === 'Var') {
              const implicitParamIndex = numExplicitPis + numImplicitParams - 1 - resultArg.index;
              if (implicitParamIndex >= 0 && implicitParamIndex < numImplicitParams) {
                implicitArgs[implicitParamIndex] = expectedSpine.args[i];
              }
            }
          }

          const allExtracted = implicitArgs.every(arg => arg !== undefined);

          if (!allExtracted) {
            throw new Error('Could not extract all implicit arguments');
          }

          // Double-check that extracted args are valid terms (have .tag property)
          if (!implicitArgs.every(arg => arg && typeof arg === 'object' && 'tag' in arg)) {
            throw new Error('Extracted implicit arguments are not valid terms');
          }

          // Build new term: apply Const to implicits, then to explicit args
          let newTerm: TTKTerm = appChain.head;

          // First apply implicits
          for (const arg of implicitArgs as TTKTerm[]) {
            if (!arg || !arg.tag) {
              throw new Error('Invalid implicit arg when building term');
            }
            newTerm = { tag: 'App', fn: newTerm, arg };
          }

          // Then apply explicit args (only the actual explicit ones, not the Holes for implicits)
          for (const arg of actualExplicitArgs) {
            if (!arg || !arg.tag) {
              throw new Error('Invalid explicit arg when building term');
            }
            newTerm = { tag: 'App', fn: newTerm, arg };
          }

          // DON'T recursively call checkType - that causes infinite loop!
          // Instead, update env.value and fall through to CONV rule
          // which will call inferType on the NEW term (with implicits applied)
          env = env.withValue(newTerm);
          // Fall through to CONV rule below
        } catch (e) {
          // Extraction failed - fall through to normal CONV rule
        }
      }

      // ──────────────────────────────────────────────────────────────
      // (APP-RETURN-TYPE-PROPAGATION) - For non-constructor functions
      // where the return type is simply one of the implicit parameters,
      // replace that parameter's Hole with the expected type.
      //
      // This enables expected type propagation through higher-order
      // functions like eitherElim, where the return type C is an implicit
      // parameter that appears in lambda arg domains (A → C), (B → C).
      // Without this, C remains an unsolved meta during lambda body
      // checking, preventing MkDPair (etc.) from extracting its implicits.
      //
      // How it works:
      //   1. Walk the full Pi chain to find the return type
      //   2. If return type is a bare Var referring to a leading implicit,
      //      replace that Hole in the term with the expected type
      //   3. Fall through to CONV with the modified term
      // ──────────────────────────────────────────────────────────────
      // Skip if any implicit is a ULevel — universe level interactions are complex
      const hasULevelImplicit = implicitParams.some(p => p.domain.tag === 'ULevel');

      if (!isConstructor && implicitParams.length > 0 && hasEnoughArgs
          && !expectedIsSort && firstArgsAreHoles && expectedType.tag !== 'Meta'
          && !hasULevelImplicit) {
        try {
          const fullType = env.getTypeDefinitionAssert(constName).value;

          // Count total Pi binders and find the return type
          let cursor = fullType;
          let totalPis = 0;
          while (cursor.tag === 'Binder' && cursor.binderKind.tag === 'BPi') {
            totalPis++;
            cursor = cursor.body;
          }
          const returnType = cursor;

          // Only fire when fully applied and return type is a simple Var
          if (explicitArgs.length === totalPis && returnType.tag === 'Var') {
            const n = implicitParams.length;
            const m = totalPis - n;
            const implicitIndex = n + m - 1 - returnType.index;

            if (implicitIndex >= 0 && implicitIndex < n) {
              // Only fire when the return-type implicit can't be solved
              // from a non-function explicit arg. If the implicit appears
              // in a data type domain (like Pair A B), the arg constrains
              // it. If it only appears in function codomains (like A → C),
              // those are callbacks whose bodies NEED C to be pre-solved.
              const returnVarBinder = totalPis - 1 - returnType.index;
              let solvableFromDataArg = false;
              {
                let checkCursor = fullType;
                for (let pos = 0; pos < totalPis; pos++) {
                  if (checkCursor.tag !== 'Binder') break;
                  if (pos >= n) {
                    // Explicit param: check if domain is NOT a function type
                    // and contains the return-type Var
                    const domain = checkCursor.domain;
                    const isFunction = domain.tag === 'Binder' && domain.binderKind.tag === 'BPi';
                    if (!isFunction) {
                      const refIndex = pos - 1 - returnVarBinder;
                      if (refIndex >= 0 && containsVarIndex(domain, refIndex)) {
                        solvableFromDataArg = true;
                        break;
                      }
                    }
                  }
                  checkCursor = checkCursor.body;
                }
              }

              if (!solvableFromDataArg) {
                // Replace the implicit's Hole with the expected type
                const newArgs = [...explicitArgs];
                newArgs[implicitIndex] = expectedType;

                let newTerm: TTKTerm = appChain.head;
                for (const arg of newArgs) {
                  newTerm = { tag: 'App', fn: newTerm, arg };
                }
                env = env.withValue(newTerm);
              }
            }
          }
        } catch {
          // Analysis failed — fall through to CONV
        }
      }
    }
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

    // IMPORTANT: If both types are Pis AND the expected type has a NAMED (non-anonymous)
    // binder, we should let unification match them instead of inserting metas.
    // This is crucial for higher-order functions like type class instances where
    // a polymorphic function is expected (e.g., passing mapMaybe to Functor.map).
    // However, if the expected type has an ANONYMOUS binder (like `A -> B -> C` where
    // the binder names are `_`), we should insert metas because those represent
    // explicit function arguments, not implicit type parameters.
    const expectedIsPi = expectedType.tag === 'Binder' && expectedType.binderKind.tag === 'BPi';
    if (expectedIsPi) {
      const expectedPi = expectedType as TTKTerm & { tag: 'Binder'; binderKind: { tag: 'BPi' } };
      const expectedBinderIsNamed = expectedPi.name !== '_' && expectedPi.name !== '';
      if (expectedBinderIsNamed) {
        // Both types have named Pi binders - let unification handle the matching
        break;
      }
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

  // NOTE: Pre-check for under-application (Pi vs non-Pi expected type)
  // is handled by the constraint solver's shape-incompatibility detection
  // in meta.ts, not here. The expected type may be a Var or App that reduces
  // to a Pi, so checking the syntactic tag is unreliable.

  // Now try to unify the inferred type with the expected type
  // First, substitute any solved level metas in both types
  const inferredTypeWithLevels = inferredEnv.substituteLevelMetasInTerm(inferredEnv.value);
  const expectedTypeWithLevels = inferredEnv.substituteLevelMetasInTerm(expectedType);

  try {
    let unifiedEnv = inferredEnv.unifyTerms(inferredTypeWithLevels, expectedTypeWithLevels);

    // TYPE-LEVEL UNIFICATION: When we unify an inferred type with an expected type that's a Meta,
    // we need to also propagate level constraints.
    // If expectedType is Meta(?A) with type Sort(?levelMeta), and inferredType has type Sort(concreteLevel),
    // we need to solve ?levelMeta := concreteLevel.
    //
    // This is critical for universe polymorphism: when Equal's implicit {A : Type u} is
    // inferred as some concrete type like `carrier_A : Type u`, we need to propagate that
    // carrier_A's level (u) to Equal's level parameter.
    if (expectedTypeWithLevels.tag === 'Meta') {
      const metaVar = unifiedEnv.metaVars.get(expectedTypeWithLevels.id);
      if (metaVar && metaVar.type.tag === 'Sort') {
        // Extract level meta from the meta's type level
        // The level could be:
        // - Meta(?levelMeta) directly
        // - App(USucc, Meta(?levelMeta)) for Type at level (Type ?levelMeta = Sort (USucc ?levelMeta))
        const metaTypeLevel = metaVar.type.level;
        let levelMetaId: string | undefined;

        if (metaTypeLevel.tag === 'Meta') {
          levelMetaId = metaTypeLevel.id;
        } else if (metaTypeLevel.tag === 'App' &&
                   metaTypeLevel.fn.tag === 'Const' && metaTypeLevel.fn.name === 'USucc' &&
                   metaTypeLevel.arg.tag === 'Meta') {
          // Level is (USucc ?levelMeta) - extract the meta from the arg
          levelMetaId = metaTypeLevel.arg.id;
        }

        if (levelMetaId) {
          // The meta has type Sort(?levelMeta) or Sort(USucc ?levelMeta) - we need to find the level of the inferred type
          // The inferred type should also be a type, so we infer its type to get the Sort
          try {
            const inferredTypeTypeEnv = inferType(unifiedEnv.withValue(inferredTypeWithLevels));
            if (inferredTypeTypeEnv.value.tag === 'Sort') {
              // Extract the base level from the inferred type
              // If inferred type's type is Sort(USucc u), the base level is u
              let inferredBaseLevel = inferredTypeTypeEnv.value.level;
              if (inferredBaseLevel.tag === 'App' &&
                  inferredBaseLevel.fn.tag === 'Const' && inferredBaseLevel.fn.name === 'USucc') {
                inferredBaseLevel = inferredBaseLevel.arg;
              }

              // Solve the level meta if it's not already solved to the same value
              const existingSolution = unifiedEnv.levelMetas.get(levelMetaId);
              if (existingSolution === undefined || !isDefinitionallyEqual(existingSolution, inferredBaseLevel)) {
                unifiedEnv = unifiedEnv.solveLevelMeta(levelMetaId, inferredBaseLevel);
              }
            }
          } catch (_) {
            // If we can't infer the type, just continue - level will remain unsolved
          }
        }
      }
    }

    // Return with the elaborated term (with implicit args inserted)
    // Set both value and elaboratedTerm to currentTerm since it has all elaboration applied
    // Use unifiedEnv for recordTypeInfo so zonking has access to solved metas
    // IMPORTANT: Record at env.indexPath (the original expression path), not unifiedEnv's
    // indexPath which may have drifted (e.g., inferType for App returns with arg's path).
    unifiedEnv.atIndexPath(env.indexPath).recordTypeInfo(inferredEnv.value, expectedType);
    return unifiedEnv.withValue(currentTerm).withElaboratedTerm(currentTerm);
  } catch (e) {
    // Even when unification fails, record type info so the user can see
    // both the inferred type and the expected type at the cursor.
    inferredEnv.atIndexPath(env.indexPath).recordTypeInfo(inferredEnv.value, expectedType);

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
