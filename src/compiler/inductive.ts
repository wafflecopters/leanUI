import { addDefinitionInTCEnv, addInductiveDefinitionInTCEnv, contextToNamesStack, createTCEnv, DefinitionsMap, extractPiSpine, InductiveDefinition, NamedArgMap, postOrderTraverseTerm, RecordInfo, setTypeInfoCollector, TCEnv, TCEnvError, validateInductiveNamingConventions } from "./term";
import { TTKTerm, levelsEqual, mkULit, levelLeq, collectLevelVars, levelVarContainedIn, prettyPrintLevel } from "./kernel";
import { inferType } from "./checker";
import { shiftTerm } from "./subst";
import type { TypeInfoMap } from "./type-info";

function checkTermOnlyContainsValidConstructors(env: TCEnv<TTKTerm>): TCEnvError[] {
  const errors: TCEnvError[] = [];

  postOrderTraverseTerm(env.value, (term, indexPath) => {
    if (term.tag === 'Const' || term.tag === 'Var' || term.tag === 'Sort' || term.tag === 'App') {
      // Valid
    } else if (term.tag === 'Binder' && term.binderKind.tag === 'BPi') {
      // Valid
    } else if (term.tag === 'Hole') {
      // Holes are allowed - they will be resolved during type checking.
      // If they remain unresolved, the "unsolved metas" check will catch them.
    } else if (term.tag === 'ULevel' || term.tag === 'ULit' || term.tag === 'UOmega') {
      // Universe-related terms are valid - they appear inside Sort levels for universe polymorphism
    } else {
      const msg = {
        Annot: 'Explicit annotation',
        Meta: 'Metavariable',
        Match: 'Pattern matching',
        Binder: undefined,
      }[term.tag] ?? (
          term.tag === 'Binder' ? term.binderKind.tag === 'BLam' ? 'Lambda Expression' : 'Let Expression' : undefined
        ) ?? 'Other syntax'
      errors.push(TCEnvError.create(`Term contains syntax not allowed in an inductive type definition: ${msg}`, env.atIndexPath(indexPath)));
    }
  }, env.indexPath);

  return errors
}

function runAndAccumulateErrors<S, T>(
  env: TCEnv<S>,
  fn: (e: TCEnv<S>) => TCEnv<T>,
  errors: TCEnvError[]
): TCEnv<T> | undefined {
  try {
    return fn(env);
  } catch (e) {
    if (e instanceof TCEnvError) {
      errors.push(e);
    } else {
      errors.push(TCEnvError.create(e instanceof Error ? e.message : String(e), env));
    }
  }
}

export function checkInductiveDeclaration(
  name: string,
  type: TTKTerm,
  constructors: Array<{ name: string; type: TTKTerm; namedArgMap?: NamedArgMap }>,
  definitions: DefinitionsMap,
  namedArgMap?: NamedArgMap,
  recordInfo?: RecordInfo,
  typeInfoCollector?: TypeInfoMap,
): {
  success: false,
  errors: TCEnvError[]
} | {
  success: true,
  newDefinitions: DefinitionsMap,
  indexPositions: number[],
  zonkedConstructors: Array<{ name: string; type: TTKTerm; namedArgMap?: NamedArgMap }>
} {
  if (typeInfoCollector) {
    setTypeInfoCollector(typeInfoCollector);
  }

  // We'll compute indexPositions after validation, so use empty array initially
  const inductiveDefinition: InductiveDefinition = { name, type, constructors, indexPositions: [] };
  const defEnv = createTCEnv({ definitions, options: { mode: 'check' } }).withValue(inductiveDefinition);

  // Validate naming conventions first
  const errors: TCEnvError[] = [];
  try {
    validateInductiveNamingConventions(defEnv);
  } catch (e) {
    if (e instanceof TCEnvError) {
      errors.push(e);
    } else {
      throw e;
    }
  }

  errors.push(
    ...checkTermOnlyContainsValidConstructors(defEnv.inInductiveDefinitionType()),
    ...constructors.flatMap((_, index) =>
      checkTermOnlyContainsValidConstructors(
        defEnv
          .inInductiveDefinitionConstructors()
          .inInductiveDefinitionConstructor(index)
          .inInductiveDefinitionConstructorType(),
      )
    )
  )

  if (errors.length > 0) {
    return { success: false, errors };
  }

  const sigResult = runAndAccumulateErrors(defEnv.inInductiveDefinitionType(), inferType, errors);
  if (sigResult?.metaVars.size ?? 0 > 0) {
    return {
      success: false, errors: [
        TCEnvError.create('Checking the inductive type signature produced unsolved metas.', defEnv)
      ]
    }
  }

  if (errors.length > 0) {
    return { success: false, errors };
  }

  let ctorsEnv = addDefinitionInTCEnv(defEnv, name, type, namedArgMap).inInductiveDefinitionConstructors();

  // Collect zonked constructor types to use in the final inductive definition
  const zonkedConstructors: Array<{ name: string; type: TTKTerm; namedArgMap?: NamedArgMap }> = [];

  constructors.forEach((ctor, index) => {
    runAndAccumulateErrors(
      ctorsEnv.inInductiveDefinitionConstructor(index).inInductiveDefinitionConstructorType(),
      e => {
        const result = inferType(e)
        // Solve meta constraints before checking for unsolved metas
        let solvedResult = result.solveMetasAndConstraints({ liftMetasToFullContext: false });

        // Default unsolved level metas to 0
        // This handles cases like {u : ULevel} where u is not constrained by the constructor
        const unsolvedLevelMetas = Array.from(solvedResult.levelMetas.entries()).filter(([_, v]) => v === undefined);
        for (const [id, _] of unsolvedLevelMetas) {
          solvedResult = solvedResult.solveLevelMeta(id, mkULit(0));
        }

        // Check for UNSOLVED term metas (solved metas have a 'solution' property)
        const unsolvedMetas = Array.from(solvedResult.metaVars.entries()).filter(([_, m]) => !m.solution);
        if (unsolvedMetas.length > 0) {
          const metaInfo = unsolvedMetas.map(([id, m]) => `${id}: ${solvedResult.prettyPrint(m.type)}`);
          errors.push(TCEnvError.create(`Checking the constructor signature produced unsolved metas: [${metaInfo.join(', ')}]`, e));
        } else {
          // Zonk the constructor type to substitute solved metas (both level and term).
          // ctor.type has Holes for implicit args, and zonkTerm substitutes these using
          // the Hole ID to look up solutions in both levelMetas and metaVars.
          const zonkedType = solvedResult.zonkTerm(ctor.type);
          zonkedConstructors.push({ name: ctor.name, type: zonkedType, namedArgMap: ctor.namedArgMap });
          ctorsEnv = addDefinitionInTCEnv(ctorsEnv, ctor.name, zonkedType, ctor.namedArgMap);
        }
        return solvedResult
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

  // Check strict positivity
  constructors.forEach((_, i) => checkStrictPositivity(name, ctorsEnv.inInductiveDefinitionConstructor(i), errors));

  // Check universe level constraints: constructor argument types must fit in result universe
  checkConstructorUniverseLevels(name, type, zonkedConstructors, ctorsEnv, errors);

  if (errors.length > 0) {
    return { success: false, errors };
  }

  // Compute index positions on the validated TTK terms (after positivity check)
  // Use zonked constructors so that metas are substituted with their solutions
  const indexPositions = inferParameterIndicesK({ name, type, constructors: zonkedConstructors });

  const newEnv = addInductiveDefinitionInTCEnv(ctorsEnv, name, type, zonkedConstructors, indexPositions, namedArgMap, recordInfo);

  return {
    success: true,
    newDefinitions: newEnv.definitions,
    indexPositions,
    zonkedConstructors
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
  errors: TCEnvError[]
): TCEnvError[] {
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
  errors: TCEnvError[]
): void {
  if (env.isConstTerm() || env.isVarTerm() || env.isSortTerm() || env.isHoleTerm() ||
      env.value.tag === 'ULevel' || env.value.tag === 'ULit' || env.value.tag === 'UOmega') {
    // Direct occurrences of constants/vars/sorts/level-terms are fine
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
  errors: TCEnvError[]
): void {
  if (env.isVarTerm() || env.isSortTerm() || env.isHoleTerm() ||
      env.value.tag === 'ULevel' || env.value.tag === 'ULit' || env.value.tag === 'UOmega') {
    // Valid - vars, sorts, holes, and level-terms don't contain occurrences of the inductive type
    // Holes may appear when type inference creates unresolved metas - they're safe to skip
  } else if (env.isConstTerm()) {
    if (env.value.name === inductiveName) {
      const msg = polarity === 'negative' ? 'negative' : '(non-strict) positive';
      errors.push(TCEnvError.create(`Constructor '${ctorName}' has a ${msg} occurrence of '${inductiveName}'.`, env));
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

/**
 * Check if a term is a "type-level" parameter (Sort or function returning Sort).
 * Type parameters like `A : Type` or `P : A -> Type` don't store data, they
 * parameterize types, so they should be skipped in universe level checks.
 */
function isTypeLevelDomain(domain: TTKTerm): boolean {
  if (domain.tag === 'Sort') return true;
  // ULevel is the type of universe level variables - these are parameters, not data
  if (domain.tag === 'ULevel') return true;
  // Pi types that return Sorts are type families (like A -> Type)
  if (domain.tag === 'Binder' && domain.binderKind.tag === 'BPi') {
    return isTypeLevelDomain(domain.body);
  }
  return false;
}

/**
 * Check that constructor argument types fit within the inductive's result universe.
 *
 * The approach: strip type parameters (binders with type-level domains), then infer
 * the type of what remains. That level must be ≤ the inductive's result level.
 *
 * Type parameters include:
 * - Sorts like `A : Type` or `A : Type 1`
 * - Type families like `P : A -> Type`
 *
 * Example violation:
 *   inductive BadList : Type 1 -> Type where
 *     BCons : {A : Type 1} -> A -> BadList A -> BadList A
 *
 * After stripping {A : Type 1}, we have `A -> BadList A -> BadList A`.
 * Its type is Sort max(2, 1, 1) = Sort 2. But BadList's result is Type = Sort 1.
 * Since 2 > 1, this is invalid.
 *
 * For BNil : {A : Type 1} -> BadList A, after stripping we have just `BadList A`
 * with type Sort 1. Since 1 <= 1, this is valid.
 */
function checkConstructorUniverseLevels(
  inductiveName: string,
  inductiveType: TTKTerm,
  constructors: Array<{ name: string; type: TTKTerm }>,
  env: TCEnv<unknown>,
  errors: TCEnvError[]
): void {
  // Extract the result type of the inductive (skip all Pi binders)
  const { body: resultType } = extractPiSpine(inductiveType);

  // The result should be a Sort - extract its level
  if (resultType.tag !== 'Sort') {
    return;
  }
  const resultLevel = resultType.level;

  // Check each constructor
  for (const ctor of constructors) {
    // First, extract the constructor's return type and count binders
    const ctorSpine = extractPiSpine(ctor.type);
    const ctorReturnType = ctorSpine.body;
    const binderCount = ctorSpine.binders.length;

    // Iterate through each argument in the constructor type
    // For each STORED DATA argument (not a type/level parameter or index), check its universe level
    let current = ctor.type;
    let currentEnv = env;
    let binderIndex = 0; // Track position from outer to inner
    let dataBindersProcessed = 0; // Track how many data (non-type-level) binders we've passed

    while (current.tag === 'Binder' && current.binderKind.tag === 'BPi') {
      const domain = current.domain;

      // Skip type-level domains (these are parameters, not data)
      if (!isTypeLevelDomain(domain)) {
        // Calculate the de Bruijn index for this binder in the return type
        // The return type is under (binderCount) binders, and this is binder #binderIndex
        // So its de Bruijn index in the return type is (binderCount - 1 - binderIndex)
        const deBruijnInReturn = binderCount - 1 - binderIndex;

        // Check if this argument is used in the return type (making it an INDEX, not stored data)
        // If it's an index, we don't need to check its universe level
        const isIndex = usesVariable(ctorReturnType, deBruijnInReturn);

        if (!isIndex) {
          // This is STORED DATA - check its type's universe level
          // The domain is some type T. We need to find the sort of T.
          try {
            const domainEnv = currentEnv.withValue(domain);
            const typeResult = inferType(domainEnv);
            const domainType = typeResult.value;

            // If the domain type is a Sort, its level tells us the universe of the data
            if (domainType.tag === 'Sort') {
              const dataLevel = domainType.level;

              // The resultLevel has de Bruijn indices relative to the INDUCTIVE type's context.
              // We need to shift it by the number of DATA binders we've already processed,
              // since those are the extra binders beyond what the inductive type has.
              const shiftedResultLevel = shiftTerm(resultLevel, dataBindersProcessed, 0);

              // Use symbolic level comparison: dataLevel ≤ shiftedResultLevel
              const leqResult = levelLeq(dataLevel, shiftedResultLevel);

              if (leqResult === false) {
                // Definite violation
                const levelContext = contextToNamesStack(currentEnv.context);
                errors.push(TCEnvError.create(
                  `Universe level violation in constructor '${ctor.name}': ` +
                  `argument type has sort ${prettyPrintLevel(dataLevel, levelContext)} but '${inductiveName}' ` +
                  `result type is Sort ${prettyPrintLevel(shiftedResultLevel, levelContext)}`,
                  domainEnv
                ));
              } else if (leqResult === 'unknown') {
                // Check if the result level properly "contains" all data level variables
                const dataVars = collectLevelVars(dataLevel);

                for (const varIndex of dataVars) {
                  if (!levelVarContainedIn(varIndex, shiftedResultLevel)) {
                    const levelContext = contextToNamesStack(currentEnv.context);
                    errors.push(TCEnvError.create(
                      `Universe level violation in constructor '${ctor.name}': ` +
                      `argument uses level variable not covered by result level ` +
                      `(argument at Sort ${prettyPrintLevel(dataLevel, levelContext)}, result at Sort ${prettyPrintLevel(shiftedResultLevel, levelContext)})`,
                      domainEnv
                    ));
                    break;
                  }
                }
              }
              // If leqResult === true, the constraint is satisfied
            }
          } catch {
            // If type inference fails, skip this check (other errors will be reported)
          }
        }

        // Track that we've processed a data binder (affects de Bruijn index shifting)
        dataBindersProcessed++;
      }

      // Extend context and continue to next binder
      currentEnv = currentEnv.extendTTKContext(current.name, domain);
      current = current.body;
      binderIndex++;
    }
  }
}

/**
 * Check if a term uses a variable at the given de Bruijn index.
 */
function usesVariable(term: TTKTerm, index: number): boolean {
  switch (term.tag) {
    case 'Var':
      return term.index === index;
    case 'Binder':
      // In binder body, the index is shifted by 1
      return usesVariable(term.domain, index) || usesVariable(term.body, index + 1);
    case 'App':
      return usesVariable(term.fn, index) || usesVariable(term.arg, index);
    case 'Annot':
      return usesVariable(term.term, index) || usesVariable(term.type, index);
    case 'Match':
      if (usesVariable(term.scrutinee, index)) return true;
      // Patterns bind variables, which makes precise tracking complex.
      // For now, conservatively return true if there are any clauses.
      if (term.clauses.length > 0) return true;
      return false;
    case 'Sort':
    case 'Const':
    case 'ULevel':
    case 'ULit':
    case 'UOmega':
    case 'Hole':
    case 'Meta':
      return false;
    default:
      return false;
  }
}

// ============================================================================
// Parameter/Index Inference for TTK (Kernel Terms)
// ============================================================================

/**
 * Inductive type definition using kernel terms (TTK).
 */
interface InductiveTypeDefK {
  name: string;
  type: TTKTerm;
  constructors: Array<{ name: string; type: TTKTerm }>;
}

/**
 * Infer which positions in an inductive type definition are indices vs parameters.
 * This operates on kernel terms (TTK) after validation.
 *
 * @param def - The inductive type definition with TTK terms
 * @returns Array of position indices that are type indices (all other positions are parameters)
 */
function inferParameterIndicesK(def: InductiveTypeDefK): number[] {
  const numPositions = countPiArgsK(def.type);

  if (numPositions === 0) {
    return [];
  }

  // Phase 1: Syntactic parameter detection
  const syntacticParams = detectSyntacticParametersK(def, numPositions);

  // Phase 2: Index promotion (equivalence classes)
  const afterPromotion = promoteIndicesK(def, numPositions, syntacticParams);

  // Phase 2.5: Dependency validation (enforce prefix property)
  const finalIndices = enforceParameterPrefixK(afterPromotion, numPositions);

  return finalIndices;
}

/**
 * Count the number of Pi binders in a TTK type.
 */
function countPiArgsK(type: TTKTerm): number {
  let count = 0;
  let current = type;

  while (current.tag === 'Binder' && current.binderKind.tag === 'BPi') {
    count++;
    current = current.body;
  }

  return count;
}

/**
 * Detect positions that are syntactic parameters.
 */
function detectSyntacticParametersK(
  def: InductiveTypeDefK,
  numPositions: number
): Set<number> {
  const params = new Set<number>();

  for (let pos = 0; pos < numPositions; pos++) {
    if (isSyntacticParameterK(def, pos, numPositions)) {
      params.add(pos);
    }
  }

  return params;
}

/**
 * Check if a specific position is a syntactic parameter.
 */
function isSyntacticParameterK(
  def: InductiveTypeDefK,
  position: number,
  numPositions: number
): boolean {
  for (const ctor of def.constructors) {
    const ctorArgs = extractInductiveArgsK(ctor.type, def.name, numPositions);

    if (!ctorArgs) {
      return false;
    }

    const termAtPos = ctorArgs[position];

    if (termAtPos.tag !== 'Var') {
      return false;
    }

    // Check that this variable appears exactly once in all positions
    let appearances = 0;
    for (const arg of ctorArgs) {
      if (arg.tag === 'Var' && arg.index === termAtPos.index) {
        appearances++;
      }
    }

    if (appearances !== 1) {
      return false;
    }
  }

  return true;
}

/**
 * Extract the arguments to the inductive type from a constructor's type.
 */
function extractInductiveArgsK(
  ctorType: TTKTerm,
  inductiveName: string,
  expectedArgs: number
): TTKTerm[] | null {
  // Navigate to the return type (skip all Pi binders)
  let returnType = ctorType;
  while (returnType.tag === 'Binder' && returnType.binderKind.tag === 'BPi') {
    returnType = returnType.body;
  }

  // Extract arguments by peeling off applications
  const args: TTKTerm[] = [];
  let current = returnType;

  while (current.tag === 'App') {
    args.unshift(current.arg);
    current = current.fn;
  }

  if (current.tag !== 'Const' || current.name !== inductiveName) {
    return null;
  }

  if (args.length !== expectedArgs) {
    return null;
  }

  return args;
}

/**
 * Promote indices to parameters when they're always equal across constructors.
 */
function promoteIndicesK(
  def: InductiveTypeDefK,
  numPositions: number,
  syntacticParams: Set<number>
): Set<number> {
  const indices = new Set<number>();
  for (let i = 0; i < numPositions; i++) {
    if (!syntacticParams.has(i)) {
      indices.add(i);
    }
  }

  if (indices.size <= 1) {
    return indices;
  }

  const equivalenceClasses = buildEquivalenceClassesK(def, numPositions, indices);

  const newIndices = new Set<number>();

  for (const eqClass of Array.from(equivalenceClasses)) {
    if (eqClass.size <= 1) {
      for (const pos of eqClass) {
        newIndices.add(pos);
      }
    } else {
      const sorted = Array.from(eqClass).sort((a: number, b: number) => a - b);
      const toPromote = sorted[0];

      if (canPromotePositionK(def, toPromote, numPositions)) {
        // Don't add to newIndices - it's promoted to parameter
      } else {
        newIndices.add(toPromote);
      }

      for (let i = 1; i < sorted.length; i++) {
        newIndices.add(sorted[i]);
      }
    }
  }

  return newIndices;
}

/**
 * Build equivalence classes of positions that are always equal across all constructors.
 */
function buildEquivalenceClassesK(
  def: InductiveTypeDefK,
  numPositions: number,
  indices: Set<number>
): Set<Set<number>> {
  const indexArray = Array.from(indices);

  const equivalent = (i: number, j: number): boolean => {
    for (const ctor of def.constructors) {
      const args = extractInductiveArgsK(ctor.type, def.name, numPositions);
      if (!args) return false;

      if (!termsEqualK(args[i], args[j])) {
        return false;
      }
    }
    return true;
  };

  // Union-find
  const parent = new Map<number, number>();
  const find = (x: number): number => {
    if (!parent.has(x)) {
      parent.set(x, x);
      return x;
    }
    const p = parent.get(x)!;
    if (p === x) return x;
    const root = find(p);
    parent.set(x, root);
    return root;
  };

  const union = (x: number, y: number) => {
    const rootX = find(x);
    const rootY = find(y);
    if (rootX !== rootY) {
      parent.set(rootX, rootY);
    }
  };

  for (let i = 0; i < indexArray.length; i++) {
    for (let j = i + 1; j < indexArray.length; j++) {
      if (equivalent(indexArray[i], indexArray[j])) {
        union(indexArray[i], indexArray[j]);
      }
    }
  }

  const classes = new Map<number, Set<number>>();
  for (const idx of indexArray) {
    const root = find(idx);
    if (!classes.has(root)) {
      classes.set(root, new Set());
    }
    classes.get(root)!.add(idx);
  }

  return new Set(classes.values());
}

/**
 * Check if a position can be promoted (must be a variable in all constructors).
 */
function canPromotePositionK(
  def: InductiveTypeDefK,
  position: number,
  numPositions: number
): boolean {
  for (const ctor of def.constructors) {
    const args = extractInductiveArgsK(ctor.type, def.name, numPositions);
    if (!args) return false;

    const term = args[position];
    if (term.tag !== 'Var') {
      return false;
    }
  }
  return true;
}

/**
 * Check if two TTK terms are structurally equal.
 */
function termsEqualK(t1: TTKTerm, t2: TTKTerm): boolean {
  if (t1.tag !== t2.tag) return false;

  switch (t1.tag) {
    case 'Var':
      return t2.tag === 'Var' && t1.index === t2.index;

    case 'Sort':
      return t2.tag === 'Sort' && levelsEqual(t1.level, t2.level);

    case 'ULevel':
      return t2.tag === 'ULevel';

    case 'ULit':
      return t2.tag === 'ULit' && t1.n === t2.n;

    case 'UOmega':
      return t2.tag === 'UOmega';

    case 'Const':
      return t2.tag === 'Const' && t1.name === t2.name;

    case 'App':
      return (
        t2.tag === 'App' &&
        termsEqualK(t1.fn, t2.fn) &&
        termsEqualK(t1.arg, t2.arg)
      );

    case 'Binder':
      return (
        t2.tag === 'Binder' &&
        t1.binderKind.tag === t2.binderKind.tag &&
        termsEqualK(t1.domain, t2.domain) &&
        termsEqualK(t1.body, t2.body)
      );

    case 'Hole':
      return t2.tag === 'Hole' && t1.id === t2.id;

    case 'Meta':
      return t2.tag === 'Meta' && t1.id === t2.id;

    case 'Annot':
      return (
        t2.tag === 'Annot' &&
        termsEqualK(t1.term, t2.term) &&
        termsEqualK(t1.type, t2.type)
      );

    case 'Match':
      return false;

    default:
      const _exhaustive: never = t1;
      return false;
  }
}

/**
 * Enforce that parameters form a prefix.
 */
function enforceParameterPrefixK(indices: Set<number>, numPositions: number): number[] {
  if (indices.size === 0) {
    return [];
  }

  const firstIndex = Math.min(...Array.from(indices));

  const result: number[] = [];
  for (let i = firstIndex; i < numPositions; i++) {
    result.push(i);
  }

  return result.sort((a, b) => a - b);
}