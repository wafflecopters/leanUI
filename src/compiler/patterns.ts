/**
 * Pattern Matching and LHS Unification
 *
 * This module handles:
 * - Validation of pattern arity (constructors are fully applied)
 * - Validation of pattern variable naming (no duplicates, no conflicts)
 * - LHS unification for match clauses
 */

import { TTKTerm, TTKClause, TTKPattern, prettyPrint as prettyPrintTTK, prettyPrintPattern, mkVar, mkConst, mkType, mkAppSpine } from './kernel';
import { arraySeg, fieldSeg, IndexPath } from '../types/source-position';
import { countPiBinders, DefinitionsMap, extractAppSpine, printCollectionFancy, TTKContext, TCEnv, TCEnvError, assertDefined, assertIsNotPi, assertIsPi, transformVarsInTerm, transformVarsInTermWithBinders, validatePatternVarName, addMetaVarInTCEnv, NamedArgMap } from './term';
import { unifyTerms } from './unify';
import { shiftTerm, subst, enumerateAppliedSubstitutions } from './subst';
import { areWhnfTypesDefEq } from './whnf';
import { checkType } from './checker';

// ============================================================================
// Logging
// ============================================================================

let loggingEnabled = false;

export function setPatternLoggingEnabled(enabled: boolean): void {
  loggingEnabled = enabled;
}

function logInfo(fn: () => (string | unknown[])) {
  if (loggingEnabled) {
    const r = fn();
    if (Array.isArray(r)) {
      console.log(...r);
    } else {
      console.log(r);
    }
  }
}

// ============================================================================
// Pattern Arity Validation
// ============================================================================

/**
 * Constructor arity info: total arguments vs positional (non-named) arguments.
 */
interface ConstructorArityInfo {
  totalArity: number;
  positionalArity: number;  // totalArity - namedArgs
  namedArgMap?: NamedArgMap;
}

/**
 * Look up a constructor by name and return its arity info.
 * Returns both total arity and positional arity (excluding named parameters).
 */
function getConstructorArityInfo(definitions: DefinitionsMap, ctorName: string): ConstructorArityInfo | undefined {
  for (const inductive of definitions.inductiveTypes.values()) {
    for (const ctor of inductive.constructors) {
      if (ctor.name === ctorName) {
        const totalArity = countPiBinders(ctor.type);
        const namedCount = ctor.namedArgMap?.size ?? 0;
        return {
          totalArity,
          positionalArity: totalArity - namedCount,
          namedArgMap: ctor.namedArgMap
        };
      }
    }
  }
  return undefined;
}

/**
 * Pad a PCtor pattern with implicit wildcards for named parameters.
 * Named parameters are at specific positions (from namedArgMap), and positional args fill the remaining slots.
 *
 * Example: Constructor VNil : {A: Type} -> List A
 * - namedArgMap: {A: 0}
 * - totalArity: 1, positionalArity: 0
 * - User writes: VNil (no args)
 * - Padded: VNil _ (wildcard at position 0 for named param A)
 *
 * Example: Constructor VCons : {A: Type} -> A -> List A -> List A
 * - namedArgMap: {A: 0}
 * - totalArity: 3, positionalArity: 2
 * - User writes: VCons x xs
 * - Padded: VCons _ x xs (wildcard at position 0 for named param A)
 */
function padPCtorPatternWithNamedWildcards(pattern: TTKPattern, definitions: DefinitionsMap): TTKPattern {
  if (pattern.tag !== 'PCtor') {
    return pattern;
  }

  const arityInfo = getConstructorArityInfo(definitions, pattern.name);
  if (!arityInfo || !arityInfo.namedArgMap || arityInfo.namedArgMap.size === 0) {
    // No named parameters - recursively pad sub-patterns only
    return {
      ...pattern,
      args: pattern.args.map(arg => padPCtorPatternWithNamedWildcards(arg, definitions)),
      namedArgs: undefined // Clear namedArgs after processing
    };
  }

  // Build the padded args array:
  // - Named patterns from {A := pattern} syntax go at their positions
  // - Positional patterns fill the remaining (non-named) positions
  // - Unfilled named positions get wildcards
  const paddedArgs: TTKPattern[] = new Array(arityInfo.totalArity);
  const namedPositions = new Set(arityInfo.namedArgMap.values());

  // First, place named args at their positions
  if (pattern.namedArgs) {
    for (const na of pattern.namedArgs) {
      const idx = arityInfo.namedArgMap.get(na.name);
      if (idx !== undefined) {
        paddedArgs[idx] = padPCtorPatternWithNamedWildcards(na.pattern, definitions);
      }
    }
  }

  // Fill remaining named positions with wildcards
  for (const pos of namedPositions) {
    if (paddedArgs[pos] === undefined) {
      paddedArgs[pos] = { tag: 'PWild', name: '_' };
    }
  }

  // Then, fill positional patterns into remaining (non-named) slots
  let positionalIndex = 0;
  for (let i = 0; i < arityInfo.totalArity; i++) {
    if (!namedPositions.has(i)) {
      if (positionalIndex < pattern.args.length) {
        paddedArgs[i] = padPCtorPatternWithNamedWildcards(pattern.args[positionalIndex], definitions);
      } else {
        // Missing positional pattern - this will be caught by arity check
        paddedArgs[i] = { tag: 'PWild', name: '_' };
      }
      positionalIndex++;
    }
  }

  return {
    tag: 'PCtor',
    name: pattern.name,
    args: paddedArgs
    // namedArgs is not included - it's been processed into args
  };
}

/**
 * Pad all patterns in a clause with implicit wildcards for named constructor parameters.
 */
function padPatternsWithNamedWildcards(patterns: TTKPattern[], definitions: DefinitionsMap): TTKPattern[] {
  return patterns.map(p => padPCtorPatternWithNamedWildcards(p, definitions));
}

/**
 * Assert that all PCtor patterns in the LHS are fully applied (have the correct number of arguments).
 * This is checked before unification to give better error messages.
 */
function assertMatchClauseLhsPatternsFullyApplied(env: TCEnv<TTKPattern[]>): void {
  const patterns = env.value;
  const errors: TCEnvError[] = [];

  function checkPattern(pattern: TTKPattern, path: IndexPath): void {
    switch (pattern.tag) {
      case 'PVar':
      case 'PWild':
        // These don't have sub-patterns to check
        break;

      case 'PCtor': {
        const arityInfo = getConstructorArityInfo(env.definitions, pattern.name);
        if (arityInfo !== undefined) {
          // Constructor patterns can only use positional arguments for non-named parameters.
          // Named parameters must be provided via {Name := pattern} syntax or omitted (inferred).
          const expectedPositional = arityInfo.positionalArity;

          // Check positional args count
          if (pattern.args.length !== expectedPositional) {
            // Build a helpful error message
            let message: string;
            if (arityInfo.namedArgMap && arityInfo.namedArgMap.size > 0) {
              const namedNames = Array.from(arityInfo.namedArgMap.keys()).join(', ');
              if (pattern.args.length > expectedPositional) {
                // User provided too many args - they're probably trying to match named params positionally
                message = `Constructor '${pattern.name}' has ${arityInfo.namedArgMap.size} named parameter${arityInfo.namedArgMap.size === 1 ? '' : 's'} (${namedNames}) that cannot be matched positionally. ` +
                  `Expected ${expectedPositional} positional argument${expectedPositional === 1 ? '' : 's'}, but got ${pattern.args.length}. ` +
                  `Named parameters can be omitted (inferred from context) or matched with explicit syntax like {${Array.from(arityInfo.namedArgMap.keys())[0]} := _}`;
              } else {
                message = `Constructor '${pattern.name}' expects ${expectedPositional} positional argument${expectedPositional === 1 ? '' : 's'}, but got ${pattern.args.length}`;
              }
            } else {
              message = `Constructor '${pattern.name}' expects ${expectedPositional} argument${expectedPositional === 1 ? '' : 's'}, but got ${pattern.args.length}`;
            }
            errors.push(TCEnvError.create(message, env.atIndexPath([...env.indexPath, ...path])));
          }

          // Validate named args if present
          if (pattern.namedArgs) {
            for (const na of pattern.namedArgs) {
              const idx = arityInfo.namedArgMap?.get(na.name);
              if (idx === undefined) {
                errors.push(TCEnvError.create(
                  `Unknown named pattern argument '${na.name}' for constructor '${pattern.name}'`,
                  env.atIndexPath([...env.indexPath, ...path])
                ));
              }
            }
          }
        }

        // Recursively check sub-patterns
        for (let i = 0; i < pattern.args.length; i++) {
          checkPattern(pattern.args[i], [...path, fieldSeg('args'), arraySeg(i)]);
        }
        break;
      }
    }
  }

  // Check all top-level patterns
  for (let i = 0; i < patterns.length; i++) {
    checkPattern(patterns[i], [arraySeg(i)]);
  }

  if (errors.length > 0) {
    throw TCEnvError.group(errors);
  }
}

// ============================================================================
// Pattern Variable Validation
// ============================================================================

/**
 * Validate pattern variables after LHS elaboration.
 *
 * Traverses the original patterns and elaborated terms in parallel to build a mapping
 * from de Bruijn indices to pattern variable names. Throws an error if:
 * - The same de Bruijn index is bound by multiple different names (e.g., A and A2 both map to #0)
 * - The same name is used multiple times (even if they refer to the same index)
 */
function assertPatternVarsValid(
  env: TCEnv<TTKPattern[]>,
  elabStack: TTKTerm[],
  signature: TTKContext
) {
  const patterns = env.value;

  // Create context for pretty printing (NOT reversed - pattern indices look up left-to-right in signature)
  const printContext = signature.map(s => s.name);

  // Map from de Bruijn index to list of (name, indexPath) entries
  const varToNames = new Map<number, { name: string; path: IndexPath }[]>();
  const nameToTerms = new Map<string, { term: TTKTerm; path: IndexPath }[]>();

  const errors: TCEnvError[] = []

  function traverse(pattern: TTKPattern, elabTerm: TTKTerm, path: IndexPath): void {
    switch (pattern.tag) {
      case 'PVar': {
        // For PVar, the elabTerm should be a Var after elaboration
        if (elabTerm.tag === 'Var') {
          const varIndex = elabTerm.index;
          const existing = varToNames.get(varIndex);
          if (existing) {
            existing.push({ name: pattern.name, path });
          } else {
            varToNames.set(varIndex, [{ name: pattern.name, path }]);
          }
        }

        const existingNameIndices = nameToTerms.get(pattern.name);
        if (existingNameIndices) {
          existingNameIndices.push({ term: elabTerm, path });
        } else {
          nameToTerms.set(pattern.name, [{ term: elabTerm, path }]);
        }
        break;
      }

      case 'PWild':
        // Wildcards don't have user-defined names, nothing to validate
        break;

      case 'PCtor': {
        // Extract the App spine from elabTerm
        const spine = extractAppSpine(elabTerm);

        if (spine.args.length !== pattern.args.length) {
          // This shouldn't happen if elaboration is correct
          throw new Error(
            `Internal error: PCtor arg count mismatch in pattern validation: ` +
            `pattern '${pattern.name}' has ${pattern.args.length} args, ` +
            `but elaborated term has ${spine.args.length} args`
          );
        }

        for (let i = 0; i < pattern.args.length; i++) {
          traverse(
            pattern.args[i],
            spine.args[i],
            [...path, fieldSeg('args'), arraySeg(i)]
          );
        }
        break;
      }
    }
  }

  // Traverse all top-level patterns paired with their elaborated terms
  for (let i = 0; i < patterns.length; i++) {
    traverse(patterns[i], elabStack[i], [arraySeg(i)]);
  }

  logInfo(() => ['varToNames: ', Object.fromEntries(Array.from(varToNames.entries()).map(([varIndex, names]) => {
    return [varIndex, names.map(n => n.name)]
  }))])
  logInfo(() => ['nameToTerms: ', Object.fromEntries(Array.from(nameToTerms.entries()).map(([name, terms]) => {
    return [name, terms.map(t => prettyPrintTTK(t.term))]
  }))])

  // Check 1: Same name used for different terms
  // e.g. A = [Var#0, Var#1] is an error, as is A = [Var#0, Succ Var#0]
  for (const [name, termEntries] of nameToTerms) {
    if (termEntries.length > 1) {
      const firstTerm = termEntries[0].term;
      for (let i = 1; i < termEntries.length; i++) {
        if (!areWhnfTypesDefEq(firstTerm, termEntries[i].term)) {
          // Format each term with its type annotation if it's a variable
          const formatTermWithType = (term: TTKTerm): string => {
            const termStr = prettyPrintTTK(term, printContext);
            if (term.tag === 'Var' && term.index < signature.length) {
              const typeStr = prettyPrintTTK(signature[term.index].type, printContext);
              return `${termStr} : ${typeStr}`;
            }
            return termStr;
          };
          const first = formatTermWithType(firstTerm);
          const second = formatTermWithType(termEntries[i].term);
          errors.push(TCEnvError.create(
            `Pattern '${name}' binds to incompatible values: ${first} vs ${second}`,
            env.atIndexPath([...env.indexPath, ...termEntries[i].path])
          ));
          break; // Only report first mismatch for this name
        }
      }
    }
  }

  // Check 2: Different names for the same de Bruijn index
  // e.g., #0 -> [A, B] is an error, but #0 -> [A, A] is allowed
  for (const [_varIndex, entries] of varToNames) {
    if (entries.length > 1) {
      const uniqueNames = [...new Set(entries.map(e => e.name))];
      if (uniqueNames.length > 1) {
        // Different names refer to same variable - conflict error
        const nameList = uniqueNames.map(n => `'${n}'`).join(' and ');
        const errorPath = entries[1].path; // Point to second occurrence
        errors.push(TCEnvError.create(
          `Pattern variables ${nameList} refer to the same binding; use a single consistent name`,
          env.atIndexPath([...env.indexPath, ...errorPath])
        ));
      }
      // If uniqueNames.length === 1, that's fine - same name used consistently
    }
  }

  if (errors.length > 0) {
    throw TCEnvError.group(errors)
  }
}

// ============================================================================
// LHS Unification Types
// ============================================================================

type PatternStackEntry = { tag: 'pattern', pattern: TTKPattern } | { tag: 'done', pattern: TTKPattern, arity: number }
type CheckStackEntry = { type: TTKTerm, ctxLength: number }

// ============================================================================
// Pattern Variable Counting
// ============================================================================

/**
 * Count the number of variables bound by a pattern.
 * Both PVar and PWild bind variables.
 */
function countPatternVarsInPattern(pattern: TTKPattern): number {
  switch (pattern.tag) {
    case 'PVar':
    case 'PWild':
      return 1;
    case 'PCtor':
      let count = 0;
      for (const arg of pattern.args) {
        count += countPatternVarsInPattern(arg);
      }
      // Also count variables in namedArgs
      if (pattern.namedArgs) {
        for (const na of pattern.namedArgs) {
          count += countPatternVarsInPattern(na.pattern);
        }
      }
      return count;
  }
}

/**
 * Count total variables bound by all patterns.
 */
function countPatternVars(patterns: TTKPattern[]): number {
  let count = 0;
  for (const p of patterns) {
    count += countPatternVarsInPattern(p);
  }
  return count;
}

// ============================================================================
// De Bruijn ↔ Levels Conversion for RHS
// ============================================================================

/**
 * Convert de Bruijn indices to "levels" representation.
 * Level 0 = first binder (outermost), like elabStack uses.
 * De Bruijn 0 = most recent binder (innermost).
 *
 * Conversion: level = contextLength - 1 - deBruijnIndex
 */
function deBruijnToLevels(term: TTKTerm, contextLength: number): TTKTerm {
  return transformVarsInTerm(term, (index) => {
    return mkVar(contextLength - 1 - index);
  });
}

/**
 * Convert levels back to de Bruijn indices.
 *
 * Conversion: deBruijnIndex = contextLength - 1 - level
 */
function levelsToDeBruijn(term: TTKTerm, contextLength: number): TTKTerm {
  return transformVarsInTerm(term, (level) => {
    return mkVar(contextLength - 1 - level);
  });
}

// ============================================================================
// LHS Unification Helpers
// ============================================================================

function prettyPrintInTTKContext(term: TTKTerm, signature: TTKContext): string {
  return prettyPrintTTK(term, signature.map(s => s.name).reverse())
}

function constructorDone(pattern: TTKPattern, arity: number, checkTypeEntry: CheckStackEntry, checkStack: CheckStackEntry[], elabStack: TTKTerm[], rhsContainer: { rhsInLevels: TTKTerm }, workEnv: TCEnv<unknown>) {
  logInfo(() => `STEP DONE(${prettyPrintPattern(pattern)}, ${arity})`);

  const nextCheckTypeEntry = checkStack.pop() as CheckStackEntry
  assertDefined(nextCheckTypeEntry, 'No next check type')

  const checkType = checkTypeEntry.type
  const nextCheckType = nextCheckTypeEntry.type

  logInfo(() => `  Pop T -> ${prettyPrintInTTKContext(checkType, workEnv.context.slice(0, checkTypeEntry.ctxLength))}`)
  logInfo(() => `  Peek T -> ${prettyPrintInTTKContext(nextCheckType, workEnv.context.slice(0, nextCheckTypeEntry.ctxLength))}`)

  assertIsPi(nextCheckType, 'Next check type must be a Pi')
  assertIsNotPi(checkType, 'Check type should not be a Pi')

  const unifyLeft = shiftTerm(checkType, workEnv.context.length - checkTypeEntry.ctxLength, 0)
  const unifyRight = shiftTerm(nextCheckType.domain, workEnv.context.length - nextCheckTypeEntry.ctxLength, 0)

  logInfo(() => `  Unifying: ${workEnv.prettyPrint(unifyLeft)} = ${workEnv.prettyPrint(unifyRight)}`)
  debugger

  // Pattern-local bindings (from constructor sub-patterns like wildcards) are at
  // de Bruijn indices 0 to (numPatternLocalBindings - 1). These should be flexible.
  // Function parameters are at indices >= numPatternLocalBindings. These should be rigid.
  // We use nextCheckTypeEntry.ctxLength because that's the context BEFORE wildcards were added.
  const numPatternLocalBindings = workEnv.context.length - nextCheckTypeEntry.ctxLength

  const unifyResult = unifyTerms(unifyLeft, unifyRight, {
    flexibleVars: true,
    rigidVarsAtOrAbove: numPatternLocalBindings,
    mode: 'pattern',
    // In K-free mode (assumeUIP=false), reject the deletion rule for rigid variables.
    // This prevents pattern matching on identity types like `Equal A x x` from implicitly
    // assuming that all proofs of `x = x` are equal to `refl`.
    allowRigidDeletion: workEnv.options.assumeUIP,
  })

  if (!unifyResult.success) {
    const leftStr = workEnv.prettyPrint(unifyLeft)
    const rightStr = workEnv.prettyPrint(unifyRight)
    if (unifyResult.reason === 'k-required') {
      throw TCEnvError.create(
        `Pattern matching on '${pattern.name}' requires axiom K (UIP). ` +
        `Cannot unify ${leftStr} with ${rightStr} without assuming uniqueness of identity proofs.`,
        workEnv
      )
    }
    throw TCEnvError.create(
      `Constructor '${pattern.name}' has result type ${leftStr} but expected ${rightStr}`,
      workEnv
    )
  }

  if (unifyResult.metaConstraints.length > 0) {
    debugger
    throw new Error('Meta constraints should not be emitted in clause lhs elaboration')
  }

  const elabHead = mkConst(pattern.name)
  let elabTerm = elabHead
  if (arity > 0) {
    const elabArgs = elabStack.slice(elabStack.length - arity)
    elabStack.length -= arity
    elabTerm = mkAppSpine(elabHead, elabArgs)
  }
  elabStack.push(elabTerm)

  // Elab var indices are backwards compared to debruijn indices
  const adjustedElabTerm = transformVarsInTerm(elabTerm, (index) => {
    return mkVar(workEnv.context.length - 1 - index)
  })

  // The Pi body is in a context of length (nextCheckTypeEntry.ctxLength + 1) because
  // the Pi binder adds one variable to the context. We need to:
  // 1. Shift FREE variables (indices >= 1) to account for the difference between
  //    the Pi body context and the current working context
  // 2. Replace the BOUND variable (index 0) with the elaborated term
  //
  // We use transformVarsInTerm instead of shiftTerm+subst because subst would
  // incorrectly shift down variables after replacement (assuming we're removing a binder),
  // but we're keeping all variables in the working context.
  const bodyCtxLength = nextCheckTypeEntry.ctxLength + 1
  const shiftAmount = workEnv.context.length - bodyCtxLength

  const returnType = transformVarsInTermWithBinders(nextCheckType.body, (varIndex, binderDepth) => {
    const adjustedIndex = varIndex - binderDepth;
    if (adjustedIndex === 0) {
      // Bound variable (the Pi's parameter) - replace with the elaborated term
      // The elaborated term is already in the working context, but we need to
      // shift it up by binderDepth to account for any inner binders we've entered
      return binderDepth > 0 ? shiftTerm(adjustedElabTerm, binderDepth, 0) : adjustedElabTerm;
    } else if (adjustedIndex > 0) {
      // Free variable from the Pi body context - shift up by shiftAmount
      return mkVar(varIndex + shiftAmount);
    } else {
      // Variable bound by an inner binder - leave unchanged
      return mkVar(varIndex);
    }
  });

  checkStack.push({ type: returnType, ctxLength: workEnv.context.length })

  for (const { varIndex, value } of enumerateAppliedSubstitutions(unifyResult.substitutions)) {
    logInfo(() => `    Apply: ${workEnv.prettyPrint(mkVar(varIndex))} -> ${workEnv.prettyPrint(value)}`)

    // Update these before the signature
    applySubstitutionToCheckStackInPlace(checkStack, workEnv.context.length, varIndex, value)
    applySubstitutionToElabStackInPlace(elabStack, workEnv.context.length, varIndex, value)
    // Also apply to RHS (which is in levels form, same as elabStack)
    rhsContainer.rhsInLevels = applySubstitutionToTermInLevels(rhsContainer.rhsInLevels, workEnv.context.length, varIndex, value)

    workEnv = workEnv.applySubstitutionToContextMetasAndConstraints(varIndex, value)
    logResultState(workEnv, undefined, checkStack, elabStack, '    AFTER APPLYING SUBSTITUTION:')
  }

  return workEnv.solveMetasAndConstraints({ liftMetasToFullContext: false })
}

function applySubstitutionToCheckStackInPlace(
  stack: CheckStackEntry[],
  mainSigLength: number,
  varIndex: number,
  value: TTKTerm
): CheckStackEntry[] {
  for (let i = 0; i < stack.length; i++) {
    const entry = stack[i];
    const m = entry.ctxLength;

    if (varIndex >= mainSigLength - m) {
      const localVarIndex = varIndex - (mainSigLength - m);
      const shiftAmount = m - mainSigLength;
      let adjustedValue = shiftAmount !== 0 ? shiftTerm(value, shiftAmount, 0) : value;

      // The value comes from the same context that's being modified by this substitution.
      // Indices in the value that are > varIndex refer to variables that will shift down
      // by 1 after the substitution removes varIndex from the context.
      // We need to pre-adjust these indices in the value.
      adjustedValue = transformVarsInTerm(adjustedValue, (idx) => {
        if (idx > varIndex) {
          return mkVar(idx - 1);
        }
        return mkVar(idx);
      });

      const newTerm = subst(localVarIndex, adjustedValue, entry.type);
      // Mutate entry in place
      stack[i] = { type: newTerm, ctxLength: entry.ctxLength - 1 };
    }
    // else, leave entry as is
  }
  return stack;
}

function applySubstitutionToElabStackInPlace(
  stack: TTKTerm[],
  mainSigLength: number,
  varIndex: number,
  value: TTKTerm
): TTKTerm[] {
  const varLevel = mainSigLength - 1 - varIndex;

  const valueInLevels = transformVarsInTerm(value, (idx) => {
    const level = mainSigLength - 1 - idx;
    if (level > varLevel) {
      return mkVar(level - 1);
    } else {
      return mkVar(level);
    }
  });

  for (let i = 0; i < stack.length; i++) {
    stack[i] = transformVarsInTerm(stack[i], (level) => {
      if (level === varLevel) {
        return valueInLevels;
      } else if (level > varLevel) {
        return mkVar(level - 1);
      } else {
        return mkVar(level);
      }
    });
  }

  return stack;
}

/**
 * Apply a substitution to a single term that uses "levels" representation.
 * Same logic as applySubstitutionToElabStackInPlace but for a single term.
 */
function applySubstitutionToTermInLevels(
  term: TTKTerm,
  mainSigLength: number,
  varIndex: number,
  value: TTKTerm
): TTKTerm {
  const varLevel = mainSigLength - 1 - varIndex;

  const valueInLevels = transformVarsInTerm(value, (idx) => {
    const level = mainSigLength - 1 - idx;
    if (level > varLevel) {
      return mkVar(level - 1);
    } else {
      return mkVar(level);
    }
  });

  return transformVarsInTerm(term, (level) => {
    if (level === varLevel) {
      return valueInLevels;
    } else if (level > varLevel) {
      return mkVar(level - 1);
    } else {
      return mkVar(level);
    }
  });
}

function processPattern(pattern: TTKPattern, checkTypeEntry: CheckStackEntry, patternStack: PatternStackEntry[], checkStack: CheckStackEntry[], elabStack: TTKTerm[], workEnv: TCEnv<unknown>) {
  const checkType = checkTypeEntry.type
  assertIsPi(checkType, 'Check type must be a Pi')

  const binderName = checkType.name
  const binderType = checkType.domain
  const binderBody = checkType.body

  logInfo(() => `\nSTEP ${prettyPrintPattern(pattern)} against (${binderName}: ${workEnv.prettyPrint(binderType)}) -> ...`);

  let env = workEnv

  if (pattern.tag === 'PWild') {
    // Wildcard pattern: create a meta variable for the binding
    const { env: newWorkEnv, name } = addMetaVarInTCEnv(env, binderType)
    logInfo(() => `  Create meta ${name} : ${env.prettyPrint(binderType)}`);

    env = newWorkEnv
      .extendTTKContext(pattern.name, binderType)

    env = env.withConstraint({ meta: name, rhs: mkVar(env.context.length - 1) })
    checkStack.push({ type: binderBody, ctxLength: env.context.length })
    elabStack.push(mkVar(env.context.length - 1))
  } else if (pattern.tag === 'PVar') {
    // Named variable pattern: validate and bind the variable
    // Validate pattern variable naming: must be lowercase, cannot shadow term definitions
    const patternNameEnv = env.withValue(pattern.name);
    validatePatternVarName(patternNameEnv);

    logInfo(() => `  Binding (${pattern.name} : ${env.prettyPrint(binderType)})`);
    env = env.extendTTKContext(pattern.name, binderType)

    checkStack.push({ type: binderBody, ctxLength: env.context.length })
    elabStack.push(mkVar(env.context.length - 1))
  } else {
    logInfo(() => `  Constructor pattern. Push DONE. Push sub-patterns. Push ${pattern.name} type`);

    checkStack.push({ type: checkType, ctxLength: env.context.length })

    patternStack.push({ tag: 'done', pattern, arity: pattern.args.length })
    for (let i = pattern.args.length - 1; i >= 0; i--) {
      patternStack.push({ tag: 'pattern', pattern: pattern.args[i] })
    }

    checkStack.push({ type: env.getTypeDefinitionAssert(pattern.name).value, ctxLength: env.context.length })
  }

  return env
}

function logResultState(workEnv: TCEnv<unknown>, patternStack: PatternStackEntry[] | undefined, checkStack: CheckStackEntry[], elabStack: TTKTerm[], header?: string) {
  logInfo(() => header ?? `\n  ~~ RESULT STATE ~~`)
  logInfo(() => `    Γ = ${workEnv.printTTKContext()}`)
  logInfo(() => `    Σ = ${workEnv.printMetas({ indentLevel: 8, innerIndentOffset: 2 })}`)
  logInfo(() => `    C = ${workEnv.printConstraints({ indentLevel: 8, innerIndentOffset: 2 })}`)
  if (patternStack) {
    logInfo(() => `    P = [${patternStack.map(p => {
      if (p.tag === 'pattern') {
        return prettyPrintPattern(p.pattern)
      } else {
        return `DONE(${prettyPrintPattern(p.pattern)}, ${p.arity})`
      }
    }).join(', ')}]`)
  }
  logInfo(() => `    T = ${printCollectionFancy(checkStack.map(s => {
    return `|${s.ctxLength}| >> ${prettyPrintInTTKContext(s.type, workEnv.context.slice(0, s.ctxLength))}`
  }), '[', ']', ',', { indentLevel: 8, innerIndentOffset: 2 })}`)
  logInfo(() => `    E = ${printCollectionFancy(elabStack.map(s => prettyPrintTTK(s)), '[', ']', ',', { indentLevel: 8, innerIndentOffset: 2 })}`)
}

// ============================================================================
// Main LHS Unification
// ============================================================================

function unifyMatchClauseLhs(termName: string, env: TCEnv<TTKPattern[]>, type: TTKTerm, rhsInLevels: TTKTerm): TCEnv<{ returnType: TTKTerm, elabStack: TTKTerm[], rhsInLevels: TTKTerm }> {
  env.assertCheckingMode('pattern')

  logInfo(() => `\n\nLHS: ${prettyPrintPattern({ tag: 'PCtor', name: termName, args: env.value })}`);
  const checkStack: CheckStackEntry[] = [{ type, ctxLength: env.context.length }]
  const patternStack: PatternStackEntry[] = env.value.map(p => ({ tag: 'pattern' as const, pattern: p })).reverse()
  const elabStack: TTKTerm[] = []
  // Container for RHS so it can be mutated during substitution application
  const rhsContainer = { rhsInLevels }

  let workEnv: TCEnv<unknown> = env

  logInfo(() => `\n  ~~ INITIAL STATE ~~`)
  logInfo(() => `    P = [${patternStack.map(p => {
    if (p.tag === 'pattern') {
      return prettyPrintPattern(p.pattern)
    } else {
      return `DONE(${prettyPrintPattern(p.pattern)}, ${p.arity})`
    }
  }).join(', ')}]`)
  logInfo(() => `    T = [${checkStack.map(s => prettyPrintInTTKContext(s.type, env.context.slice(0, s.ctxLength))).join(', ')}]`)

  while (patternStack.length > 0) {
    const patternEntry = patternStack.pop() as PatternStackEntry
    const checkTypeEntry = checkStack.pop() as CheckStackEntry

    if (!checkTypeEntry) {
      debugger
      throw new Error('No next check type')
    }

    if (patternEntry.tag === 'done') {
      workEnv = constructorDone(patternEntry.pattern, patternEntry.arity, checkTypeEntry, checkStack, elabStack, rhsContainer, workEnv)
    } else {
      workEnv = processPattern(patternEntry.pattern, checkTypeEntry, patternStack, checkStack, elabStack, workEnv)
    }

    logResultState(workEnv, patternStack, checkStack, elabStack)
  }

  if (checkStack.length !== 1) {
    debugger
    throw new Error('Check stack not empty')
  }

  // Validate pattern variables: check for duplicate names or conflicting bindings
  assertPatternVarsValid(env, elabStack, workEnv.context);

  workEnv = workEnv.solveMetasAndConstraints({ liftMetasToFullContext: true })

  return workEnv.withValue({ returnType: checkStack[0].type, elabStack, rhsInLevels: rhsContainer.rhsInLevels })
}

// ============================================================================
// Exported API
// ============================================================================

/**
 * Check a match clause by validating patterns and unifying the LHS.
 * Returns the checked clause with the solved/reified RHS.
 */
export function checkMatchClause(
  termName: string,
  env: TCEnv<TTKClause>,
  type: TTKTerm,
): TCEnv<TTKClause> {
  // First check arity (with helpful error messages for named param violations)
  assertMatchClauseLhsPatternsFullyApplied(env.inMatchClausePatterns())

  // Get the original RHS and patterns
  const originalRhs = env.value.rhs;
  const originalPatterns = env.value.patterns;

  // Pad patterns with implicit wildcards for named constructor parameters
  // This is needed because constructor types may have named Pi binders that need patterns
  const paddedPatterns = padPatternsWithNamedWildcards(originalPatterns, env.definitions);

  // The RHS was parsed with de Bruijn indices based on the ORIGINAL patterns.
  // When we pad patterns with wildcards for named params, we need to adjust RHS indices.
  // The shift depends on WHERE the wildcards are inserted in the context.
  //
  // Key insight: wildcards are inserted at the BEGINNING of each PCtor's args
  // (because named params come first). For each PCtor that gets wildcards:
  // - Variables bound BEFORE that PCtor in traversal order need to be shifted
  // - Variables bound BY or AFTER that PCtor don't shift
  //
  // We compute a series of shifts, one for each PCtor with named params.
  let shiftedRhs = originalRhs;

  // Compute shifts for each top-level pattern
  let varsAfterCurrent = 0;
  for (let i = originalPatterns.length - 1; i >= 0; i--) {
    const originalPattern = originalPatterns[i];
    const paddedPattern = paddedPatterns[i];

    const originalVars = countPatternVarsInPattern(originalPattern);
    const paddedVars = countPatternVarsInPattern(paddedPattern);
    const wildcardCount = paddedVars - originalVars;

    if (wildcardCount > 0) {
      // This pattern got wildcards. Variables bound BEFORE this pattern need to shift.
      // The cutoff is: variables in this pattern's original sub-patterns + variables after this pattern
      const cutoff = originalVars + varsAfterCurrent;
      shiftedRhs = shiftTerm(shiftedRhs, wildcardCount, cutoff);
    }

    varsAfterCurrent += paddedVars;
  }

  const paddedContextLength = countPatternVars(paddedPatterns);
  const rhsInLevels = deBruijnToLevels(shiftedRhs, paddedContextLength);

  // Create env with padded patterns for unification
  const paddedClause: TTKClause = { ...env.value, patterns: paddedPatterns };
  const paddedEnv = env.withValue(paddedClause);

  // Run LHS unification with padded patterns
  const result = unifyMatchClauseLhs(termName, paddedEnv.inMatchClausePatterns().withCheckingMode('pattern'), type, rhsInLevels);
  result.assertNoConstraints();

  const { returnType, elabStack, rhsInLevels: transformedRhsInLevels } = result.value;

  // Convert the transformed RHS back to de Bruijn indices using the final context length
  const finalContextLength = result.context.length;
  const transformedRhs = levelsToDeBruijn(transformedRhsInLevels, finalContextLength);

  // Convert elabStack to de Bruijn indices as well
  const elabArgs = elabStack.map(term => levelsToDeBruijn(term, finalContextLength));

  // Type check the transformed RHS
  const checkEnv = result.withValue(transformedRhs).withCheckingMode('check');
  const checkedEnv = checkType(checkEnv, returnType);

  // Solve any constraints from RHS checking to populate meta solutions
  const solvedEnv = checkedEnv.solveMetasAndConstraints({ liftMetasToFullContext: false });

  // Extract context names for pretty printing (de Bruijn order: index 0 = most recent)
  // TTKContext has oldest at index 0 (appended), but we need most recent at index 0
  const contextNames = result.context.map(entry => entry.name).reverse();

  // Return the checked clause with the solved RHS, elaborated arguments, and meta solutions
  const checkedClause: TTKClause = {
    patterns: env.value.patterns,
    rhs: solvedEnv.value,
    elabArgs,
    contextNames,
    metaVars: solvedEnv.metaVars
  };
  return result.withValue(checkedClause);
}

/**
 * Check if patterns are absurd (type-theoretically impossible).
 * This runs LHS unification only - if it fails, the patterns are absurd.
 *
 * @param termName The name of the term (for error messages)
 * @param env The TCEnv containing the patterns to check
 * @param type The expected type
 * @returns true if patterns are absurd, false if they could be inhabited
 */
export function arePatternsAbsurd(
  termName: string,
  env: TCEnv<TTKPattern[]>,
  type: TTKTerm,
): boolean {
  try {
    // Use a dummy RHS (a hole) - we only care about LHS unification
    const dummyRhs: TTKTerm = { tag: 'Hole', id: '_absurd_check' };
    unifyMatchClauseLhs(termName, env.withCheckingMode('pattern'), type, dummyRhs);
    return false; // Unification succeeded - not absurd
  } catch (e) {
    // Unification failed - patterns are absurd
    return true;
  }
}
