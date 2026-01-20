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
import { countPiBinders, DefinitionsMap, extractAppSpine, printCollectionFancy, TTKContext, TCEnv, TCEnvError, assertDefined, assertIsNotPi, assertIsPi, transformVarsInTerm, validatePatternVarName, addMetaVarInTCEnv } from './term';
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
 * Look up a constructor by name and return its expected arity (number of arguments).
 */
function getConstructorArity(definitions: DefinitionsMap, ctorName: string): number | undefined {
  for (const inductive of definitions.inductiveTypes.values()) {
    for (const ctor of inductive.constructors) {
      if (ctor.name === ctorName) {
        return countPiBinders(ctor.type);
      }
    }
  }
  return undefined;
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
        const expectedArity = getConstructorArity(env.definitions, pattern.name);
        if (expectedArity !== undefined && pattern.args.length !== expectedArity) {
          errors.push(TCEnvError.create(
            `Constructor '${pattern.name}' expects ${expectedArity} argument${expectedArity === 1 ? '' : 's'}, but got ${pattern.args.length}`,
            env.atIndexPath([...env.indexPath, ...path])
          ));
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
          const termsList = termEntries.map(e => prettyPrintTTK(e.term, printContext)).join(', ');
          errors.push(TCEnvError.create(
            `Pattern '${name}' unifies to unequal expressions: ${termsList}`,
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
// LHS Unification Helpers
// ============================================================================

function prettyPrintInTTKContext(term: TTKTerm, signature: TTKContext): string {
  return prettyPrintTTK(term, signature.map(s => s.name).reverse())
}

function constructorDone(pattern: TTKPattern, arity: number, checkTypeEntry: CheckStackEntry, checkStack: CheckStackEntry[], elabStack: TTKTerm[], workEnv: TCEnv<unknown>) {
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

  const unifyResult = unifyTerms(unifyLeft, unifyRight)

  if (!unifyResult.success) {
    debugger
    throw new Error('TODO: unification failed')
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

  const shiftAmount = workEnv.context.length - nextCheckTypeEntry.ctxLength
  const adjustedBody = shiftTerm(nextCheckType.body, shiftAmount, 0)

  checkStack.push({ type: subst(shiftAmount, adjustedElabTerm, adjustedBody), ctxLength: workEnv.context.length })

  for (const { varIndex, value } of enumerateAppliedSubstitutions(unifyResult.substitutions)) {
    logInfo(() => `    Apply: ${workEnv.prettyPrint(mkVar(varIndex))} -> ${workEnv.prettyPrint(value)}`)

    // Update these 2 before the signature
    applySubstitutionToCheckStackInPlace(checkStack, workEnv.context.length, varIndex, value)
    applySubstitutionToElabStackInPlace(elabStack, workEnv.context.length, varIndex, value)

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
      const shiftedValue = shiftAmount !== 0 ? shiftTerm(value, shiftAmount, 0) : value;

      const newTerm = subst(localVarIndex, shiftedValue, entry.type);
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

function unifyMatchClauseLhs(termName: string, env: TCEnv<TTKPattern[]>, type: TTKTerm): TCEnv<{ returnType: TTKTerm, elabStack: TTKTerm[] }> {
  logInfo(() => `\n\nLHS: ${prettyPrintPattern({ tag: 'PCtor', name: termName, args: env.value })}`);
  const checkStack: CheckStackEntry[] = [{ type, ctxLength: env.context.length }]
  const patternStack: PatternStackEntry[] = env.value.map(p => ({ tag: 'pattern' as const, pattern: p })).reverse()
  const elabStack: TTKTerm[] = []

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
      workEnv = constructorDone(patternEntry.pattern, patternEntry.arity, checkTypeEntry, checkStack, elabStack, workEnv)
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

  return workEnv.withValue({ returnType: checkStack[0].type, elabStack })
}

// ============================================================================
// Exported API
// ============================================================================

/**
 * Check a match clause by validating patterns and unifying the LHS.
 */
export function checkMatchClause(
  termName: string,
  env: TCEnv<TTKClause>,
  type: TTKTerm,
): TCEnv<void> {
  assertMatchClauseLhsPatternsFullyApplied(env.inMatchClausePatterns())
  const result = unifyMatchClauseLhs(termName, env.inMatchClausePatterns(), type);
  result.assertNoConstraints();

  const { returnType } = result.value

  const checkEnv = result.atValueAndPathOfEnv(env).inMatchClauseRhs()
  const checkedEnv = checkType(checkEnv, returnType);

  // debugger

  return result.withoutValue();
}
