import type { ElabDeclaration } from './compile-types';
import { elabToKernelWithMap, type NamedArgMap } from './elab';
import type { TTKTerm } from './kernel';
import { countKernelClauseBindings } from './pattern-binders';
import { checkType } from './checker';
import { prepareKernelGoalType } from './prepare-kernel-goal-type';
import type { TacticInfoTree } from '../tactics/info-tree';
import type { TTacticBlock } from './surface';
import { createNamedArgInfoLookup, setDefinitionValueInTCEnv, type DefinitionsMap, type TCEnv, TCEnvError, type TermDefinition } from './term';
import type { ElabMap, SourceMap } from '../types/source-position';

export interface TacticBlockElaborationResult {
  term: TTKTerm;
  infoTree: TacticInfoTree;
}

export type ElaborateTacticBlockFn = (
  block: TTacticBlock,
  goalType: TTKTerm,
  definitions: DefinitionsMap,
  elabMap: ElabMap,
  sourceMap: SourceMap,
  context: Array<{ name: string; type: TTKTerm }>,
  recursiveTermName?: string,
) => TacticBlockElaborationResult;

function containsSelfReference(term: TTKTerm, name: string): boolean {
  switch (term.tag) {
    case 'Const':
      return term.name === name;
    case 'App':
      return containsSelfReference(term.fn, name) || containsSelfReference(term.arg, name);
    case 'Binder':
      return containsSelfReference(term.domain, name) || containsSelfReference(term.body, name);
    case 'Sort':
      return containsSelfReference(term.level, name);
    case 'Annot':
      return containsSelfReference(term.term, name) || containsSelfReference(term.type, name);
    case 'Match':
      return term.clauses.some(clause => containsSelfReference(clause.rhs, name));
    default:
      return false;
  }
}

function containsUnsolvedMeta(term: TTKTerm, metaVars: Map<string, { solution?: TTKTerm }>): boolean {
  switch (term.tag) {
    case 'Meta': {
      const meta = metaVars.get(term.id);
      if (meta) return !meta.solution;
      // Implicit-argument placeholders are inserted during elaboration and are
      // not always tracked in metaVars. They behave like omitted implicit args,
      // not like trusted proof obligations for the final kernel term.
      return !term.id.startsWith('_implicit');
    }
    case 'App':
      return containsUnsolvedMeta(term.fn, metaVars) || containsUnsolvedMeta(term.arg, metaVars);
    case 'Binder':
      return containsUnsolvedMeta(term.domain, metaVars) ||
        containsUnsolvedMeta(term.body, metaVars) ||
        (term.binderKind.tag === 'BLet' && containsUnsolvedMeta(term.binderKind.defVal, metaVars));
    case 'Sort':
      return containsUnsolvedMeta(term.level, metaVars);
    case 'Annot':
      return containsUnsolvedMeta(term.term, metaVars) || containsUnsolvedMeta(term.type, metaVars);
    case 'Match':
      return containsUnsolvedMeta(term.scrutinee, metaVars) ||
        term.clauses.some(clause => containsUnsolvedMeta(clause.rhs, metaVars));
    default:
      return false;
  }
}

type RecursiveVarOrigin =
  | { kind: 'original'; argPosition: number }
  | { kind: 'smaller'; argPosition: number }
  | { kind: 'local' };

function collectLeadingLambdas(term: TTKTerm): { arity: number; body: TTKTerm } {
  let arity = 0;
  let body = term;
  while (body.tag === 'Binder' && body.binderKind.tag === 'BLam') {
    arity++;
    body = body.body;
  }
  return { arity, body };
}

function collectAppSpine(term: TTKTerm): { head: TTKTerm; args: TTKTerm[] } {
  const args: TTKTerm[] = [];
  let head = term;
  while (head.tag === 'App') {
    args.push(head.arg);
    head = head.fn;
  }
  args.reverse();
  return { head, args };
}

function prependOrigins(
  origins: RecursiveVarOrigin[],
  count: number,
  origin: RecursiveVarOrigin,
): RecursiveVarOrigin[] {
  return [...Array.from({ length: count }, () => origin), ...origins];
}

function isRecursiveCallStructurallySmaller(
  args: TTKTerm[],
  origins: RecursiveVarOrigin[],
  requiredArity: number,
): boolean {
  if (args.length < requiredArity) {
    return true;
  }
  for (let argPosition = 0; argPosition < args.length; argPosition++) {
    const arg = args[argPosition];
    if (arg.tag !== 'Var') continue;
    const origin = origins[arg.index];
    if (origin?.kind === 'smaller' && origin.argPosition === argPosition) {
      return true;
    }
  }
  return false;
}

function isMatchGuardedStructuralRecursion(term: TTKTerm, recursiveName: string): boolean {
  const { arity, body } = collectLeadingLambdas(term);
  if (arity === 0) return false;

  const initialOrigins: RecursiveVarOrigin[] = Array.from(
    { length: arity },
    (_, deBruijn) => ({ kind: 'original', argPosition: arity - 1 - deBruijn }),
  );

  let sawRecursiveCall = false;

  const visit = (current: TTKTerm, origins: RecursiveVarOrigin[]): boolean => {
    const { head, args } = collectAppSpine(current);
    if (head.tag === 'Const' && head.name === recursiveName) {
      sawRecursiveCall = true;
      if (!isRecursiveCallStructurallySmaller(args, origins, arity)) {
        return false;
      }
    }

    switch (current.tag) {
      case 'App':
        return visit(current.fn, origins) && visit(current.arg, origins);
      case 'Binder': {
        const withLocal = prependOrigins(origins, 1, { kind: 'local' });
        return visit(current.domain, origins)
          && (current.binderKind.tag !== 'BLet' || visit(current.binderKind.defVal, origins))
          && visit(current.body, withLocal);
      }
      case 'Sort':
        return visit(current.level, origins);
      case 'Annot':
        return visit(current.term, origins) && visit(current.type, origins);
      case 'Match': {
        if (!visit(current.scrutinee, origins)) return false;
        const scrutineeOrigin = current.scrutinee.tag === 'Var' ? origins[current.scrutinee.index] : undefined;
        const clauseOrigin = scrutineeOrigin && scrutineeOrigin.kind !== 'local'
          ? { kind: 'smaller' as const, argPosition: scrutineeOrigin.argPosition }
          : { kind: 'local' as const };
        return current.clauses.every(clause =>
          visit(clause.rhs, prependOrigins(origins, countKernelClauseBindings(clause), clauseOrigin)),
        );
      }
      default:
        return true;
    }
  };

  return visit(body, initialOrigins) && sawRecursiveCall;
}

export function checkSimpleTermValue(
  decl: ElabDeclaration,
  termName: string,
  termEnv: TCEnv<TermDefinition>,
  zonkedKernelType: TTKTerm,
  namedArgMap: NamedArgMap | undefined,
  elaborateTacticBlock: ElaborateTacticBlockFn,
): { success: true; definitions: DefinitionsMap; checkedValue: TTKTerm; zonkedType: TTKTerm; tacticInfoTree?: TacticInfoTree } | { success: false; errors: TCEnvError[] } {
  if (!decl.surfaceValue || decl.surfaceValue.tag === 'Match') {
    return { success: false, errors: [TCEnvError.create('Expected non-match term value', termEnv)] };
  }

  const valuePath = [{ kind: 'field', name: 'value' }] as const;
  const appNamedArgLookup = createNamedArgInfoLookup(termEnv.definitions);

  let kernelValue: TTKTerm;
  let tacticInfoTree: TacticInfoTree | undefined;
  const preparedKernelType = prepareKernelGoalType(
    zonkedKernelType,
    termEnv.context,
    termEnv.definitions,
  );
  if (decl.surfaceValue.tag === 'TacticBlock') {
    try {
      // Let the tactic engine prepare the goal type exactly once when it
      // creates the initial proof state. Passing a pre-prepared theorem type
      // here would double-prepare dependent Pi bodies and skew de Bruijn
      // references during the intro/cases pipeline.
      const tacticResult = elaborateTacticBlock(
        decl.surfaceValue,
        zonkedKernelType,
        termEnv.definitions,
        decl.elabMap ?? new Map(),
        decl.sourceMap ?? new Map(),
        [],
        termName,
      );
      kernelValue = tacticResult.term;
      tacticInfoTree = tacticResult.infoTree;
    } catch (error) {
      if (error instanceof TCEnvError) {
        throw error;
      }
      const errorMessage = error instanceof Error ? error.message : String(error);
      throw TCEnvError.create(errorMessage, termEnv);
    }
  } else {
    kernelValue = elabToKernelWithMap(
      decl.surfaceValue,
      decl.elabMap ?? new Map(),
      [...valuePath],
      [...valuePath],
      namedArgMap,
      appNamedArgLookup,
    );
  }

  try {
    const valueEnv = termEnv.withValue(kernelValue);
    const result = checkType(valueEnv, preparedKernelType);

    let solvedResult: typeof result;
    try {
      solvedResult = result.solveMetasAndConstraints({ liftMetasToFullContext: false });
    } catch (error) {
      if (error instanceof Error && !(error instanceof TCEnvError)) {
        throw TCEnvError.create(error.message, result);
      }
      throw error;
    }

    const zonkedType = solvedResult.zonkTerm(preparedKernelType);
    if (containsUnsolvedMeta(solvedResult.value, solvedResult.metaVars) || containsUnsolvedMeta(zonkedType, solvedResult.metaVars)) {
      return {
        success: false,
        errors: [TCEnvError.create('Checking the value produced unsolved metas.', termEnv)],
      };
    }

    const zonkedValue = solvedResult.zonkTerm(solvedResult.value);
    if (containsSelfReference(zonkedValue, termName)) {
      const allowsStructuredRecursion = decl.surfaceValue.tag === 'TacticBlock'
        && isMatchGuardedStructuralRecursion(zonkedValue, termName);
      if (allowsStructuredRecursion) {
        const resultEnv = setDefinitionValueInTCEnv(termEnv, termName, zonkedValue);
        return {
          success: true,
          definitions: resultEnv.definitions,
          checkedValue: zonkedValue,
          zonkedType,
          tacticInfoTree,
        };
      }
      return {
        success: false,
        errors: [
          TCEnvError.create(
            `Definition '${termName}' is non-terminating: simple definitions cannot be recursive. Use pattern matching for recursive definitions.`,
            termEnv,
          ),
        ],
      };
    }

    const resultEnv = setDefinitionValueInTCEnv(termEnv, termName, zonkedValue);
    return {
      success: true,
      definitions: resultEnv.definitions,
      checkedValue: zonkedValue,
      zonkedType,
      tacticInfoTree,
    };
  } catch (error) {
    if (error instanceof TCEnvError) {
      return { success: false, errors: [error] };
    }
    return { success: false, errors: [TCEnvError.create(String(error), termEnv)] };
  }
}
