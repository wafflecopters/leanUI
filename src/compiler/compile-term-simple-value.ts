import type { ElabDeclaration } from './compile-types';
import { elabToKernelWithMap, type NamedArgMap } from './elab';
import type { TTKTerm } from './kernel';
import { checkType } from './checker';
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
  if (decl.surfaceValue.tag === 'TacticBlock') {
    try {
      const tacticResult = elaborateTacticBlock(
        decl.surfaceValue,
        zonkedKernelType,
        termEnv.definitions,
        decl.elabMap ?? new Map(),
        decl.sourceMap ?? new Map(),
        [],
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

  if (decl.surfaceValue.tag === 'TacticBlock') {
    const resultEnv = setDefinitionValueInTCEnv(termEnv, termName, kernelValue);
    return {
      success: true,
      definitions: resultEnv.definitions,
      checkedValue: kernelValue,
      zonkedType: zonkedKernelType,
      tacticInfoTree,
    };
  }

  try {
    const valueEnv = termEnv.withValue(kernelValue);
    const result = checkType(valueEnv, zonkedKernelType);

    let solvedResult: typeof result;
    try {
      solvedResult = result.solveMetasAndConstraints({ liftMetasToFullContext: false });
    } catch (error) {
      if (error instanceof Error && !(error instanceof TCEnvError)) {
        throw TCEnvError.create(error.message, result);
      }
      throw error;
    }

    const unsolvedMetas = Array.from(solvedResult.metaVars.values()).filter(meta => !meta.solution && !meta.isHole);
    if (unsolvedMetas.length > 0) {
      return {
        success: false,
        errors: [TCEnvError.create('Checking the value produced unsolved metas.', termEnv)],
      };
    }

    const zonkedValue = solvedResult.zonkTerm(solvedResult.value);
    if (containsSelfReference(zonkedValue, termName)) {
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
      zonkedType: zonkedKernelType,
    };
  } catch (error) {
    if (error instanceof TCEnvError) {
      return { success: false, errors: [error] };
    }
    return { success: false, errors: [TCEnvError.create(String(error), termEnv)] };
  }
}
