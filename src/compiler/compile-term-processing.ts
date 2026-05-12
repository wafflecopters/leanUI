import type { ElabDeclaration } from './compile-types';
import type { TypeInfoMap } from './type-info';
import { TCEnvError, setDefinitionValueInTCEnv, type DefinitionsMap, type TermDefinition } from './term';
import type { TTKTerm } from './kernel';
import { prepareTermSignature } from './compile-term-signature';
import { validateAnnotatedAbsurdClauses } from './compile-term-absurdity';
import { checkSimpleTermValue, type ElaborateTacticBlockFn } from './compile-term-simple-value';
import { computeEffectiveTotalArity, prepareMatchSurfaceClauses } from './compile-term-match-preparation';
import { checkTermValue } from './compile-term-value';

export interface CheckTermDeclarationOptions {
  allowUnsolvedSigMetas?: boolean;
  skipTotality?: boolean;
  withScrutineeCount?: number;
  newScrutineeCount?: number;
  typeInfoCollector?: TypeInfoMap;
  warningsCollector?: TCEnvError[];
  assumeK?: boolean;
}

export type CheckTermDeclarationResult =
  | { success: false; errors: TCEnvError[]; totalityResult?: import('./totality').TotalityResult }
  | { success: true; definitions: DefinitionsMap; checkedValue: TTKTerm; zonkedType: TTKTerm; totalityResult?: import('./totality').TotalityResult; tacticInfoTree?: import('../tactics/info-tree').TacticInfoTree };

export function checkTermDeclaration(
  decl: ElabDeclaration,
  definitions: DefinitionsMap,
  elaborateTacticBlock: ElaborateTacticBlockFn,
  options?: CheckTermDeclarationOptions,
): CheckTermDeclarationResult {
  const signatureResult = prepareTermSignature(decl, definitions, {
    allowUnsolvedSigMetas: options?.allowUnsolvedSigMetas,
    assumeK: options?.assumeK,
    typeInfoCollector: options?.typeInfoCollector,
    warningsCollector: options?.warningsCollector,
  });
  if (!signatureResult.success) {
    return signatureResult;
  }

  const {
    termEnv,
    zonkedKernelType,
    namedArgMap,
    argNamedArgInfos,
    totalArity,
  } = signatureResult.prepared;
  const termName = decl.name as string;
  const env = termEnv;

  try {
    if (decl.isPostulate) {
      return {
        success: true,
        definitions: termEnv.definitions,
        checkedValue: { tag: 'Hole', id: '_postulate' },
        zonkedType: zonkedKernelType,
      };
    }

    const absurdValidation = validateAnnotatedAbsurdClauses(decl, termEnv, zonkedKernelType, namedArgMap);
    if (!absurdValidation.success) {
      return { success: false, errors: absurdValidation.errors };
    }
    const annotatedAbsurdClauses = absurdValidation.annotatedAbsurdClauses;

    if (decl.surfaceValue && decl.surfaceValue.tag !== 'Match') {
      return checkSimpleTermValue(
        decl,
        termName,
        termEnv,
        zonkedKernelType,
        namedArgMap,
        elaborateTacticBlock,
      );
    }

    const {
      surfaceClauses,
      surfaceClauseIndices,
    } = prepareMatchSurfaceClauses(decl.surfaceValue);

    const effectiveTotalArity = computeEffectiveTotalArity(
      zonkedKernelType,
      totalArity,
      termEnv.definitions,
    );

    const result = checkTermValue(
      termName,
      termEnv,
      zonkedKernelType,
      surfaceClauses,
      surfaceClauseIndices,
      decl.elabMap ?? new Map(),
      namedArgMap,
      effectiveTotalArity,
      annotatedAbsurdClauses,
      {
        skipTotality: options?.skipTotality,
        withScrutineeCount: options?.withScrutineeCount,
        newScrutineeCount: options?.newScrutineeCount,
      },
      argNamedArgInfos,
    );
    if (!result.success) {
      return { success: false, errors: result.errors, totalityResult: result.totalityResult };
    }

    const resultEnv = setDefinitionValueInTCEnv(termEnv, termName, result.checkedValue);
    return {
      success: true,
      definitions: resultEnv.definitions,
      checkedValue: result.checkedValue,
      zonkedType: zonkedKernelType,
      totalityResult: result.totalityResult,
    };
  } catch (error) {
    if (error instanceof TCEnvError) {
      return {
        success: false,
        errors: [error],
      };
    }
    return {
      success: false,
      errors: [TCEnvError.create(error instanceof Error ? error.message : String(error), env)],
    };
  }
}
