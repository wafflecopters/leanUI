import type { ParsedDeclaration } from '../parser/parser';
import type { SourceMap } from '../types/source-position';
import type { DefinitionsMap, TCEnvError } from './term';
import type { TypeInfoMap } from './type-info';
import type { ElaborateTacticBlockFn } from './compile-term-simple-value';
import { createCompiledDeclaration, createElabErrorResult } from './compile-declaration-result';
import { elaborateTermDeclaration } from './compile-term-elaboration';
import { checkTermDeclaration, type CheckTermDeclarationOptions } from './compile-term-processing';

export interface ProcessTermDeclarationResult {
  success: boolean;
  compiled: import('./compile').CompiledDeclaration;
  newDefinitions: DefinitionsMap;
  errorCount: number;
}

export interface ProcessTermDeclarationOptions extends CheckTermDeclarationOptions {}

/**
 * Elaborate and check a single term declaration, assembling the final compiled
 * declaration shape used by the rest of the pipeline.
 */
export function processTermDeclaration(
  decl: ParsedDeclaration,
  sourceMap: SourceMap,
  definitions: DefinitionsMap,
  elaborateTacticBlock: ElaborateTacticBlockFn,
  options?: ProcessTermDeclarationOptions,
): ProcessTermDeclarationResult {
  const typeInfoMap: TypeInfoMap = new Map();
  const warnings: TCEnvError[] = [];

  let elaborated: ReturnType<typeof elaborateTermDeclaration>;
  try {
    elaborated = elaborateTermDeclaration(decl, sourceMap, definitions);
  } catch (error) {
    return createElabErrorResult(error, decl, sourceMap, new Map(), definitions);
  }
  const { elabDecl, kernelType, elabMap } = elaborated;

  const result = checkTermDeclaration(
    elabDecl,
    definitions,
    elaborateTacticBlock,
    { ...options, typeInfoCollector: typeInfoMap, warningsCollector: warnings },
  );
  const finalTypeInfoMap = typeInfoMap.size > 0 ? typeInfoMap : undefined;

  if (!result.success) {
    return {
      success: false,
      compiled: createCompiledDeclaration(
        decl,
        kernelType,
        undefined,
        undefined,
        elabMap,
        sourceMap,
        false,
        [...result.errors, ...warnings],
        definitions,
        result.totalityResult,
        undefined,
        undefined,
        undefined,
        undefined,
        undefined,
        undefined,
        undefined,
        finalTypeInfoMap,
        undefined,
      ),
      newDefinitions: definitions,
      errorCount: result.errors.length,
    };
  }

  return {
    success: true,
    compiled: createCompiledDeclaration(
      decl,
      result.zonkedType,
      result.checkedValue,
      undefined,
      elabMap,
      sourceMap,
      true,
      warnings,
      result.definitions,
      result.totalityResult,
      undefined,
      undefined,
      undefined,
      undefined,
      undefined,
      undefined,
      undefined,
      finalTypeInfoMap,
      result.tacticInfoTree,
    ),
    newDefinitions: result.definitions,
    errorCount: 0,
  };
}
