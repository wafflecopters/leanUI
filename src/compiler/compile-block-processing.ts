import { resolvePatternsInDeclarations } from '../parser/pattern-resolution';
import { validateDeclarations, type SymbolContext } from '../types/name-resolution';
import {
  type ElabMap,
  type IndexPath,
  type SourceMap,
  serializeIndexPath,
} from '../types/source-position';
import {
  addDefinition,
  createNamedArgInfoLookup,
  createTCEnv,
  TCEnvError,
  type DefinitionsMap,
} from './term';
import {
  buildConstructorParamNames,
  elabToKernelWithMap,
  extractArgNamedArgInfos,
  extractNamedArgMap,
  setConstructorParamNames,
  type ConstructorParamNames,
} from './elab';
import type { TTKTerm } from './kernel';
import { desugarWithClauses } from './with-desugar';
import {
  mergeAuxTypeInfoIntoMain,
  remapWithClauseElabMap,
  remapWithScrutineeInMainElabMap,
} from './compile-with-aux-mapping';
import { processInductiveDeclaration } from './compile-inductive-processing';
import { processRecordDeclaration } from './compile-record-processing';
import { processTermDeclaration } from './compile-term-declaration';
import { computeCodeStartLine } from './compile-source-utils';
import type { ElaborateTacticBlockFn } from './compile-term-simple-value';
import type { RecheckZonkedTermFn } from './compile-zonk-recheck';
import { adjustSourceMapToAbsolute } from './compile-source-utils';

import type {
  CompileOptions,
  CompiledBlock,
  CompiledDeclaration,
  NameResolutionErrorWithRange,
  ParsedBlock,
} from './compile-types';

export interface CompileOneBlockResult {
  compiled: CompiledBlock;
  newDefinitions: DefinitionsMap;
  newSymbolContext: SymbolContext;
  newConstructorParamNames: ConstructorParamNames;
  checkErrorCount: number;
  nameErrorCount: number;
}

function appendZonkRecheckError(
  compiled: CompiledDeclaration,
  definitions: DefinitionsMap,
  errorMessage: string,
): void {
  const errEnv = createTCEnv({ definitions, options: { mode: 'check' } });
  compiled.checkErrors.push(TCEnvError.create(errorMessage, errEnv));
  compiled.checkSuccess = false;
}

function syncConstructorParamNames(
  constructorParamNames: ConstructorParamNames,
  compiled: CompiledDeclaration,
): void {
  if (!compiled.kernelConstructors) return;
  const newCtorParamNames = buildConstructorParamNames(compiled.kernelConstructors);
  for (const [ctorName, paramInfo] of newCtorParamNames) {
    constructorParamNames.set(ctorName, paramInfo);
  }
  setConstructorParamNames(constructorParamNames);
}

function collectAuxiliaryErrorsForMain(
  auxiliaryName: string | undefined,
  mainName: string,
  auxiliaryCompiled: CompiledDeclaration,
  auxErrorsForMain: TCEnvError[],
  auxElabMapForMain: ElabMap,
): void {
  for (const err of auxiliaryCompiled.checkErrors) {
    if (auxiliaryName && mainName && err.message.includes(auxiliaryName)) {
      auxErrorsForMain.push(TCEnvError.create(err.message.split(auxiliaryName).join(mainName), err.env));
    } else {
      auxErrorsForMain.push(err);
    }
  }
  if (auxiliaryCompiled.elabMap) {
    for (const [key, value] of auxiliaryCompiled.elabMap) {
      auxElabMapForMain.set(key, value);
    }
  }
}

/**
 * Compile a single parsed block given the accumulated state from prior blocks.
 * This is the extracted inner loop of compileTTFromText / compileIncrementalTT.
 */
export function compileOneBlock(
  block: ParsedBlock,
  blockIndex: number,
  definitions: DefinitionsMap,
  symbolContext: SymbolContext,
  constructorParamNames: ConstructorParamNames,
  assumeK: boolean,
  elaborateTacticBlock: ElaborateTacticBlockFn,
  recheckZonkedTerm: RecheckZonkedTermFn,
  options?: CompileOptions,
): CompileOneBlockResult {
  let checkErrorCount = 0;
  let nameErrorCount = 0;
  constructorParamNames = new Map(constructorParamNames);

  if (block.kind === 'comment') {
    return {
      compiled: {
        blockIndex,
        sourceLines: block.sourceLines,
        startLine: block.startLine,
        codeStartLine: computeCodeStartLine(block.sourceLines, block.startLine),
        parseSuccess: true,
        parseErrors: [],
        nameResolutionSuccess: true,
        nameResolutionErrors: [],
        declarations: [],
        isComment: true,
      },
      newDefinitions: definitions,
      newSymbolContext: symbolContext,
      newConstructorParamNames: constructorParamNames,
      checkErrorCount: 0,
      nameErrorCount: 0,
    };
  }

  if (block.kind === 'error') {
    return {
      compiled: {
        blockIndex,
        sourceLines: block.sourceLines,
        startLine: block.startLine,
        codeStartLine: computeCodeStartLine(block.sourceLines, block.startLine),
        parseSuccess: false,
        parseErrors: block.errors,
        nameResolutionSuccess: true,
        nameResolutionErrors: [],
        declarations: [],
        isComment: false,
      },
      newDefinitions: definitions,
      newSymbolContext: symbolContext,
      newConstructorParamNames: constructorParamNames,
      checkErrorCount: 0,
      nameErrorCount: 0,
    };
  }

  const compiledDecls: CompiledDeclaration[] = [];
  const blockNameErrors: NameResolutionErrorWithRange[] = [];

  for (let declIndex = 0; declIndex < block.declarations.length; declIndex++) {
    const origDecl = block.declarations[declIndex];

    if (origDecl.kind === 'notation') continue;

    const sourceMap = adjustSourceMapToAbsolute(block.sourceMaps[declIndex], block.startLine, block.posOffset);

    const nameResult = validateDeclarations([origDecl], symbolContext);
    if (nameResult.success) {
      symbolContext = nameResult.value;
    } else {
      for (const err of nameResult.errors) {
        blockNameErrors.push({
          message: err.message,
          symbolName: err.symbolName,
          path: serializeIndexPath(err.path),
          declarationIndex: declIndex,
        });
        nameErrorCount++;
      }
      if (origDecl.name) {
        symbolContext = new Set([...symbolContext, origDecl.name]);
      }
      if (origDecl.constructors) {
        for (const ctor of origDecl.constructors) {
          symbolContext = new Set([...symbolContext, ctor.name]);
        }
      }
    }

    const [resolvedDecl] = resolvePatternsInDeclarations([origDecl], symbolContext);
    const originalSurfaceValue = resolvedDecl.value;
    const desugaredDecls = desugarWithClauses([resolvedDecl]);
    const mainDecl = desugaredDecls[0];
    const auxiliaryDecls = desugaredDecls.slice(1);

    if (auxiliaryDecls.length > 0 && originalSurfaceValue) {
      mainDecl.originalSurfaceValue = originalSurfaceValue;
    }

    for (const auxDecl of auxiliaryDecls) {
      const auxNameResult = validateDeclarations([auxDecl], symbolContext);
      if (auxNameResult.success) {
        symbolContext = auxNameResult.value;
      }
    }

    if (auxiliaryDecls.length > 0 && mainDecl.kind === 'def' && mainDecl.type && mainDecl.name) {
      try {
        const typePath: IndexPath = [{ kind: 'field', name: 'type' }];
        const appNamedArgLookup = createNamedArgInfoLookup(definitions);
        const elabMap: ElabMap = new Map();
        const mainKernelType = elabToKernelWithMap(mainDecl.type, elabMap, typePath, typePath, undefined, appNamedArgLookup);
        const mainNamedArgMap = extractNamedArgMap(mainDecl.type);
        const mainArgNamedArgInfos = extractArgNamedArgInfos(mainDecl.type);
        definitions = addDefinition(
          definitions,
          mainDecl.name,
          mainKernelType,
          undefined,
          mainNamedArgMap.size > 0 ? mainNamedArgMap : undefined,
          mainArgNamedArgInfos.size > 0 ? mainArgNamedArgInfos : undefined,
        );
      } catch {
        // If type elaboration fails, continue - error will be caught later.
      }
    }

    const failedAuxNames = new Set<string>();
    const auxErrorsForMain: TCEnvError[] = [];
    const auxElabMapForMain: ElabMap = new Map();
    const compiledAuxiliaries: CompiledDeclaration[] = [];

    for (const auxDecl of auxiliaryDecls) {
      const result = processTermDeclaration(
        auxDecl,
        sourceMap,
        definitions,
        elaborateTacticBlock,
        {
          allowUnsolvedSigMetas: true,
          withScrutineeCount: auxDecl.withScrutineeCount,
          newScrutineeCount: auxDecl.newScrutineeCount,
          assumeK,
        },
      );
      remapWithClauseElabMap(
        result.compiled,
        sourceMap,
        auxDecl.withScrutineeCount ?? 0,
        auxDecl.newScrutineeCount ?? auxDecl.withScrutineeCount ?? 0,
      );
      result.compiled.isWithAuxiliary = true;
      compiledAuxiliaries.push(result.compiled);
      compiledDecls.push(result.compiled);

      if (result.success) {
        definitions = result.newDefinitions;
      } else {
        if (auxDecl.name) failedAuxNames.add(auxDecl.name);
        collectAuxiliaryErrorsForMain(
          auxDecl.name,
          mainDecl.name ?? '',
          result.compiled,
          auxErrorsForMain,
          auxElabMapForMain,
        );
      }
      checkErrorCount += result.errorCount;
    }

    if (mainDecl.kind === 'inductive') {
      const result = processInductiveDeclaration(mainDecl, sourceMap, definitions);
      compiledDecls.push(result.compiled);
      if (result.success) {
        definitions = result.newDefinitions;
        syncConstructorParamNames(constructorParamNames, result.compiled);
        if (options?.recheckZonkedTerms && result.compiled.kernelConstructors) {
          for (const ctor of result.compiled.kernelConstructors) {
            const recheckErr = recheckZonkedTerm(ctor.type, definitions, `${mainDecl.name}.${ctor.name} constructor type`);
            if (recheckErr) {
              appendZonkRecheckError(result.compiled, definitions, recheckErr);
              checkErrorCount++;
            }
          }
        }
      }
      checkErrorCount += result.errorCount;
      continue;
    }

    if (mainDecl.kind === 'record') {
      const result = processRecordDeclaration(mainDecl, sourceMap, definitions);
      compiledDecls.push(result.compiled);
      if (result.success) {
        definitions = result.newDefinitions;
        syncConstructorParamNames(constructorParamNames, result.compiled);
        if (options?.recheckZonkedTerms && result.compiled.kernelConstructors) {
          for (const ctor of result.compiled.kernelConstructors) {
            const recheckErr = recheckZonkedTerm(ctor.type, definitions, `${mainDecl.name}.${ctor.name} constructor type`);
            if (recheckErr) {
              appendZonkRecheckError(result.compiled, definitions, recheckErr);
              checkErrorCount++;
            }
          }
        }
      }
      checkErrorCount += result.errorCount;
      continue;
    }

    const result = processTermDeclaration(
      mainDecl,
      sourceMap,
      definitions,
      elaborateTacticBlock,
      { assumeK },
    );
    if (auxiliaryDecls.length > 0) {
      remapWithScrutineeInMainElabMap(result.compiled, sourceMap);
      for (const auxCompiled of compiledAuxiliaries) {
        mergeAuxTypeInfoIntoMain(result.compiled, auxCompiled);
      }
    }
    if (failedAuxNames.size > 0) {
      const originalCount = result.compiled.checkErrors.length;
      result.compiled.checkErrors = result.compiled.checkErrors.filter(err => {
        for (const auxName of failedAuxNames) {
          if (err.message.includes(`Type definition not found: ${auxName}`)) return false;
        }
        return true;
      });
      checkErrorCount -= (originalCount - result.compiled.checkErrors.length);
    }
    if (auxErrorsForMain.length > 0) {
      result.compiled.withClauseErrors = auxErrorsForMain;
      if (auxElabMapForMain.size > 0) {
        result.compiled.withClauseElabMap = auxElabMapForMain;
      }
    }
    compiledDecls.push(result.compiled);
    if (result.success) {
      definitions = result.newDefinitions;
      if (options?.recheckZonkedTerms && result.compiled.kernelType) {
        const recheckErr = recheckZonkedTerm(result.compiled.kernelType, definitions, `${mainDecl.name} type signature`);
        if (recheckErr) {
          appendZonkRecheckError(result.compiled, definitions, recheckErr);
          checkErrorCount++;
        }
      }
      if (options?.recheckZonkedTerms && result.compiled.kernelValue) {
        const recheckErr = recheckZonkedTerm(result.compiled.kernelValue, definitions, `${mainDecl.name} value`);
        if (recheckErr) {
          appendZonkRecheckError(result.compiled, definitions, recheckErr);
          checkErrorCount++;
        }
      }
    }
    checkErrorCount += result.errorCount;
  }

  return {
    compiled: {
      blockIndex,
      sourceLines: block.sourceLines,
      startLine: block.startLine,
      codeStartLine: computeCodeStartLine(block.sourceLines, block.startLine),
      parseSuccess: true,
      parseErrors: [],
      nameResolutionSuccess: blockNameErrors.length === 0,
      nameResolutionErrors: blockNameErrors,
      declarations: compiledDecls,
      isComment: false,
    },
    newDefinitions: definitions,
    newSymbolContext: symbolContext,
    newConstructorParamNames: constructorParamNames,
    checkErrorCount,
    nameErrorCount,
  };
}
