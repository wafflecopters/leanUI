import type { ParsedDeclaration } from '../parser/parser';
import type { ElabMap, IndexPath, SourceMap } from '../types/source-position';
import {
  countParameters,
  elabToKernelWithMap,
  extractArgNamedArgInfos,
  extractNamedArgMap,
  type NamedArgMap,
} from './elab';
import type { TTKTerm } from './kernel';
import { createCompiledDeclaration, createElabErrorResult } from './compile-declaration-result';
import { checkInductiveDeclaration } from './inductive';
import type { ProcessDeclarationResult } from './compile-types';
import {
  createNamedArgInfoLookup,
  createTCEnv,
  TCEnvError,
  type DefinitionsMap,
  type NamedArgInfo,
} from './term';
import type { TypeInfoMap } from './type-info';

export function createCtorAppNamedArgLookup(
  decl: ParsedDeclaration,
  definitions: DefinitionsMap
): (name: string) => NamedArgInfo | undefined {
  const inductiveNamedArgMap = decl.type ? extractNamedArgMap(decl.type) : undefined;
  const inductiveTotalArity = decl.type ? countParameters(decl.type) : undefined;
  const inductiveArgNamedArgInfos = decl.type ? extractArgNamedArgInfos(decl.type) : undefined;
  const baseAppLookup = createNamedArgInfoLookup(definitions);

  return (name: string): NamedArgInfo | undefined => {
    if (decl.name && name === decl.name && inductiveNamedArgMap && inductiveNamedArgMap.size > 0) {
      return {
        namedArgMap: inductiveNamedArgMap,
        totalArity: inductiveTotalArity ?? 0,
        argNamedArgInfos: inductiveArgNamedArgInfos?.size ? inductiveArgNamedArgInfos : undefined,
      };
    }
    return baseAppLookup(name);
  };
}

export function processInductiveDeclaration(
  decl: ParsedDeclaration,
  sourceMap: SourceMap,
  definitions: DefinitionsMap,
): ProcessDeclarationResult {
  const elabMap: ElabMap = new Map();
  const typeInfoMap: TypeInfoMap = new Map();

  let kernelType: TTKTerm | undefined;
  if (decl.type) {
    try {
      const typePath: IndexPath = [{ kind: 'field', name: 'type' }];
      kernelType = elabToKernelWithMap(decl.type, elabMap, typePath, typePath);
    } catch (e) {
      return createElabErrorResult(e, decl, sourceMap, elabMap, definitions);
    }
  }

  const inductiveNamedArgMap = decl.type ? extractNamedArgMap(decl.type) : undefined;
  const ctorAppLookup = createCtorAppNamedArgLookup(decl, definitions);

  let kernelConstructors: Array<{ name: string; type: TTKTerm; namedArgMap?: NamedArgMap }> | undefined;
  if (decl.constructors) {
    kernelConstructors = [];
    for (let ctorIndex = 0; ctorIndex < decl.constructors.length; ctorIndex++) {
      const ctor = decl.constructors[ctorIndex];
      try {
        const ctorTypePath: IndexPath = [
          { kind: 'field', name: 'constructors' },
          { kind: 'array', index: ctorIndex },
          { kind: 'field', name: 'type' },
        ];
        const ctorKernelType = elabToKernelWithMap(
          ctor.type,
          elabMap,
          ctorTypePath,
          ctorTypePath,
          undefined,
          ctorAppLookup
        );
        const ctorNamedArgMap = extractNamedArgMap(ctor.type);
        kernelConstructors.push({
          name: ctor.name,
          type: ctorKernelType,
          namedArgMap: ctorNamedArgMap.size > 0 ? ctorNamedArgMap : undefined,
        });
      } catch (e) {
        return createElabErrorResult(e, decl, sourceMap, elabMap, definitions);
      }
    }
  }

  if (!kernelType || !kernelConstructors) {
    const env = createTCEnv({ definitions, options: { mode: 'check' } });
    const error = TCEnvError.create('Inductive type declaration is ill-formed', env);
    return {
      success: false,
      compiled: createCompiledDeclaration(
        decl,
        kernelType,
        undefined,
        kernelConstructors,
        elabMap,
        sourceMap,
        false,
        [error],
        undefined
      ),
      newDefinitions: definitions,
      errorCount: 1,
    };
  }

  const result = checkInductiveDeclaration(
    decl.name || 'anonymous',
    kernelType,
    kernelConstructors,
    definitions,
    inductiveNamedArgMap,
    undefined,
    typeInfoMap
  );
  const finalTypeInfoMap = typeInfoMap.size > 0 ? typeInfoMap : undefined;

  if (!result.success) {
    return {
      success: false,
      compiled: createCompiledDeclaration(
        decl,
        kernelType,
        undefined,
        kernelConstructors,
        elabMap,
        sourceMap,
        false,
        result.errors,
        undefined,
        undefined,
        undefined,
        undefined,
        undefined,
        undefined,
        undefined,
        undefined,
        undefined,
        finalTypeInfoMap
      ),
      newDefinitions: definitions,
      errorCount: result.errors.length,
    };
  }

  return {
    success: true,
    compiled: createCompiledDeclaration(
      decl,
      kernelType,
      undefined,
      result.zonkedConstructors,
      elabMap,
      sourceMap,
      true,
      [],
      result.newDefinitions,
      undefined,
      result.indexPositions,
      undefined,
      undefined,
      undefined,
      undefined,
      undefined,
      undefined,
      finalTypeInfoMap
    ),
    newDefinitions: result.newDefinitions,
    errorCount: 0,
  };
}
