import type { ParsedDeclaration } from '../parser/parser';
import type { ElabMap, SourceMap } from '../types/source-position';
import { deserializeIndexPath, serializeIndexPath } from '../types/source-position';
import { extractNamedArgMap, NamedArgElabError, type NamedArgMap } from './elab';
import type { TTKTerm } from './kernel';
import { prettyPrint as prettyPrintTTK, prettyPrintFormatted } from './kernel';
import { createNamedArgLookup, createTCEnv, TCEnvError, type DefinitionsMap } from './term';
import type { TTerm } from './surface';
import type { TypeInfoMap } from './type-info';
import type { TotalityResult } from './totality';
import type { TacticInfoTree } from '../tactics/info-tree';
import { TacticSession } from '../tactics/tactic-session';
import { tacticCommandsToProofTree } from '../proof-tree/tactic-to-tree';
import type { CompiledDeclaration, ProcessDeclarationResult } from './compile';

export function createCompiledDeclaration(
  decl: ParsedDeclaration,
  kernelType: TTKTerm | undefined,
  kernelValue: TTKTerm | undefined,
  kernelConstructors: Array<{ name: string; type: TTKTerm; namedArgMap?: NamedArgMap }> | undefined,
  elabMap: ElabMap,
  sourceMap: SourceMap,
  checkSuccess: boolean,
  checkErrors: TCEnvError[],
  definitions?: DefinitionsMap,
  totalityResult?: TotalityResult,
  indexPositions?: number[],
  elabErrorPath?: string,
  isRecord?: boolean,
  surfaceParams?: Array<{ name: string; type: TTerm }>,
  surfaceFields?: Array<{ name: string; type: TTerm }>,
  surfaceExtendsExprs?: TTerm[],
  prettyProjections?: Array<{ name: string; prettyType: string }>,
  typeInfoMap?: TypeInfoMap,
  tacticInfoTree?: TacticInfoTree,
): CompiledDeclaration {
  const namedArgLookup = definitions ? createNamedArgLookup(definitions) : undefined;
  const prettyPrintOptions = namedArgLookup ? { namedArgLookup } : {};
  const namedArgMap = decl.type ? extractNamedArgMap(decl.type) : undefined;

  return {
    name: decl.name,
    kind: decl.kind === 'inductive' ? 'inductive' : 'term',
    surfaceType: decl.type,
    surfaceValue: decl.originalSurfaceValue ?? decl.value,
    surfaceConstructors: decl.constructors,
    isRecord,
    surfaceParams,
    surfaceFields,
    surfaceExtendsExprs,
    kernelType,
    kernelValue,
    kernelConstructors,
    namedArgMap: namedArgMap && namedArgMap.size > 0 ? namedArgMap : undefined,
    indexPositions,
    prettyType: kernelType ? prettyPrintFormatted(kernelType, [], undefined, prettyPrintOptions) : undefined,
    prettyValue: kernelValue ? prettyPrintFormatted(kernelValue, [], undefined, prettyPrintOptions) : undefined,
    prettyConstructors: kernelConstructors?.map(c => ({
      name: c.name,
      prettyType: prettyPrintTTK(c.type),
    })),
    prettyProjections,
    checkSuccess,
    checkErrors,
    totalityResult,
    elabMap,
    sourceMap,
    elabErrorPath,
    withScrutineeCount: decl.withScrutineeCount,
    newScrutineeCount: decl.newScrutineeCount,
    withScrutineeExprs: decl.withScrutineeExprs,
    typeInfoMap,
    tacticInfoTree,
    tacticTrace: (() => {
      const sv = (decl.originalSurfaceValue ?? decl.value) as any;
      if (!checkSuccess || !kernelType || !sv || sv.tag !== 'TacticBlock') return undefined;
      try {
        const session = TacticSession.create(kernelType, definitions!);
        const final = session.applyCommands(sv.tactics);
        return final.trace.length > 0 ? [...final.trace] : undefined;
      } catch {
        return undefined;
      }
    })(),
    proofTree: (() => {
      const sv = (decl.originalSurfaceValue ?? decl.value) as any;
      if (!sv || sv.tag !== 'TacticBlock' || !sv.tactics || sv.tactics.length === 0) return undefined;
      try {
        return tacticCommandsToProofTree(sv.tactics);
      } catch {
        return undefined;
      }
    })(),
    syntax: decl.syntax,
    constructorSyntax: (() => {
      const constructorSyntax = decl.constructors
        ?.filter(ctor => ctor.syntax !== undefined)
        .map(ctor => ({ name: ctor.name, syntax: ctor.syntax! }));
      return constructorSyntax && constructorSyntax.length > 0 ? constructorSyntax : undefined;
    })(),
  };
}

export function createElabErrorResult(
  e: unknown,
  decl: ParsedDeclaration,
  sourceMap: SourceMap,
  elabMap: ElabMap,
  definitions: DefinitionsMap,
): ProcessDeclarationResult {
  const errorMessage = e instanceof Error ? e.message : String(e);
  const elabErrorPath = e instanceof NamedArgElabError && e.surfacePath
    ? serializeIndexPath(e.surfacePath)
    : undefined;
  const errorPath = elabErrorPath ? deserializeIndexPath(elabErrorPath) : [];
  const env = createTCEnv({ definitions, indexPath: errorPath, options: { mode: 'check' } });
  const error = TCEnvError.create(errorMessage, env);

  return {
    success: false,
    compiled: createCompiledDeclaration(
      decl,
      undefined,
      undefined,
      undefined,
      elabMap,
      sourceMap,
      false,
      [error],
      definitions,
      undefined,
      undefined,
      elabErrorPath,
      undefined
    ),
    newDefinitions: definitions,
    errorCount: 1,
  };
}
