import type { ParsedDeclaration } from '../parser/parser';
import type { ElabDeclaration } from './compile-types';
import { elabToKernelWithMap } from './elab';
import type { TTKTerm } from './kernel';
import { type ElabMap, type IndexPath, type SourceMap } from '../types/source-position';
import { createNamedArgInfoLookup, type DefinitionsMap } from './term';
import { resolveWithScrutineeTypes } from './compile-with-scrutinee-resolution';

export interface ElaboratedTermDeclaration {
  elabDecl: ElabDeclaration;
  kernelType?: TTKTerm;
  elabMap: ElabMap;
}

/**
 * Elaborate just enough of a parsed term declaration to hand it off to the
 * term-checking pipeline. Value elaboration still happens incrementally later.
 */
export function elaborateTermDeclaration(
  decl: ParsedDeclaration,
  sourceMap: SourceMap,
  definitions: DefinitionsMap,
): ElaboratedTermDeclaration {
  const elabMap: ElabMap = new Map();
  let kernelType: TTKTerm | undefined;

  if (decl.type) {
    let typeToElaborate = decl.type;
    if (decl.withScrutineeExprs && decl.withScrutineeExprs.length > 0) {
      typeToElaborate = resolveWithScrutineeTypes(
        decl.type,
        decl.withScrutineeExprs,
        definitions,
      );
    }

    const typePath: IndexPath = [{ kind: 'field', name: 'type' }];
    kernelType = elabToKernelWithMap(
      typeToElaborate,
      elabMap,
      typePath,
      typePath,
      undefined,
      createNamedArgInfoLookup(definitions),
    );
  }

  return {
    elabDecl: {
      name: decl.name,
      kind: 'term',
      surfaceType: decl.type,
      surfaceValue: decl.value,
      kernelType,
      isPostulate: decl.isPostulate,
      elabMap,
      sourceMap,
      syntax: decl.syntax,
      withScrutineeCount: decl.withScrutineeCount,
      newScrutineeCount: decl.newScrutineeCount,
      withScrutineeExprs: decl.withScrutineeExprs,
    },
    kernelType,
    elabMap,
  };
}
