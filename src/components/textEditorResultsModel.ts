import type { CompileResult, CompiledDeclaration } from '../compiler/compile';
import type { TTKTerm } from '../compiler/kernel';
import { prettyPrint as prettyPrintTTK } from '../compiler/kernel';

export interface ParamIndexInfo {
  name: string;
  type: string;
  isIndex: boolean;
}

export interface DeclarationStatusSummary {
  kind: 'success' | 'error' | 'warning';
  text: string;
}

export function getCompileResultsErrorCount(
  compileResult: Pick<CompileResult, 'totalParseErrors' | 'totalNameErrors' | 'totalCheckErrors'>
): number {
  return compileResult.totalParseErrors + compileResult.totalNameErrors + compileResult.totalCheckErrors;
}

export function extractParamIndexInfo(
  kernelType: TTKTerm | undefined,
  indexPositions: number[] | undefined
): ParamIndexInfo[] {
  if (!kernelType) return [];

  const indexSet = new Set(indexPositions ?? []);
  const result: ParamIndexInfo[] = [];
  let current = kernelType;
  let position = 0;

  while (current.tag === 'Binder' && current.binderKind.tag === 'BPi') {
    result.push({
      name: current.name || '_',
      type: prettyPrintTTK(current.domain),
      isIndex: indexSet.has(position),
    });
    current = current.body;
    position++;
  }

  return result;
}

export function getDeclarationStatusSummary(
  declaration: Pick<CompiledDeclaration, 'checkSuccess' | 'checkErrors'>
): DeclarationStatusSummary {
  if (declaration.checkSuccess) {
    return { kind: 'success', text: 'OK' };
  }

  const errors = declaration.checkErrors?.filter(error => error.severity === 'error').length ?? 0;
  const warnings = declaration.checkErrors?.filter(error => error.severity === 'warning').length ?? 0;

  if (errors === 0 && warnings > 0) {
    return {
      kind: 'warning',
      text: `${warnings} warning${warnings !== 1 ? 's' : ''}`,
    };
  }

  if (errors === 0) {
    return { kind: 'error', text: 'FAIL' };
  }

  const warningSuffix = warnings > 0
    ? `, ${warnings} warning${warnings !== 1 ? 's' : ''}`
    : '';
  return {
    kind: 'error',
    text: `${errors} error${errors !== 1 ? 's' : ''}${warningSuffix}`,
  };
}
