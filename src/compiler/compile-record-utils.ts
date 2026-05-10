import { arraySeg, appendPath, fieldSeg, type ElabMap } from '../types/source-position';
import { mkPi, type TTKRecordField, type TTKRecordParam, type TTKTerm } from './kernel';
import { mkAppTT, mkConstTT, mkPiTT, mkTypeTT, mkVarTT, type TTerm } from './surface';

export function extractZonkedFieldTypes(
  ctorType: TTKTerm,
  numParams: number,
  origFields: TTKRecordField[]
): TTKRecordField[] {
  let current = ctorType;

  for (let i = 0; i < numParams; i++) {
    if (current.tag !== 'Binder') {
      return origFields;
    }
    current = current.body;
  }

  const zonkedFields: TTKRecordField[] = [];
  for (let i = 0; i < origFields.length; i++) {
    if (current.tag !== 'Binder') {
      break;
    }
    zonkedFields.push({
      name: origFields[i].name,
      type: current.domain,
      implicit: origFields[i].implicit,
    });
    current = current.body;
  }

  return zonkedFields.length === origFields.length ? zonkedFields : origFields;
}

export function buildRecordTypeFromParams(params: TTKRecordParam[], resultSort: TTKTerm): TTKTerm {
  let result: TTKTerm = resultSort;
  for (let i = params.length - 1; i >= 0; i--) {
    result = mkPi(params[i].type, result, params[i].name);
  }
  return result;
}

export function buildSurfaceRecordType(params: Array<{ name: string; type: TTerm }>): TTerm {
  let result: TTerm = mkTypeTT(0);
  for (let i = params.length - 1; i >= 0; i--) {
    result = mkPiTT(params[i].type, result, params[i].name);
  }
  return result;
}

export function buildSurfaceConstructorType(
  params: Array<{ name: string; type: TTerm }>,
  fields: Array<{ name: string; type: TTerm }>,
  recordName: string
): TTerm {
  let returnType: TTerm = mkConstTT(recordName);
  for (let i = 0; i < params.length; i++) {
    const paramIndex = fields.length + params.length - 1 - i;
    returnType = mkAppTT(returnType, mkVarTT(paramIndex));
  }

  let result = returnType;
  for (let i = fields.length - 1; i >= 0; i--) {
    result = mkPiTT(fields[i].type, result, fields[i].name);
  }
  for (let i = params.length - 1; i >= 0; i--) {
    result = mkPiTT(params[i].type, result, params[i].name);
  }

  return result;
}

export function addRecordCtorTypeElabMappings(
  elabMap: ElabMap,
  numParams: number,
  numFields: number
): void {
  const totalBinders = numParams + numFields;

  for (let i = 0; i < totalBinders; i++) {
    let kernelPath = 'constructors[0].type';
    for (let j = 0; j < i; j++) {
      kernelPath += '.body';
    }
    kernelPath += '.domain';

    let surfacePath: string;
    if (i < numParams) {
      surfacePath = `params[${i}].type`;
    } else {
      surfacePath = `fields[${i - numParams}].type`;
    }

    elabMap.set(kernelPath, surfacePath);
  }
}
