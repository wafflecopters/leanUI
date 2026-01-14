export class TypeCheckError extends Error {
  constructor(message: string, public term?: TTKTerm, public signature?: Signature, public termPath?: IndexPath, public definitions?: DefinitionsMap) {
    super(message);
    this.name = 'TypeCheckError';
  }
}

// INFERENCE

import { arraySeg, IndexPath } from "../types/source-position"
import { shiftTerm, TTKTerm } from "../types/tt-kernel"
import { DefinitionsMap, Signature } from "./term";

function inferBinderType(term: TTKTerm & { tag: 'Binder' }, path: IndexPath, signature: Signature, _definitions: DefinitionsMap): TTKTerm {
  if (term.binderKind.tag === 'BPi') {
    const domResult = inferType(term.domain, [...path, arraySeg(0)], signature, _definitions)
    const bodyResult = inferType(term.body, [...path, arraySeg(1)], [...signature, { name: term.name, type: term.domain }], _definitions)

    return maxSort(domResult, bodyResult)
  }
  debugger
  throw new Error('Not implemented')
}

export function inferType(term: TTKTerm, path: IndexPath, signature: Signature, definitions: DefinitionsMap): TTKTerm {
  if (term.tag === 'Const') {
    const type = definitions.get(term.name)
    if (!type) {
      throw new TypeCheckError(`Constant '${term.name}' not found in definitions`, term, [], path, definitions)
    }
    return type
  } else if (term.tag === 'Binder') {
    return inferBinderType(term, path, signature, definitions)
  } else if (term.tag === 'Sort') {
    return { tag: 'Sort', level: term.level + 1 }
  } else if (term.tag === 'Var') {
    return lookupTypeAtIndexSignature(signature, term.index)
  } else if (term.tag === 'App') {
    const fnResult = inferType(term.fn, path, signature, definitions)
    const argResult = inferType(term.arg, path, signature, definitions)

    debugger
    return { tag: 'App', fn: fnResult, arg: argResult }
  }
  debugger
  throw new Error('Not implemented')
}

// CHECKING

export function checkType(_term: TTKTerm, _expectedType: TTKTerm, _path: IndexPath, _signature: Signature, _definitions: DefinitionsMap): void {
  debugger
  throw new Error('Not implemented')
}

// Helpers

function maxSort(lhs: TTKTerm, rhs: TTKTerm): TTKTerm {
  if (lhs.tag === 'Sort' && rhs.tag === 'Sort') {
    return { tag: 'Sort', level: Math.max(lhs.level, rhs.level) }
  }
  debugger
  throw new Error('Not implemented')
}

export function lookupTypeAtIndexSignature(signature: Signature, index: number): TTKTerm {
  const binder = signature[index];
  if (!binder) {
    debugger
    throw new TypeCheckError(`Type index ${index} not found in signature`)
  }
  const type = binder.type;

  // Shift indices to be at tail of signature
  // The type at position `index` needs to be shifted by (signature.length - 1 - index)
  // to move it to the tail position
  const shiftAmount = signature.length - 1 - index;
  return shiftAmount > 0 ? shiftTerm(type, shiftAmount, 0) : type;
}