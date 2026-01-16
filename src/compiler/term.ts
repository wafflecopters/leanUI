import { IndexPath } from "../types/source-position";
import { TTKContext, TTKTerm } from "../types/tt-kernel";

export type Constraint = {
  tag: 'TypeEq';
  lhs: TTKTerm;
  rhs: TTKTerm;
  description?: string;
} | {
  tag: 'TermEq';
  lhs: TTKTerm;
  rhs: TTKTerm;
  type: TTKTerm;
  description?: string;
}

export interface CheckError {
  message: string;
  path: IndexPath;  // Location in the AST where error occurred
  term?: TTKTerm;
  context?: TTKContext;
  definitions?: DefinitionsMap;
  expected?: TTKTerm;
  actual?: TTKTerm;
}

export type Signature = { name: string, type: TTKTerm, guardedConstant?: { value: TTKTerm, guards: Constraint[] } }[];

export type InductiveDefinition = {
  type: TTKTerm,
  constructors: Array<{ name: string; type: TTKTerm }>,
  indexPositions: number[],
}

export type DefinitionsMap = {
  types: Map<string, TTKTerm>,
  inductiveTypes: Map<string, InductiveDefinition>
}

export function createDefinitionsMap(): DefinitionsMap {
  return {
    types: new Map<string, TTKTerm>(),
    inductiveTypes: new Map<string, InductiveDefinition>(),
  };
}

export function addDefinition(definitions: DefinitionsMap, name: string, type: TTKTerm): DefinitionsMap {
  const newMap = new Map<string, TTKTerm>(definitions.types);
  newMap.set(name, type);
  return {
    ...definitions,
    types: newMap,
  };
}

export function addInductiveDefinition(definitions: DefinitionsMap, name: string, type: TTKTerm, constructors: Array<{ name: string; type: TTKTerm }>, indexPositions: number[]): DefinitionsMap {
  const newMap = new Map<string, InductiveDefinition>(definitions.inductiveTypes);
  newMap.set(name, { type, constructors, indexPositions: indexPositions ?? [] });
  return { ...definitions, inductiveTypes: newMap };
}

export function getTypeDefinition(definitions: DefinitionsMap, name: string) {
  return definitions.types.get(name);
}

export type PiSpine = { binders: Signature, body: TTKTerm, term: TTKTerm };
export type AppSpine = { fn: TTKTerm, args: TTKTerm[] };

export function signatureToNamesStack(signature: Signature): string[] {
  return signature.map(n => n.name).reverse()
}

export function extractPiSpine(term: TTKTerm): PiSpine {
  const binders: Signature = [];
  let current = term;
  while (current.tag === 'Binder' && current.binderKind.tag === 'BPi') {
    binders.push({ name: current.name, type: current.domain });
    current = current.body;
  }
  return { binders, body: current, term };
}

export function extractAppSpine(term: TTKTerm): AppSpine {
  const args: TTKTerm[] = [];
  let current = term;
  while (current.tag === 'App') {
    args.unshift(current.arg);
    current = current.fn;
  }
  return { fn: current, args };
}