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

export type DefinitionsMap = Map<string, TTKTerm>

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