import { arraySeg, fieldSeg, IndexPath, IndexPathSegment } from "../types/source-position";
import { mkConst, mkProp, TTKClause, TTKContext, TTKPattern, TTKTerm } from "../types/tt-kernel";
import { TypeCheckError } from "./checker";

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

export type Signature = { name: string, type: TTKTerm, value?: TTKTerm }[];

export type MetaVarState =
  | { tag: 'unsolved' }
  | { tag: 'solved', term: TTKTerm }
  | { tag: 'guarded', term: TTKTerm, constraints: Constraint[] }

export type MetaVar = {
  ctx: Signature,
  type: TTKTerm,
  state: MetaVarState
}

export type TCEnv = {
  signature: Signature,
  definitions: DefinitionsMap,
  metaVars: Map<string, MetaVar>,
}

export function createTCEnv(definitions?: DefinitionsMap, signature?: Signature, metaVars?: Map<string, MetaVar>): TCEnv {
  return {
    signature: signature ?? [],
    definitions: definitions ?? createDefinitionsMap(),
    metaVars: metaVars ?? new Map<string, MetaVar>(),
  }
}

export function updateSignatureInTCEnv(env: TCEnv, fn: (s: Signature) => Signature): TCEnv {
  return {
    ...env,
    signature: fn(env.signature),
  }
}

export function extendSignatureInTCEnv(env: TCEnv, name: string, type: TTKTerm, value?: TTKTerm): TCEnv {
  return updateSignatureInTCEnv(env, (s) => [...s, { name, type, value }]);
}

export function updateDefinitionsInTCEnv(env: TCEnv, fn: (d: DefinitionsMap) => DefinitionsMap): TCEnv {
  return {
    ...env,
    definitions: fn(env.definitions),
  }
}

export function addDefinitionInTCEnv(env: TCEnv, name: string, type: TTKTerm): TCEnv {
  return updateDefinitionsInTCEnv(env, (d) => addDefinition(d, name, type));
}

export function addInductiveDefinitionInTCEnv(env: TCEnv, name: string, type: TTKTerm, constructors: Array<{ name: string; type: TTKTerm }>, indexPositions: number[]): TCEnv {
  return updateDefinitionsInTCEnv(env, (d) => addInductiveDefinition(d, name, type, constructors, indexPositions));
}

export function updateMetaVarsInTCEnv(env: TCEnv, fn: (m: Map<string, MetaVar>) => Map<string, MetaVar>): TCEnv {
  return {
    ...env,
    metaVars: fn(env.metaVars),
  }
}

export function addMetaVarInTCEnv(env: TCEnv, name: string, type: TTKTerm, value?: TTKTerm): TCEnv {
  return updateMetaVarsInTCEnv(env, (m) => m.set(name, { ctx: env.signature, type, state: { tag: 'unsolved' } }));
}

export type InductiveDefinition = {
  name: string,
  type: TTKTerm,
  constructors: Array<{ name: string; type: TTKTerm }>,
  indexPositions: number[],
}

export type TermDefinition = {
  name: string,
  type: TTKTerm,
  value?: TTKTerm,
}

export type DefinitionsMap = {
  terms: Map<string, TermDefinition>,
  inductiveTypes: Map<string, InductiveDefinition>
}

export function createDefinitionsMap(): DefinitionsMap {
  return {
    terms: new Map<string, TermDefinition>(),
    inductiveTypes: new Map<string, InductiveDefinition>(),
  };
}

export function addDefinition(definitions: DefinitionsMap, name: string, type: TTKTerm, value?: TTKTerm): DefinitionsMap {
  const newMap = new Map<string, TermDefinition>(definitions.terms);
  newMap.set(name, { name, type, value });
  return {
    ...definitions,
    terms: newMap,
  };
}

export function addInductiveDefinition(definitions: DefinitionsMap, name: string, type: TTKTerm, constructors: Array<{ name: string; type: TTKTerm }>, indexPositions: number[]): DefinitionsMap {
  const newMap = new Map<string, InductiveDefinition>(definitions.inductiveTypes);
  newMap.set(name, { name, type, constructors, indexPositions: indexPositions ?? [] });
  return { ...definitions, inductiveTypes: newMap };
}

export function getTypeDefinition(definitions: DefinitionsMap, name: string) {
  return definitions.terms.get(name)?.type;
}

export function getTermDefinition(definitions: DefinitionsMap, name: string) {
  return definitions.terms.get(name);
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

export function transformVarsInTerm(term: TTKTerm, transform: (varIndex: number, signature: Signature) => TTKTerm): TTKTerm {
  return transformVarsInTermAcc(term, transform, []);
}

function transformVarsInTermAcc(term: TTKTerm, transform: (varIndex: number, signature: Signature) => TTKTerm, signature: Signature): TTKTerm {
  if (term.tag === 'Var') {
    return transform(term.index, signature);
  } else if (term.tag === 'Binder') {
    const bodySignature = [...signature, { name: term.name, type: term.domain }];
    return { tag: 'Binder', name: term.name, binderKind: term.binderKind, domain: transformVarsInTermAcc(term.domain, transform, signature), body: transformVarsInTermAcc(term.body, transform, bodySignature) };
  } else if (term.tag === 'App') {
    return { tag: 'App', fn: transformVarsInTermAcc(term.fn, transform, signature), arg: transformVarsInTermAcc(term.arg, transform, signature) };
  } else if (term.tag === 'Const') {
    return { tag: 'Const', name: term.name, type: transformVarsInTermAcc(term.type, transform, signature) };
  } else if (term.tag === 'Sort') {
    return { tag: 'Sort', level: term.level };
  } else if (term.tag === 'Hole') {
    return { tag: 'Hole', id: term.id, type: transformVarsInTermAcc(term.type, transform, signature), context: term.context };
  } else if (term.tag === 'Annot') {
    return { tag: 'Annot', term: transformVarsInTermAcc(term.term, transform, signature), type: transformVarsInTermAcc(term.type, transform, signature) };
  } else if (term.tag === 'Match') {
    return { tag: 'Match', scrutinee: transformVarsInTermAcc(term.scrutinee, transform, signature), clauses: term.clauses.map(c => ({ patterns: c.patterns, rhs: transformVarsInTermAcc(c.rhs, transform, signature) })) };
  }

  const _never: never = term
  throw new Error(`Unexpected tag: ${(term as { tag: string }).tag}`);
}

export const MatchPartIndex = {
  Scrutinee: fieldSeg('scrutinee'),
  Clauses: fieldSeg('clauses'),
  ClausePatterns: fieldSeg('patterns'),
} satisfies Record<string, IndexPathSegment>;

export const MatchClausePartIndex = {
  Patterns: fieldSeg('patterns'),
  Rhs: fieldSeg('rhs'),
} satisfies Record<string, IndexPathSegment>;

export const AppPartIndex = {
  Fn: fieldSeg('fn'),
  Arg: fieldSeg('arg'),
} satisfies Record<string, IndexPathSegment>;

export const AnnotPartIndex = {
  Term: fieldSeg('term'),
  Type: fieldSeg('type'),
} satisfies Record<string, IndexPathSegment>;

export const BinderPartSegment = {
  Name: fieldSeg('name'),
  Domain: fieldSeg('domain'),
  Body: fieldSeg('body'),
  Value: fieldSeg('value'),
} satisfies Record<string, IndexPathSegment>;

export const InductiveDefinitionPartIndex = {
  Name: fieldSeg('name'),
  Type: fieldSeg('type'),
  Constructors: fieldSeg('constructors'),
  ConstructorName: fieldSeg('name'),
  ConstructorType: fieldSeg('type'),
} satisfies Record<string, IndexPathSegment>;

export const TermDefinitionPartIndex = {
  Name: fieldSeg('name'),
  Type: fieldSeg('type'),
  Value: fieldSeg('value'),
} satisfies Record<string, IndexPathSegment>;

class TCEnv2<T> {
  constructor(
    public readonly signature: Signature,
    public readonly definitions: DefinitionsMap,
    public readonly metaVars: Map<string, MetaVar>,
    public readonly indexPath: IndexPath,
    public readonly valueStack: unknown[],
    public readonly value: T
  ) {
  }

  withTermDefinition(this: TCEnv2<TTKTerm>, name: string, type: TTKTerm, value?: TTKTerm): TCEnv2<TTKTerm> {
    return new TCEnv2(
      this.signature,
      addDefinition(this.definitions, name, type, value),
      this.metaVars,
      this.indexPath,
      this.valueStack,
      this.value
    );
  }

  withInductiveDefinition(this: TCEnv2<TTKTerm>, name: string, type: TTKTerm, constructors: Array<{ name: string; type: TTKTerm }>, indexPositions: number[]): TCEnv2<TTKTerm> {
    return new TCEnv2(
      this.signature,
      addInductiveDefinition(this.definitions, name, type, constructors, indexPositions),
      this.metaVars,
      this.indexPath,
      this.valueStack,
      this.value
    );
  }

  withUnsolvedMetaVar(this: TCEnv2<TTKTerm>, name: string, type: TTKTerm): TCEnv2<TTKTerm> {
    const newMetaVars = new Map<string, MetaVar>(this.metaVars);
    newMetaVars.set(name, { ctx: this.signature, type, state: { tag: 'unsolved' } });
    return new TCEnv2(this.signature, this.definitions, newMetaVars, this.indexPath, this.valueStack, this.value);
  }

  // Match
  inMatchScrutinee(this: TCEnv2<TTKTerm & { tag: 'Match' }>): TCEnv2<TTKTerm> {
    return new TCEnv2(
      this.signature,
      this.definitions,
      this.metaVars,
      [...this.indexPath, MatchPartIndex.Scrutinee],
      [...this.valueStack, this.value],
      this.value.scrutinee
    );
  }

  inMatchClauses(this: TCEnv2<TTKTerm & { tag: 'Match' }>): TCEnv2<TTKClause[]> {
    return new TCEnv2(
      this.signature,
      this.definitions,
      this.metaVars,
      [...this.indexPath, MatchPartIndex.Clauses],
      [...this.valueStack, this.value],
      this.value.clauses
    );
  }

  inMatchClause(this: TCEnv2<TTKClause[]>, clauseIndex: number): TCEnv2<TTKClause> {
    if (clauseIndex < 0 || clauseIndex >= this.value.length || !Number.isInteger(clauseIndex)) {
      throw this.invalidIndexError('clauses', this.value, clauseIndex);
    }

    return new TCEnv2(
      this.signature,
      this.definitions,
      this.metaVars,
      [...this.indexPath, arraySeg(clauseIndex)],
      [...this.valueStack, this.value],
      this.value[clauseIndex]
    );
  }

  inMatchClausePatterns(this: TCEnv2<TTKClause>): TCEnv2<TTKPattern[]> {
    return new TCEnv2(
      this.signature,
      this.definitions,
      this.metaVars,
      [...this.indexPath, MatchClausePartIndex.Patterns],
      [...this.valueStack, this.value],
      this.value.patterns
    );
  }

  inMatchClausePattern(this: TCEnv2<TTKPattern[]>, patternIndex: number): TCEnv2<TTKPattern> {
    if (patternIndex < 0 || patternIndex >= this.value.length || !Number.isInteger(patternIndex)) {
      throw this.invalidIndexError('patterns', this.value, patternIndex);
    }

    return new TCEnv2(
      this.signature,
      this.definitions,
      this.metaVars,
      [...this.indexPath, MatchClausePartIndex.Patterns, arraySeg(patternIndex)],
      [...this.valueStack, this.value],
      this.value[patternIndex]
    );
  }

  inMatchClauseRhs(this: TCEnv2<TTKClause>): TCEnv2<TTKTerm> {
    return new TCEnv2(
      this.signature,
      this.definitions,
      this.metaVars,
      [...this.indexPath, MatchClausePartIndex.Rhs],
      [...this.valueStack, this.value],
      this.value.rhs
    );
  }

  inMatchClauseCtorPatterns(this: TCEnv2<TTKPattern & { tag: 'PCtor' }>): TCEnv2<TTKPattern[]> {
    return new TCEnv2(
      this.signature,
      this.definitions,
      this.metaVars,
      [...this.indexPath, MatchClausePartIndex.Patterns],
      [...this.valueStack, this.value],
      this.value.args
    );
  }

  // App
  inAppFn(this: TCEnv2<TTKTerm & { tag: 'App' }>): TCEnv2<TTKTerm> {
    return new TCEnv2(
      this.signature,
      this.definitions,
      this.metaVars,
      [...this.indexPath, AppPartIndex.Fn],
      [...this.valueStack, this.value],
      this.value.fn
    );
  }

  inAppArg(this: TCEnv2<TTKTerm & { tag: 'App' }>): TCEnv2<TTKTerm> {
    return new TCEnv2(
      this.signature,
      this.definitions,
      this.metaVars,
      [...this.indexPath, AppPartIndex.Arg],
      [...this.valueStack, this.value],
      this.value.arg
    );
  }

  // Annot
  inAnnotTerm(this: TCEnv2<TTKTerm & { tag: 'Annot' }>): TCEnv2<TTKTerm> {
    return new TCEnv2(
      this.signature,
      this.definitions,
      this.metaVars,
      [...this.indexPath, AnnotPartIndex.Term],
      [...this.valueStack, this.value],
      this.value.term
    );
  }

  inAnnotType(this: TCEnv2<TTKTerm & { tag: 'Annot' }>): TCEnv2<TTKTerm> {
    return new TCEnv2(
      this.signature,
      this.definitions,
      this.metaVars,
      [...this.indexPath, AnnotPartIndex.Type],
      [...this.valueStack, this.value],
      this.value.type
    );
  }

  // Binder Pi
  inBinderPiName(this: TCEnv2<TTKTerm & { tag: 'Binder' } & { binderKind: { tag: 'BPi' } }>): TCEnv2<string> {
    return new TCEnv2(
      this.signature,
      this.definitions,
      this.metaVars,
      [...this.indexPath, BinderPartSegment.Name],
      [...this.valueStack, this.value],
      this.value.name
    );
  }

  inBinderPiDomain(this: TCEnv2<TTKTerm & { tag: 'Binder' } & { binderKind: { tag: 'BPi' } }>): TCEnv2<TTKTerm> {
    return new TCEnv2(
      this.signature,
      this.definitions,
      this.metaVars,
      [...this.indexPath, BinderPartSegment.Domain],
      [...this.valueStack, this.value],
      this.value.domain
    );
  }

  inBinderPiBody(this: TCEnv2<TTKTerm & { tag: 'Binder' } & { binderKind: { tag: 'BPi' } }>): TCEnv2<TTKTerm> {
    return new TCEnv2(
      [...this.signature, { name: this.value.name, type: this.value.domain }],
      this.definitions,
      this.metaVars,
      [...this.indexPath, BinderPartSegment.Body],
      [...this.valueStack, this.value],
      this.value.body
    );
  }

  // Binder Lambda
  inBinderLambdaName(this: TCEnv2<TTKTerm & { tag: 'Binder' } & { binderKind: { tag: 'BLam' } }>): TCEnv2<string> {
    return new TCEnv2(
      this.signature,
      this.definitions,
      this.metaVars,
      [...this.indexPath, BinderPartSegment.Name],
      [...this.valueStack, this.value],
      this.value.name
    );
  }

  inBinderLambdaDomain(this: TCEnv2<TTKTerm & { tag: 'Binder' } & { binderKind: { tag: 'BLam' } }>): TCEnv2<TTKTerm> {
    return new TCEnv2(
      this.signature,
      this.definitions,
      this.metaVars,
      [...this.indexPath, BinderPartSegment.Domain],
      [...this.valueStack, this.value],
      this.value.domain
    );
  }

  inBinderLambdaBody(this: TCEnv2<TTKTerm & { tag: 'Binder' } & { binderKind: { tag: 'BLam' } }>): TCEnv2<TTKTerm> {
    return new TCEnv2(
      [...this.signature, { name: this.value.name, type: this.value.domain }],
      this.definitions,
      this.metaVars,
      [...this.indexPath, BinderPartSegment.Body],
      [...this.valueStack, this.value],
      this.value.body
    );
  }

  // Binder Let
  inBinderLetName(this: TCEnv2<TTKTerm & { tag: 'Binder' } & { binderKind: { tag: 'BLet' } }>): TCEnv2<string> {
    return new TCEnv2(
      this.signature,
      this.definitions,
      this.metaVars,
      [...this.indexPath, BinderPartSegment.Name],
      [...this.valueStack, this.value],
      this.value.name
    );
  }

  inBinderLetDomain(this: TCEnv2<TTKTerm & { tag: 'Binder' } & { binderKind: { tag: 'BLet' } }>): TCEnv2<TTKTerm> {
    return new TCEnv2(
      this.signature,
      this.definitions,
      this.metaVars,
      [...this.indexPath, BinderPartSegment.Domain],
      [...this.valueStack, this.value],
      this.value.domain
    );
  }

  inBinderLetBody(this: TCEnv2<TTKTerm & { tag: 'Binder' } & { binderKind: { tag: 'BLet' } }>): TCEnv2<TTKTerm> {
    return new TCEnv2(
      [...this.signature, { name: this.value.name, type: this.value.domain }],
      this.definitions,
      this.metaVars,
      [...this.indexPath, BinderPartSegment.Body],
      [...this.valueStack, this.value],
      this.value.body
    );
  }

  inBinderLetValue(this: TCEnv2<TTKTerm & { tag: 'Binder' } & { binderKind: { tag: 'BLet' } }>): TCEnv2<TTKTerm> {
    return new TCEnv2(
      this.signature,
      this.definitions,
      this.metaVars,
      [...this.indexPath, BinderPartSegment.Value],
      [...this.valueStack, this.value],
      this.value.binderKind.defVal
    );
  }

  // Inductive Definition
  inInductiveDefinitionName(this: TCEnv2<InductiveDefinition>): TCEnv2<string> {
    return new TCEnv2(
      this.signature,
      this.definitions,
      this.metaVars,
      [...this.indexPath, InductiveDefinitionPartIndex.Name],
      [...this.valueStack, this.value],
      this.value.name
    );
  }

  inInductiveDefinitionType(this: TCEnv2<InductiveDefinition>): TCEnv2<TTKTerm> {
    return new TCEnv2(
      this.signature,
      this.definitions,
      this.metaVars,
      [...this.indexPath, InductiveDefinitionPartIndex.Type],
      [...this.valueStack, this.value],
      this.value.type
    );
  }

  inInductiveDefinitionConstructors(this: TCEnv2<InductiveDefinition>): TCEnv2<Array<{ name: string; type: TTKTerm }>> {
    return new TCEnv2(
      this.signature,
      this.definitions,
      this.metaVars,
      [...this.indexPath, InductiveDefinitionPartIndex.Constructors],
      [...this.valueStack, this.value],
      this.value.constructors
    );
  }

  inInductiveDefinitionConstructorName(this: TCEnv2<Array<{ name: string; type: TTKTerm }>>, constructorIndex: number): TCEnv2<string> {
    if (constructorIndex < 0 || constructorIndex >= this.value.length || !Number.isInteger(constructorIndex)) {
      throw this.invalidIndexError('constructors', this.value, constructorIndex);
    }

    return new TCEnv2(
      this.signature,
      this.definitions,
      this.metaVars,
      [...this.indexPath, arraySeg(constructorIndex), InductiveDefinitionPartIndex.ConstructorName],
      [...this.valueStack, this.value],
      this.value[constructorIndex].name
    );
  }

  inInductiveDefinitionConstructorType(this: TCEnv2<Array<{ name: string; type: TTKTerm }>>, constructorIndex: number): TCEnv2<TTKTerm> {
    if (constructorIndex < 0 || constructorIndex >= this.value.length || !Number.isInteger(constructorIndex)) {
      throw this.invalidIndexError('constructors', this.value, constructorIndex);
    }

    return new TCEnv2(
      this.signature,
      this.definitions,
      this.metaVars,
      [...this.indexPath, arraySeg(constructorIndex), InductiveDefinitionPartIndex.ConstructorType],
      [...this.valueStack, this.value],
      this.value[constructorIndex].type
    );
  }

  // PRIVATE HELPERS
  private invalidIndexError<S>(field: string, values: S[], index: number): TCEnvError<T> {
    return new TCEnvError<T>(`Invalid index ${index} for ${field} with length ${values.length}.`, this);
  }
}

export class TCEnvError<T> {
  constructor(
    public readonly message: string,
    public readonly env: TCEnv2<T>
  ) { }
}