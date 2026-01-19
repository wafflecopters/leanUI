import { arraySeg, fieldSeg, IndexPath, IndexPathSegment } from "../types/source-position";
import { prettyPrint, TTKClause, TTKContext, TTKPattern, TTKTerm } from "./kernel";
import { applySubstitutionToConstraints, applySubstitutionToContext, applySubstitutionToMetaVars, shiftTerm, subst } from "./subst";
import { areTypesDefEq } from "./whnf";

export interface CheckError {
  message: string;
  path: IndexPath;  // Location in the AST where error occurred
  term?: TTKTerm;
  context?: TTKContext;
  definitions?: DefinitionsMap;
  expected?: TTKTerm;
  actual?: TTKTerm;
}

export type Constraint = {
  ctx: Signature,
  meta: string,
  rhs: TTKTerm,
}


export type Signature = { name: string, type: TTKTerm, value?: TTKTerm }[];

export type MetaVar = {
  ctx: Signature,
  type: TTKTerm,
  solution?: TTKTerm
}

export function createTCEnv(definitions?: DefinitionsMap, signature?: Signature, metaVars?: Map<string, MetaVar>): TCEnv<null> {
  return new TCEnv(
    signature ?? [],
    definitions ?? createDefinitionsMap(),
    metaVars ?? new Map<string, MetaVar>(),
    [],
    [],
    [],
    null
  );
}

export function updateSignatureInTCEnv<T>(env: TCEnv<T>, fn: (s: Signature) => Signature): TCEnv<T> {
  return new TCEnv(
    fn(env.signature),
    env.definitions,
    env.metaVars,
    env.constraints,
    env.indexPath,
    env.valueStack,
    env.value
  );
}

export function extendSignatureInTCEnv<T>(env: TCEnv<T>, name: string, type: TTKTerm, value?: TTKTerm): TCEnv<T> {
  return updateSignatureInTCEnv(env, (s) => [...s, { name, type, value }]);
}

export function updateDefinitionsInTCEnv<T>(env: TCEnv<T>, fn: (d: DefinitionsMap) => DefinitionsMap): TCEnv<T> {
  return new TCEnv(
    env.signature,
    fn({ ...env.definitions }),
    env.metaVars,
    env.constraints,
    env.indexPath,
    env.valueStack,
    env.value
  );
}

export function addDefinitionInTCEnv<T>(env: TCEnv<T>, name: string, type: TTKTerm): TCEnv<T> {
  return updateDefinitionsInTCEnv(env, (d) => addDefinition(d, name, type));
}

export function setDefinitionValueInTCEnv<T>(env: TCEnv<T>, name: string, value: TTKTerm): TCEnv<T> {
  return updateDefinitionsInTCEnv(env, (d) => setDefinitionValue(d, name, value));
}

export function addInductiveDefinitionInTCEnv<T>(env: TCEnv<T>, name: string, type: TTKTerm, constructors: Array<{ name: string; type: TTKTerm }>, indexPositions: number[]): TCEnv<T> {
  return updateDefinitionsInTCEnv(env, (d) => addInductiveDefinition(d, name, type, constructors, indexPositions));
}

export function updateMetaVarsInTCEnv<T>(env: TCEnv<T>, fn: (m: Map<string, MetaVar>) => Map<string, MetaVar>): TCEnv<T> {
  return new TCEnv(
    env.signature,
    env.definitions,
    fn(new Map(env.metaVars)),
    env.constraints,
    env.indexPath,
    env.valueStack,
    env.value
  );
}

export function addMetaVarInTCEnv<T>(env: TCEnv<T>, type: TTKTerm): { env: TCEnv<T>, name: string } {
  const name = `?m${env.metaVars.size}`;

  return { env: updateMetaVarsInTCEnv(env, (m) => m.set(name, { ctx: env.signature, type })), name };
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

export function setDefinitionValue(definitions: DefinitionsMap, name: string, value: TTKTerm): DefinitionsMap {
  const newMap = new Map<string, TermDefinition>(definitions.terms);
  const existing = newMap.get(name);
  if (!existing) {
    debugger
    throw new Error(`Definition ${name} not found`);
  }
  newMap.set(name, { ...existing, value });
  return { ...definitions, terms: newMap };
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

export type PiSpine = { binders: Signature, body: TTKTerm, term?: TTKTerm };
export type AppSpine = { fn: TTKTerm, args: TTKTerm[] };

export function signatureToNamesStack(signature: Signature): string[] {
  return signature.map(n => n.name).reverse()
}

export function countPiBinders(term: TTKTerm): number {
  let count = 0;
  let current = term;
  while (current.tag === 'Binder' && current.binderKind.tag === 'BPi') {
    count++;
    current = current.body;
  }
  return count;
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

export const ClausePartIndex = {
  Patterns: fieldSeg('patterns'),
  Rhs: fieldSeg('rhs'),
} satisfies Record<string, IndexPathSegment>;

export const MatchClauseCtorPatternPartIndex = {
  Args: fieldSeg('args'),
} satisfies Record<string, IndexPathSegment>;

export const HolePartIndex = {
  Type: fieldSeg('type'),
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

export const TermPartIndex = {
  Name: fieldSeg('name'),
  Type: fieldSeg('type'),
  Value: fieldSeg('value'),
} satisfies Record<string, IndexPathSegment>;

export const TermDefinitionPartIndex = {
  Name: fieldSeg('name'),
  Type: fieldSeg('type'),
  Value: fieldSeg('value'),
} satisfies Record<string, IndexPathSegment>;

export function printCollectionFancy(items: string[], openBracket: string, closeBracket: string, separator: string, options?: { indentLevel?: number, prefixOpeningBracket?: boolean, innerIndentOffset?: number }): string {
  if (items.length === 0) {
    return openBracket + closeBracket;
  }
  if (items.length === 1) {
    return openBracket + items[0] + closeBracket;
  }
  const bracketPrefix = options?.indentLevel && items.length > 1 ? ' '.repeat(options.indentLevel) : '';
  const itemPrefix = options?.indentLevel && items.length > 1 ? ' '.repeat(options.indentLevel + (options.innerIndentOffset ?? 1)) : '';
  return `${options?.prefixOpeningBracket ? bracketPrefix : ''}${openBracket}\n${items.map(item => `${itemPrefix}${item}`).join(`${separator}\n`)}\n${bracketPrefix}${closeBracket}`;
}

export class TCEnv<T> {
  constructor(
    public readonly signature: Signature,
    public readonly definitions: DefinitionsMap,
    public readonly metaVars: Map<string, MetaVar>,
    public readonly constraints: Constraint[],
    public readonly indexPath: IndexPath,
    public readonly valueStack: unknown[],
    public readonly value: T
  ) {
  }

  hasConstraints(): this is TCEnv<T> & { constraints: Constraint[] } {
    return this.constraints.length > 0;
  }

  solveConstraints(): TCEnv<T> {
    if (!this.hasConstraints()) {
      return this;
    }

    debugger

    return this;
  }

  prettyPrint(term: TTKTerm): string {
    return prettyPrint(term, this.signature.map(s => s.name).reverse());
  }

  static printSignature(signature: Signature): string {
    return `{${signature.map((s, i) => {
      const sig = signature.slice(0, i)
      return `${s.name} : ${prettyPrint(s.type, sig.map(s => s.name).reverse())}`
    }).join(', ')}}`;
  }

  printSignature(): string {
    return TCEnv.printSignature(this.signature);
  }

  printMetas(options?: { indentLevel?: number, innerIndentOffset?: number }): string {
    const itemStrs = Array.from(this.metaVars.entries()).map(([name, meta]) => {
      return `${name} : ${TCEnv.printSignature(meta.ctx)} -> ${prettyPrint(meta.type, meta.ctx.map(s => s.name))}`
    })

    return printCollectionFancy(itemStrs, '{', '}', ',', options);
  }

  static printConstraint(constraint: Constraint): string {
    return `{ctx: ${TCEnv.printSignature(constraint.ctx)}, meta: ${constraint.meta}, rhs: ${prettyPrint(constraint.rhs)}}`
  }

  printConstraints(options?: { indentLevel?: number, innerIndentOffset?: number }): string {
    const itemStrs = this.constraints.map(TCEnv.printConstraint);
    return printCollectionFancy(itemStrs, '[', ']', ',', options);
  }

  applySubstitutionToContextMetasAndConstraints(varIndex: number, value: TTKTerm): TCEnv<T> {
    const newSignature = applySubstitutionToContext(this.signature, varIndex, value);
    const newMetaVars = applySubstitutionToMetaVars(this.metaVars, this.signature.length, varIndex, value);
    const newConstraints = applySubstitutionToConstraints(this.constraints, this.signature.length, varIndex, value);

    return new TCEnv(
      newSignature,
      this.definitions,
      newMetaVars,
      newConstraints,
      this.indexPath,
      this.valueStack,
      this.value
    );
  }

  hasDefinedValue(): this is TCEnv<NonNullable<T>> {
    return this.value !== undefined;
  }

  withoutValue(): TCEnv<void> {
    return new TCEnv(this.signature, this.definitions, this.metaVars, this.constraints, this.indexPath, this.valueStack, undefined);
  }

  withValue<S>(value: S): TCEnv<S> {
    return new TCEnv(this.signature, this.definitions, this.metaVars, this.constraints, this.indexPath, this.valueStack, value);
  }

  mapValue<S>(fn: (value: T) => S): TCEnv<S> {
    return this.withValue(fn(this.value));
  }

  atValueAndPathOfEnv<S>(otherEnv: TCEnv<S>): TCEnv<S> {
    return new TCEnv(this.signature, this.definitions, this.metaVars, this.constraints, otherEnv.indexPath, otherEnv.valueStack, otherEnv.value);
  }

  atIndexPath(indexPath: IndexPath): TCEnv<void> {
    return new TCEnv(this.signature, this.definitions, this.metaVars, this.constraints, indexPath, [], undefined);
  }

  // Terms

  extendSignature(name: string, type: TTKTerm, value?: TTKTerm): TCEnv<T> {
    return new TCEnv(
      [...this.signature, { name, type, value }],
      this.definitions,
      this.metaVars,
      this.constraints,
      this.indexPath,
      this.valueStack,
      this.value
    );
  }

  withConstraint(constraint: Omit<Constraint, 'ctx'>): TCEnv<T> {
    return new TCEnv(this.signature, this.definitions, this.metaVars, [...this.constraints, { ctx: this.signature, ...constraint }], this.indexPath, this.valueStack, this.value);
  }

  isAppTerm(this: TCEnv<TTKTerm>): this is TCEnv<TTKTerm & { tag: 'App' }> {
    return this.value.tag === 'App';
  }

  isBinderTerm(this: TCEnv<TTKTerm>): this is TCEnv<TTKTerm & { tag: 'Binder' }> {
    return this.value.tag === 'Binder';
  }

  isBinderPiTerm(this: TCEnv<TTKTerm>): this is TCEnv<TTKTerm & { tag: 'Binder' } & { binderKind: { tag: 'BPi' } }> {
    return this.value.tag === 'Binder' && this.value.binderKind.tag === 'BPi';
  }

  isBinderLambdaTerm(this: TCEnv<TTKTerm>): this is TCEnv<TTKTerm & { tag: 'Binder' } & { binderKind: { tag: 'BLam' } }> {
    return this.value.tag === 'Binder' && this.value.binderKind.tag === 'BLam';
  }

  isBinderLetTerm(this: TCEnv<TTKTerm>): this is TCEnv<TTKTerm & { tag: 'Binder' } & { binderKind: { tag: 'BLet' } }> {
    return this.value.tag === 'Binder' && this.value.binderKind.tag === 'BLet';
  }

  isMatchTerm(this: TCEnv<TTKTerm>): this is TCEnv<TTKTerm & { tag: 'Match' }> {
    return this.value.tag === 'Match';
  }

  isAnnotTerm(this: TCEnv<TTKTerm>): this is TCEnv<TTKTerm & { tag: 'Annot' }> {
    return this.value.tag === 'Annot';
  }

  isHoleTerm(this: TCEnv<TTKTerm>): this is TCEnv<TTKTerm & { tag: 'Hole' }> {
    return this.value.tag === 'Hole';
  }

  isConstTerm(this: TCEnv<TTKTerm>): this is TCEnv<TTKTerm & { tag: 'Const' }> {
    return this.value.tag === 'Const';
  }

  isSortTerm(this: TCEnv<TTKTerm>): this is TCEnv<TTKTerm & { tag: 'Sort' }> {
    return this.value.tag === 'Sort';
  }

  isVarTerm(this: TCEnv<TTKTerm>): this is TCEnv<TTKTerm & { tag: 'Var' }> {
    return this.value.tag === 'Var';
  }

  // WITH DEFINITIONS

  withTermDefinition(this: TCEnv<TTKTerm>, name: string, type: TTKTerm, value?: TTKTerm): TCEnv<TTKTerm> {
    return new TCEnv(
      this.signature,
      addDefinition(this.definitions, name, type, value),
      this.metaVars,
      this.constraints,
      this.indexPath,
      this.valueStack,
      this.value
    );
  }

  withInductiveDefinition(this: TCEnv<TTKTerm>, name: string, type: TTKTerm, constructors: Array<{ name: string; type: TTKTerm }>, indexPositions: number[]): TCEnv<TTKTerm> {
    return new TCEnv(
      this.signature,
      addInductiveDefinition(this.definitions, name, type, constructors, indexPositions),
      this.metaVars,
      this.constraints,
      this.indexPath,
      this.valueStack,
      this.value
    );
  }

  // Match
  inMatchScrutinee(this: TCEnv<TTKTerm & { tag: 'Match' }>): TCEnv<TTKTerm> {
    return new TCEnv(
      this.signature,
      this.definitions,
      this.metaVars,
      this.constraints,
      [...this.indexPath, MatchPartIndex.Scrutinee],
      [...this.valueStack, this.value],
      this.value.scrutinee
    );
  }

  inMatchClauses(this: TCEnv<TTKTerm & { tag: 'Match' }>): TCEnv<TTKClause[]> {
    return new TCEnv(
      this.signature,
      this.definitions,
      this.metaVars,
      this.constraints,
      [...this.indexPath, MatchPartIndex.Clauses],
      [...this.valueStack, this.value],
      this.value.clauses
    );
  }

  inMatchClause(this: TCEnv<TTKClause[]>, clauseIndex: number): TCEnv<TTKClause> {
    this.assertIndexValid('clauses', this.value, clauseIndex);

    return new TCEnv(
      this.signature,
      this.definitions,
      this.metaVars,
      this.constraints,
      [...this.indexPath, arraySeg(clauseIndex)],
      [...this.valueStack, this.value],
      this.value[clauseIndex]
    );
  }

  inMatchClausePatterns(this: TCEnv<TTKClause>): TCEnv<TTKPattern[]> {
    return new TCEnv(
      this.signature,
      this.definitions,
      this.metaVars,
      this.constraints,
      [...this.indexPath, ClausePartIndex.Patterns],
      [...this.valueStack, this.value],
      this.value.patterns
    );
  }

  inMatchClausePattern(this: TCEnv<TTKPattern[]>, patternIndex: number): TCEnv<TTKPattern> {
    this.assertIndexValid('patterns', this.value, patternIndex);

    return new TCEnv(
      this.signature,
      this.definitions,
      this.metaVars,
      this.constraints,
      [...this.indexPath, arraySeg(patternIndex)],
      [...this.valueStack, this.value],
      this.value[patternIndex]
    );
  }

  inMatchClauseRhs(this: TCEnv<TTKClause>): TCEnv<TTKTerm> {
    return new TCEnv(
      this.signature,
      this.definitions,
      this.metaVars,
      this.constraints,
      [...this.indexPath, ClausePartIndex.Rhs],
      [...this.valueStack, this.value],
      this.value.rhs
    );
  }

  inMatchClauseCtorArgs(this: TCEnv<TTKPattern & { tag: 'PCtor' }>): TCEnv<TTKPattern[]> {
    return new TCEnv(
      this.signature,
      this.definitions,
      this.metaVars,
      this.constraints,
      [...this.indexPath, MatchClauseCtorPatternPartIndex.Args],
      [...this.valueStack, this.value],
      this.value.args
    );
  }

  // App
  inAppFn(this: TCEnv<TTKTerm & { tag: 'App' }>): TCEnv<TTKTerm> {
    return new TCEnv(
      this.signature,
      this.definitions,
      this.metaVars,
      this.constraints,
      [...this.indexPath, AppPartIndex.Fn],
      [...this.valueStack, this.value],
      this.value.fn
    );
  }

  inAppArg(this: TCEnv<TTKTerm & { tag: 'App' }>): TCEnv<TTKTerm> {
    return new TCEnv(
      this.signature,
      this.definitions,
      this.metaVars,
      this.constraints,
      [...this.indexPath, AppPartIndex.Arg],
      [...this.valueStack, this.value],
      this.value.arg
    );
  }

  // Annot
  inAnnotTerm(this: TCEnv<TTKTerm & { tag: 'Annot' }>): TCEnv<TTKTerm> {
    return new TCEnv(
      this.signature,
      this.definitions,
      this.metaVars,
      this.constraints,
      [...this.indexPath, AnnotPartIndex.Term],
      [...this.valueStack, this.value],
      this.value.term
    );
  }

  inAnnotType(this: TCEnv<TTKTerm & { tag: 'Annot' }>): TCEnv<TTKTerm> {
    return new TCEnv(
      this.signature,
      this.definitions,
      this.metaVars,
      this.constraints,
      [...this.indexPath, AnnotPartIndex.Type],
      [...this.valueStack, this.value],
      this.value.type
    );
  }

  // Binder Pi
  inBinderPiName(this: TCEnv<TTKTerm & { tag: 'Binder' } & { binderKind: { tag: 'BPi' } }>): TCEnv<string> {
    return new TCEnv(
      this.signature,
      this.definitions,
      this.metaVars,
      this.constraints,
      [...this.indexPath, BinderPartSegment.Name],
      [...this.valueStack, this.value],
      this.value.name
    );
  }

  inBinderPiDomain(this: TCEnv<TTKTerm & { tag: 'Binder' } & { binderKind: { tag: 'BPi' } }>): TCEnv<TTKTerm> {
    return new TCEnv(
      this.signature,
      this.definitions,
      this.metaVars,
      this.constraints,
      [...this.indexPath, BinderPartSegment.Domain],
      [...this.valueStack, this.value],
      this.value.domain
    );
  }

  inBinderPiBody(this: TCEnv<TTKTerm & { tag: 'Binder' } & { binderKind: { tag: 'BPi' } }>): TCEnv<TTKTerm> {
    return new TCEnv(
      [...this.signature, { name: this.value.name, type: this.value.domain }],
      this.definitions,
      this.metaVars,
      this.constraints,
      [...this.indexPath, BinderPartSegment.Body],
      [...this.valueStack, this.value],
      this.value.body
    );
  }

  // Binder Lambda
  inBinderLambdaName(this: TCEnv<TTKTerm & { tag: 'Binder' } & { binderKind: { tag: 'BLam' } }>): TCEnv<string> {
    return new TCEnv(
      this.signature,
      this.definitions,
      this.metaVars,
      this.constraints,
      [...this.indexPath, BinderPartSegment.Name],
      [...this.valueStack, this.value],
      this.value.name
    );
  }

  inBinderLambdaDomain(this: TCEnv<TTKTerm & { tag: 'Binder' } & { binderKind: { tag: 'BLam' } }>): TCEnv<TTKTerm> {
    return new TCEnv(
      this.signature,
      this.definitions,
      this.metaVars,
      this.constraints,
      [...this.indexPath, BinderPartSegment.Domain],
      [...this.valueStack, this.value],
      this.value.domain
    );
  }

  inBinderLambdaBody(this: TCEnv<TTKTerm & { tag: 'Binder' } & { binderKind: { tag: 'BLam' } }>): TCEnv<TTKTerm> {
    return new TCEnv(
      [...this.signature, { name: this.value.name, type: this.value.domain }],
      this.definitions,
      this.metaVars,
      this.constraints,
      [...this.indexPath, BinderPartSegment.Body],
      [...this.valueStack, this.value],
      this.value.body
    );
  }

  // Binder Let
  inBinderLetName(this: TCEnv<TTKTerm & { tag: 'Binder' } & { binderKind: { tag: 'BLet' } }>): TCEnv<string> {
    return new TCEnv(
      this.signature,
      this.definitions,
      this.metaVars,
      this.constraints,
      [...this.indexPath, BinderPartSegment.Name],
      [...this.valueStack, this.value],
      this.value.name
    );
  }

  inBinderLetDomain(this: TCEnv<TTKTerm & { tag: 'Binder' } & { binderKind: { tag: 'BLet' } }>): TCEnv<TTKTerm> {
    return new TCEnv(
      this.signature,
      this.definitions,
      this.metaVars,
      this.constraints,
      [...this.indexPath, BinderPartSegment.Domain],
      [...this.valueStack, this.value],
      this.value.domain
    );
  }

  inBinderLetBody(this: TCEnv<TTKTerm & { tag: 'Binder' } & { binderKind: { tag: 'BLet' } }>): TCEnv<TTKTerm> {
    return new TCEnv(
      [...this.signature, { name: this.value.name, type: this.value.domain }],
      this.definitions,
      this.metaVars,
      this.constraints,
      [...this.indexPath, BinderPartSegment.Body],
      [...this.valueStack, this.value],
      this.value.body
    );
  }

  inBinderLetValue(this: TCEnv<TTKTerm & { tag: 'Binder' } & { binderKind: { tag: 'BLet' } }>): TCEnv<TTKTerm> {
    return new TCEnv(
      this.signature,
      this.definitions,
      this.metaVars,
      this.constraints,
      [...this.indexPath, BinderPartSegment.Value],
      [...this.valueStack, this.value],
      this.value.binderKind.defVal
    );
  }

  // Inductive Definition
  inInductiveDefinitionName(this: TCEnv<InductiveDefinition>): TCEnv<string> {
    return new TCEnv(
      this.signature,
      this.definitions,
      this.metaVars,
      this.constraints,
      [...this.indexPath, InductiveDefinitionPartIndex.Name],
      [...this.valueStack, this.value],
      this.value.name
    );
  }

  inInductiveDefinitionType(this: TCEnv<InductiveDefinition>): TCEnv<TTKTerm> {
    return new TCEnv(
      this.signature,
      this.definitions,
      this.metaVars,
      this.constraints,
      [...this.indexPath, InductiveDefinitionPartIndex.Type],
      [...this.valueStack, this.value],
      this.value.type
    );
  }

  inInductiveDefinitionConstructors(this: TCEnv<InductiveDefinition>): TCEnv<Array<{ name: string; type: TTKTerm }>> {
    return new TCEnv(
      this.signature,
      this.definitions,
      this.metaVars,
      this.constraints,
      [...this.indexPath, InductiveDefinitionPartIndex.Constructors],
      [...this.valueStack, this.value],
      this.value.constructors
    );
  }

  inInductiveDefinitionConstructor(this: TCEnv<Array<{ name: string; type: TTKTerm }>>, constructorIndex: number): TCEnv<{ name: string; type: TTKTerm }> {
    this.assertIndexValid('constructors', this.value, constructorIndex);

    return new TCEnv(
      this.signature,
      this.definitions,
      this.metaVars,
      this.constraints,
      [...this.indexPath, arraySeg(constructorIndex)],
      [...this.valueStack, this.value],
      this.value[constructorIndex]
    );
  }

  inInductiveDefinitionConstructorName(this: TCEnv<{ name: string; type: TTKTerm }>): TCEnv<string> {
    return new TCEnv(
      this.signature,
      this.definitions,
      this.metaVars,
      this.constraints,
      [...this.indexPath, InductiveDefinitionPartIndex.ConstructorName],
      [...this.valueStack, this.value],
      this.value.name
    );
  }

  inInductiveDefinitionConstructorType(this: TCEnv<{ name: string; type: TTKTerm }>): TCEnv<TTKTerm> {
    return new TCEnv(
      this.signature,
      this.definitions,
      this.metaVars,
      this.constraints,
      [...this.indexPath, InductiveDefinitionPartIndex.ConstructorType],
      [...this.valueStack, this.value],
      this.value.type
    );
  }

  // Term
  inTermName(this: TCEnv<TermDefinition>): TCEnv<string> {
    return new TCEnv(
      this.signature,
      this.definitions,
      this.metaVars,
      this.constraints,
      [...this.indexPath, TermPartIndex.Name],
      [...this.valueStack, this.value],
      this.value.name
    );
  }

  inTermType(this: TCEnv<TermDefinition>): TCEnv<TTKTerm> {
    return new TCEnv(
      this.signature,
      this.definitions,
      this.metaVars,
      this.constraints,
      [...this.indexPath, TermPartIndex.Type],
      [...this.valueStack, this.value],
      this.value.type
    );
  }

  inTermValue(this: TCEnv<TermDefinition>): TCEnv<TTKTerm | undefined> {
    return new TCEnv(
      this.signature,
      this.definitions,
      this.metaVars,
      this.constraints,
      [...this.indexPath, TermPartIndex.Value],
      [...this.valueStack, this.value],
      this.value.value
    );
  }

  // Patterns
  isMatchClauseCtorPattern(this: TCEnv<TTKPattern>): this is TCEnv<TTKPattern & { tag: 'PCtor' }> {
    return this.value.tag === 'PCtor';
  }

  isMatchClauseVarPattern(this: TCEnv<TTKPattern>): this is TCEnv<TTKPattern & { tag: 'PVar' }> {
    return this.value.tag === 'PVar';
  }

  // Error Checkors
  assertAreTypesDefinitionallyEqual(this: TCEnv<TTKTerm>, lhs: TTKTerm, rhs: TTKTerm, message?: string): TCEnv<TTKTerm> {
    if (!areTypesDefEq(lhs, rhs)) {
      throw this.expectedTypesToBeDefinitionallyEqualError(lhs, rhs, message);
    }
    return this;
  }

  assertIndexValid<S>(field: string, values: S[], index: number): TCEnv<T> {
    if (index < 0 || index >= values.length || !Number.isInteger(index)) {
      throw this.invalidIndexError(field, values, index);
    }
    return this;
  }

  getTypeDefinitionAssert(name: string): TCEnv<TTKTerm> {
    const definition = getTypeDefinition(this.definitions, name);
    if (!definition) {
      throw this.typeDefinitionNotFoundError(name);
    }
    return this.withValue(definition);
  }

  getTypeAtIndexInSignatureAssert(index: number): TCEnv<TTKTerm> {
    const type = lookupTypeAtIndexSignature(this.signature, index);
    if (!type) {
      throw this.typeAtIndexNotFoundInSignatureError(index);
    }
    return this.withValue(type);
  }

  assertEqualLengths<A, B>(a: A[], b: B[], message?: string): TCEnv<T> {
    if (a.length !== b.length) {
      throw this.expectedEqualLengthsError(a, b, message);
    }
    return this;
  }

  // ERRORS
  private invalidIndexError<S>(field: string, values: S[], index: number): TCEnvError<T> {
    return new TCEnvError<T>(`Invalid index ${index} for ${field} with length ${values.length}.`, this);
  }

  expectedBinderPiError(this: TCEnv<TTKTerm>): TCEnvError<TTKTerm> {
    return new TCEnvError<TTKTerm>(`Expected binder Pi type, got: ${this.prettyPrint(this.value)}`, this);
  }

  expectedCheckTypeToBeBinderPiError(this: TCEnv<TTKTerm>, checkType: TTKTerm): TCEnvError<TTKTerm> {
    return new TCEnvError<TTKTerm>(`Expected check type to be binder Pi type, got: ${prettyPrint(checkType)}`, this);
  }

  expectedTypesToBeDefinitionallyEqualError(this: TCEnv<TTKTerm>, lhs: TTKTerm, rhs: TTKTerm, message?: string): TCEnvError<TTKTerm> {
    return new TCEnvError<TTKTerm>(`Expected types to be definitionally equal: ${this.prettyPrint(lhs)} vs ${this.prettyPrint(rhs)}${message ? `: ${message}` : ''}`, this);
  }

  typeDefinitionNotFoundError(name: string): TCEnvError<T> {
    return new TCEnvError<T>(`Type definition not found: ${name}`, this);
  }

  typeAtIndexNotFoundInSignatureError(index: number): TCEnvError<T> {
    return new TCEnvError<T>(`Type at index ${index} not found in signature`, this);
  }

  expectedEqualLengthsError<A, B>(a: A[], b: B[], message?: string): TCEnvError<T> {
    return new TCEnvError<T>(`Expected equal lengths: ${a.length} vs ${b.length}${message ? `: ${message}` : ''}`, this);
  }

  unknownTagError(data: { tag: string }, typeName: string, message?: string): TCEnvError<T> {
    return new TCEnvError<T>(`Unknown tag: ${data.tag} for ${typeName}${message ? `: ${message}` : ''}`, this);
  }
}

export class TCEnvError<T> {
  constructor(
    public readonly message: string,
    public readonly env: TCEnv<T>
  ) { }
}

function lookupTypeAtIndexSignature(signature: Signature, index: number): TTKTerm | undefined {
  const sigIndex = signature.length - 1 - index
  const binder = signature[sigIndex];
  if (!binder) {
    return undefined;
  }
  const type = binder.type;

  // Shift indices to be at tail of signature
  const shiftAmount = signature.length - sigIndex;
  return shiftAmount > 0 ? shiftTerm(type, shiftAmount, 0) : type;
}

export function postOrderTraverseTerm(term: TTKTerm, fn: (term: TTKTerm, indexPath: IndexPath) => void, indexPath: IndexPath) {
  fn(term, indexPath);

  if (term.tag === 'Binder') {
    postOrderTraverseTerm(term.domain, fn, [...indexPath, BinderPartSegment.Domain]);
    postOrderTraverseTerm(term.body, fn, [...indexPath, BinderPartSegment.Body]);
    if (term.binderKind.tag === 'BLet') {
      postOrderTraverseTerm(term.binderKind.defVal, fn, [...indexPath, BinderPartSegment.Value]);
    }
  } else if (term.tag === 'App') {
    postOrderTraverseTerm(term.fn, fn, [...indexPath, AppPartIndex.Fn]);
    postOrderTraverseTerm(term.arg, fn, [...indexPath, AppPartIndex.Arg]);
  } else if (term.tag === 'Hole') {
    postOrderTraverseTerm(term.type, fn, [...indexPath, HolePartIndex.Type]);
  } else if (term.tag === 'Annot') {
    postOrderTraverseTerm(term.term, fn, [...indexPath, AnnotPartIndex.Term]);
    postOrderTraverseTerm(term.type, fn, [...indexPath, AnnotPartIndex.Type]);
  } else if (term.tag === 'Match') {
    postOrderTraverseTerm(term.scrutinee, fn, [...indexPath, MatchPartIndex.Scrutinee]);
    term.clauses.forEach((clause, clauseIndex) => {
      postOrderTraverseTerm(clause.rhs, fn, [...indexPath, MatchPartIndex.Clauses, arraySeg(clauseIndex), ClausePartIndex.Rhs]);
    });
  } else if (term.tag === 'Sort') {
    // No children
  } else if (term.tag === 'Const') {
    // No children
  } else if (term.tag === 'Var') {
    // No children
  } else {
    const _never: never = term as never;
    throw new Error(`Unhandled term type: ${(_never as { tag: string }).tag}`);
  }
}

export function assertIsPi(term: TTKTerm, msg?: string): asserts term is TTKTerm & { tag: 'Binder'; binderKind: { tag: 'BPi' } } {
  if (term.tag !== 'Binder' || term.binderKind.tag !== 'BPi') {
    throw new Error(msg ?? `Expected Pi type, got: ${prettyPrint(term)}`);
  }
}

export function assertIsNotPi(term: TTKTerm, msg?: string): asserts term is Exclude<TTKTerm, { tag: 'Binder'; binderKind: { tag: 'BPi' } }> {
  if (term.tag === 'Binder' && term.binderKind.tag === 'BPi') {
    throw new Error(msg ?? `Expected non-Pi type, got: ${prettyPrint(term)}`);
  }
}

export function assertDefined<T>(value: T | undefined, msg?: string): asserts value is T {
  if (!value) {
    throw new Error(msg ?? `Expected defined value, got: ${value}`);
  }
}