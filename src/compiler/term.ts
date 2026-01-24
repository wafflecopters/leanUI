import { arraySeg, fieldSeg, IndexPath, IndexPathSegment } from "../types/source-position";
import { prettyPrint, TTKClause, TTKPattern, TTKTerm, TTKContext, mkPi, mkLSucc, mkULit, mkMeta, simplifyLevel } from "./kernel";
import { normalize as doNormalize } from "./normalize";
export type { TTKContext } from "./kernel";
import { solveConstraints } from "./meta";
import { applySubstitutionToConstraints, applySubstitutionToContext, applySubstitutionToMetaVars, enumerateAppliedSubstitutions, shiftTerm } from "./subst";
import { unifyTerms } from "./unify";
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
  ctx: TTKContext,
  meta: string,
  rhs: TTKTerm,
}

export type MetaVar = {
  ctx: TTKContext,
  type: TTKTerm,
  solution?: TTKTerm
}

export type TCEnvOptions = {
  mode: 'pattern' | 'check'
}

export function createTCEnv(data: {
  definitions?: DefinitionsMap,
  context?: TTKContext,
  metaVars?: Map<string, MetaVar>,
  constraints?: Constraint[],
  indexPath?: IndexPath,
  valueStack?: unknown[],
  value?: null,
  levelMetas?: Map<string, LevelMeta>,
  options: TCEnvOptions
}): TCEnv<null> {
  return new TCEnv(
    data.context ?? [],
    data.definitions ?? createDefinitionsMap(),
    data.metaVars ?? new Map<string, MetaVar>(),
    data.constraints ?? [],
    data.indexPath ?? [],
    data.valueStack ?? [],
    null,
    data.levelMetas ?? new Map<string, LevelMeta>(),
    data.options
  );
}

export function updateTTKContextInTCEnv<T>(env: TCEnv<T>, fn: (s: TTKContext) => TTKContext): TCEnv<T> {
  return new TCEnv(
    fn(env.context),
    env.definitions,
    env.metaVars,
    env.constraints,
    env.indexPath,
    env.valueStack,
    env.value,
    env.levelMetas,
    env.options
  );
}

export function extendTTKContextInTCEnv<T>(env: TCEnv<T>, name: string, type: TTKTerm, value?: TTKTerm): TCEnv<T> {
  return updateTTKContextInTCEnv(env, (s) => [...s, { name, type, value }]);
}

export function updateDefinitionsInTCEnv<T>(env: TCEnv<T>, fn: (d: DefinitionsMap) => DefinitionsMap): TCEnv<T> {
  return new TCEnv(
    env.context,
    fn({ ...env.definitions }),
    env.metaVars,
    env.constraints,
    env.indexPath,
    env.valueStack,
    env.value,
    env.levelMetas,
    env.options
  );
}

export function addDefinitionInTCEnv<T>(env: TCEnv<T>, name: string, type: TTKTerm, namedArgMap?: NamedArgMap): TCEnv<T> {
  return updateDefinitionsInTCEnv(env, (d) => addDefinition(d, name, type, undefined, namedArgMap));
}

export function setDefinitionValueInTCEnv<T>(env: TCEnv<T>, name: string, value: TTKTerm): TCEnv<T> {
  return updateDefinitionsInTCEnv(env, (d) => setDefinitionValue(d, name, value));
}

export function addInductiveDefinitionInTCEnv<T>(env: TCEnv<T>, name: string, type: TTKTerm, constructors: Array<{ name: string; type: TTKTerm; namedArgMap?: NamedArgMap }>, indexPositions: number[], namedArgMap?: NamedArgMap): TCEnv<T> {
  return updateDefinitionsInTCEnv(env, (d) => addInductiveDefinition(d, name, type, constructors, indexPositions, namedArgMap));
}

export function updateMetaVarsInTCEnv<T>(env: TCEnv<T>, fn: (m: Map<string, MetaVar>) => Map<string, MetaVar>): TCEnv<T> {
  return new TCEnv(
    env.context,
    env.definitions,
    fn(new Map(env.metaVars)),
    env.constraints,
    env.indexPath,
    env.valueStack,
    env.value,
    env.levelMetas,
    env.options
  );
}

export function addMetaVarInTCEnv<T>(env: TCEnv<T>, type: TTKTerm): { env: TCEnv<T>, name: string } {
  const name = `?m${env.metaVars.size}`;

  return { env: updateMetaVarsInTCEnv(env, (m) => m.set(name, { ctx: env.context, type })), name };
}

/**
 * Map from named argument label to its 0-based position index.
 * Stored with definitions to support named argument resolution.
 */
export type NamedArgMap = Map<string, number>;

export type InductiveDefinition = {
  name: string,
  type: TTKTerm,
  constructors: Array<{
    name: string;
    type: TTKTerm;
    namedArgMap?: NamedArgMap;  // Named args for this constructor
  }>,
  indexPositions: number[],
  namedArgMap?: NamedArgMap,  // Named args for the inductive type itself
}

export type TermDefinition = {
  name: string,
  type: TTKTerm,
  value?: TTKTerm,
  namedArgMap?: NamedArgMap,  // Named args from the type signature
}

export type DefinitionsMap = {
  terms: Map<string, TermDefinition>,
  inductiveTypes: Map<string, InductiveDefinition>,
  inductiveNameOfConstructor: Map<string, string>,
}

export function createDefinitionsMap(): DefinitionsMap {
  return {
    terms: new Map<string, TermDefinition>(),
    inductiveTypes: new Map<string, InductiveDefinition>(),
    inductiveNameOfConstructor: new Map<string, string>(),
  };
}

export function addDefinition(
  definitions: DefinitionsMap,
  name: string,
  type: TTKTerm,
  value?: TTKTerm,
  namedArgMap?: NamedArgMap
): DefinitionsMap {
  const newMap = new Map<string, TermDefinition>(definitions.terms);
  newMap.set(name, { name, type, value, namedArgMap });
  return {
    ...definitions,
    terms: newMap,
  };
}

/**
 * Create a NamedArgMapLookup function from a definitions map.
 * This is used during elaboration to resolve named arguments.
 */
export function createNamedArgLookup(definitions: DefinitionsMap): (name: string) => NamedArgMap | undefined {
  return (name: string) => {
    // Check term definitions
    const termDef = definitions.terms.get(name);
    if (termDef?.namedArgMap) {
      return termDef.namedArgMap;
    }

    // Check inductive types
    const inductiveDef = definitions.inductiveTypes.get(name);
    if (inductiveDef?.namedArgMap) {
      return inductiveDef.namedArgMap;
    }

    // Check constructors
    for (const [, inductive] of definitions.inductiveTypes) {
      for (const ctor of inductive.constructors) {
        if (ctor.name === name && ctor.namedArgMap) {
          return ctor.namedArgMap;
        }
      }
    }

    return undefined;
  };
}

/**
 * Info about named arguments and arity for a definition.
 */
export interface NamedArgInfo {
  namedArgMap: NamedArgMap;
  totalArity: number;
}

/**
 * Create a lookup function that returns both namedArgMap and totalArity.
 * This is used during elaboration to properly handle implicit argument insertion.
 */
export function createNamedArgInfoLookup(definitions: DefinitionsMap): (name: string) => NamedArgInfo | undefined {
  return (name: string) => {
    // Check term definitions
    const termDef = definitions.terms.get(name);
    if (termDef?.namedArgMap && termDef.type) {
      return {
        namedArgMap: termDef.namedArgMap,
        totalArity: countPiBinders(termDef.type)
      };
    }

    // Check inductive types
    const inductiveDef = definitions.inductiveTypes.get(name);
    if (inductiveDef?.namedArgMap) {
      return {
        namedArgMap: inductiveDef.namedArgMap,
        totalArity: countPiBinders(inductiveDef.type)
      };
    }

    // Check constructors
    for (const [, inductive] of definitions.inductiveTypes) {
      for (const ctor of inductive.constructors) {
        if (ctor.name === name && ctor.namedArgMap) {
          return {
            namedArgMap: ctor.namedArgMap,
            totalArity: countPiBinders(ctor.type)
          };
        }
      }
    }

    return undefined;
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

export function addInductiveDefinition(
  definitions: DefinitionsMap,
  name: string,
  type: TTKTerm,
  constructors: Array<{ name: string; type: TTKTerm; namedArgMap?: NamedArgMap }>,
  indexPositions: number[],
  namedArgMap?: NamedArgMap
): DefinitionsMap {
  const newMap = new Map<string, InductiveDefinition>(definitions.inductiveTypes);
  newMap.set(name, { name, type, constructors, indexPositions: indexPositions ?? [], namedArgMap });

  const newCtroMap = new Map<string, string>(definitions.inductiveNameOfConstructor);
  for (const ctor of constructors) {
    newCtroMap.set(ctor.name, name);
  }
  return { ...definitions, inductiveTypes: newMap, inductiveNameOfConstructor: newCtroMap };
}

export function getTypeDefinition(definitions: DefinitionsMap, name: string) {
  return definitions.terms.get(name)?.type;
}

export function getTermDefinition(definitions: DefinitionsMap, name: string) {
  return definitions.terms.get(name);
}

export type PiSpine = { binders: TTKContext, body: TTKTerm, term?: TTKTerm };
export type AppSpine = { fn: TTKTerm, args: TTKTerm[] };

export function contextToNamesStack(context: TTKContext): string[] {
  return context.map(n => n.name).reverse()
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
  const binders: TTKContext = [];
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

export function transformVarsInTerm(term: TTKTerm, transform: (varIndex: number, context: TTKContext) => TTKTerm): TTKTerm {
  return transformVarsInTermAcc(term, transform, []);
}

function transformVarsInTermAcc(term: TTKTerm, transform: (varIndex: number, context: TTKContext) => TTKTerm, context: TTKContext): TTKTerm {
  if (term.tag === 'Var') {
    return transform(term.index, context);
  } else if (term.tag === 'Binder') {
    const bodyTTKContext = [...context, { name: term.name, type: term.domain }];
    return { tag: 'Binder', name: term.name, binderKind: term.binderKind, domain: transformVarsInTermAcc(term.domain, transform, context), body: transformVarsInTermAcc(term.body, transform, bodyTTKContext) };
  } else if (term.tag === 'App') {
    return { tag: 'App', fn: transformVarsInTermAcc(term.fn, transform, context), arg: transformVarsInTermAcc(term.arg, transform, context) };
  } else if (term.tag === 'Const') {
    return { tag: 'Const', name: term.name };
  } else if (term.tag === 'Sort') {
    return { tag: 'Sort', level: term.level };
  } else if (term.tag === 'Hole') {
    return { tag: 'Hole', id: term.id };
  } else if (term.tag === 'Meta') {
    return { tag: 'Meta', id: term.id };
  } else if (term.tag === 'Annot') {
    return { tag: 'Annot', term: transformVarsInTermAcc(term.term, transform, context), type: transformVarsInTermAcc(term.type, transform, context) };
  } else if (term.tag === 'Match') {
    return { tag: 'Match', scrutinee: transformVarsInTermAcc(term.scrutinee, transform, context), clauses: term.clauses.map(c => ({ patterns: c.patterns, rhs: transformVarsInTermAcc(c.rhs, transform, context) })) };
  } else if (term.tag === 'ULevel') {
    return { tag: 'ULevel' };
  } else if (term.tag === 'ULit') {
    return { tag: 'ULit', n: term.n };
  } else if (term.tag === 'UOmega') {
    return { tag: 'UOmega' };
  }

  const _never: never = term
  throw new Error(`Unexpected tag: ${(term as { tag: string }).tag}`);
}

/**
 * Replace all Holes in a term with fresh Metas.
 * Returns the updated env (with new metas in metaVars) and the transformed term.
 */
function replaceHolesWithMetasInTerm<S>(env: TCEnv<S>, term: TTKTerm): { env: TCEnv<S>, term: TTKTerm } {
  switch (term.tag) {
    case 'Hole': {
      // Create a fresh meta for this hole
      // We don't know the type yet, so we create a type meta as well
      const { env: envWithTypeMeta, metaTerm: typeMeta } = env.createMetaForType();
      const metaName = `?m${envWithTypeMeta.metaVars.size}`;
      const newMetaVars = new Map(envWithTypeMeta.metaVars);
      newMetaVars.set(metaName, { ctx: envWithTypeMeta.context, type: typeMeta });
      const metaTerm: TTKTerm = { tag: 'Meta', id: metaName };
      const newEnv = new TCEnv(
        envWithTypeMeta.context,
        envWithTypeMeta.definitions,
        newMetaVars,
        envWithTypeMeta.constraints,
        envWithTypeMeta.indexPath,
        envWithTypeMeta.valueStack,
        envWithTypeMeta.value,
        envWithTypeMeta.levelMetas,
        envWithTypeMeta.options
      );
      return { env: newEnv, term: metaTerm };
    }

    case 'Var':
    case 'Const':
    case 'Sort':
    case 'Meta':
    case 'ULevel':
    case 'ULit':
    case 'UOmega':
      return { env, term };

    case 'Binder': {
      const { env: env1, term: domain } = replaceHolesWithMetasInTerm(env, term.domain);
      const { env: env2, term: body } = replaceHolesWithMetasInTerm(env1, term.body);
      return {
        env: env2,
        term: { tag: 'Binder', name: term.name, binderKind: term.binderKind, domain, body }
      };
    }

    case 'App': {
      const { env: env1, term: fn } = replaceHolesWithMetasInTerm(env, term.fn);
      const { env: env2, term: arg } = replaceHolesWithMetasInTerm(env1, term.arg);
      return { env: env2, term: { tag: 'App', fn, arg } };
    }

    case 'Annot': {
      const { env: env1, term: innerTerm } = replaceHolesWithMetasInTerm(env, term.term);
      const { env: env2, term: type } = replaceHolesWithMetasInTerm(env1, term.type);
      return { env: env2, term: { tag: 'Annot', term: innerTerm, type } };
    }

    case 'Match': {
      let currentEnv = env;
      const { env: env1, term: scrutinee } = replaceHolesWithMetasInTerm(currentEnv, term.scrutinee);
      currentEnv = env1;

      const clauses = term.clauses.map(c => {
        const { env: clauseEnv, term: rhs } = replaceHolesWithMetasInTerm(currentEnv, c.rhs);
        currentEnv = clauseEnv;
        return { patterns: c.patterns, rhs };
      });

      return { env: currentEnv, term: { tag: 'Match', scrutinee, clauses } };
    }
  }
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

// Note: Holes are now simple { tag: 'Hole', id: string } with no type field
// HolePartIndex removed as holes no longer have substructure

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

/**
 * Level metavariable tracking.
 * Now that levels are terms, level metas are just TTKTerm values.
 * - undefined means unsolved
 * - TTKTerm value means solved to that level term
 */
export type LevelMeta = TTKTerm | undefined;

/**
 * Substitute solved level metas into a level term.
 * Level terms are: ULit, UOmega, Var (for level variables), Meta (for level metas),
 * or App of USucc/UMax/UIMax.
 */
function substituteLevelMetas(level: TTKTerm, levelMetas: Map<string, LevelMeta>): TTKTerm {
  switch (level.tag) {
    case 'ULit':
    case 'UOmega':
    case 'Var':
    case 'ULevel':
    case 'Const':
      return level;
    case 'Meta': {
      const solution = levelMetas.get(level.id);
      if (solution !== undefined) {
        // Recursively substitute in case the solution contains other metas
        return substituteLevelMetas(solution, levelMetas);
      }
      return level;
    }
    case 'App':
      return {
        tag: 'App',
        fn: substituteLevelMetas(level.fn, levelMetas),
        arg: substituteLevelMetas(level.arg, levelMetas)
      };
    default:
      // For other term types (Sort, Binder, etc.), just return as-is
      // These shouldn't appear as level terms in normal usage
      return level;
  }
}

/**
 * Substitute solved level metas into a term (recursively in all levels).
 */
function substituteLevelMetasInTerm(term: TTKTerm, levelMetas: Map<string, LevelMeta>): TTKTerm {
  switch (term.tag) {
    case 'Var':
    case 'Const':
    case 'Hole':
    case 'Meta':
    case 'ULevel':
    case 'ULit':
    case 'UOmega':
      return term;

    case 'Sort':
      // After substitution, simplify the level (e.g., max(2, 2) -> 2)
      return { tag: 'Sort', level: simplifyLevel(substituteLevelMetas(term.level, levelMetas)) };

    case 'App':
      return {
        tag: 'App',
        fn: substituteLevelMetasInTerm(term.fn, levelMetas),
        arg: substituteLevelMetasInTerm(term.arg, levelMetas)
      };

    case 'Binder': {
      const newDomain = substituteLevelMetasInTerm(term.domain, levelMetas);
      const newBody = substituteLevelMetasInTerm(term.body, levelMetas);
      if (term.binderKind.tag === 'BLet') {
        return {
          tag: 'Binder',
          name: term.name,
          binderKind: {
            tag: 'BLet',
            defVal: substituteLevelMetasInTerm(term.binderKind.defVal, levelMetas)
          },
          domain: newDomain,
          body: newBody
        };
      }
      return {
        tag: 'Binder',
        name: term.name,
        binderKind: term.binderKind,
        domain: newDomain,
        body: newBody
      };
    }

    case 'Annot':
      return {
        tag: 'Annot',
        term: substituteLevelMetasInTerm(term.term, levelMetas),
        type: substituteLevelMetasInTerm(term.type, levelMetas)
      };

    case 'Match':
      return {
        tag: 'Match',
        scrutinee: substituteLevelMetasInTerm(term.scrutinee, levelMetas),
        clauses: term.clauses.map(c => ({
          ...c,
          rhs: substituteLevelMetasInTerm(c.rhs, levelMetas)
        }))
      };

    default: {
      const _exhaustive: never = term;
      throw new Error(`Unknown term tag: ${(_exhaustive as TTKTerm).tag}`);
    }
  }
}

export class TCEnv<T> {
  constructor(
    public readonly context: TTKContext,
    public readonly definitions: DefinitionsMap,
    public readonly metaVars: Map<string, MetaVar>,
    public readonly constraints: Constraint[],
    public readonly indexPath: IndexPath,
    public readonly valueStack: unknown[],
    public readonly value: T,
    public readonly levelMetas: Map<string, LevelMeta>,
    public readonly options: TCEnvOptions,
    /**
     * The elaborated term (with Holes replaced by Metas, etc.)
     * Used by inferType to pass the elaborated term to checkType's CONV case.
     */
    public readonly elaboratedTerm?: TTKTerm
  ) {
  }

  then<S>(fn: (env: TCEnv<T>) => S): S {
    return fn(this);
  }

  hasConstraints(): this is TCEnv<T> & { constraints: Constraint[] } {
    return this.constraints.length > 0;
  }

  prettyPrint(term: TTKTerm): string {
    return prettyPrint(term, this.context.map(s => s.name).reverse());
  }

  static printTTKContext(context: TTKContext): string {
    return `{${context.map((s, i) => {
      const sig = context.slice(0, i)
      return `${s.name} : ${prettyPrint(s.type, sig.map(s => s.name).reverse())}`
    }).join(', ')}}`;
  }

  printTTKContext(): string {
    return TCEnv.printTTKContext(this.context);
  }

  printMetas(options?: { indentLevel?: number, innerIndentOffset?: number }): string {
    const itemStrs = Array.from(this.metaVars.entries()).map(([name, meta]) => {
      return `${name} : ${TCEnv.printTTKContext(meta.ctx)} -> ${prettyPrint(meta.type, meta.ctx.map(s => s.name))}`
    })

    return printCollectionFancy(itemStrs, '{', '}', ',', options);
  }

  static printConstraint(constraint: Constraint): string {
    return `{ctx: ${TCEnv.printTTKContext(constraint.ctx)}, meta: ${constraint.meta}, rhs: ${prettyPrint(constraint.rhs)}}`
  }

  printConstraints(options?: { indentLevel?: number, innerIndentOffset?: number }): string {
    const itemStrs = this.constraints.map(TCEnv.printConstraint);
    return printCollectionFancy(itemStrs, '[', ']', ',', options);
  }

  withCheckingMode(mode: 'pattern' | 'check'): TCEnv<T> {
    return new TCEnv(this.context, this.definitions, this.metaVars, this.constraints, this.indexPath, this.valueStack, this.value, this.levelMetas, { ...this.options, mode });
  }

  applySubstitutionToContextMetasAndConstraints(varIndex: number, value: TTKTerm): TCEnv<T> {
    const newTTKContext = applySubstitutionToContext(this.context, varIndex, value);
    const newMetaVars = applySubstitutionToMetaVars(this.metaVars, this.context.length, varIndex, value);
    const newConstraints = applySubstitutionToConstraints(this.constraints, this.context.length, varIndex, value);

    return new TCEnv(
      newTTKContext,
      this.definitions,
      newMetaVars,
      newConstraints,
      this.indexPath,
      this.valueStack,
      this.value,
      this.levelMetas,
      this.options
    );
  }

  solveMetasAndConstraints(options: { liftMetasToFullContext: boolean }): TCEnv<T> {
    if (!this.hasConstraints()) {
      return this;
    }

    const { constraints, metaVars } = solveConstraints(
      this.metaVars,
      this.constraints,
      options.liftMetasToFullContext ? this.context : undefined
    );
    return new TCEnv(
      this.context,
      this.definitions,
      metaVars,
      constraints,
      this.indexPath,
      this.valueStack,
      this.value,
      this.levelMetas,
      this.options
    );
  }

  /**
   * Unify two terms, applying all resulting substitutions to the context,
   * metas, and constraints. Also adds any meta constraints produced by unification.
   *
   * Returns a new TCEnv with all substitutions and constraints applied.
   * Throws if unification fails.
   *
   * Note: This preserves the value type T since unification only affects
   * the context, metas, and constraints - not the value itself.
   */
  unifyTerms<S extends TTKTerm>(this: TCEnv<S>, lhs: TTKTerm, rhs: TTKTerm): TCEnv<S> {
    const result = unifyTerms(lhs, rhs, {
      mode: this.options.mode,
      definitions: this.definitions
    });

    if (!result.success) {
      throw (this as unknown as TCEnv<TTKTerm>).unificationFailedError(lhs, rhs, result.reason);
    }

    // Apply all substitutions sequentially
    // enumerateAppliedSubstitutions handles adjusting indices as each substitution
    // removes a variable from the context
    let env: TCEnv<S> = this;
    for (const { varIndex, value } of enumerateAppliedSubstitutions(result.substitutions)) {
      env = env.applySubstitutionToContextMetasAndConstraints(varIndex, value);
    }

    // Add any meta constraints from unification
    for (const metaConstraint of result.metaConstraints) {
      env = env.withConstraint(metaConstraint);
    }

    // Solve level constraints
    for (const levelConstraint of result.levelConstraints) {
      env = env.solveLevelMeta(levelConstraint.lmvar, levelConstraint.rhs);
    }

    return env;
  }

  hasDefinedValue(): this is TCEnv<NonNullable<T>> {
    return this.value !== undefined;
  }

  withoutValue(): TCEnv<void> {
    return new TCEnv(this.context, this.definitions, this.metaVars, this.constraints, this.indexPath, this.valueStack, undefined, this.levelMetas, this.options);
  }

  withValue<S>(value: S): TCEnv<S> {
    return new TCEnv(this.context, this.definitions, this.metaVars, this.constraints, this.indexPath, this.valueStack, value, this.levelMetas, this.options, this.elaboratedTerm);
  }

  /**
   * Set the elaborated term (used by inferType to communicate the elaborated term to checkType).
   */
  withElaboratedTerm(term: TTKTerm): TCEnv<T> {
    return new TCEnv(this.context, this.definitions, this.metaVars, this.constraints, this.indexPath, this.valueStack, this.value, this.levelMetas, this.options, term);
  }

  mapValue<S>(fn: (value: T) => S): TCEnv<S> {
    return this.withValue(fn(this.value));
  }

  atValueAndPathOfEnv<S>(otherEnv: TCEnv<S>): TCEnv<S> {
    return new TCEnv(this.context, this.definitions, this.metaVars, this.constraints, otherEnv.indexPath, otherEnv.valueStack, otherEnv.value, this.levelMetas, this.options, this.elaboratedTerm);
  }

  /**
   * Create a new env with this env's context/definitions/value/path,
   * but with metaVars/constraints/levelMetas from another env.
   * Used when checking Pi body: we want the original context but updated metas.
   */
  withMetasConstraintsLevelMetasFrom<S>(otherEnv: TCEnv<S>): TCEnv<T> {
    return new TCEnv(this.context, this.definitions, otherEnv.metaVars, otherEnv.constraints, this.indexPath, this.valueStack, this.value, otherEnv.levelMetas, this.options);
  }

  atIndexPath(indexPath: IndexPath): TCEnv<void> {
    return new TCEnv(this.context, this.definitions, this.metaVars, this.constraints, indexPath, [], undefined, this.levelMetas, this.options);
  }

  atIndexPathAndValue<S>(indexPath: IndexPath, value: S): TCEnv<S> {
    return new TCEnv(this.context, this.definitions, this.metaVars, this.constraints, indexPath, [value], value, this.levelMetas, this.options);
  }

  // Terms

  extendTTKContext(name: string, type: TTKTerm, value?: TTKTerm): TCEnv<T> {
    return new TCEnv(
      [...this.context, { name, type, value }],
      this.definitions,
      this.metaVars,
      this.constraints,
      this.indexPath,
      this.valueStack,
      this.value,
      this.levelMetas,
      this.options
    );
  }

  withConstraint(constraint: Omit<Constraint, 'ctx'>): TCEnv<T> {
    return new TCEnv(this.context, this.definitions, this.metaVars, [...this.constraints, { ctx: this.context, ...constraint }], this.indexPath, this.valueStack, this.value, this.levelMetas, this.options);
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

  isULevelTerm(this: TCEnv<TTKTerm>): this is TCEnv<TTKTerm & { tag: 'ULevel' }> {
    return this.value.tag === 'ULevel';
  }

  /**
   * Create a fresh meta variable for a hole during type checking.
   * The meta gets the expected type and current context.
   * The hole is replaced with a Meta term in the returned env's value.
   */
  createMetaForHole(this: TCEnv<TTKTerm & { tag: 'Hole' }>, expectedType: TTKTerm, _message?: string): TCEnv<TTKTerm> {
    const name = `?m${this.metaVars.size}`;
    const newMetaVars = new Map(this.metaVars);
    newMetaVars.set(name, { ctx: this.context, type: expectedType });

    // Replace the Hole with a Meta term (elaboration: Hole -> Meta)
    const metaTerm: TTKTerm = { tag: 'Meta', id: name };

    return new TCEnv(
      this.context,
      this.definitions,
      newMetaVars,
      this.constraints,
      this.indexPath,
      this.valueStack,
      metaTerm,
      this.levelMetas,
      this.options
    );
  }

  /**
   * Create a fresh meta variable for a type (used when inferring holes).
   * The meta has type `Type` with a fresh level metavariable.
   * Returns the updated env and the meta term.
   */
  createMetaForType<S>(this: TCEnv<S>): { env: TCEnv<S>, metaTerm: TTKTerm } {
    // First create a fresh level meta for the type's universe
    const { env: envWithLevel, sort: typeSort } = this.typeSortFresh();

    const name = `?m${envWithLevel.metaVars.size}`;
    const newMetaVars = new Map(envWithLevel.metaVars);
    newMetaVars.set(name, { ctx: envWithLevel.context, type: typeSort });

    const metaTerm: TTKTerm = { tag: 'Meta', id: name };

    const env = new TCEnv(
      envWithLevel.context,
      envWithLevel.definitions,
      newMetaVars,
      envWithLevel.constraints,
      envWithLevel.indexPath,
      envWithLevel.valueStack,
      envWithLevel.value,
      envWithLevel.levelMetas,
      envWithLevel.options
    );

    return { env, metaTerm };
  }

  /**
   * Create a fresh meta variable with a given type.
   * Used for inserting implicit arguments during type checking.
   * Returns the updated env and the meta term.
   */
  createMetaWithType<S>(this: TCEnv<S>, metaType: TTKTerm): { env: TCEnv<S>, metaTerm: TTKTerm } {
    const name = `?m${this.metaVars.size}`;
    const newMetaVars = new Map(this.metaVars);
    newMetaVars.set(name, { ctx: this.context, type: metaType });

    const metaTerm: TTKTerm = { tag: 'Meta', id: name };

    const env = new TCEnv(
      this.context,
      this.definitions,
      newMetaVars,
      this.constraints,
      this.indexPath,
      this.valueStack,
      this.value,
      this.levelMetas,
      this.options
    );

    return { env, metaTerm };
  }

  /**
   * Replace all Holes in a term with fresh Metas.
   * This is useful for elaborating a term before checking, so that the
   * resulting term structure contains Metas (which can be looked up during printing)
   * rather than Holes.
   *
   * Returns the updated env (with new metas in metaVars) and the elaborated term.
   */
  replaceHolesWithMetas<S>(this: TCEnv<S>, term: TTKTerm): { env: TCEnv<S>, term: TTKTerm } {
    return replaceHolesWithMetasInTerm(this, term);
  }

  /**
   * Check if this lambda binder has a hole as its domain (unannotated lambda).
   */
  lambdaDomainIsHole(this: TCEnv<TTKTerm & { tag: 'Binder' } & { binderKind: { tag: 'BLam' } }>): boolean {
    return this.value.domain.tag === 'Hole';
  }

  /**
   * Normalize a term to its normal form.
   */
  normalize(this: TCEnv<unknown>, term: TTKTerm): TTKTerm {
    return doNormalize(term);
  }

  /**
   * Create a fresh level metavariable for universe inference.
   * Returns the updated env and the level meta term.
   * Now that levels are terms, level metas are just Meta terms with special IDs.
   */
  freshLevelMeta<S>(this: TCEnv<S>): { env: TCEnv<S>, level: TTKTerm } {
    const id = `l${this.levelMetas.size}`;
    const newLevelMetas = new Map(this.levelMetas);
    newLevelMetas.set(id, undefined);  // unsolved

    const level: TTKTerm = mkMeta(id);

    const env = new TCEnv(
      this.context,
      this.definitions,
      this.metaVars,
      this.constraints,
      this.indexPath,
      this.valueStack,
      this.value,
      newLevelMetas,
      this.options
    );

    return { env, level };
  }

  /**
   * Solve a level metavariable by assigning it a value.
   * The value is substituted into all other level metas.
   */
  solveLevelMeta<S>(this: TCEnv<S>, id: string, value: TTKTerm): TCEnv<S> {
    const newLevelMetas = new Map(this.levelMetas);

    // Substitute any existing level meta solutions into the value
    const substitutedValue = substituteLevelMetas(value, this.levelMetas);

    // Set the solution
    newLevelMetas.set(id, substitutedValue);

    return new TCEnv(
      this.context,
      this.definitions,
      this.metaVars,
      this.constraints,
      this.indexPath,
      this.valueStack,
      this.value,
      newLevelMetas,
      this.options
    );
  }

  /**
   * Substitute solved level metas into a term.
   * This is needed before unification to ensure level metas are resolved.
   */
  substituteLevelMetasInTerm(term: TTKTerm): TTKTerm {
    return substituteLevelMetasInTerm(term, this.levelMetas);
  }

  /**
   * Substitute solved level metas into a level term.
   */
  substituteLevelMetasInLevel(level: TTKTerm): TTKTerm {
    return substituteLevelMetas(level, this.levelMetas);
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
      this.context,
      addDefinition(this.definitions, name, type, value),
      this.metaVars,
      this.constraints,
      this.indexPath,
      this.valueStack,
      this.value,
      this.levelMetas,
      this.options
    );
  }

  withInductiveDefinition(this: TCEnv<TTKTerm>, name: string, type: TTKTerm, constructors: Array<{ name: string; type: TTKTerm }>, indexPositions: number[]): TCEnv<TTKTerm> {
    return new TCEnv(
      this.context,
      addInductiveDefinition(this.definitions, name, type, constructors, indexPositions),
      this.metaVars,
      this.constraints,
      this.indexPath,
      this.valueStack,
      this.value,
      this.levelMetas,
      this.options
    );
  }

  // Match
  inMatchScrutinee(this: TCEnv<TTKTerm & { tag: 'Match' }>): TCEnv<TTKTerm> {
    return new TCEnv(
      this.context,
      this.definitions,
      this.metaVars,
      this.constraints,
      [...this.indexPath, MatchPartIndex.Scrutinee],
      [...this.valueStack, this.value],
      this.value.scrutinee,
      this.levelMetas,
      this.options
    );
  }

  inMatchClauses(this: TCEnv<TTKTerm & { tag: 'Match' }>): TCEnv<TTKClause[]> {
    return new TCEnv(
      this.context,
      this.definitions,
      this.metaVars,
      this.constraints,
      [...this.indexPath, MatchPartIndex.Clauses],
      [...this.valueStack, this.value],
      this.value.clauses,
      this.levelMetas,
      this.options
    );
  }

  inMatchClause(this: TCEnv<TTKClause[]>, clauseIndex: number): TCEnv<TTKClause> {
    this.assertIndexValid('clauses', this.value, clauseIndex);

    return new TCEnv(
      this.context,
      this.definitions,
      this.metaVars,
      this.constraints,
      [...this.indexPath, arraySeg(clauseIndex)],
      [...this.valueStack, this.value],
      this.value[clauseIndex],
      this.levelMetas,
      this.options
    );
  }

  inMatchClausePatterns(this: TCEnv<TTKClause>): TCEnv<TTKPattern[]> {
    return new TCEnv(
      this.context,
      this.definitions,
      this.metaVars,
      this.constraints,
      [...this.indexPath, ClausePartIndex.Patterns],
      [...this.valueStack, this.value],
      this.value.patterns,
      this.levelMetas,
      this.options
    );
  }

  inMatchClausePattern(this: TCEnv<TTKPattern[]>, patternIndex: number): TCEnv<TTKPattern> {
    this.assertIndexValid('patterns', this.value, patternIndex);

    return new TCEnv(
      this.context,
      this.definitions,
      this.metaVars,
      this.constraints,
      [...this.indexPath, arraySeg(patternIndex)],
      [...this.valueStack, this.value],
      this.value[patternIndex],
      this.levelMetas,
      this.options
    );
  }

  inMatchClauseRhs(this: TCEnv<TTKClause>): TCEnv<TTKTerm> {
    return new TCEnv(
      this.context,
      this.definitions,
      this.metaVars,
      this.constraints,
      [...this.indexPath, ClausePartIndex.Rhs],
      [...this.valueStack, this.value],
      this.value.rhs,
      this.levelMetas,
      this.options
    );
  }

  inMatchClauseCtorArgs(this: TCEnv<TTKPattern & { tag: 'PCtor' }>): TCEnv<TTKPattern[]> {
    return new TCEnv(
      this.context,
      this.definitions,
      this.metaVars,
      this.constraints,
      [...this.indexPath, MatchClauseCtorPatternPartIndex.Args],
      [...this.valueStack, this.value],
      this.value.args,
      this.levelMetas,
      this.options
    );
  }

  // App
  inAppFn(this: TCEnv<TTKTerm & { tag: 'App' }>): TCEnv<TTKTerm> {
    return new TCEnv(
      this.context,
      this.definitions,
      this.metaVars,
      this.constraints,
      [...this.indexPath, AppPartIndex.Fn],
      [...this.valueStack, this.value],
      this.value.fn,
      this.levelMetas,
      this.options
    );
  }

  inAppArg(this: TCEnv<TTKTerm & { tag: 'App' }>): TCEnv<TTKTerm> {
    return new TCEnv(
      this.context,
      this.definitions,
      this.metaVars,
      this.constraints,
      [...this.indexPath, AppPartIndex.Arg],
      [...this.valueStack, this.value],
      this.value.arg,
      this.levelMetas,
      this.options
    );
  }

  // Annot
  inAnnotTerm(this: TCEnv<TTKTerm & { tag: 'Annot' }>): TCEnv<TTKTerm> {
    return new TCEnv(
      this.context,
      this.definitions,
      this.metaVars,
      this.constraints,
      [...this.indexPath, AnnotPartIndex.Term],
      [...this.valueStack, this.value],
      this.value.term,
      this.levelMetas,
      this.options
    );
  }

  inAnnotType(this: TCEnv<TTKTerm & { tag: 'Annot' }>): TCEnv<TTKTerm> {
    return new TCEnv(
      this.context,
      this.definitions,
      this.metaVars,
      this.constraints,
      [...this.indexPath, AnnotPartIndex.Type],
      [...this.valueStack, this.value],
      this.value.type,
      this.levelMetas,
      this.options
    );
  }

  // Binder Pi
  inBinderPiName(this: TCEnv<TTKTerm & { tag: 'Binder' } & { binderKind: { tag: 'BPi' } }>): TCEnv<string> {
    return new TCEnv(
      this.context,
      this.definitions,
      this.metaVars,
      this.constraints,
      [...this.indexPath, BinderPartSegment.Name],
      [...this.valueStack, this.value],
      this.value.name,
      this.levelMetas,
      this.options
    );
  }

  inBinderPiDomain(this: TCEnv<TTKTerm & { tag: 'Binder' } & { binderKind: { tag: 'BPi' } }>): TCEnv<TTKTerm> {
    return new TCEnv(
      this.context,
      this.definitions,
      this.metaVars,
      this.constraints,
      [...this.indexPath, BinderPartSegment.Domain],
      [...this.valueStack, this.value],
      this.value.domain,
      this.levelMetas,
      this.options
    );
  }

  inBinderPiBody(this: TCEnv<TTKTerm & { tag: 'Binder' } & { binderKind: { tag: 'BPi' } }>): TCEnv<TTKTerm> {
    return new TCEnv(
      [...this.context, { name: this.value.name, type: this.value.domain }],
      this.definitions,
      this.metaVars,
      this.constraints,
      [...this.indexPath, BinderPartSegment.Body],
      [...this.valueStack, this.value],
      this.value.body,
      this.levelMetas,
      this.options
    );
  }

  // Binder Lambda
  inBinderLambdaName(this: TCEnv<TTKTerm & { tag: 'Binder' } & { binderKind: { tag: 'BLam' } }>): TCEnv<string> {
    return new TCEnv(
      this.context,
      this.definitions,
      this.metaVars,
      this.constraints,
      [...this.indexPath, BinderPartSegment.Name],
      [...this.valueStack, this.value],
      this.value.name,
      this.levelMetas,
      this.options
    );
  }

  inBinderLambdaDomain(this: TCEnv<TTKTerm & { tag: 'Binder' } & { binderKind: { tag: 'BLam' } }>): TCEnv<TTKTerm> {
    return new TCEnv(
      this.context,
      this.definitions,
      this.metaVars,
      this.constraints,
      [...this.indexPath, BinderPartSegment.Domain],
      [...this.valueStack, this.value],
      this.value.domain,
      this.levelMetas,
      this.options
    );
  }

  inBinderLambdaBody(this: TCEnv<TTKTerm & { tag: 'Binder' } & { binderKind: { tag: 'BLam' } }>): TCEnv<TTKTerm> {
    return new TCEnv(
      [...this.context, { name: this.value.name, type: this.value.domain }],
      this.definitions,
      this.metaVars,
      this.constraints,
      [...this.indexPath, BinderPartSegment.Body],
      [...this.valueStack, this.value],
      this.value.body,
      this.levelMetas,
      this.options
    );
  }

  // Binder Let
  inBinderLetName(this: TCEnv<TTKTerm & { tag: 'Binder' } & { binderKind: { tag: 'BLet' } }>): TCEnv<string> {
    return new TCEnv(
      this.context,
      this.definitions,
      this.metaVars,
      this.constraints,
      [...this.indexPath, BinderPartSegment.Name],
      [...this.valueStack, this.value],
      this.value.name,
      this.levelMetas,
      this.options
    );
  }

  inBinderLetDomain(this: TCEnv<TTKTerm & { tag: 'Binder' } & { binderKind: { tag: 'BLet' } }>): TCEnv<TTKTerm> {
    return new TCEnv(
      this.context,
      this.definitions,
      this.metaVars,
      this.constraints,
      [...this.indexPath, BinderPartSegment.Domain],
      [...this.valueStack, this.value],
      this.value.domain,
      this.levelMetas,
      this.options
    );
  }

  inBinderLetBody(this: TCEnv<TTKTerm & { tag: 'Binder' } & { binderKind: { tag: 'BLet' } }>): TCEnv<TTKTerm> {
    return new TCEnv(
      [...this.context, { name: this.value.name, type: this.value.domain }],
      this.definitions,
      this.metaVars,
      this.constraints,
      [...this.indexPath, BinderPartSegment.Body],
      [...this.valueStack, this.value],
      this.value.body,
      this.levelMetas,
      this.options
    );
  }

  inBinderLetValue(this: TCEnv<TTKTerm & { tag: 'Binder' } & { binderKind: { tag: 'BLet' } }>): TCEnv<TTKTerm> {
    return new TCEnv(
      this.context,
      this.definitions,
      this.metaVars,
      this.constraints,
      [...this.indexPath, BinderPartSegment.Value],
      [...this.valueStack, this.value],
      this.value.binderKind.defVal,
      this.levelMetas,
      this.options
    );
  }

  // Inductive Definition
  inInductiveDefinitionName(this: TCEnv<InductiveDefinition>): TCEnv<string> {
    return new TCEnv(
      this.context,
      this.definitions,
      this.metaVars,
      this.constraints,
      [...this.indexPath, InductiveDefinitionPartIndex.Name],
      [...this.valueStack, this.value],
      this.value.name,
      this.levelMetas,
      this.options
    );
  }

  inInductiveDefinitionType(this: TCEnv<InductiveDefinition>): TCEnv<TTKTerm> {
    return new TCEnv(
      this.context,
      this.definitions,
      this.metaVars,
      this.constraints,
      [...this.indexPath, InductiveDefinitionPartIndex.Type],
      [...this.valueStack, this.value],
      this.value.type,
      this.levelMetas,
      this.options
    );
  }

  inInductiveDefinitionConstructors(this: TCEnv<InductiveDefinition>): TCEnv<Array<{ name: string; type: TTKTerm }>> {
    return new TCEnv(
      this.context,
      this.definitions,
      this.metaVars,
      this.constraints,
      [...this.indexPath, InductiveDefinitionPartIndex.Constructors],
      [...this.valueStack, this.value],
      this.value.constructors,
      this.levelMetas,
      this.options
    );
  }

  inInductiveDefinitionConstructor(this: TCEnv<Array<{ name: string; type: TTKTerm }>>, constructorIndex: number): TCEnv<{ name: string; type: TTKTerm }> {
    this.assertIndexValid('constructors', this.value, constructorIndex);

    return new TCEnv(
      this.context,
      this.definitions,
      this.metaVars,
      this.constraints,
      [...this.indexPath, arraySeg(constructorIndex)],
      [...this.valueStack, this.value],
      this.value[constructorIndex],
      this.levelMetas,
      this.options
    );
  }

  inInductiveDefinitionConstructorName(this: TCEnv<{ name: string; type: TTKTerm }>): TCEnv<string> {
    return new TCEnv(
      this.context,
      this.definitions,
      this.metaVars,
      this.constraints,
      [...this.indexPath, InductiveDefinitionPartIndex.ConstructorName],
      [...this.valueStack, this.value],
      this.value.name,
      this.levelMetas,
      this.options
    );
  }

  inInductiveDefinitionConstructorType(this: TCEnv<{ name: string; type: TTKTerm }>): TCEnv<TTKTerm> {
    return new TCEnv(
      this.context,
      this.definitions,
      this.metaVars,
      this.constraints,
      [...this.indexPath, InductiveDefinitionPartIndex.ConstructorType],
      [...this.valueStack, this.value],
      this.value.type,
      this.levelMetas,
      this.options
    );
  }

  // Term
  inTermName(this: TCEnv<TermDefinition>): TCEnv<string> {
    return new TCEnv(
      this.context,
      this.definitions,
      this.metaVars,
      this.constraints,
      [...this.indexPath, TermPartIndex.Name],
      [...this.valueStack, this.value],
      this.value.name,
      this.levelMetas,
      this.options
    );
  }

  inTermType(this: TCEnv<TermDefinition>): TCEnv<TTKTerm> {
    return new TCEnv(
      this.context,
      this.definitions,
      this.metaVars,
      this.constraints,
      [...this.indexPath, TermPartIndex.Type],
      [...this.valueStack, this.value],
      this.value.type,
      this.levelMetas,
      this.options
    );
  }

  inTermValue(this: TCEnv<TermDefinition>): TCEnv<TTKTerm | undefined> {
    return new TCEnv(
      this.context,
      this.definitions,
      this.metaVars,
      this.constraints,
      [...this.indexPath, TermPartIndex.Value],
      [...this.valueStack, this.value],
      this.value.value,
      this.levelMetas,
      this.options
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
  assertTermsAreDefinitionallyEqual(this: TCEnv<TTKTerm>, lhs: TTKTerm, rhs: TTKTerm, message?: string): TCEnv<TTKTerm> {
    if (!areTypesDefEq(lhs, rhs, this.definitions)) {
      throw this.expectedTermsToBeDefinitionallyEqualError(lhs, rhs, message);
    }
    return this;
  }

  assertValueIsDefinitionallyEqual(this: TCEnv<TTKTerm>, rhs: TTKTerm, message?: string): TCEnv<TTKTerm> {
    if (!areTypesDefEq(this.value, rhs, this.definitions)) {
      throw this.expectedTermsToBeDefinitionallyEqualError(this.value, rhs, message);
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

  getTypeAtIndexInContextAssert(index: number): TCEnv<TTKTerm> {
    const type = lookupTypeAtIndexContext(this.context, index);
    if (!type) {
      throw this.typeAtIndexNotFoundInContextError(index);
    }
    return this.withValue(type);
  }

  assertEqualLengths<A, B>(a: A[], b: B[], message?: string): TCEnv<T> {
    if (a.length !== b.length) {
      throw this.expectedEqualLengthsError(a, b, message);
    }
    return this;
  }

  assertNoConstraints(this: TCEnv<T>): TCEnv<T> {
    if (this.hasConstraints()) {
      throw this.unsolvedConstraintsError();
    }
    return this;
  }

  assertCheckingMode(this: TCEnv<T>, mode: 'pattern' | 'check'): TCEnv<T> {
    if (this.options.mode !== mode) {
      throw this.expectedModeError(mode);
    }
    return this;
  }

  expectedModeError(this: TCEnv<T>, mode: 'pattern' | 'check'): TCEnvError {
    return TCEnvError.create(`Expected mode ${mode}, got: ${this.options.mode}`, this);
  }

  withSortOfSort(this: TCEnv<TTKTerm & { tag: 'Sort' }>): TCEnv<TTKTerm> {
    return this.withValue({ tag: 'Sort', level: mkLSucc(this.value.level) });
  }

  ensurePi(this: TCEnv<TTKTerm>): TCEnv<TTKTerm & { tag: 'Binder' } & { binderKind: { tag: 'BPi' } }> {
    const normalized = this.normalize(this.value);

    if (normalized.tag === 'Binder' && normalized.binderKind.tag === 'BPi') {
      return this.withValue({ tag: 'Binder', name: normalized.name, binderKind: { tag: 'BPi' }, domain: normalized.domain, body: normalized.body });
    }

    if (normalized.tag === 'Hole' || normalized.tag === 'Meta') {
      // Create: Π(x: ?A). ?B with fresh level metas
      const { env: env1, sort: domainSort } = this.typeSortFresh();
      const { env: domainEnv, name: domainMetaId } = addMetaVarInTCEnv(env1, domainSort);
      const { env: env2, sort: codomainSort } = domainEnv.typeSortFresh();
      const { env: codomainEnv, name: codomainMetaId } = addMetaVarInTCEnv(env2, codomainSort);
      const domainMeta: TTKTerm = { tag: 'Meta', id: domainMetaId };
      const codomainMeta: TTKTerm = { tag: 'Meta', id: codomainMetaId };
      const piType = mkPi(domainMeta, codomainMeta);

      // Unify the original type with this Pi
      return codomainEnv.unifyTerms(this.value, piType).withValue({
        tag: 'Binder',
        name: 'x',  // Default name for inferred Pi
        binderKind: { tag: 'BPi' },
        domain: domainMeta,
        body: codomainMeta
      });
    }

    throw this.expectedBinderPiError();
  }

  /**
   * Get a Type sort with a fresh level metavariable.
   * Use this when you need proper universe inference and can thread the env through.
   */
  typeSortFresh<S>(this: TCEnv<S>): { env: TCEnv<S>, sort: TTKTerm & { tag: 'Sort' } } {
    const { env, level } = this.freshLevelMeta();
    return { env, sort: { tag: 'Sort', level } };
  }

  /**
   * Get a Type sort with a fixed level (Sort 0 = Prop).
   *
   * Use `typeSortFresh()` for proper universe inference - it creates
   * a fresh level metavariable and returns the updated env.
   *
   * This method is kept for convenience in cases where universe
   * polymorphism isn't needed.
   */
  typeSort(): TTKTerm & { tag: 'Sort' } {
    return { tag: 'Sort', level: mkULit(0) };
  }

  // ERRORS
  unsolvedConstraintsError(this: TCEnv<T>): TCEnvError {
    return TCEnvError.create(`Unsolved constraints: ${this.printConstraints()}`, this);
  }

  private invalidIndexError<S>(field: string, values: S[], index: number): TCEnvError {
    return TCEnvError.create(`Invalid index ${index} for ${field} with length ${values.length}.`, this);
  }

  expectedBinderPiError(this: TCEnv<TTKTerm>): TCEnvError {
    return TCEnvError.create(`Expected binder Pi type, got: ${this.prettyPrint(this.value)}`, this);
  }

  expectedCheckTypeToBeBinderPiError(this: TCEnv<TTKTerm>, checkType: TTKTerm): TCEnvError {
    return TCEnvError.create(`Expected check type to be binder Pi type, got: ${prettyPrint(checkType)}`, this);
  }

  expectedTermsToBeDefinitionallyEqualError(this: TCEnv<TTKTerm>, lhs: TTKTerm, rhs: TTKTerm, message?: string): TCEnvError {
    return TCEnvError.create(`Expected terms to be definitionally equal: ${this.prettyPrint(lhs)} vs ${this.prettyPrint(rhs)}${message ? `: ${message}` : ''}`, this);
  }

  unificationFailedError(this: TCEnv<TTKTerm>, lhs: TTKTerm, rhs: TTKTerm, reason: 'conflict' | 'cycle'): TCEnvError {
    const reasonMsg = reason === 'conflict' ? 'conflicting heads' : 'occurs check failed (cyclic)';
    return TCEnvError.create(`Unification failed (${reasonMsg}): ${this.prettyPrint(lhs)} vs ${this.prettyPrint(rhs)}`, this);
  }

  typeDefinitionNotFoundError(name: string): TCEnvError {
    return TCEnvError.create(`Type definition not found: ${name}`, this);
  }

  typeAtIndexNotFoundInContextError(index: number): TCEnvError {
    return TCEnvError.create(`Type at index ${index} not found in context`, this);
  }

  expectedEqualLengthsError<A, B>(a: A[], b: B[], message?: string): TCEnvError {
    return TCEnvError.create(`Expected equal lengths: ${a.length} vs ${b.length}${message ? `: ${message}` : ''}`, this);
  }

  unknownTagError(data: { tag: string }, typeName: string, message?: string): TCEnvError {
    return TCEnvError.create(`Unknown tag: ${data.tag} for ${typeName}${message ? `: ${message}` : ''}`, this);
  }

  // Duplicate name errors
  nameAlreadyDefinedError(this: TCEnv<string>, existingKind: 'term' | 'inductive' | 'constructor'): TCEnvError {
    return TCEnvError.create(`Name '${this.value}' is already defined as a ${existingKind}`, this);
  }

  // Pattern variable errors
  patternVarShadowsTermError(this: TCEnv<string>): TCEnvError {
    return TCEnvError.create(`Pattern variable '${this.value}' shadows an existing term definition`, this);
  }
}

/**
 * Error Philosophy:
 *
 * Errors should be semantic and user-friendly at the top level, with technical
 * details available for those who want to dig deeper.
 *
 * - PRIMARY MESSAGE: What went wrong in terms the user understands
 *   e.g., "'Succ' expects Nat but was applied to (Nat -> Nat -> Nat)"
 *
 * - CAUSE/DETAILS: Technical details about why it failed
 *   e.g., "unification failed: (Nat -> Nat -> Nat) vs Nat"
 *
 * When catching low-level errors (like unification failures), higher-level code
 * should use `wrappedBy()` to provide a semantic message that becomes the new
 * primary, with the original error becoming the cause/detail.
 */
export abstract class TCEnvError {
  abstract get errors(): TCEnvError[];
  abstract get message(): string;
  abstract get env(): TCEnv<unknown>;
  abstract get causeStack(): string[];

  /**
   * Get the full error message including cause stack.
   * Format:
   *   <primary message>
   *   ↳ <cause 1>
   *   ↳ <cause 2>
   */
  get fullMessage(): string {
    if (this.causeStack.length === 0) {
      return this.message;
    }
    const causeLines = this.causeStack.map(cause => `↳ ${cause}`).join('\n');
    return `${this.message}\n${causeLines}`;
  }

  /**
   * Wrap this error with a new primary message.
   * The current error's message becomes a cause/detail.
   *
   * Use this when catching low-level errors to provide semantic context:
   *   catch (e) {
   *     throw e.wrappedBy("'Succ' expects Nat but was applied to ...");
   *   }
   */
  wrappedBy(primaryMessage: string): TCEnvError {
    return new TCEnvWrappedError(primaryMessage, this);
  }

  /**
   * Add a cause/detail below the current message without changing the primary.
   * Use sparingly - prefer wrappedBy() for most cases.
   */
  withCause(cause: string): TCEnvError {
    return new TCEnvCauseError(this, cause);
  }

  static create<T>(message: string, env: TCEnv<T>): TCEnvError {
    return new TCEnvErrorUnit(message, env);
  }

  static group(errors: TCEnvError[]): TCEnvError {
    return new TCEnvGroupError(errors);
  }
}

class TCEnvErrorUnit<T> extends TCEnvError {
  constructor(
    public readonly message: string,
    public readonly env: TCEnv<T>
  ) { super(); }

  get errors(): TCEnvError[] {
    return [this];
  }

  get causeStack(): string[] {
    return [];
  }
}

class TCEnvGroupError extends TCEnvError {
  constructor(
    private readonly _errors: TCEnvError[],
  ) { super(); }

  get errors(): TCEnvError[] {
    return this._errors.flatMap(e => e.errors);
  }

  get message(): string {
    return this._errors[0]?.message ?? 'Multiple errors';
  }

  get env(): TCEnv<unknown> {
    return this._errors[0]?.env;
  }

  get causeStack(): string[] {
    return this._errors[0]?.causeStack ?? [];
  }
}

/**
 * Wraps an inner error with a new primary message.
 * The inner error's message becomes a cause/detail.
 */
class TCEnvWrappedError extends TCEnvError {
  constructor(
    private readonly primaryMessage: string,
    private readonly inner: TCEnvError
  ) { super(); }

  get errors(): TCEnvError[] {
    return this.inner.errors;
  }

  get message(): string {
    return this.primaryMessage;
  }

  get env(): TCEnv<unknown> {
    return this.inner.env;
  }

  get causeStack(): string[] {
    return [this.inner.message, ...this.inner.causeStack];
  }
}

/**
 * Adds a cause/detail below the current message without changing the primary.
 */
class TCEnvCauseError extends TCEnvError {
  constructor(
    private readonly inner: TCEnvError,
    private readonly cause: string
  ) { super(); }

  get errors(): TCEnvError[] {
    return this.inner.errors;
  }

  get message(): string {
    return this.inner.message;
  }

  get env(): TCEnv<unknown> {
    return this.inner.env;
  }

  get causeStack(): string[] {
    return [...this.inner.causeStack, this.cause];
  }
}

/**
 * Validate that names in an inductive definition are not already defined.
 * Checks:
 * 1. Inductive type name is not already defined
 * 2. Constructor names are not already defined
 */
export function validateInductiveNamingConventions(env: TCEnv<InductiveDefinition>): void {
  // Validate inductive type name is not a duplicate
  validateInductiveNameNotDefined(env);

  // Validate all constructor names are not duplicates
  const ctorsEnv = env.inInductiveDefinitionConstructors();
  for (let i = 0; i < ctorsEnv.value.length; i++) {
    const ctorEnv = ctorsEnv.inInductiveDefinitionConstructor(i);
    validateConstructorNameNotDefined(ctorEnv);
  }
}

// ============================================================================
// Duplicate Name Checking
// ============================================================================

/**
 * Check what kind of definition a name already has in the definitions map.
 * Returns undefined if the name is not defined.
 */
export function getExistingDefinitionKind(definitions: DefinitionsMap, name: string): 'term' | 'inductive' | 'constructor' | undefined {
  if (definitions.terms.has(name)) {
    return 'term';
  }
  if (definitions.inductiveTypes.has(name)) {
    return 'inductive';
  }
  // Check if name is a constructor
  for (const indDef of definitions.inductiveTypes.values()) {
    for (const ctor of indDef.constructors) {
      if (ctor.name === name) {
        return 'constructor';
      }
    }
  }
  return undefined;
}

/**
 * Validate that a term name is not already defined.
 */
export function validateTermNameNotDefined(env: TCEnv<TermDefinition>): void {
  const nameEnv = env.inTermName();
  const existingKind = getExistingDefinitionKind(env.definitions, nameEnv.value);
  if (existingKind) {
    throw nameEnv.nameAlreadyDefinedError(existingKind);
  }
}

/**
 * Validate that an inductive type name is not already defined.
 */
export function validateInductiveNameNotDefined(env: TCEnv<InductiveDefinition>): void {
  const nameEnv = env.inInductiveDefinitionName();
  const existingKind = getExistingDefinitionKind(env.definitions, nameEnv.value);
  if (existingKind) {
    throw nameEnv.nameAlreadyDefinedError(existingKind);
  }
}

/**
 * Validate that a constructor name is not already defined.
 */
export function validateConstructorNameNotDefined(env: TCEnv<{ name: string; type: TTKTerm }>): void {
  const nameEnv = env.inInductiveDefinitionConstructorName();
  const existingKind = getExistingDefinitionKind(env.definitions, nameEnv.value);
  if (existingKind) {
    throw nameEnv.nameAlreadyDefinedError(existingKind);
  }
}

// ============================================================================
// Pattern Variable Validation
// ============================================================================

/**
 * Validate a pattern variable name:
 * Cannot shadow a term definition in scope
 */
export function validatePatternVarName(env: TCEnv<string>): void {
  const name = env.value;

  // Check for shadowing term definitions
  if (env.definitions.terms.has(name)) {
    throw env.patternVarShadowsTermError();
  }
}

function lookupTypeAtIndexContext(context: TTKContext, index: number): TTKTerm | undefined {
  const sigIndex = context.length - 1 - index
  const binder = context[sigIndex];
  if (!binder) {
    return undefined;
  }
  const type = binder.type;

  // Shift indices to be at tail of context
  const shiftAmount = context.length - sigIndex;
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
    // No children - holes are simple { tag: 'Hole', id: string }
  } else if (term.tag === 'Meta') {
    // No children - metas are simple { tag: 'Meta', id: string }
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
