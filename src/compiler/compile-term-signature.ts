import type { ElabDeclaration } from './compile-types';
import { extractArgNamedArgInfos, extractNamedArgMap, type NamedArgMap, countParameters } from './elab';
import { inferType } from './checker';
import type { TTKTerm } from './kernel';
import type { TypeInfoMap } from './type-info';
import {
  addDefinitionInTCEnv,
  createTCEnv,
  type ArgNamedArgInfos,
  type DefinitionsMap,
  type TCEnv,
  TCEnvError,
  type TermDefinition,
  validateTermNameNotDefined,
} from './term';

export interface PrepareTermSignatureOptions {
  allowUnsolvedSigMetas?: boolean;
  assumeK?: boolean;
  typeInfoCollector?: TypeInfoMap;
  warningsCollector?: TCEnvError[];
}

export interface PreparedTermSignature {
  termEnv: TCEnv<TermDefinition>;
  zonkedKernelType: TTKTerm;
  namedArgMap?: NamedArgMap;
  argNamedArgInfos?: ArgNamedArgInfos;
  totalArity?: number;
}

function failCheck(message: string, definitions: DefinitionsMap, assumeK?: boolean): { success: false; errors: TCEnvError[] } {
  const env = createTCEnv({ definitions, options: { mode: 'check', assumeK } });
  return {
    success: false,
    errors: [TCEnvError.create(message, env)],
  };
}

/**
 * Convert any remaining unsolved Meta nodes in a term to Hole nodes.
 * Used after zonking elaborated type signatures so unresolved placeholders can
 * still flow through later pattern-matching code as explicit holes.
 */
export function unsolvedMetasToHoles(term: TTKTerm): TTKTerm {
  switch (term.tag) {
    case 'Meta':
      return { tag: 'Hole', id: term.id };
    case 'App':
      return { tag: 'App', fn: unsolvedMetasToHoles(term.fn), arg: unsolvedMetasToHoles(term.arg) };
    case 'Binder': {
      const binderKind = term.binderKind.tag === 'BLet'
        ? { tag: 'BLet' as const, defVal: unsolvedMetasToHoles(term.binderKind.defVal) }
        : term.binderKind;
      return {
        tag: 'Binder',
        name: term.name,
        binderKind,
        domain: unsolvedMetasToHoles(term.domain),
        body: unsolvedMetasToHoles(term.body),
      };
    }
    case 'Sort': {
      const level = unsolvedMetasToHoles(term.level);
      return level === term.level ? term : { tag: 'Sort', level };
    }
    case 'Annot':
      return { tag: 'Annot', term: unsolvedMetasToHoles(term.term), type: unsolvedMetasToHoles(term.type) };
    case 'Match':
      return {
        tag: 'Match',
        scrutinee: unsolvedMetasToHoles(term.scrutinee),
        clauses: term.clauses.map(clause => ({ ...clause, rhs: unsolvedMetasToHoles(clause.rhs) })),
      };
    default:
      return term;
  }
}

/**
 * Check a term declaration's signature, solve signature-level constraints, and
 * seed the definition environment for subsequent value checking.
 */
export function prepareTermSignature(
  decl: ElabDeclaration,
  definitions: DefinitionsMap,
  options: PrepareTermSignatureOptions = {},
): { success: true; prepared: PreparedTermSignature } | { success: false; errors: TCEnvError[] } {
  if (!decl.name) {
    return failCheck('Term declaration is ill-formed (no name)', definitions, options.assumeK);
  }

  if (decl.kind !== 'term') {
    return failCheck('Declaration is not a term', definitions, options.assumeK);
  }

  if (!decl.kernelType) {
    return failCheck('Term declaration is ill-formed', definitions, options.assumeK);
  }

  let env = createTCEnv({
    definitions,
    options: {
      mode: 'check',
      allowDuplicatePiNames: options.allowUnsolvedSigMetas,
      assumeK: options.assumeK,
    },
    typeInfoCollector: options.typeInfoCollector,
    warningsCollector: options.warningsCollector,
  });

  try {
    const placeholderValue: TTKTerm = {
      tag: 'Match',
      scrutinee: { tag: 'Hole', id: '_scrutinee' },
      clauses: [],
    };

    let termEnv = env.withValue<TermDefinition>({
      name: decl.name,
      type: decl.kernelType,
      value: placeholderValue,
    });

    validateTermNameNotDefined(termEnv);

    const sigResult = inferType(termEnv.inTermType());
    const solvedSigResult = sigResult.solveMetasAndConstraints({ liftMetasToFullContext: false });
    const unsolvedSigMetas = Array.from(solvedSigResult.metaVars.values()).filter(meta => !meta.solution && !meta.isHole);
    if (unsolvedSigMetas.length > 0 && !options.allowUnsolvedSigMetas) {
      return {
        success: false,
        errors: [TCEnvError.create('Checking the signature produced unsolved metas.', env)],
      };
    }

    const namedArgMap = decl.surfaceType ? extractNamedArgMap(decl.surfaceType) : undefined;
    const argNamedArgInfos = decl.surfaceType ? extractArgNamedArgInfos(decl.surfaceType) : undefined;
    const totalArity = decl.surfaceType ? countParameters(decl.surfaceType) : undefined;
    const sigElaboratedType = sigResult.elaboratedTerm ?? decl.kernelType;
    const zonkedKernelType = unsolvedMetasToHoles(solvedSigResult.zonkTerm(sigElaboratedType));

    termEnv = addDefinitionInTCEnv(
      termEnv,
      decl.name,
      zonkedKernelType,
      namedArgMap,
      argNamedArgInfos?.size ? argNamedArgInfos : undefined,
    );

    return {
      success: true,
      prepared: {
        termEnv,
        zonkedKernelType,
        namedArgMap,
        argNamedArgInfos: argNamedArgInfos?.size ? argNamedArgInfos : undefined,
        totalArity,
      },
    };
  } catch (error) {
    if (error instanceof TCEnvError) {
      return { success: false, errors: [error] };
    }
    return {
      success: false,
      errors: [TCEnvError.create(error instanceof Error ? error.message : String(error), env)],
    };
  }
}
