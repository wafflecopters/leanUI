import { createNamedArgInfoLookup, createTCEnv, type DefinitionsMap } from './term';
import { inferType } from './checker';
import { elabToKernelWithMap } from './elab';
import type { ElabMap } from '../types/source-position';
import type { TTKTerm } from './kernel';
import {
  kernelTypeToSurface,
} from './compile-bridge';
import {
  mkAppTT,
  type TTerm,
} from './surface';

export function resolveWithScrutineeTypes(
  declType: TTerm,
  allScrutinees: TTerm[],
  definitions: DefinitionsMap
): TTerm {
  if (allScrutinees.length === 0) return declType;

  const numExistingScrutinees = countScrutineesBeforeHoles(declType);
  const functionParams = extractFunctionParams(declType);
  const holeSubstitutions = new Map<string, TTerm>();

  for (let i = 0; i < allScrutinees.length; i++) {
    const scrutinee = allScrutinees[i];
    const holeName = `_scrut${i}_type`;
    const isFromParentWith = i < numExistingScrutinees;

    if (isFromParentWith) {
      const simpleType = tryExtractReturnType(scrutinee, definitions);
      if (simpleType) {
        holeSubstitutions.set(holeName, simpleType);
      }
      continue;
    }

    try {
      const elabMap: ElabMap = new Map();
      const kernelScrutinee = elabToKernelWithMap(
        scrutinee,
        elabMap,
        [],
        [],
        undefined,
        createNamedArgInfoLookup(definitions)
      );

      let env = createTCEnv({ definitions, options: { mode: 'check' } });
      for (const param of functionParams) {
        env = env.extendTTKContext(param.name, param.type);
      }

      try {
        const inferResult = inferType(env.withValue(kernelScrutinee));
        const solvedResult = inferResult.solveMetasAndConstraints({ liftMetasToFullContext: false });
        const inferredType = solvedResult.zonkTerm(inferResult.value);
        holeSubstitutions.set(holeName, kernelTypeToSurface(inferredType, definitions));
      } catch {
        const simpleType = tryExtractReturnType(scrutinee, definitions);
        if (simpleType) {
          holeSubstitutions.set(holeName, simpleType);
        }
      }
    } catch {
      // Leave unresolved when elaboration or inference fails.
    }
  }

  return substituteHoles(declType, holeSubstitutions);
}

function tryExtractReturnType(term: TTerm, definitions: DefinitionsMap): TTerm | undefined {
  let current = term;
  const args: TTerm[] = [];
  while (current.tag === 'App') {
    args.unshift(current.arg);
    current = current.fn;
  }

  if (current.tag !== 'Const') {
    return undefined;
  }

  const def = definitions.terms.get(current.name);
  const type = def?.type;
  if (!type) {
    return undefined;
  }

  let argIdx = 0;
  let currentType = kernelTypeToSurface(type, definitions);
  while (
    argIdx < args.length &&
    (currentType.tag === 'Binder' || currentType.tag === 'MultiBinder') &&
    currentType.binderKind.tag === 'BPiTT'
  ) {
    if (currentType.tag === 'Binder') {
      currentType = currentType.body;
      argIdx += 1;
      continue;
    }

    const binderCount = currentType.names.length;
    const remainingArgs = args.length - argIdx;
    const consumed = Math.min(binderCount, remainingArgs);
    currentType = currentType.body;
    argIdx += consumed;
  }

  return argIdx === args.length ? currentType : undefined;
}

export function countScrutineesBeforeHoles(type: TTerm): number {
  let count = 0;
  let currentType = type;

  while (true) {
    if (currentType.tag === 'Binder' && currentType.binderKind.tag === 'BPiTT') {
      if (currentType.name.startsWith('_scrut') && currentType.domain && currentType.domain.tag === 'Hole') {
        break;
      }
      if (currentType.name.startsWith('_scrut')) {
        count++;
      }
      currentType = currentType.body;
    } else if (currentType.tag === 'MultiBinder' && currentType.binderKind.tag === 'BPiTT') {
      const hasScrutName = currentType.names.some(name => name.startsWith('_scrut'));
      if (hasScrutName && currentType.domain.tag === 'Hole') {
        break;
      }
      for (const name of currentType.names) {
        if (name.startsWith('_scrut')) {
          count++;
        }
      }
      currentType = currentType.body;
    } else {
      break;
    }
  }

  return count;
}

function extractFunctionParams(type: TTerm): Array<{ name: string; type: TTKTerm }> {
  const params: Array<{ name: string; type: TTKTerm }> = [];
  let currentType = type;

  while (true) {
    if (currentType.tag === 'Binder' && currentType.binderKind.tag === 'BPiTT') {
      if (currentType.name.startsWith('_scrut')) {
        break;
      }
      const domain = currentType.domain;
      if (domain && isHoleType(domain)) {
        break;
      }
      if (domain) {
        const elabMap: ElabMap = new Map();
        const kernelDomain = elabToKernelWithMap(domain, elabMap, [], []);
        params.push({ name: currentType.name, type: kernelDomain });
      }
      currentType = currentType.body;
    } else if (currentType.tag === 'MultiBinder' && currentType.binderKind.tag === 'BPiTT') {
      if (currentType.names.some(name => name.startsWith('_scrut'))) {
        break;
      }
      if (isHoleType(currentType.domain)) {
        break;
      }
      const elabMap: ElabMap = new Map();
      const kernelDomain = elabToKernelWithMap(currentType.domain, elabMap, [], []);
      for (const name of currentType.names) {
        params.push({ name, type: kernelDomain });
      }
      currentType = currentType.body;
    } else {
      break;
    }
  }

  return params;
}

function isHoleType(term: TTerm): boolean {
  return term.tag === 'Hole';
}

export function substituteHoles(term: TTerm, substitutions: Map<string, TTerm>): TTerm {
  switch (term.tag) {
    case 'Hole': {
      const substitution = substitutions.get(term.id);
      return substitution ?? term;
    }
    case 'Var':
    case 'Const':
    case 'Sort':
    case 'ULevel':
    case 'ULit':
    case 'UOmega':
    case 'NatLit':
    case 'RatLit':
      return term;
    case 'App':
      return mkAppTT(
        substituteHoles(term.fn, substitutions),
        substituteHoles(term.arg, substitutions)
      );
    case 'Binder': {
      const newDomain = term.domain ? substituteHoles(term.domain, substitutions) : undefined;
      const newBody = substituteHoles(term.body, substitutions);
      let newBinderKind = term.binderKind;
      if (term.binderKind.tag === 'BLetTT') {
        newBinderKind = {
          tag: 'BLetTT',
          defVal: substituteHoles(term.binderKind.defVal, substitutions),
        };
      }
      return { ...term, domain: newDomain, body: newBody, binderKind: newBinderKind };
    }
    case 'MultiBinder': {
      const newDomain = substituteHoles(term.domain, substitutions);
      const newBody = substituteHoles(term.body, substitutions);
      let newBinderKind = term.binderKind;
      if (term.binderKind.tag === 'BLetTT') {
        newBinderKind = {
          tag: 'BLetTT',
          defVal: substituteHoles(term.binderKind.defVal, substitutions),
        };
      }
      return { ...term, domain: newDomain, body: newBody, binderKind: newBinderKind };
    }
    case 'Match': {
      const newScrutinee = substituteHoles(term.scrutinee, substitutions);
      const newClauses = term.clauses.map(clause => ({
        ...clause,
        rhs: substituteHoles(clause.rhs, substitutions),
      }));
      return { ...term, scrutinee: newScrutinee, clauses: newClauses };
    }
    case 'Annot': {
      const newTerm = substituteHoles(term.term, substitutions);
      const newType = substituteHoles(term.type, substitutions);
      return { ...term, term: newTerm, type: newType };
    }
    case 'TacticBlock':
      return term;
    case 'WithClause':
      return term;
    case 'AbsurdMarker':
      return term;
    default: {
      const _exhaustive: never = term;
      return _exhaustive;
    }
  }
}
