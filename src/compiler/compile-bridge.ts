import type { DefinitionsMap, NamedArgMap } from './term';
import type { TTKTerm } from './kernel';
import {
  mkAppTT,
  mkConstTT,
  mkHoleTT,
  mkPropTT,
  mkPiTT,
  mkULitTT,
  mkVarTT,
  type TTerm,
} from './surface';

/**
 * Convert a surface TTerm to a kernel TTKTerm (structural conversion).
 * Only handles the term forms that commonly appear in scrutinee expressions.
 */
export function surfaceTermToKernel(term: TTerm): TTKTerm {
  switch (term.tag) {
    case 'Var':
      return { tag: 'Var', index: term.index };
    case 'Const':
      return { tag: 'Const', name: term.name };
    case 'App':
      return { tag: 'App', fn: surfaceTermToKernel(term.fn), arg: surfaceTermToKernel(term.arg) };
    case 'Hole':
      return { tag: 'Hole', id: term.id };
    case 'Sort':
      return { tag: 'Sort', level: surfaceTermToKernel(term.level) };
    case 'ULit':
      return { tag: 'ULit', n: term.n };
    default:
      return { tag: 'Hole', id: `_unsupported_${term.tag}` };
  }
}

/**
 * Look up the namedArgMap for a constant (term, inductive type, or constructor).
 */
export function lookupNamedArgMap(
  name: string,
  definitions: DefinitionsMap
): NamedArgMap | undefined {
  const termDef = definitions.terms.get(name);
  if (termDef?.namedArgMap) return termDef.namedArgMap;

  const indDef = definitions.inductiveTypes.get(name);
  if (indDef?.namedArgMap) return indDef.namedArgMap;

  const indName = definitions.inductiveNameOfConstructor.get(name);
  if (indName) {
    const parentInd = definitions.inductiveTypes.get(indName);
    if (parentInd) {
      const ctor = parentInd.constructors.find(candidate => candidate.name === name);
      if (ctor?.namedArgMap) return ctor.namedArgMap;
    }
  }

  return undefined;
}

/**
 * Collect an application spine: f a1 a2 ... an → { head: f, args: [a1, a2, ..., an] }
 */
export function collectAppSpine(term: TTKTerm): { head: TTKTerm; args: TTKTerm[] } {
  const args: TTKTerm[] = [];
  let head = term;
  while (head.tag === 'App') {
    args.unshift(head.arg);
    head = head.fn;
  }
  return { head, args };
}

/**
 * Convert a kernel TTKTerm to a surface TTerm (structural conversion).
 * Only handles the type forms that commonly appear as scrutinee types.
 *
 * When definitions are provided, implicit arguments in applications are
 * omitted so the resulting surface term can be re-elaborated correctly.
 */
export function kernelTypeToSurface(term: TTKTerm, definitions?: DefinitionsMap): TTerm {
  const prop = mkPropTT();

  switch (term.tag) {
    case 'Var':
      return mkVarTT(term.index);
    case 'Const':
      return mkConstTT(term.name);
    case 'App': {
      if (definitions) {
        const { head, args } = collectAppSpine(term);
        if (head.tag === 'Const') {
          const namedArgMap = lookupNamedArgMap(head.name, definitions);
          if (namedArgMap && namedArgMap.size > 0) {
            const implicitPositions = new Set<number>(namedArgMap.values());
            let result: TTerm = mkConstTT(head.name);
            for (let i = 0; i < args.length; i++) {
              if (!implicitPositions.has(i)) {
                result = mkAppTT(result, kernelTypeToSurface(args[i], definitions));
              }
            }
            return result;
          }
        }
      }
      return mkAppTT(
        kernelTypeToSurface(term.fn, definitions),
        kernelTypeToSurface(term.arg, definitions)
      );
    }
    case 'Sort':
      return { tag: 'Sort', level: kernelTypeToSurface(term.level, definitions) } as TTerm;
    case 'ULit':
      return mkULitTT(term.n);
    case 'Hole':
      return mkHoleTT(term.id, prop);
    case 'Binder':
      if (term.binderKind.tag === 'BPi') {
        return mkPiTT(
          kernelTypeToSurface(term.domain, definitions),
          kernelTypeToSurface(term.body, definitions),
          term.name
        );
      }
      return mkHoleTT('_unsupported_binder', prop);
    default:
      return mkHoleTT(`_unsupported_${term.tag}`, prop);
  }
}

/**
 * Replace a Hole with a given name in a surface term tree.
 */
export function replaceHoleInSurfaceTerm(
  term: TTerm,
  holeName: string,
  replacement: TTerm
): TTerm {
  switch (term.tag) {
    case 'Hole':
      return term.id === holeName ? replacement : term;
    case 'Binder': {
      const newDomain = term.domain
        ? replaceHoleInSurfaceTerm(term.domain, holeName, replacement)
        : undefined;
      const newBody = replaceHoleInSurfaceTerm(term.body, holeName, replacement);
      if (newDomain === term.domain && newBody === term.body) return term;
      return { ...term, domain: newDomain, body: newBody };
    }
    case 'MultiBinder': {
      const newDomain = replaceHoleInSurfaceTerm(term.domain, holeName, replacement);
      const newBody = replaceHoleInSurfaceTerm(term.body, holeName, replacement);
      if (newDomain === term.domain && newBody === term.body) return term;
      return { ...term, domain: newDomain, body: newBody };
    }
    case 'App': {
      const newFn = replaceHoleInSurfaceTerm(term.fn, holeName, replacement);
      const newArg = replaceHoleInSurfaceTerm(term.arg, holeName, replacement);
      if (newFn === term.fn && newArg === term.arg) return term;
      return { ...term, fn: newFn, arg: newArg };
    }
    case 'Annot': {
      const newTerm = replaceHoleInSurfaceTerm(term.term, holeName, replacement);
      const newType = replaceHoleInSurfaceTerm(term.type, holeName, replacement);
      if (newTerm === term.term && newType === term.type) return term;
      return { tag: 'Annot', term: newTerm, type: newType };
    }
    default:
      return term;
  }
}
