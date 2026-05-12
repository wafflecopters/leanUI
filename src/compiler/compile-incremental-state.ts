import type { BlockContributions } from './incremental';
import type { ConstructorParamNames } from './elab';
import type { DefinitionsMap, InductiveDefinition, TermDefinition } from './term';
import type { SymbolContext } from '../types/name-resolution';

export function computeBlockContributions(
  beforeDefs: DefinitionsMap,
  afterDefs: DefinitionsMap,
  beforeSymbols: SymbolContext,
  afterSymbols: SymbolContext,
  beforeCtorParams: ConstructorParamNames,
  afterCtorParams: ConstructorParamNames,
): BlockContributions {
  const terms: [string, TermDefinition][] = [];
  for (const [name, def] of afterDefs.terms) {
    if (!beforeDefs.terms.has(name)) {
      terms.push([name, def]);
    }
  }

  const inductiveTypes: [string, InductiveDefinition][] = [];
  for (const [name, def] of afterDefs.inductiveTypes) {
    if (!beforeDefs.inductiveTypes.has(name)) {
      inductiveTypes.push([name, def]);
    }
  }

  const constructorMappings: [string, string][] = [];
  for (const [ctor, ind] of afterDefs.inductiveNameOfConstructor) {
    if (!beforeDefs.inductiveNameOfConstructor.has(ctor)) {
      constructorMappings.push([ctor, ind]);
    }
  }

  const symbolNames: string[] = [];
  for (const name of afterSymbols) {
    if (!beforeSymbols.has(name)) {
      symbolNames.push(name);
    }
  }

  const constructorParamEntries: [string, unknown[]][] = [];
  for (const [name, params] of afterCtorParams) {
    if (!beforeCtorParams.has(name)) {
      constructorParamEntries.push([name, params]);
    }
  }

  return { terms, inductiveTypes, constructorMappings, symbolNames, constructorParamEntries };
}

export function applyBlockContributions(
  definitions: DefinitionsMap,
  symbolContext: SymbolContext,
  constructorParamNames: ConstructorParamNames,
  contributions: BlockContributions,
): {
  definitions: DefinitionsMap;
  symbolContext: SymbolContext;
  constructorParamNames: ConstructorParamNames;
} {
  let newTerms = definitions.terms;
  if (contributions.terms.length > 0) {
    newTerms = new Map(newTerms);
    for (const [name, def] of contributions.terms) {
      newTerms.set(name, def);
    }
  }

  let newIndTypes = definitions.inductiveTypes;
  let newCtorMap = definitions.inductiveNameOfConstructor;
  if (contributions.inductiveTypes.length > 0) {
    newIndTypes = new Map(newIndTypes);
    for (const [name, def] of contributions.inductiveTypes) {
      newIndTypes.set(name, def);
    }
  }
  if (contributions.constructorMappings.length > 0) {
    newCtorMap = new Map(newCtorMap);
    for (const [ctor, ind] of contributions.constructorMappings) {
      newCtorMap.set(ctor, ind);
    }
  }

  // Carry forward ALL impl/coercion/op registries (incl. the recently-added
  // intImplByCtor / ofIntByTargetHead / simpLemmas). Forgetting any of these
  // here silently drops a registration when the cached-block path replays,
  // so e.g. @impl=nat from an earlier block disappears for the current
  // block and NatLit inference reverts to "no @impl=nat registered".
  definitions = {
    ...definitions,
    terms: newTerms,
    inductiveTypes: newIndTypes,
    inductiveNameOfConstructor: newCtorMap,
  };

  if (contributions.symbolNames.length > 0) {
    symbolContext = new Set(symbolContext);
    for (const name of contributions.symbolNames) {
      symbolContext.add(name);
    }
  }

  if (contributions.constructorParamEntries.length > 0) {
    constructorParamNames = new Map(constructorParamNames);
    for (const [name, params] of contributions.constructorParamEntries) {
      constructorParamNames.set(name, params as any);
    }
  }

  return { definitions, symbolContext, constructorParamNames };
}
