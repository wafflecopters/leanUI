import { arraySeg, appendPath, fieldSeg, serializeIndexPath, type ElabMap, type IndexPath } from '../types/source-position';
import { elabPatternToKernelWithMap, elabToKernelWithMap, fixRhsForConstructorPatterns, fixRhsForVariablePatterns, hasNamedPatterns, reorderPatterns, applyVarPermutation, type NamedArgMap } from './elab';
import { type TClause } from './surface';
import { checkMatchClause, arePatternsAbsurd } from './patterns';
import { checkStructuralRecursion } from './recursion';
import { checkTotality, type TotalityResult } from './totality';
import { countPiBindersWhnf, whnf } from './whnf';
import { type DefinitionsMap, createNamedArgInfoLookup, MatchPartIndex, type TCEnv, TCEnvError, type TermDefinition, TermDefinitionPartIndex, extractPiSpine } from './term';
import { countPiBinders, } from './term';
import { prettyPrintPattern, prettyPrintPatternList, type TTKClause, type TTKPattern, type TTKTerm } from './kernel';

function getNthPiArgType(type: TTKTerm, n: number): TTKTerm | null {
  let current = type;
  for (let i = 0; i < n; i++) {
    if (current.tag !== 'Binder' || current.binderKind.tag !== 'BPi') {
      return null;
    }
    current = current.body;
  }
  if (current.tag !== 'Binder' || current.binderKind.tag !== 'BPi') {
    return null;
  }
  return current.domain;
}

function extractInductiveTypeName(type: TTKTerm, definitions: DefinitionsMap): string | null {
  let head = type;
  while (head.tag === 'App') {
    head = head.fn;
  }

  if (head.tag === 'Const' && definitions.inductiveTypes.has(head.name)) {
    return head.name;
  }

  return null;
}

export function tryCaseSplitsInSearchOfAbsurdity(
  termName: string,
  patterns: TTKPattern[],
  type: TTKTerm,
  definitions: DefinitionsMap,
  env: TCEnv<unknown>
): boolean {
  const expectedArgCount = countPiBinders(type);

  const trySplitAtPosition = (pos: number): boolean => {
    const argType = getNthPiArgType(type, pos);
    if (!argType) return false;

    const typeName = extractInductiveTypeName(argType, definitions);
    if (!typeName) return false;

    const inductiveDef = definitions.inductiveTypes.get(typeName);
    if (!inductiveDef) return false;

    if (inductiveDef.constructors.length === 0) {
      return true;
    }

    let allConstructorsFail = true;
    for (const ctor of inductiveDef.constructors) {
      const ctorArity = countPiBinders(ctor.type);
      const ctorPattern: TTKPattern = {
        tag: 'PCtor',
        name: ctor.name,
        args: Array(ctorArity).fill(null).map(() => ({ tag: 'PWild' as const, name: '_' })),
      };

      const newPatterns: TTKPattern[] = [];
      for (let j = 0; j < expectedArgCount; j++) {
        if (j === pos) {
          newPatterns.push(ctorPattern);
        } else if (j < patterns.length) {
          newPatterns.push(patterns[j]);
        } else {
          newPatterns.push({ tag: 'PWild', name: '_' });
        }
      }

      const newEnv = env.withValue(newPatterns);
      if (!arePatternsAbsurd(termName, newEnv, type)) {
        allConstructorsFail = false;
        break;
      }
    }

    return allConstructorsFail;
  };

  const replacePatternAtPath = (
    pats: TTKPattern[],
    path: number[],
    newPattern: TTKPattern
  ): TTKPattern[] => {
    if (path.length === 0) return pats;

    const [first, ...rest] = path;
    return pats.map((p, i) => {
      if (i !== first) return p;
      if (rest.length === 0) return newPattern;

      if (p.tag === 'PCtor') {
        return { ...p, args: replacePatternAtPath(p.args, rest, newPattern) };
      }
      return p;
    });
  };

  const trySplitAtPath = (path: number[], argType: TTKTerm): boolean => {
    const typeName = extractInductiveTypeName(argType, definitions);
    if (!typeName) return false;

    const inductiveDef = definitions.inductiveTypes.get(typeName);
    if (!inductiveDef) return false;

    if (inductiveDef.constructors.length === 0) {
      return true;
    }

    let allConstructorsFail = true;
    for (const ctor of inductiveDef.constructors) {
      const ctorArity = countPiBinders(ctor.type);
      const ctorPattern: TTKPattern = {
        tag: 'PCtor',
        name: ctor.name,
        args: Array(ctorArity).fill(null).map(() => ({ tag: 'PWild' as const, name: '_' })),
      };

      const paddedPatterns: TTKPattern[] = [];
      for (let j = 0; j < expectedArgCount; j++) {
        if (j < patterns.length) {
          paddedPatterns.push(patterns[j]);
        } else {
          paddedPatterns.push({ tag: 'PWild', name: '_' });
        }
      }

      const newPatterns = replacePatternAtPath(paddedPatterns, path, ctorPattern);
      const newEnv = env.withValue(newPatterns);
      if (!arePatternsAbsurd(termName, newEnv, type)) {
        allConstructorsFail = false;
        break;
      }
    }

    return allConstructorsFail;
  };

  const collectWildcardPaths = (
    pattern: TTKPattern,
    basePath: number[]
  ): { path: number[]; ctorName: string; argIndex: number }[] => {
    const results: { path: number[]; ctorName: string; argIndex: number }[] = [];

    if (pattern.tag === 'PCtor') {
      for (let i = 0; i < pattern.args.length; i++) {
        const arg = pattern.args[i];
        const argPath = [...basePath, i];

        if (arg.tag === 'PWild' || arg.tag === 'PVar') {
          results.push({ path: argPath, ctorName: pattern.name, argIndex: i });
        } else if (arg.tag === 'PCtor') {
          results.push(...collectWildcardPaths(arg, argPath));
        }
      }
    }

    return results;
  };

  const getConstructorType = (ctorName: string): TTKTerm | undefined => {
    const inductiveName = definitions.inductiveNameOfConstructor.get(ctorName);
    if (!inductiveName) return undefined;
    const inductiveDef = definitions.inductiveTypes.get(inductiveName);
    if (!inductiveDef) return undefined;
    const ctor = inductiveDef.constructors.find(c => c.name === ctorName);
    return ctor?.type;
  };

  for (let pos = 0; pos < patterns.length; pos++) {
    const pattern = patterns[pos];
    if (pattern.tag === 'PVar' || pattern.tag === 'PWild') {
      if (trySplitAtPosition(pos)) {
        return true;
      }
    }
  }

  for (let pos = patterns.length; pos < expectedArgCount; pos++) {
    if (trySplitAtPosition(pos)) {
      return true;
    }
  }

  for (let pos = 0; pos < patterns.length; pos++) {
    const pattern = patterns[pos];
    if (pattern.tag === 'PCtor') {
      const wildcardPaths = collectWildcardPaths(pattern, [pos]);

      for (const { path, ctorName, argIndex } of wildcardPaths) {
        const ctorType = getConstructorType(ctorName);
        if (!ctorType) continue;

        const argType = getNthPiArgType(ctorType, argIndex);
        if (!argType) continue;

        if (trySplitAtPath(path, argType)) {
          return true;
        }
      }
    }
  }

  return false;
}

function checkMatchClauseFromSurface(
  termName: string,
  surfaceClause: TClause,
  type: TTKTerm,
  termEnv: TCEnv<TermDefinition>,
  elabMap: ElabMap,
  clauseIndex: number,
  originalSurfaceIndex: number,
  namedArgMap: NamedArgMap | undefined,
  totalArity: number | undefined,
  argNamedArgInfos?: import('./term').ArgNamedArgInfos,
): TTKClause {
  const clauseSurfacePath: IndexPath = [
    { kind: 'field', name: 'value' },
    { kind: 'field', name: 'clauses' },
    { kind: 'array', index: originalSurfaceIndex },
  ];
  const clauseKernelPath: IndexPath = [
    { kind: 'field', name: 'value' },
    { kind: 'field', name: 'clauses' },
    { kind: 'array', index: clauseIndex },
  ];

  let patternsToElab = surfaceClause.patterns;
  let rhsToElab = surfaceClause.rhs;
  const hasClauseNamedPatterns = surfaceClause.namedPatterns && surfaceClause.namedPatterns.length > 0;
  let sourceIndexMap: (number | null)[] | undefined;

  if (namedArgMap && namedArgMap.size > 0) {
    const reorderResult = reorderPatterns(surfaceClause.patterns, namedArgMap, surfaceClause.namedPatterns, totalArity);
    if ('error' in reorderResult && reorderResult.error !== undefined) {
      throw TCEnvError.create(reorderResult.error, termEnv);
    }
    patternsToElab = reorderResult.ordered!;
    sourceIndexMap = reorderResult.sourceIndexMap;

    if (hasNamedPatterns(surfaceClause.patterns) || hasClauseNamedPatterns) {
      rhsToElab = applyVarPermutation(surfaceClause.rhs, reorderResult.varIndexPermutation!);
    }
  }

  rhsToElab = fixRhsForConstructorPatterns(patternsToElab, rhsToElab, termEnv.definitions);
  rhsToElab = fixRhsForVariablePatterns(patternsToElab, rhsToElab, termEnv.definitions);

  const kernelPatterns: TTKPattern[] = patternsToElab.map((pattern, patternIndex) => {
    const sourcePatternIndex = sourceIndexMap?.[patternIndex] ?? patternIndex;
    const effectiveSourceIndex = sourcePatternIndex ?? patternIndex;
    const patternSurfacePath = appendPath(clauseSurfacePath, fieldSeg('patterns'), arraySeg(effectiveSourceIndex));
    const patternKernelPath = appendPath(clauseKernelPath, fieldSeg('patterns'), arraySeg(patternIndex));
    return elabPatternToKernelWithMap(pattern, elabMap, patternSurfacePath, patternKernelPath);
  });

  if (sourceIndexMap) {
    for (let i = 0; i < sourceIndexMap.length; i++) {
      if (sourceIndexMap[i] === null) {
        const syntheticPath = serializeIndexPath(appendPath(clauseKernelPath, fieldSeg('patterns'), arraySeg(i)));
        elabMap.delete(syntheticPath);
      }
    }
  }

  elabMap.set(serializeIndexPath(clauseKernelPath), serializeIndexPath(clauseSurfacePath));

  const rhsSurfacePath = appendPath(clauseSurfacePath, fieldSeg('rhs'));
  const rhsKernelPath = appendPath(clauseKernelPath, fieldSeg('rhs'));

  const baseNamedArgLookup = createNamedArgInfoLookup(termEnv.definitions);
  const appNamedArgLookup = (name: string) => {
    if (name === termName && namedArgMap && namedArgMap.size > 0) {
      return {
        namedArgMap,
        totalArity: totalArity ?? 0,
        argNamedArgInfos: argNamedArgInfos?.size ? argNamedArgInfos : undefined,
      };
    }
    return baseNamedArgLookup(name);
  };

  const kernelRhs = elabToKernelWithMap(
    rhsToElab,
    elabMap,
    rhsSurfacePath,
    rhsKernelPath,
    namedArgMap,
    appNamedArgLookup
  );

  const fullKernelClause: TTKClause = {
    patterns: kernelPatterns,
    rhs: kernelRhs,
  };

  const clauseEnv = termEnv.atIndexPathAndValue(
    [...termEnv.indexPath, TermDefinitionPartIndex.Value, MatchPartIndex.Clauses, arraySeg(clauseIndex)],
    fullKernelClause
  );
  const checkedClauseEnv = checkMatchClause(termName, clauseEnv, type);

  return checkedClauseEnv.value;
}

export function checkTermValue(
  name: string | undefined,
  termEnv: TCEnv<TermDefinition>,
  type: TTKTerm,
  surfaceClauses: TClause[],
  surfaceClauseIndices: number[],
  elabMap: ElabMap,
  namedArgMap: NamedArgMap | undefined,
  totalArity: number | undefined,
  annotatedAbsurdClauses: number[] = [],
  options?: { skipTotality?: boolean; withScrutineeCount?: number; newScrutineeCount?: number },
  argNamedArgInfos?: import('./term').ArgNamedArgInfos,
): { success: false, errors: TCEnvError[]; totalityResult?: TotalityResult } | { success: true, checkedValue: TTKTerm; totalityResult?: TotalityResult } {
  const errors: TCEnvError[] = [];
  const checkedClauses: TTKClause[] = [];

  const hasNoClauses = surfaceClauses.length === 0;
  const firstClauseRootPatternsCount = hasNoClauses ? 0 : surfaceClauses[0].patterns.length;
  const maxAllowedPatternsCount = countPiBindersWhnf(type, termEnv.definitions);

  for (let clauseIndex = 0; clauseIndex < surfaceClauses.length; clauseIndex++) {
    const surfaceClause = surfaceClauses[clauseIndex];
    const originalSurfaceIndex = surfaceClauseIndices[clauseIndex];
    const rootPatternsCount = surfaceClause.patterns.length;

    if (rootPatternsCount !== firstClauseRootPatternsCount) {
      errors.push(TCEnvError.create(`Mismatch in pattern count: clause ${clauseIndex + 1} has ${rootPatternsCount} patterns, expected ${firstClauseRootPatternsCount}.`, termEnv));
    } else if (rootPatternsCount > maxAllowedPatternsCount) {
      errors.push(TCEnvError.create(`Pattern count exceeds type binders count: clause ${clauseIndex + 1} has ${rootPatternsCount} patterns, expected <= ${maxAllowedPatternsCount}.`, termEnv));
    } else {
      try {
        const checkedClause = checkMatchClauseFromSurface(
          name ?? '???',
          surfaceClause,
          type,
          termEnv,
          elabMap,
          clauseIndex,
          originalSurfaceIndex,
          namedArgMap,
          totalArity,
          argNamedArgInfos
        );
        checkedClauses.push(checkedClause);
      } catch (e) {
        const clauseEnv = termEnv.atIndexPath(
          appendPath(termEnv.indexPath, fieldSeg('value'), fieldSeg('clauses'), arraySeg(originalSurfaceIndex))
        );
        if (e instanceof TCEnvError) {
          errors.push(e);
        } else {
          errors.push(TCEnvError.create(String(e), clauseEnv));
        }
      }
    }
  }

  if (errors.length > 0) {
    return { success: false, errors };
  }

  const checkedValue: TTKTerm = {
    tag: 'Match',
    scrutinee: { tag: 'Hole', id: '_scrutinee' },
    clauses: checkedClauses,
  };

  if (name) {
    const recursionResult = checkStructuralRecursion(name, checkedClauses);
    if (!recursionResult.isValid) {
      const recursionErrors = recursionResult.errors.map(({ clauseIndex, error }) => {
        const errorPath: IndexPath = [
          fieldSeg('value'),
          fieldSeg('clauses'),
          arraySeg(clauseIndex),
          fieldSeg('rhs'),
          ...error.rhsPath,
        ];
        const errorEnv = termEnv.atIndexPath(errorPath);
        return TCEnvError.create(error.message, errorEnv);
      });
      return { success: false, errors: recursionErrors };
    }
  }

  const absurdityChecker = (patterns: TTKPattern[]): boolean => {
    const termName = name ?? '???';
    const piSpine = extractPiSpine(type);
    const normalizedReturnType = whnf(piSpine.body, { definitions: termEnv.definitions, fuel: 100 });

    let normalizedType = normalizedReturnType;
    for (let i = piSpine.binders.length - 1; i >= 0; i--) {
      const binder = piSpine.binders[i];
      normalizedType = {
        tag: 'Binder',
        name: binder.name,
        binderKind: { tag: 'BPi' },
        domain: binder.type,
        body: normalizedType,
      };
    }
    const expectedArgCount = countPiBinders(normalizedType);

    const paddedPatterns = [...patterns];
    while (paddedPatterns.length < expectedArgCount) {
      paddedPatterns.push({ tag: 'PWild', name: '_' });
    }

    const patternEnv = termEnv.withValue(paddedPatterns);
    if (arePatternsAbsurd(termName, patternEnv, normalizedType)) {
      return true;
    }

    return tryCaseSplitsInSearchOfAbsurdity(termName, patterns, normalizedType, termEnv.definitions, termEnv);
  };

  let totalityClauses = checkedClauses.map(c => ({
    patterns: c.patterns,
    elabArgs: c.elabArgs,
    contextNames: c.contextNames,
  }));

  if (options?.withScrutineeCount && options.withScrutineeCount > 0 && totalityClauses.length > 0) {
    const totalPatterns = totalityClauses[0].patterns.length;
    const scrutineesToCheck = options.newScrutineeCount ?? options.withScrutineeCount;
    const frozenCount = totalPatterns - scrutineesToCheck;
    if (frozenCount > 0) {
      totalityClauses = totalityClauses.map(c => ({
        ...c,
        patterns: [
          ...c.patterns.slice(0, frozenCount).map((_p, i) => ({ tag: 'PVar' as const, name: `_ctxt${i}` })),
          ...c.patterns.slice(frozenCount),
        ],
      }));
    }
  }

  const totalityResult = checkTotality(name ?? '???', totalityClauses, termEnv.definitions, absurdityChecker);

  if (options?.withScrutineeCount && options.withScrutineeCount > 0 && totalityClauses.length > 0) {
    const totalPatterns = totalityClauses[0].patterns.length;
    const scrutineesToCheck = options.newScrutineeCount ?? options.withScrutineeCount;
    const frozenCount = totalPatterns - scrutineesToCheck;
    if (frozenCount > 0) {
      totalityResult.frozenPositionCount = frozenCount;
    }
  }

  const formatMissingPatterns = (patterns: TTKPattern[]): string => {
    const expectedArgCount = countPiBinders(type);
    const paddedPatterns = [...patterns];
    while (paddedPatterns.length < expectedArgCount) {
      paddedPatterns.push({ tag: 'PWild', name: '_' });
    }

    const positionToName = new Map<number, string>();
    if (namedArgMap) {
      for (const [argName, position] of namedArgMap) {
        positionToName.set(position, argName);
      }
    }

    return paddedPatterns.map((p, i) => {
      const argName = positionToName.get(i);
      const patternStr = prettyPrintPattern(p);
      if (argName) {
        return `{${argName}:=${patternStr}}`;
      }
      return patternStr;
    }).join(' ');
  };

  const totalityErrors: TCEnvError[] = [];
  if (!options?.skipTotality) {
    for (const { clauseIndex, patterns } of totalityResult.unreachableClauses) {
      totalityErrors.push(TCEnvError.create(
        `Redundant clause: ${name ? `${name} ` : ''}${prettyPrintPatternList(patterns)}`,
        termEnv.atIndexPath(appendPath(termEnv.indexPath, fieldSeg('value'), fieldSeg('clauses'), arraySeg(clauseIndex)))
      ));
    }
    if (!totalityResult.isExhaustive) {
      const formattedClauses = totalityResult.missingValidClauses.map(c => formatMissingPatterns(c.patterns)).join('\n');
      totalityErrors.push(TCEnvError.create(
        `Function ${name ? `${name} ` : ''}is non-total. Missing clause${totalityResult.missingValidClauses.length === 1 ? '' : 's'}:\n${formattedClauses}`,
        termEnv
      ));
    }
  }

  const enrichedTotalityResult: TotalityResult = {
    ...totalityResult,
    annotatedAbsurdClauses: annotatedAbsurdClauses.length > 0 ? annotatedAbsurdClauses : undefined,
  };

  if (totalityErrors.length > 0) {
    return { success: false, errors: totalityErrors, totalityResult: enrichedTotalityResult };
  }

  const unsolvedWildcards = findUnsolvedWildcards(checkedValue);
  if (unsolvedWildcards.length > 0) {
    return {
      success: false,
      errors: [
        TCEnvError.create(
          `Function ${name ? `'${name}' ` : ''}contains unsolved wildcards. Wildcards must be uniquely determined by context.`,
          termEnv
        ),
      ],
      totalityResult: enrichedTotalityResult,
    };
  }

  return { success: true, checkedValue, totalityResult: enrichedTotalityResult };
}

export function findUnsolvedWildcards(term: TTKTerm, path: string[] = []): string[][] {
  const results: string[][] = [];

  switch (term.tag) {
    case 'Hole':
      if (term.id === '_') {
        results.push([...path, 'Hole._']);
      }
      break;
    case 'Meta':
      if (term.id === '_') {
        results.push([...path, 'Meta._']);
      }
      break;
    case 'Var':
    case 'Const':
    case 'Sort':
    case 'ULevel':
    case 'ULit':
    case 'UOmega':
      break;
    case 'App':
      results.push(...findUnsolvedWildcards(term.fn, [...path, 'fn']));
      results.push(...findUnsolvedWildcards(term.arg, [...path, 'arg']));
      break;
    case 'Binder':
      results.push(...findUnsolvedWildcards(term.domain, [...path, 'domain']));
      results.push(...findUnsolvedWildcards(term.body, [...path, 'body']));
      if (term.binderKind.tag === 'BLet') {
        results.push(...findUnsolvedWildcards(term.binderKind.defVal, [...path, 'binderKind', 'defVal']));
      }
      break;
    case 'Match':
      results.push(...findUnsolvedWildcards(term.scrutinee, [...path, 'scrutinee']));
      term.clauses.forEach((clause, i) => {
        results.push(...findUnsolvedWildcards(clause.rhs, [...path, 'clauses', String(i), 'rhs']));
      });
      break;
    case 'Annot':
      results.push(...findUnsolvedWildcards(term.term, [...path, 'term']));
      results.push(...findUnsolvedWildcards(term.type, [...path, 'type']));
      break;
  }

  return results;
}
