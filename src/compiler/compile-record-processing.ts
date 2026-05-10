import type { ParsedDeclaration } from '../parser/parser';
import { arraySeg, type ElabMap, fieldSeg, type IndexPath, type SourceMap } from '../types/source-position';
import { countSurfaceClauseBindings } from './pattern-binders';
import { countParameters, defaultRecordConstructorName, elabToKernelWithMap, extractArgNamedArgInfos, extractNamedArgMap, type NamedArgMap } from './elab';
import { mkType, prettyPrint as prettyPrintTTK, type TTKRecordDef, type TTKRecordField, type TTKRecordParam, type TTKTerm } from './kernel';
import { checkInductiveDeclaration } from './inductive';
import {
  addRecordCtorTypeElabMappings,
  buildRecordTypeFromParams,
  buildSurfaceConstructorType,
  buildSurfaceRecordType,
  extractZonkedFieldTypes,
} from './compile-record-utils';
import { createCompiledDeclaration, createElabErrorResult } from './compile-declaration-result';
import { generateProjections, recordToInductiveDefinition } from './record';
import type { ProcessDeclarationResult } from './compile';
import {
  addDefinition,
  countPiBinders,
  createNamedArgInfoLookup,
  createTCEnv,
  type DefinitionsMap,
  getTermDefinition,
  TCEnvError,
} from './term';
import { mkHoleTT, mkPropTT, type TTerm } from './surface';

export function extractParentRecordFields(
  parentName: string,
  definitions: DefinitionsMap
): TTKRecordField[] | { error: string } {
  const parentInductive = definitions.inductiveTypes.get(parentName);
  if (!parentInductive) {
    return { error: `Parent record "${parentName}" not found` };
  }

  const recordInfo = parentInductive.recordInfo;
  if (!recordInfo) {
    return { error: `"${parentName}" is not a record (no recordInfo)` };
  }

  if (parentInductive.constructors.length !== 1) {
    return { error: `"${parentName}" has ${parentInductive.constructors.length} constructors, expected 1` };
  }
  const ctorType = parentInductive.constructors[0].type;
  const totalBinders = countPiBinders(ctorType);
  const fieldCount = recordInfo.fieldNames.length;
  const paramCount = totalBinders - fieldCount;

  const fields: TTKRecordField[] = [];
  let current: TTKTerm = ctorType;
  let binderIndex = 0;

  while (current.tag === 'Binder' && current.binderKind.tag === 'BPi') {
    if (binderIndex >= paramCount) {
      const fieldIdx = binderIndex - paramCount;
      const isImplicit = recordInfo.implicitFields.includes(fieldIdx);
      fields.push({
        name: current.name,
        type: current.domain,
        implicit: isImplicit,
      });
    }
    current = current.body;
    binderIndex++;
  }

  return fields;
}

export function substituteInheritedFieldRefs(
  term: TTerm,
  inheritedFieldNames: string[],
  localFieldIndex: number
): TTerm {
  if (inheritedFieldNames.length === 0) {
    return term;
  }

  const numInherited = inheritedFieldNames.length;

  function transform(t: TTerm, depth: number): TTerm {
    switch (t.tag) {
      case 'Const': {
        const inheritedIdx = inheritedFieldNames.indexOf(t.name);
        if (inheritedIdx >= 0) {
          const varIndex = localFieldIndex + (numInherited - 1 - inheritedIdx) + depth;
          return { tag: 'Var', index: varIndex };
        }
        return t;
      }
      case 'Var': {
        const adjustedCutoff = localFieldIndex + depth;
        if (t.index >= adjustedCutoff) {
          return { tag: 'Var', index: t.index + numInherited };
        }
        return t;
      }
      case 'Sort':
        return { tag: 'Sort', level: transform(t.level, depth) };
      case 'ULevel':
      case 'ULit':
      case 'UOmega':
      case 'Hole':
      case 'AbsurdMarker':
      case 'NatLit':
      case 'RatLit':
        return t;
      case 'App': {
        const newFn = transform(t.fn, depth);
        const newArg = transform(t.arg, depth);
        if (newFn === t.fn && newArg === t.arg) return t;
        return { tag: 'App', fn: newFn, arg: newArg, argName: t.argName };
      }
      case 'Binder': {
        const newDomain = t.domain ? transform(t.domain, depth) : undefined;
        const newBody = transform(t.body, depth + 1);
        if (newDomain === t.domain && newBody === t.body) return t;
        return { ...t, domain: newDomain, body: newBody };
      }
      case 'MultiBinder': {
        const newDomain = transform(t.domain, depth);
        const newBody = transform(t.body, depth + t.names.length);
        if (newDomain === t.domain && newBody === t.body) return t;
        return { ...t, domain: newDomain, body: newBody };
      }
      case 'Match': {
        const newScrutinee = transform(t.scrutinee, depth);
        const newClauses = t.clauses.map(c => ({
          ...c,
          rhs: transform(c.rhs, depth + countSurfaceClauseBindings(c)),
        }));
        return { tag: 'Match', scrutinee: newScrutinee, clauses: newClauses };
      }
      case 'Annot':
        return { tag: 'Annot', term: transform(t.term, depth), type: transform(t.type, depth) };
      case 'WithClause':
        return t;
      case 'TacticBlock':
        return {
          tag: 'TacticBlock',
          tactics: t.tactics.map(cmd => ({
            name: cmd.name,
            args: cmd.args.map(arg => transform(arg, depth)),
          })),
        };
      default: {
        const _exhaustive: never = t;
        return _exhaustive;
      }
    }
  }

  return transform(term, 0);
}

type LocalBinderImplicitInfo = { namedArgMap: NamedArgMap; totalArity: number } | null;

export function insertFieldImplicitHoles(
  term: TTerm,
  currentFieldIndex: number,
  fieldImplicitInfos: Map<number, { namedArgMap: NamedArgMap; totalArity: number }>
): TTerm {
  let holeCounter = 0;

  function tryInsertImplicits(
    head: TTerm,
    transformedArgs: TTerm[],
    info: { namedArgMap: NamedArgMap; totalArity: number }
  ): TTerm | null {
    if (info.namedArgMap.size > 0 && transformedArgs.length < info.totalArity) {
      const namedPositions = new Set(info.namedArgMap.values());
      const newArgs: TTerm[] = [];
      let posIdx = 0;

      for (let pos = 0; pos < info.totalArity && (posIdx < transformedArgs.length || namedPositions.has(pos)); pos++) {
        if (namedPositions.has(pos)) {
          newArgs.push(mkHoleTT(`_field_implicit_f${currentFieldIndex}_${holeCounter++}`, mkPropTT()));
        } else if (posIdx < transformedArgs.length) {
          newArgs.push(transformedArgs[posIdx++]);
        } else {
          break;
        }
      }
      while (posIdx < transformedArgs.length) {
        newArgs.push(transformedArgs[posIdx++]);
      }

      let result: TTerm = head;
      for (const arg of newArgs) {
        result = { tag: 'App', fn: result, arg };
      }
      return result;
    }
    return null;
  }

  function transform(t: TTerm, depth: number, localBinderStack: LocalBinderImplicitInfo[]): TTerm {
    if (t.tag === 'App') {
      const args: TTerm[] = [];
      let current: TTerm = t;
      while (current.tag === 'App') {
        args.unshift(current.arg);
        current = current.fn;
      }
      const head = current;
      const transformedArgs = args.map(a => transform(a, depth, localBinderStack));

      if (head.tag === 'Var') {
        const topLevelIndex = head.index - depth;
        if (topLevelIndex >= 0 && topLevelIndex < currentFieldIndex) {
          const fieldListIndex = (currentFieldIndex - 1) - topLevelIndex;
          const info = fieldImplicitInfos.get(fieldListIndex);
          if (info) {
            const result = tryInsertImplicits(head, transformedArgs, info);
            if (result) return result;
          }
        } else if (head.index < depth) {
          const stackIndex = depth - 1 - head.index;
          if (stackIndex >= 0 && stackIndex < localBinderStack.length) {
            const info = localBinderStack[stackIndex];
            if (info) {
              const result = tryInsertImplicits(head, transformedArgs, info);
              if (result) return result;
            }
          }
        }
      }

      let result: TTerm = transform(head, depth, localBinderStack);
      for (const arg of transformedArgs) {
        result = { tag: 'App', fn: result, arg };
      }
      return result;
    }

    if (t.tag === 'Binder') {
      const domain = t.domain ? transform(t.domain, depth, localBinderStack) : t.domain;
      let binderInfo: LocalBinderImplicitInfo = null;
      if (t.domain) {
        const domainNamedArgMap = extractNamedArgMap(t.domain);
        if (domainNamedArgMap.size > 0) {
          binderInfo = { namedArgMap: domainNamedArgMap, totalArity: countParameters(t.domain) };
        }
      }
      const body = transform(t.body, depth + 1, [...localBinderStack, binderInfo]);
      if (domain === t.domain && body === t.body) return t;
      return { ...t, domain, body };
    }

    if (t.tag === 'MultiBinder') {
      const domain = transform(t.domain, depth, localBinderStack);
      let binderInfo: LocalBinderImplicitInfo = null;
      const domainNamedArgMap = extractNamedArgMap(t.domain);
      if (domainNamedArgMap.size > 0) {
        binderInfo = { namedArgMap: domainNamedArgMap, totalArity: countParameters(t.domain) };
      }
      const bodyStack = [...localBinderStack];
      for (let i = 0; i < t.names.length; i++) bodyStack.push(binderInfo);
      const body = transform(t.body, depth + t.names.length, bodyStack);
      if (domain === t.domain && body === t.body) return t;
      return { ...t, domain, body };
    }

    if (t.tag === 'Match') {
      const scrutinee = transform(t.scrutinee, depth, localBinderStack);
      const clauses = t.clauses.map(c => {
        const binderCount = countSurfaceClauseBindings(c);
        const clauseStack = [...localBinderStack];
        for (let i = 0; i < binderCount; i++) clauseStack.push(null);
        const rhs = transform(c.rhs, depth + binderCount, clauseStack);
        if (rhs === c.rhs) return c;
        return { ...c, rhs };
      });
      if (scrutinee === t.scrutinee && clauses.every((c, i) => c === t.clauses[i])) return t;
      return { ...t, scrutinee, clauses };
    }

    if (t.tag === 'Annot') {
      const newTerm = transform(t.term, depth, localBinderStack);
      const newType = transform(t.type, depth, localBinderStack);
      if (newTerm === t.term && newType === t.type) return t;
      return { ...t, term: newTerm, type: newType };
    }

    return t;
  }

  return transform(term, 0, []);
}

export function processRecordDeclaration(
  decl: ParsedDeclaration,
  sourceMap: SourceMap,
  definitions: DefinitionsMap,
): ProcessDeclarationResult {
  const elabMap: ElabMap = new Map();
  const appNamedArgLookup = createNamedArgInfoLookup(definitions);

  const inheritedFields: TTKRecordField[] = [];
  const inheritedFieldNames: string[] = [];
  const inheritedFieldParents: string[] = [];
  if (decl.extends && decl.extends.length > 0) {
    for (const parentName of decl.extends) {
      const parentFields = extractParentRecordFields(parentName, definitions);
      if ('error' in parentFields) {
        const env = createTCEnv({ definitions, options: { mode: 'check' } });
        const error = TCEnvError.create(parentFields.error, env);
        return {
          success: false,
          compiled: createCompiledDeclaration(
            decl, mkType(0), undefined, undefined, elabMap, sourceMap,
            false, [error], undefined, undefined, undefined
          ),
          newDefinitions: definitions,
          errorCount: 1,
        };
      }
      for (const field of parentFields) {
        const clash = inheritedFields.find(f => f.name === field.name);
        if (clash) {
          const env = createTCEnv({ definitions, options: { mode: 'check' } });
          const error = TCEnvError.create(`Field "${field.name}" is inherited from multiple parent records`, env);
          return {
            success: false,
            compiled: createCompiledDeclaration(
              decl, mkType(0), undefined, undefined, elabMap, sourceMap,
              false, [error], undefined, undefined, undefined
            ),
            newDefinitions: definitions,
            errorCount: 1,
          };
        }
        inheritedFields.push(field);
        inheritedFieldNames.push(field.name);
        inheritedFieldParents.push(parentName);
      }
    }
  }

  const kernelParams: TTKRecordParam[] = [];
  const levelNamesInScope: Set<string> = new Set();
  if (decl.params) {
    for (let i = 0; i < decl.params.length; i++) {
      const param = decl.params[i];
      try {
        const paramTypePath: IndexPath = [
          { kind: 'field', name: 'params' },
          { kind: 'array', index: i },
          { kind: 'field', name: 'type' },
        ];
        const kernelType = elabToKernelWithMap(param.type, elabMap, paramTypePath, paramTypePath, undefined, appNamedArgLookup, undefined, levelNamesInScope);
        kernelParams.push({ name: param.name, type: kernelType, implicit: param.implicit });
        if (kernelType.tag === 'ULevel') {
          levelNamesInScope.add(param.name);
        }
      } catch (e) {
        return createElabErrorResult(e, decl, sourceMap, elabMap, definitions);
      }
    }
  }

  const kernelFields: TTKRecordField[] = [];
  const fieldImplicitInfos = new Map<number, { namedArgMap: NamedArgMap; totalArity: number }>();
  if (decl.fields) {
    for (let i = 0; i < decl.fields.length; i++) {
      const field = decl.fields[i];
      try {
        const fieldTypePath: IndexPath = [
          { kind: 'field', name: 'fields' },
          { kind: 'array', index: i },
          { kind: 'field', name: 'type' },
        ];
        let processedType = substituteInheritedFieldRefs(field.type, inheritedFieldNames, i);
        if (fieldImplicitInfos.size > 0) {
          processedType = insertFieldImplicitHoles(processedType, i, fieldImplicitInfos);
        }
        const kernelType = elabToKernelWithMap(processedType, elabMap, fieldTypePath, fieldTypePath, undefined, appNamedArgLookup, undefined, levelNamesInScope);
        kernelFields.push({ name: field.name, type: kernelType, implicit: field.implicit });
        const fieldNamedArgMap = extractNamedArgMap(field.type);
        if (fieldNamedArgMap.size > 0) {
          fieldImplicitInfos.set(i, { namedArgMap: fieldNamedArgMap, totalArity: countParameters(field.type) });
        }
      } catch (e) {
        return createElabErrorResult(e, decl, sourceMap, elabMap, definitions);
      }
    }
  }

  for (const localField of kernelFields) {
    const clash = inheritedFields.find(f => f.name === localField.name);
    if (clash) {
      const env = createTCEnv({ definitions, options: { mode: 'check' } });
      const error = TCEnvError.create(`Field "${localField.name}" clashes with inherited field from parent record`, env);
      return {
        success: false,
        compiled: createCompiledDeclaration(
          decl, mkType(0), undefined, undefined, elabMap, sourceMap,
          false, [error], undefined, undefined, undefined
        ),
        newDefinitions: definitions,
        errorCount: 1,
      };
    }
  }

  const allFields = [...inheritedFields, ...kernelFields];

  let resultSort: TTKTerm;
  if (decl.type) {
    try {
      const typePath: IndexPath = [{ kind: 'field', name: 'type' }];
      resultSort = elabToKernelWithMap(decl.type, elabMap, typePath, typePath);
    } catch (e) {
      return createElabErrorResult(e, decl, sourceMap, elabMap, definitions);
    }
  } else {
    resultSort = mkType(0);
  }

  const recordType = buildRecordTypeFromParams(kernelParams, resultSort);
  const recordNamedArgMap: NamedArgMap = new Map();
  if (decl.params) {
    for (let i = 0; i < decl.params.length; i++) {
      const param = decl.params[i];
      if (param.implicit) {
        recordNamedArgMap.set(param.name, i);
      }
    }
  }

  const recordName = decl.name || 'anonymous';
  const constructorName = decl.constructorName ?? defaultRecordConstructorName(recordName);
  const ttkRecord: TTKRecordDef = {
    name: recordName,
    constructorName,
    type: recordType,
    params: kernelParams,
    fields: allFields,
  };

  const inductiveDef = recordToInductiveDefinition(ttkRecord);
  if (recordNamedArgMap.size > 0) {
    inductiveDef.namedArgMap = recordNamedArgMap;
  }

  addRecordCtorTypeElabMappings(elabMap, kernelParams.length, kernelFields.length);

  const result = checkInductiveDeclaration(
    inductiveDef.name,
    inductiveDef.type,
    inductiveDef.constructors,
    definitions,
    inductiveDef.namedArgMap,
    inductiveDef.recordInfo
  );

  const syntheticCtor = {
    name: constructorName,
    type: buildSurfaceConstructorType(decl.params || [], decl.fields || [], recordName),
    ...(decl.recordConstructorSyntax !== undefined ? { syntax: decl.recordConstructorSyntax } : {}),
  };

  if (!result.success) {
    const syntheticDecl: ParsedDeclaration = {
      kind: 'inductive',
      name: recordName,
      type: decl.params ? buildSurfaceRecordType(decl.params) : undefined,
      constructors: [syntheticCtor],
    };
    return {
      success: false,
      compiled: createCompiledDeclaration(
        syntheticDecl, inductiveDef.type, undefined, inductiveDef.constructors, elabMap, sourceMap,
        false, result.errors, definitions, undefined, undefined, undefined,
        true, decl.fields
      ),
      newDefinitions: definitions,
      errorCount: result.errors.length,
    };
  }

  const syntheticDecl: ParsedDeclaration = {
    kind: 'inductive',
    name: recordName,
    type: decl.params ? buildSurfaceRecordType(decl.params) : undefined,
    constructors: [syntheticCtor],
    syntax: decl.syntax,
  };

  const zonkedCtorType = result.zonkedConstructors[0].type;
  const zonkedFields = extractZonkedFieldTypes(zonkedCtorType, kernelParams.length, allFields);
  const zonkedRecord: TTKRecordDef = {
    ...ttkRecord,
    fields: zonkedFields,
  };
  const projections = generateProjections(zonkedRecord);

  let finalDefinitions = result.newDefinitions;
  const numParams = ttkRecord.params.length;
  const numInherited = inheritedFields.length;
  for (let projIdx = 0; projIdx < projections.length; projIdx++) {
    const proj = projections[projIdx];
    const projNamedArgMap: NamedArgMap = new Map();
    for (let k = 0; k < numParams; k++) {
      projNamedArgMap.set(ttkRecord.params[k].name, k);
    }

    const fieldImplicitOffset = numParams + 1;
    if (projIdx < numInherited) {
      const parentName = inheritedFieldParents[projIdx];
      const fieldName = zonkedRecord.fields[projIdx].name;
      const parentProjDef = getTermDefinition(finalDefinitions, `${parentName}.${fieldName}`);
      if (parentProjDef?.namedArgMap) {
        const parentRecord = finalDefinitions.inductiveTypes.get(parentName);
        const parentNumParams = parentRecord?.recordInfo?.paramCount ?? 0;
        const parentImplicitOffset = parentNumParams + 1;
        for (const [name, pos] of parentProjDef.namedArgMap) {
          if (pos >= parentImplicitOffset) {
            const fieldOffset = pos - parentImplicitOffset;
            projNamedArgMap.set(name, fieldImplicitOffset + fieldOffset);
          }
        }
      }
    } else {
      const localIdx = projIdx - numInherited;
      if (decl.fields && localIdx < decl.fields.length) {
        const fieldNamedArgMap = extractNamedArgMap(decl.fields[localIdx].type);
        for (const [name, pos] of fieldNamedArgMap) {
          projNamedArgMap.set(name, pos + fieldImplicitOffset);
        }
      }
    }

    let projArgNamedArgInfos: import('./term').ArgNamedArgInfos | undefined;
    if (projIdx >= numInherited) {
      const localIdx = projIdx - numInherited;
      if (decl.fields && localIdx < decl.fields.length) {
        const fieldArgInfos = extractArgNamedArgInfos(decl.fields[localIdx].type);
        if (fieldArgInfos.size > 0) {
          projArgNamedArgInfos = new Map();
          for (const [pos, info] of fieldArgInfos) {
            projArgNamedArgInfos.set(pos + fieldImplicitOffset, info);
          }
        }
      }
    }

    finalDefinitions = addDefinition(finalDefinitions, proj.name, proj.type, proj.value, projNamedArgMap, projArgNamedArgInfos);
  }

  const prettyProjections = projections.map(proj => ({
    name: proj.name,
    prettyType: prettyPrintTTK(proj.type),
  }));

  return {
    success: true,
    compiled: createCompiledDeclaration(
      syntheticDecl, inductiveDef.type, undefined, result.zonkedConstructors, elabMap, sourceMap,
      true, [], finalDefinitions, undefined, result.indexPositions, undefined,
      true, decl.params, decl.fields, decl.extendsExprs, prettyProjections
    ),
    newDefinitions: finalDefinitions,
    errorCount: 0,
  };
}
