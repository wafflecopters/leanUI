/**
 * TT Elaboration Layer
 *
 * This module is the ONLY place that knows about both TT (surface syntax)
 * and TTK (kernel syntax). It provides:
 *
 * 1. elabToKernel: TT → TTK - Deep traversal converting surface terms to kernel
 * 2. elabToKernelWithMap: TT → TTK with source position tracking
 * 3. inlineExtension: Inline extended record fields before elaboration
 *
 * The elaboration pipeline for records is:
 *   RecordDef (with extends) → inlineExtension → RecordDef (no extends) → elabRecordToKernel → TTKRecordDef
 */

import type {
  TTerm,
  TContext,
  TBinding,
  TPattern,
  RecordDef,
  RecordField,
  RecordParam,
} from './surface';

import type {
  TTKTerm,
  TTKContext,
  TTKBinding,
  TTKBinderKind,
  TTKPattern,
  TTKRecordDef,
  TTKRecordField,
  TTKRecordParam,
} from './kernel';

import {
  ElabMap,
  IndexPath,
  appendPath,
  fieldSeg,
  arraySeg,
  serializeIndexPath
} from '../types/source-position';

// Re-export TTKRecordDef for consumers
export type { TTKRecordDef };

// ============================================================================
// Constructor Parameter Names
// ============================================================================

/**
 * Map from constructor name to its parameter names.
 * Used during pattern elaboration to generate meaningful wildcard names.
 *
 * For example, if VCons : (A : Type) -> (n : Nat) -> A -> Vec A n -> Vec A (Succ n)
 * then constructorParamNames.get("VCons") = ["A", "n", "", ""]
 * (empty string for unnamed parameters)
 */
export type ConstructorParamNames = Map<string, string[]>;

/**
 * Extract parameter names from a constructor's type (a Pi type).
 *
 * For example, given:
 *   VCons : (A : Type) -> (n : Nat) -> A -> Vec A n -> Vec A (Succ n)
 *
 * Returns: ["A", "n", "", ""] (empty strings for unnamed/anonymous binders)
 *
 * This walks the Pi chain and collects the binder names until we hit the return type.
 */
export function extractConstructorParamNames(ctorType: TTKTerm): string[] {
  const names: string[] = [];
  let current = ctorType;

  while (current.tag === 'Binder' && current.binderKind.tag === 'BPi') {
    // Use the binder name, or empty string if it's "_" or empty
    const name = current.name === '_' || current.name === '' ? '' : current.name;
    names.push(name);
    current = current.body;
  }

  return names;
}

/**
 * Build a map of constructor parameter names from elaborated constructors.
 */
export function buildConstructorParamNames(
  constructors: Array<{ name: string; type: TTKTerm }>
): ConstructorParamNames {
  const map: ConstructorParamNames = new Map();
  for (const ctor of constructors) {
    map.set(ctor.name, extractConstructorParamNames(ctor.type));
  }
  return map;
}

// ============================================================================
// Wildcard Name Generation
// ============================================================================

/**
 * Counter for generating unique wildcard names during elaboration.
 * The counter is reset at the start of each clause, so 0 is always the first
 * wildcard in each clause.
 */
let wildcardCounter = 0;

/**
 * Current constructor parameter names context.
 * Set when elaborating patterns inside a constructor pattern.
 */
let currentCtorParamNames: string[] | null = null;

/**
 * Current position within constructor arguments.
 * Tracks which parameter we're at when elaborating sub-patterns.
 */
let currentCtorParamIndex: number = 0;

/**
 * Current term parameter names for top-level pattern elaboration.
 * Set from the term's type signature before elaborating its value.
 */
let currentTermParamNames: string[] | null = null;

/**
 * Current position within top-level term parameters.
 */
let currentTermParamIndex: number = 0;

/**
 * Global map of constructor parameter names.
 * Set before elaborating term bodies.
 */
let globalConstructorParamNames: ConstructorParamNames = new Map();

/**
 * Set the global constructor parameter names map for pattern elaboration.
 */
export function setConstructorParamNames(map: ConstructorParamNames): void {
  globalConstructorParamNames = map;
}

/**
 * Set the current term parameter names for top-level pattern elaboration.
 * Call this before elaborating a term's value, using param names from its type.
 */
export function setCurrentTermParamNames(names: string[] | null): void {
  currentTermParamNames = names;
  currentTermParamIndex = 0;
}

/**
 * Generate a fresh unique name for a wildcard pattern within the current clause.
 *
 * The name format is: paramName + counter
 * - If we're inside a constructor pattern and know the parameter name, use it
 * - If we're at a top-level pattern and know the term's parameter name, use it
 * - If the parameter is unnamed, use "?"
 * - The counter ensures uniqueness within the clause
 */
function freshWildcardName(): string {
  const counter = wildcardCounter++;

  // If we have constructor context (nested inside a constructor pattern), use the parameter name
  if (currentCtorParamNames !== null && currentCtorParamIndex < currentCtorParamNames.length) {
    const paramName = currentCtorParamNames[currentCtorParamIndex];
    if (paramName && paramName !== '') {
      return `${paramName}${counter}`;
    }
  }

  // If we have term context (top-level patterns), use the term's parameter name
  if (currentTermParamNames !== null && currentTermParamIndex < currentTermParamNames.length) {
    const paramName = currentTermParamNames[currentTermParamIndex];
    if (paramName && paramName !== '') {
      return `${paramName}${counter}`;
    }
  }

  // No parameter name available, use "?"
  return `?${counter}`;
}

/**
 * Reset the wildcard counter (useful for testing).
 */
export function resetWildcardCounter(): void {
  wildcardCounter = 0;
  currentCtorParamNames = null;
  currentCtorParamIndex = 0;
  currentTermParamNames = null;
  currentTermParamIndex = 0;
}

// ============================================================================
// Term Elaboration: TT → TTK
// ============================================================================

/**
 * Elaborate a surface term (TT) to a kernel term (TTK).
 *
 * Currently this is a structural copy since TT and TTK are identical.
 * As we add sugar to TT, this function will desugar it.
 *
 * @param term - Surface term (TT)
 * @returns Kernel term (TTK)
 */
export function elabToKernel(term: TTerm): TTKTerm {
  switch (term.tag) {
    case 'Var':
      return { tag: 'Var', index: term.index };

    case 'Sort':
      return { tag: 'Sort', level: term.level };

    case 'Const':
      return {
        tag: 'Const',
        name: term.name,
        type: elabToKernel(term.type)
      };

    case 'Binder': {
      const domain = elabToKernel(term.domain);
      const body = elabToKernel(term.body);

      let binderKind: TTKBinderKind;
      switch (term.binderKind.tag) {
        case 'BPiTT':
          binderKind = { tag: 'BPi' };
          break;
        case 'BLamTT':
          binderKind = { tag: 'BLam' };
          break;
        case 'BLetTT':
          binderKind = { tag: 'BLet', defVal: elabToKernel(term.binderKind.defVal) };
          break;
      }

      return {
        tag: 'Binder',
        name: term.name,
        binderKind,
        domain,
        body
      };
    }

    case 'App':
      return {
        tag: 'App',
        fn: elabToKernel(term.fn),
        arg: elabToKernel(term.arg)
      };

    case 'Hole':
      return {
        tag: 'Hole',
        id: term.id,
        type: elabToKernel(term.type),
        context: elabContextToKernel(term.context)
      };

    case 'Annot':
      return {
        tag: 'Annot',
        term: elabToKernel(term.term),
        type: elabToKernel(term.type)
      };

    case 'Match':
      return {
        tag: 'Match',
        scrutinee: elabToKernel(term.scrutinee),
        clauses: term.clauses.map(c => {
          // Reset wildcard counter for each clause so _w0 is the first wildcard in each clause
          wildcardCounter = 0;
          // Reset term param index for each clause
          currentTermParamIndex = 0;
          return {
            patterns: c.patterns.map(p => {
              const result = elabPatternToKernel(p);
              // Increment term param index after each top-level pattern
              currentTermParamIndex++;
              return result;
            }),
            rhs: elabToKernel(c.rhs)
          };
        })
      };
  }
}

/**
 * Elaborate a surface pattern (TPattern) to a kernel pattern (TTKPattern).
 *
 * Surface PWild patterns become kernel PWild with generated unique names.
 * When inside a constructor pattern, the wildcard name includes the
 * constructor's parameter name (e.g., "A0", "n1", "?2" for unnamed params).
 */
export function elabPatternToKernel(pattern: TPattern): TTKPattern {
  switch (pattern.tag) {
    case 'PVar':
      return { tag: 'PVar', name: pattern.name };
    case 'PWild':
      // Generate a unique name for the wildcard, keeping it as PWild in kernel
      return { tag: 'PWild', name: freshWildcardName() };
    case 'PCtor': {
      // Look up the constructor's parameter names
      const paramNames = globalConstructorParamNames.get(pattern.name);

      // Elaborate each argument with the appropriate parameter context
      const elabArgs: TTKPattern[] = [];
      for (let i = 0; i < pattern.args.length; i++) {
        // Save current context
        const savedParamNames = currentCtorParamNames;
        const savedParamIndex = currentCtorParamIndex;

        // Set context for this argument
        if (paramNames) {
          currentCtorParamNames = paramNames;
          currentCtorParamIndex = i;
        }

        // Elaborate the sub-pattern
        elabArgs.push(elabPatternToKernel(pattern.args[i]));

        // Restore context
        currentCtorParamNames = savedParamNames;
        currentCtorParamIndex = savedParamIndex;
      }

      return {
        tag: 'PCtor',
        name: pattern.name,
        args: elabArgs
      };
    }
  }
}

/**
 * Elaborate a surface context to kernel context.
 */
export function elabContextToKernel(ctx: TContext): TTKContext {
  return ctx.map((binding): TTKBinding => ({
    name: binding.name,
    type: elabToKernel(binding.type)
  }));
}

/**
 * Elaborate a surface binding to kernel binding.
 */
export function elabBindingToKernel(binding: TBinding): TTKBinding {
  return {
    name: binding.name,
    type: elabToKernel(binding.type)
  };
}

// ============================================================================
// Elaboration with Source Position Tracking
// ============================================================================

/**
 * Elaborate a TTerm to TTKTerm while tracking path correspondence.
 *
 * @param term - The surface term to elaborate
 * @param elabMap - Map to populate with kernel→surface path mappings
 * @param surfacePath - Current path in the surface AST
 * @param kernelPath - Current path in the kernel AST
 * @returns The elaborated kernel term
 */
export function elabToKernelWithMap(
  term: TTerm,
  elabMap: ElabMap,
  surfacePath: IndexPath = [],
  kernelPath: IndexPath = []
): TTKTerm {
  // Record the correspondence between kernel and surface paths
  const kernelKey = serializeIndexPath(kernelPath);
  const surfaceKey = serializeIndexPath(surfacePath);
  elabMap.set(kernelKey, surfaceKey);

  // Recursively elaborate with path tracking
  switch (term.tag) {
    case 'Var':
      return { tag: 'Var', index: term.index };

    case 'Sort':
      return { tag: 'Sort', level: term.level };

    case 'Const':
      return {
        tag: 'Const',
        name: term.name,
        type: elabToKernelWithMap(
          term.type,
          elabMap,
          appendPath(surfacePath, fieldSeg('type')),
          appendPath(kernelPath, fieldSeg('type'))
        )
      };

    case 'Binder': {
      const domain = elabToKernelWithMap(
        term.domain,
        elabMap,
        appendPath(surfacePath, fieldSeg('domain')),
        appendPath(kernelPath, fieldSeg('domain'))
      );
      const body = elabToKernelWithMap(
        term.body,
        elabMap,
        appendPath(surfacePath, fieldSeg('body')),
        appendPath(kernelPath, fieldSeg('body'))
      );

      let binderKind: TTKBinderKind;
      switch (term.binderKind.tag) {
        case 'BPiTT':
          binderKind = { tag: 'BPi' };
          break;
        case 'BLamTT':
          binderKind = { tag: 'BLam' };
          break;
        case 'BLetTT':
          binderKind = {
            tag: 'BLet',
            defVal: elabToKernelWithMap(
              term.binderKind.defVal,
              elabMap,
              appendPath(surfacePath, fieldSeg('binderKind'), fieldSeg('defVal')),
              appendPath(kernelPath, fieldSeg('binderKind'), fieldSeg('defVal'))
            )
          };
          break;
      }

      return {
        tag: 'Binder',
        name: term.name,
        binderKind,
        domain,
        body
      };
    }

    case 'App':
      return {
        tag: 'App',
        fn: elabToKernelWithMap(
          term.fn,
          elabMap,
          appendPath(surfacePath, fieldSeg('fn')),
          appendPath(kernelPath, fieldSeg('fn'))
        ),
        arg: elabToKernelWithMap(
          term.arg,
          elabMap,
          appendPath(surfacePath, fieldSeg('arg')),
          appendPath(kernelPath, fieldSeg('arg'))
        )
      };

    case 'Hole':
      return {
        tag: 'Hole',
        id: term.id,
        type: elabToKernelWithMap(
          term.type,
          elabMap,
          appendPath(surfacePath, fieldSeg('type')),
          appendPath(kernelPath, fieldSeg('type'))
        ),
        context: term.context.map((binding, i) => ({
          name: binding.name,
          type: elabToKernelWithMap(
            binding.type,
            elabMap,
            appendPath(surfacePath, fieldSeg('context'), arraySeg(i), fieldSeg('type')),
            appendPath(kernelPath, fieldSeg('context'), arraySeg(i), fieldSeg('type'))
          )
        }))
      };

    case 'Annot':
      return {
        tag: 'Annot',
        term: elabToKernelWithMap(
          term.term,
          elabMap,
          appendPath(surfacePath, fieldSeg('term')),
          appendPath(kernelPath, fieldSeg('term'))
        ),
        type: elabToKernelWithMap(
          term.type,
          elabMap,
          appendPath(surfacePath, fieldSeg('type')),
          appendPath(kernelPath, fieldSeg('type'))
        )
      };

    case 'Match':
      return {
        tag: 'Match',
        scrutinee: elabToKernelWithMap(
          term.scrutinee,
          elabMap,
          appendPath(surfacePath, fieldSeg('scrutinee')),
          appendPath(kernelPath, fieldSeg('scrutinee'))
        ),
        clauses: term.clauses.map((clause, i) => {
          const clauseSurfacePath = appendPath(surfacePath, fieldSeg('clauses'), arraySeg(i));
          const clauseKernelPath = appendPath(kernelPath, fieldSeg('clauses'), arraySeg(i));

          // Record the clause mapping
          elabMap.set(serializeIndexPath(clauseKernelPath), serializeIndexPath(clauseSurfacePath));

          // Reset wildcard counter for each clause so _w0 is the first wildcard in each clause
          wildcardCounter = 0;
          // Reset term param index for each clause
          currentTermParamIndex = 0;

          return {
            patterns: clause.patterns.map((pattern, patternIndex) => {
              const patternSurfacePath = appendPath(clauseSurfacePath, fieldSeg('patterns'), arraySeg(patternIndex));
              const patternKernelPath = appendPath(clauseKernelPath, fieldSeg('patterns'), arraySeg(patternIndex));
              const result = elabPatternToKernelWithMap(pattern, elabMap, patternSurfacePath, patternKernelPath);
              // Increment term param index after each top-level pattern
              currentTermParamIndex++;
              return result;
            }),
            rhs: elabToKernelWithMap(
              clause.rhs,
              elabMap,
              appendPath(clauseSurfacePath, fieldSeg('rhs')),
              appendPath(clauseKernelPath, fieldSeg('rhs'))
            )
          };
        })
      };
  }
}

/**
 * Elaborate a surface pattern (TPattern) to a kernel pattern (TTKPattern)
 * while tracking path correspondence in the elabMap.
 */
function elabPatternToKernelWithMap(
  pattern: TPattern,
  elabMap: ElabMap,
  surfacePath: IndexPath,
  kernelPath: IndexPath
): TTKPattern {
  // Record the correspondence between kernel and surface paths
  const kernelKey = serializeIndexPath(kernelPath);
  const surfaceKey = serializeIndexPath(surfacePath);
  elabMap.set(kernelKey, surfaceKey);

  switch (pattern.tag) {
    case 'PVar':
      return { tag: 'PVar', name: pattern.name };
    case 'PWild':
      // Generate a unique name for the wildcard, keeping it as PWild in kernel
      return { tag: 'PWild', name: freshWildcardName() };
    case 'PCtor': {
      // Look up the constructor's parameter names
      const paramNames = globalConstructorParamNames.get(pattern.name);

      // Elaborate each argument with the appropriate parameter context
      const elabArgs: TTKPattern[] = [];
      for (let argIndex = 0; argIndex < pattern.args.length; argIndex++) {
        // Save current context
        const savedParamNames = currentCtorParamNames;
        const savedParamIndex = currentCtorParamIndex;

        // Set context for this argument
        if (paramNames) {
          currentCtorParamNames = paramNames;
          currentCtorParamIndex = argIndex;
        }

        const argSurfacePath = appendPath(surfacePath, fieldSeg('args'), arraySeg(argIndex));
        const argKernelPath = appendPath(kernelPath, fieldSeg('args'), arraySeg(argIndex));
        elabArgs.push(elabPatternToKernelWithMap(pattern.args[argIndex], elabMap, argSurfacePath, argKernelPath));

        // Restore context
        currentCtorParamNames = savedParamNames;
        currentCtorParamIndex = savedParamIndex;
      }

      return {
        tag: 'PCtor',
        name: pattern.name,
        args: elabArgs
      };
    }
  }
}

/**
 * Look up a surface path given a kernel path.
 *
 * If the exact kernel path is not found, tries parent paths.
 * This handles cases where errors occur at a more specific location
 * than we've recorded.
 */
export function lookupSurfacePath(
  kernelPath: IndexPath,
  elabMap: ElabMap
): string | undefined {
  // Try exact match first
  const kernelKey = serializeIndexPath(kernelPath);
  const surfaceKey = elabMap.get(kernelKey);
  if (surfaceKey !== undefined) {
    return surfaceKey;
  }

  // Try parent paths (walking up the tree)
  for (let i = kernelPath.length - 1; i >= 0; i--) {
    const parentPath = kernelPath.slice(0, i);
    const parentKey = serializeIndexPath(parentPath);
    const parentSurfaceKey = elabMap.get(parentKey);
    if (parentSurfaceKey !== undefined) {
      return parentSurfaceKey;
    }
  }

  // No match found
  return undefined;
}

// ============================================================================
// Record Extension: Inline Extended Fields
// ============================================================================

/**
 * Error thrown when record extension fails.
 */
export class RecordExtensionError extends Error {
  constructor(message: string) {
    super(message);
    this.name = 'RecordExtensionError';
  }
}

/**
 * A registry of record definitions for looking up extended records.
 */
export interface RecordRegistry {
  get(name: string): RecordDef | undefined;
}

/**
 * Create a simple record registry from an array of records.
 */
export function createRecordRegistry(records: RecordDef[]): RecordRegistry {
  const map = new Map<string, RecordDef>();
  for (const record of records) {
    map.set(record.name, record);
  }
  return {
    get: (name) => map.get(name)
  };
}

/**
 * Inline all extended record fields into the given record.
 *
 * This is the first step of record elaboration:
 *   RecordDef (with extends) → RecordDef (no extends)
 */
export function inlineExtension(
  record: RecordDef,
  registry: RecordRegistry
): RecordDef {
  // If no extensions, return as-is
  if (!record.extends || record.extends.length === 0) {
    return record;
  }

  // Collect all inherited fields
  const inheritedFields: RecordField[] = [];
  const seenFieldNames = new Set<string>();

  for (const parentName of record.extends) {
    const parent = registry.get(parentName);
    if (!parent) {
      throw new RecordExtensionError(
        `Record "${record.name}" extends unknown record "${parentName}"`
      );
    }

    // Recursively inline parent's extensions first
    const resolvedParent = inlineExtension(parent, registry);

    // Add parent's fields, checking for clashes
    for (const field of resolvedParent.fields) {
      if (seenFieldNames.has(field.name)) {
        throw new RecordExtensionError(
          `Record "${record.name}" has field name clash: "${field.name}" is defined in multiple extended records`
        );
      }
      seenFieldNames.add(field.name);
      inheritedFields.push(field);
    }
  }

  // Check for clashes with record's own fields
  for (const field of record.fields) {
    if (seenFieldNames.has(field.name)) {
      throw new RecordExtensionError(
        `Record "${record.name}" has field name clash: "${field.name}" is defined both locally and in an extended record`
      );
    }
  }

  // Return new record with inherited fields prepended
  return {
    name: record.name,
    type: record.type,
    params: record.params,
    fields: [...inheritedFields, ...record.fields],
    // Clear extends - they've been inlined
    extends: undefined
  };
}

// ============================================================================
// Record Elaboration: RecordDef → TTKRecordDef
// ============================================================================

/**
 * Elaborate a record field from TT to TTK.
 */
export function elabRecordFieldToKernel(field: RecordField): TTKRecordField {
  return {
    name: field.name,
    type: elabToKernel(field.type)
  };
}

/**
 * Elaborate a record param from TT to TTK.
 */
function elabRecordParamToKernel(param: RecordParam): TTKRecordParam {
  return {
    name: param.name,
    type: elabToKernel(param.type),
  };
}

/**
 * Elaborate a record definition from TT to TTK.
 *
 * This assumes extensions have already been inlined via inlineExtension.
 */
export function elabRecordToKernel(record: RecordDef): TTKRecordDef {
  if (record.extends && record.extends.length > 0) {
    throw new Error(
      `Record "${record.name}" still has extends - call inlineExtension first`
    );
  }

  return {
    name: record.name,
    type: elabToKernel(record.type),
    params: record.params.map(elabRecordParamToKernel),
    fields: record.fields.map(elabRecordFieldToKernel),
  };
}

/**
 * Full elaboration pipeline for a record:
 * 1. Inline extensions
 * 2. Convert to kernel
 */
export function elabRecordFull(
  record: RecordDef,
  registry: RecordRegistry
): TTKRecordDef {
  const inlined = inlineExtension(record, registry);
  return elabRecordToKernel(inlined);
}
