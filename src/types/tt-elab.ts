/**
 * TT Elaboration Layer
 *
 * This module is the ONLY place that knows about both TT (surface syntax)
 * and TTK (kernel syntax). It provides:
 *
 * 1. elabToKernel: TT → TTK - Deep traversal converting surface terms to kernel
 * 2. inlineExtension: Inline extended record fields before elaboration
 *
 * The elaboration pipeline for records is:
 *   RecordDef (with extends) → inlineExtension → RecordDef (no extends) → elabRecordToKernel → TTKRecordDef
 */

import type {
  TTerm,
  TContext,
  TBinding,
  RecordDef,
  RecordField,
  RecordParam,
} from './tt-core';

import type {
  TTKTerm,
  TTKContext,
  TTKBinding,
  TTKBinderKind,
  TTKRecordDef,
  TTKRecordField,
  TTKRecordParam,
} from './tt-kernel';

// Re-export TTKRecordDef for consumers
export type { TTKRecordDef };

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
        case 'BPi':
          binderKind = { tag: 'BPi' };
          break;
        case 'BLam':
          binderKind = { tag: 'BLam' };
          break;
        case 'BLet':
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
 *
 * The function:
 * 1. Recursively resolves extended records
 * 2. Collects all fields from extended records
 * 3. Checks for field name clashes (throws error if found)
 * 4. Returns a new RecordDef with all fields inlined
 *
 * @param record - The record to process
 * @param registry - Registry to look up extended records
 * @returns A new RecordDef with extensions inlined
 * @throws RecordExtensionError if there are field name clashes
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
 * If the record has extends, this will throw an error.
 *
 * @param record - The record definition (should have no extends)
 * @returns Kernel record definition
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
 *
 * @param record - The record to elaborate
 * @param registry - Registry for looking up extended records
 * @returns Kernel record definition
 */
export function elabRecordFull(
  record: RecordDef,
  registry: RecordRegistry
): TTKRecordDef {
  const inlined = inlineExtension(record, registry);
  return elabRecordToKernel(inlined);
}

