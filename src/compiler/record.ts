/**
 * Record (structure) type checking and conversion.
 *
 * Records are stored internally as single-constructor inductives with extra metadata.
 * This module handles:
 * - Converting TTKRecordDef to InductiveDefinition
 * - Type checking record declarations
 * - Generating projection functions
 */

import { TTKRecordDef, TTKTerm, TTKRecordField, TTKRecordParam, mkPi, mkVar, mkConst, mkApp } from './kernel';
import { InductiveDefinition, RecordInfo, NamedArgMap } from './term';
import { shiftTerm } from './subst';

/**
 * Substitute field references with projection calls in a term.
 *
 * In the original field type context [prev_fields..., params...]:
 * - Field refs are at indices 0 to fieldIdx-1
 * - Param refs are at indices fieldIdx to fieldIdx+numParams-1
 *
 * In the projection type context [r, params...]:
 * - r is at index 0
 * - Params are at indices 1 to numParams
 *
 * For a field ref at index j (where j < fieldIdx), we substitute with:
 *   Record.field_j param_0 ... param_{n-1} r
 * Which in de Bruijn: App(...App(Const(projName), Var(numParams))..., Var(1)), Var(0))
 * At depth d: App(...App(Const(projName), Var(d+numParams))..., Var(d+1)), Var(d))
 *
 * The field index j maps to prevFieldNames[fieldIdx - 1 - j] since fields are
 * stored in the opposite order (most recent first in de Bruijn).
 */
function substituteFieldRefsWithProjections(
  term: TTKTerm,
  recordName: string,
  prevFieldNames: string[],  // Names of fields 0 to fieldIdx-1, in order
  numParams: number,
  fieldIdx: number  // Number of previous fields (= cutoff for field refs)
): TTKTerm {
  function subst(t: TTKTerm, depth: number): TTKTerm {
    switch (t.tag) {
      case 'Var': {
        // Adjust for depth to get original context index
        const adjustedIdx = t.index - depth;
        if (adjustedIdx >= 0 && adjustedIdx < fieldIdx) {
          // This is a field reference - substitute with projection call
          // Field at adjustedIdx (in original context) is prevFieldNames[fieldIdx - 1 - adjustedIdx]
          const fieldName = prevFieldNames[fieldIdx - 1 - adjustedIdx];
          const projName = `${recordName}.${fieldName}`;

          // Build: projName param_{n-1} ... param_0 r
          // In the projection context at depth d:
          // - params are at indices d+numParams, d+numParams-1, ..., d+1
          // - r is at index d
          let result: TTKTerm = mkConst(projName);
          // Add params in order (first param first)
          for (let i = 0; i < numParams; i++) {
            result = mkApp(result, mkVar(depth + numParams - i));
          }
          // Add record argument r
          result = mkApp(result, mkVar(depth));
          return result;
        }
        // Param ref or local binder ref
        // Param refs (adjustedIdx >= fieldIdx) need to be shifted
        // Original context: [field_{idx-1}, ..., field_0, params...]
        //   - params at indices fieldIdx to fieldIdx+numParams-1
        // Projection context: [r, params...]
        //   - params at indices 1 to numParams
        // Shift amount: 1 - fieldIdx
        if (adjustedIdx >= fieldIdx) {
          const shiftAmount = 1 - fieldIdx;
          if (shiftAmount !== 0) {
            return mkVar(t.index + shiftAmount);
          }
        }
        // Local binder ref (adjustedIdx < 0) or no shift needed - keep as-is
        return t;
      }

      case 'Const':
      case 'Sort':
      case 'ULevel':
      case 'ULit':
      case 'UOmega':
      case 'Hole':
        return t;

      case 'App': {
        const newFn = subst(t.fn, depth);
        const newArg = subst(t.arg, depth);
        if (newFn === t.fn && newArg === t.arg) return t;
        return mkApp(newFn, newArg);
      }

      case 'Binder': {
        const newDomain = subst(t.domain, depth);
        const newBody = subst(t.body, depth + 1);
        if (newDomain === t.domain && newBody === t.body) return t;
        return { ...t, domain: newDomain, body: newBody };
      }

      case 'Match': {
        // Count pattern binders to adjust depth
        const patternBinderCount = t.clauses.reduce((acc, c) =>
          Math.max(acc, c.patterns.reduce((a, p) => a + countPatternBinders(p), 0)), 0);
        const newScrutinee = subst(t.scrutinee, depth);
        const newClauses = t.clauses.map(c => ({
          ...c,
          rhs: subst(c.rhs, depth + patternBinderCount)
        }));
        return { tag: 'Match', scrutinee: newScrutinee, clauses: newClauses };
      }

      default:
        return t;
    }
  }

  return subst(term, 0);
}

function countPatternBinders(p: import('./kernel').TTKPattern): number {
  switch (p.tag) {
    case 'PVar':
    case 'PWild':
      return 1;
    case 'PCtor':
      return p.args.reduce((acc, arg) => acc + countPatternBinders(arg), 0);
    default:
      return 0;
  }
}

// ============================================================================
// Record → Inductive Conversion
// ============================================================================

/**
 * Build the type of a record from its parameters.
 *
 * For a record like:
 *   record Pair (A : Type) (B : Type) where ...
 *
 * The type is: (A : Type) → (B : Type) → Type
 *
 * @param params - The record parameters
 * @param resultSort - The result sort (usually Type_0)
 * @returns The type of the record
 */
export function buildRecordType(
  params: TTKRecordParam[],
  resultSort: TTKTerm
): TTKTerm {
  // Build from right to left: last param → ... → first param → resultSort
  let result = resultSort;
  for (let i = params.length - 1; i >= 0; i--) {
    const param = params[i];
    result = mkPi(param.type, result, param.name);
  }
  return result;
}

/**
 * Build the constructor type for a record.
 *
 * For a record like:
 *   record Pair (A : Type) (B : Type) where
 *     fst : A
 *     snd : B
 *
 * The constructor type is:
 *   (A : Type) → (B : Type) → (fst : A) → (snd : B) → Pair A B
 *
 * Where field types are shifted to account for param binders.
 *
 * @param recordName - Name of the record type
 * @param params - Record parameters
 * @param fields - Record fields (types are in param context)
 * @returns The type of the constructor
 */
export function buildRecordConstructorType(
  recordName: string,
  params: TTKRecordParam[],
  fields: TTKRecordField[]
): TTKTerm {
  const numParams = params.length;
  const numFields = fields.length;

  // Build the return type: Record A B (applied to all params)
  // After all binders (params + fields), params are at indices:
  //   param[0] is at index numFields + numParams - 1
  //   param[i] is at index numFields + numParams - 1 - i
  let returnType: TTKTerm = mkConst(recordName);
  for (let i = 0; i < numParams; i++) {
    const paramIndex = numFields + numParams - 1 - i;
    returnType = mkApp(returnType, mkVar(paramIndex));
  }

  // Add field types as inner binders
  // Field types in the input are already in the right context:
  // the parser includes previous fields (most recent first), so field i's type
  // has indices that account for fields 0..i-1 and all params.
  // No shifting needed.
  let result = returnType;
  for (let i = fields.length - 1; i >= 0; i--) {
    const field = fields[i];
    // Note: implicit fields are tracked in recordInfo.implicitFields, not in the Pi type
    result = mkPi(field.type, result, field.name);
  }

  // Add param types as outer binders
  // Params don't need shifting as they're the outermost
  for (let i = numParams - 1; i >= 0; i--) {
    const param = params[i];
    result = mkPi(param.type, result, param.name);
  }

  return result;
}

/**
 * Convert a TTKRecordDef to an InductiveDefinition.
 *
 * This is the core transformation that allows records to be treated
 * as single-constructor inductives with additional metadata.
 */
export function recordToInductiveDefinition(record: TTKRecordDef): InductiveDefinition {
  // Build the constructor type
  const ctorType = buildRecordConstructorType(
    record.name,
    record.params,
    record.fields
  );

  // Set up namedArgMap for ALL record params in the constructor.
  // For record constructors, all type params are inferrable from the return type,
  // so they all get holes auto-inserted in applications like `MkPair b a`.
  // This is how Lean/Idris handle record constructors - you don't need to provide
  // the type params explicitly, they're inferred from context.
  // Pattern matching uses recordInfo.paramCount to insert wildcards for ALL params.
  const ctorNamedArgMap: NamedArgMap = new Map();
  for (let i = 0; i < record.params.length; i++) {
    const param = record.params[i];
    ctorNamedArgMap.set(param.name, i);
  }

  // For now, we DON'T set up namedArgMap for the record type.
  // This allows type parameters to be passed positionally (e.g., Pair Nat Nat).
  // Named argument syntax will be handled separately in the future.
  const typeNamedArgMap: NamedArgMap = new Map();

  // Build record info
  const recordInfo: RecordInfo = {
    fieldNames: record.fields.map(f => f.name),
    implicitFields: record.fields
      .map((f, i) => f.implicit ? i : -1)
      .filter(i => i >= 0),
    projections: record.fields.map(f => `${record.name}.${f.name}`),
    isEtaExpandable: true,
    paramCount: record.params.length,
  };

  return {
    name: record.name,
    type: record.type,
    constructors: [{
      name: record.constructorName,
      type: ctorType,
      namedArgMap: ctorNamedArgMap.size > 0 ? ctorNamedArgMap : undefined,
    }],
    indexPositions: [], // Records have no indices (only parameters)
    namedArgMap: typeNamedArgMap.size > 0 ? typeNamedArgMap : undefined,
    recordInfo,
  };
}

// ============================================================================
// Record Type Checking
// ============================================================================

// TODO: Implement checkRecordDeclaration
// This will validate:
// - Record type is a valid sort
// - Each field type is valid in its context
// - No unsolved metas
// - Parameter/extends compatibility

// ============================================================================
// Projection Generation
// ============================================================================

import { mkLambda, TTKClause, TTKPattern } from './kernel';
import { TermDefinition } from './term';

/**
 * A generated projection definition for a record field.
 */
export interface ProjectionDefinition {
  name: string;           // e.g., "Point.x"
  type: TTKTerm;         // e.g., Point → Nat
  value: TTKTerm;        // e.g., λ p. match p with { MkPoint x y => x }
}

/**
 * Generate projection functions for all fields of a record.
 *
 * For a record like:
 *   record Pair (A : Type) (B : Type) where
 *     fst : A
 *     snd : B
 *
 * Generates:
 *   Pair.fst : (A : Type) → (B : Type) → Pair A B → A
 *   Pair.fst A B p = match p with { MkPair _ _ f s => f }
 *
 *   Pair.snd : (A : Type) → (B : Type) → Pair A B → B
 *   Pair.snd A B p = match p with { MkPair _ _ f s => s }
 *
 * @param record - The record definition
 * @returns Array of projection definitions, one per field
 */
export function generateProjections(record: TTKRecordDef): ProjectionDefinition[] {
  const projections: ProjectionDefinition[] = [];
  const numParams = record.params.length;
  const numFields = record.fields.length;

  for (let fieldIdx = 0; fieldIdx < numFields; fieldIdx++) {
    const field = record.fields[fieldIdx];
    const projName = `${record.name}.${field.name}`;

    // Build the projection type:
    // (P1 : T1) → ... → (Pn : Tn) → R P1 ... Pn → Fi[shifted]
    const projType = buildProjectionType(record, fieldIdx);

    // Build the projection value:
    // λ P1 ... Pn. λ r. match r with { Ctor p1 ... pn f1 ... fm => fi }
    const projValue = buildProjectionValue(record, fieldIdx);

    projections.push({
      name: projName,
      type: projType,
      value: projValue,
    });
  }

  return projections;
}

/**
 * Build the type of a projection function.
 *
 * For Pair.fst: (A : Type) → (B : Type) → Pair A B → A
 *
 * The field type needs to be shifted to account for the lambda binders.
 * Original field type is in context with just params (P1...Pn).
 * Final position is: (P1)...(Pn)(r), so params shift by 1 (for r).
 */
function buildProjectionType(record: TTKRecordDef, fieldIdx: number): TTKTerm {
  const numParams = record.params.length;
  const field = record.fields[fieldIdx];

  // Build the record application: R P1 ... Pn
  // After params are bound but before the record arg,
  // params are at indices: P1 = numParams-1, P2 = numParams-2, ..., Pn = 0
  let recordApp: TTKTerm = mkConst(record.name);
  for (let i = 0; i < numParams; i++) {
    // param[i] is at index (numParams - 1 - i) when we're building the record arg binder
    const paramIdx = numParams - 1 - i;
    recordApp = mkApp(recordApp, mkVar(paramIdx));
  }

  // The return type is the field type with field refs substituted.
  // Original field type is in context [prev_fields..., params...]:
  //   - Param refs (indices >= fieldIdx) are at same positions in projection context
  //   - Field refs (indices < fieldIdx) should become projection calls: Record.field params... r
  const returnType = substituteFieldRefsWithProjections(
    field.type,
    record.name,
    record.fields.slice(0, fieldIdx).map(f => f.name),  // Previous field names
    numParams,
    fieldIdx
  );

  // Build the innermost Pi: (r : R P1...Pn) → Fi[shifted]
  let result: TTKTerm = mkPi(recordApp, returnType, 'r');

  // Add param binders from right to left
  // Each param's domain is already correct (in the context above it)
  for (let i = numParams - 1; i >= 0; i--) {
    const param = record.params[i];
    result = mkPi(param.type, result, param.name);
  }

  return result;
}

/**
 * Build the value of a projection function.
 *
 * For Pair.fst: λ A. λ B. λ p. match p with { MkPair a b f s => f }
 *
 * The match pattern binds all constructor arguments (params + fields).
 * The RHS returns the appropriate field variable.
 */
function buildProjectionValue(record: TTKRecordDef, fieldIdx: number): TTKTerm {
  const numParams = record.params.length;
  const numFields = record.fields.length;
  const totalCtorArgs = numParams + numFields;

  // Build the pattern: Ctor p1 ... pn f1 ... fm
  // We use wildcards for everything except the field we want
  const patternArgs: TTKPattern[] = [];
  for (let i = 0; i < totalCtorArgs; i++) {
    const isTargetField = i === numParams + fieldIdx;
    if (isTargetField) {
      // Use a named variable for the field we're projecting
      patternArgs.push({ tag: 'PVar', name: record.fields[fieldIdx].name });
    } else if (i < numParams) {
      // Param patterns - use wildcards
      patternArgs.push({ tag: 'PWild', name: `_p${i}` });
    } else {
      // Other field patterns - use wildcards
      const otherFieldIdx = i - numParams;
      patternArgs.push({ tag: 'PWild', name: `_${record.fields[otherFieldIdx].name}` });
    }
  }

  const pattern: TTKPattern = {
    tag: 'PCtor',
    name: record.constructorName,
    args: patternArgs,
  };

  // The RHS: return the field variable.
  // Since only the target field uses PVar (all others are PWild), and WHNF's
  // matchPattern returns bindings only for PVar (not PWild), the RHS must use
  // Var(0) — the single PVar binding. This matches the PVar-only convention
  // used by pattern-matching functions compiled via checkTermValue.
  const rhs: TTKTerm = mkVar(0);

  const clause: TTKClause = {
    patterns: [pattern],
    rhs: rhs,
  };

  // Build the match expression: match r with { ... }
  // r is at index 0 (innermost lambda)
  const matchExpr: TTKTerm = {
    tag: 'Match',
    scrutinee: mkVar(0),
    clauses: [clause],
  };

  // Build the lambdas from inside out
  // First, the record argument lambda
  // The domain is R P1 ... Pn where params are at indices numParams-1, ..., 0
  let recordDomain: TTKTerm = mkConst(record.name);
  for (let i = 0; i < numParams; i++) {
    const paramIdx = numParams - 1 - i;
    recordDomain = mkApp(recordDomain, mkVar(paramIdx));
  }

  let result: TTKTerm = mkLambda(recordDomain, matchExpr, 'r');

  // Add param lambdas from right to left
  for (let i = numParams - 1; i >= 0; i--) {
    const param = record.params[i];
    result = mkLambda(param.type, result, param.name);
  }

  return result;
}

/**
 * Convert projection definitions to TermDefinitions for adding to the definitions map.
 */
export function projectionsToTermDefinitions(projections: ProjectionDefinition[]): TermDefinition[] {
  return projections.map(proj => ({
    name: proj.name,
    type: proj.type,
    value: proj.value,
  }));
}
