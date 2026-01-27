/**
 * Name Resolution - Symbol Validation and Context Building
 *
 * This phase sits between parsing and type checking:
 * 1. Parser produces TTerm with Const nodes (string names)
 * 2. Name resolution validates that all Const names exist in context
 * 3. Type checker receives validated terms
 *
 * Key responsibilities:
 * - Check that all constant references are defined
 * - Build up global context as declarations are processed
 * - Report undefined symbol errors with locations
 */

import { TTerm } from '../compiler/surface';
import { IndexPath } from './source-position';
import { defaultRecordConstructorName } from '../compiler/elab';

// ============================================================================
// Reserved Names
// ============================================================================

/**
 * Set of reserved keywords that cannot be used as names for types,
 * constructors, terms, records, etc.
 *
 * These include:
 * - Type and Prop (universe sorts)
 * - ULevel (type of universe levels)
 * - USucc, UMax, UIMax (universe level operations)
 */
export const RESERVED_NAMES: ReadonlySet<string> = new Set([
  'Type',
  'Prop',
  'ULevel',
  'USucc',
  'UMax',
  'UIMax',
]);

/**
 * Check if a name is reserved and cannot be used as a declaration name.
 */
export function isReservedName(name: string): boolean {
  return RESERVED_NAMES.has(name);
}

// ============================================================================
// Error Types
// ============================================================================

export interface NameResolutionError {
  message: string;
  symbolName: string;
  path: IndexPath;
}

export type NameResolutionResult<T = void> =
  | { success: true; value: T }
  | { success: false; errors: NameResolutionError[] };

// ============================================================================
// Symbol Context
// ============================================================================

/**
 * Context for name resolution - tracks which symbols are in scope.
 * This is simpler than the type-checking context - we only care about names.
 */
export type SymbolContext = Set<string>;

/**
 * Create a new empty symbol context
 */
export function emptySymbolContext(): SymbolContext {
  return new Set<string>();
}

/**
 * Add a symbol to the context
 */
export function addSymbol(ctx: SymbolContext, name: string): SymbolContext {
  const newCtx = new Set(ctx);
  newCtx.add(name);
  return newCtx;
}

/**
 * Check if a symbol is defined in the context
 */
export function isSymbolDefined(ctx: SymbolContext, name: string): boolean {
  return ctx.has(name);
}

// ============================================================================
// Term Validation
// ============================================================================

/**
 * Validate that all constant references in a term are defined in the context.
 *
 * This recursively walks the AST and collects all undefined symbol errors.
 *
 * @param term - The term to validate
 * @param ctx - The symbol context
 * @param path - Current position in the AST (for error reporting)
 * @returns Result with collected errors
 */
export function validateTerm(
  term: TTerm,
  ctx: SymbolContext,
  path: IndexPath = []
): NameResolutionResult {
  const errors: NameResolutionError[] = [];

  function walk(t: TTerm, p: IndexPath): void {
    switch (t.tag) {
      case 'Var':
      case 'Hole':
      case 'ULevel':
      case 'ULit':
      case 'UOmega':
        // These don't reference symbols
        break;

      case 'Sort':
        // Levels are validated during elaboration, not name resolution
        break;

      case 'Const':
        // Check if constant is defined (skip reserved names - they're built-ins)
        if (!isReservedName(t.name) && !isSymbolDefined(ctx, t.name)) {
          errors.push({
            message: `Undefined symbol '${t.name}'`,
            symbolName: t.name,
            path: p
          });
        }
        break;

      case 'Binder':
        // Validate domain (if present - let bindings may have optional domain)
        if (t.domain !== undefined) {
          walk(t.domain, [...p, { kind: 'field', name: 'domain' }]);
        }

        // For let bindings, validate the definition value
        if (t.binderKind.tag === 'BLetTT') {
          walk(t.binderKind.defVal, [...p, { kind: 'field', name: 'defVal' }]);
        }

        // Validate body
        walk(t.body, [...p, { kind: 'field', name: 'body' }]);
        break;

      case 'App':
        walk(t.fn, [...p, { kind: 'field', name: 'fn' }]);
        walk(t.arg, [...p, { kind: 'field', name: 'arg' }]);
        break;

      case 'Annot':
        walk(t.term, [...p, { kind: 'field', name: 'term' }]);
        walk(t.type, [...p, { kind: 'field', name: 'type' }]);
        break;

      case 'Match':
        // Validate scrutinee
        walk(t.scrutinee, [...p, { kind: 'field' as const, name: 'scrutinee' }]);

        // Validate each clause
        t.clauses.forEach((clause, i) => {
          const clausePath: IndexPath = [...p, { kind: 'field' as const, name: 'clauses' }, { kind: 'array' as const, index: i }];
          walk(clause.rhs, [...clausePath, { kind: 'field' as const, name: 'rhs' }]);
        });
        break;
    }
  }

  walk(term, path);

  if (errors.length > 0) {
    return { success: false, errors };
  }
  return { success: true, value: undefined };
}

// ============================================================================
// Declaration Validation
// ============================================================================

/**
 * Validate a single declaration and return an updated context.
 *
 * The declaration itself is added to the context BEFORE validating its body,
 * allowing self-reference (needed for recursive definitions).
 *
 * @param name - Name of the declaration being defined
 * @param declType - Optional type annotation
 * @param declValue - Optional value/definition
 * @param constructors - Optional constructors (for inductive types)
 * @param ctx - Current symbol context
 * @returns Result with updated context or errors
 */
export function validateDeclaration(
  name: string | undefined,
  declType: TTerm | undefined,
  declValue: TTerm | undefined,
  constructors: Array<{ name: string; type: TTerm }> | undefined,
  ctx: SymbolContext
): NameResolutionResult<SymbolContext> {
  const errors: NameResolutionError[] = [];

  // Check for reserved name
  if (name && isReservedName(name)) {
    errors.push({
      message: `'${name}' is a reserved keyword and cannot be used as a name`,
      symbolName: name,
      path: []  // Path to the declaration name itself
    });
  }

  // Check for duplicate declaration name
  if (name && isSymbolDefined(ctx, name)) {
    errors.push({
      message: `Symbol '${name}' is already defined`,
      symbolName: name,
      path: []  // Path to the declaration name itself
    });
  }

  // Add this declaration to context FIRST (for self-reference)
  let newCtx = ctx;
  if (name) {
    newCtx = addSymbol(ctx, name);
  }

  // Validate type if present
  if (declType) {
    const typeResult = validateTerm(declType, newCtx, [{ kind: 'field', name: 'type' }]);
    if (!typeResult.success) {
      errors.push(...typeResult.errors);
    }
  }

  // Validate value if present
  if (declValue) {
    const valueResult = validateTerm(declValue, newCtx, [{ kind: 'field', name: 'value' }]);
    if (!valueResult.success) {
      errors.push(...valueResult.errors);
    }
  }

  // Validate constructors if present (inductive type)
  if (constructors) {
    // Check for reserved and duplicate constructor names, and add to context
    constructors.forEach((ctor, i) => {
      // Check for reserved name
      if (isReservedName(ctor.name)) {
        errors.push({
          message: `'${ctor.name}' is a reserved keyword and cannot be used as a constructor name`,
          symbolName: ctor.name,
          path: [
            { kind: 'field' as const, name: 'constructors' },
            { kind: 'array' as const, index: i }
          ]
        });
      }
      // Check for duplicate
      if (isSymbolDefined(newCtx, ctor.name)) {
        errors.push({
          message: `Constructor '${ctor.name}' is already defined`,
          symbolName: ctor.name,
          path: [
            { kind: 'field' as const, name: 'constructors' },
            { kind: 'array' as const, index: i }
          ]
        });
      }
      newCtx = addSymbol(newCtx, ctor.name);
    });

    // Validate each constructor type
    constructors.forEach((ctor, i) => {
      const ctorPath = [
        { kind: 'field' as const, name: 'constructors' },
        { kind: 'array' as const, index: i },
        { kind: 'field' as const, name: 'type' }
      ];
      const ctorResult = validateTerm(ctor.type, newCtx, ctorPath);
      if (!ctorResult.success) {
        errors.push(...ctorResult.errors);
      }
    });
  }

  if (errors.length > 0) {
    return { success: false, errors };
  }
  return { success: true, value: newCtx };
}

/**
 * Validate a list of declarations, building up the context as we go.
 *
 * Each declaration is validated and then added to the context for subsequent
 * declarations. This allows forward references within the same block.
 *
 * @param declarations - Array of declarations to validate
 * @param initialCtx - Initial symbol context (from previous blocks)
 * @returns Result with final context or all collected errors
 */
export function validateDeclarations(
  declarations: Array<{
    name?: string;
    type?: TTerm;
    value?: TTerm;
    constructors?: Array<{ name: string; type: TTerm }>;
    // Record-specific properties
    kind?: string;
    constructorName?: string;
    fields?: Array<{ name: string; type?: TTerm }>;
  }>,
  initialCtx: SymbolContext = emptySymbolContext()
): NameResolutionResult<SymbolContext> {
  const allErrors: NameResolutionError[] = [];
  let ctx = initialCtx;

  for (const decl of declarations) {
    const result = validateDeclaration(
      decl.name,
      decl.type,
      decl.value,
      decl.constructors,
      ctx
    );

    if (result.success) {
      ctx = result.value;
    } else {
      // Collect errors but continue processing
      // Still add the declaration to context to avoid cascading errors
      allErrors.push(...result.errors);
      if (decl.name) {
        ctx = addSymbol(ctx, decl.name);
      }
      if (decl.constructors) {
        decl.constructors.forEach(ctor => {
          ctx = addSymbol(ctx, ctor.name);
        });
      }
    }

    // For record declarations, also add the constructor name and projection names
    if (decl.kind === 'record' && decl.name) {
      const ctorName = decl.constructorName ?? defaultRecordConstructorName(decl.name);
      ctx = addSymbol(ctx, ctorName);

      // Add projection names for each field (e.g., Point.x, Point.y)
      if (decl.fields) {
        for (const field of decl.fields) {
          const projName = `${decl.name}.${field.name}`;
          ctx = addSymbol(ctx, projName);
        }
      }
    }
  }

  if (allErrors.length > 0) {
    return { success: false, errors: allErrors };
  }
  return { success: true, value: ctx };
}
