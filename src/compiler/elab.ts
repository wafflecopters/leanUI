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
  TLevel,
} from './surface';

import { mkHoleTT, mkPropTT } from './surface';

import type {
  TTKTerm,
  TTKContext,
  TTKBinderKind,
  TTKPattern,
  TTKRecordDef,
  TTKRecordField,
  TTKRecordParam,
} from './kernel';

import { mkLevelNum, mkMeta, mkHole, mkLSucc, mkLMax, mkLIMax, mkULit, mkUOmega, mkSort, mkVar } from './kernel';
import { shiftTerm } from './subst';

// Counter for generating unique meta IDs for implicit let types
let implicitLetTypeCounter = 0;

function freshImplicitLetTypeHole(letName: string): TTKTerm {
  // Use a Hole (not a Meta) for implicit let types.
  // The type checker will convert this to a properly registered Meta
  // with type inference during checkType.
  return mkHole(`${letName}_type_${implicitLetTypeCounter++}`);
}

import {
  ElabMap,
  IndexPath,
  appendPath,
  fieldSeg,
  arraySeg,
  serializeIndexPath
} from '../types/source-position';

import type { DefinitionsMap } from './term';

// Re-export TTKRecordDef for consumers
export type { TTKRecordDef };

// ============================================================================
// Elaboration Environment (ElabEnv)
// ============================================================================

/**
 * Elaboration environment that tracks path through the surface AST.
 *
 * Similar to TCEnv in the type checker, ElabEnv provides:
 * 1. Path tracking for error location reporting
 * 2. Navigation methods that update paths automatically
 * 3. Error creation with automatic path inclusion
 *
 * The surfacePath tracks position in the source AST, which maps via
 * sourceMap to actual source code locations.
 */
export class ElabEnv<T = TTerm> {
  constructor(
    /** Current path in the surface AST */
    public readonly surfacePath: IndexPath,
    /** Current path in the kernel AST (may differ due to desugaring) */
    public readonly kernelPath: IndexPath,
    /** Map recording kernel→surface path correspondence */
    public readonly elabMap: ElabMap,
    /** Named arg map for pattern reordering (from function type) */
    public readonly patternNamedArgMap: NamedArgMap | undefined,
    /** Lookup for named arg maps of functions (for application elaboration) */
    public readonly appNamedArgLookup: NamedArgMapLookup | undefined,
    /** The current surface term being elaborated */
    public readonly value: T
  ) { }

  /**
   * Record the current kernel→surface path mapping in elabMap.
   */
  recordMapping(): void {
    const kernelKey = serializeIndexPath(this.kernelPath);
    const surfaceKey = serializeIndexPath(this.surfacePath);
    this.elabMap.set(kernelKey, surfaceKey);
  }

  /**
   * Create an elaboration error at the current surface path.
   */
  error(message: string): NamedArgElabError {
    return new NamedArgElabError(message, this.surfacePath);
  }

  /**
   * Create a new ElabEnv with updated value but same paths.
   */
  withValue<S>(value: S): ElabEnv<S> {
    return new ElabEnv(
      this.surfacePath,
      this.kernelPath,
      this.elabMap,
      this.patternNamedArgMap,
      this.appNamedArgLookup,
      value
    );
  }

  // ============================================================================
  // Navigation Methods - Binder
  // ============================================================================

  inBinderDomain(this: ElabEnv<TTerm & { tag: 'Binder' }>): ElabEnv<TTerm> {
    return new ElabEnv(
      appendPath(this.surfacePath, fieldSeg('domain')),
      appendPath(this.kernelPath, fieldSeg('domain')),
      this.elabMap,
      this.patternNamedArgMap,
      this.appNamedArgLookup,
      this.value.domain!
    );
  }

  inBinderBody(this: ElabEnv<TTerm & { tag: 'Binder' }>): ElabEnv<TTerm> {
    return new ElabEnv(
      appendPath(this.surfacePath, fieldSeg('body')),
      appendPath(this.kernelPath, fieldSeg('body')),
      this.elabMap,
      this.patternNamedArgMap,
      this.appNamedArgLookup,
      this.value.body
    );
  }

  inBinderLetDefVal(this: ElabEnv<TTerm & { tag: 'Binder'; binderKind: { tag: 'BLetTT'; defVal: TTerm } }>): ElabEnv<TTerm> {
    return new ElabEnv(
      appendPath(this.surfacePath, fieldSeg('binderKind'), fieldSeg('defVal')),
      appendPath(this.kernelPath, fieldSeg('binderKind'), fieldSeg('defVal')),
      this.elabMap,
      this.patternNamedArgMap,
      this.appNamedArgLookup,
      this.value.binderKind.defVal
    );
  }

  // ============================================================================
  // Navigation Methods - MultiBinder
  // ============================================================================

  inMultiBinderDomain(this: ElabEnv<TTerm & { tag: 'MultiBinder' }>): ElabEnv<TTerm> {
    return new ElabEnv(
      appendPath(this.surfacePath, fieldSeg('domain')),
      appendPath(this.kernelPath, fieldSeg('domain')),
      this.elabMap,
      this.patternNamedArgMap,
      this.appNamedArgLookup,
      this.value.domain
    );
  }

  /**
   * Navigate to MultiBinder body.
   * Note: kernel path needs special handling since MultiBinder expands to nested Binders.
   * @param nestingDepth - Number of names in the MultiBinder (for kernel path calculation)
   */
  inMultiBinderBody(this: ElabEnv<TTerm & { tag: 'MultiBinder' }>, nestingDepth: number): ElabEnv<TTerm> {
    // Kernel path: nested under n 'body' segments due to expansion
    let innerKernelPath = this.kernelPath;
    for (let i = 0; i < nestingDepth; i++) {
      innerKernelPath = appendPath(innerKernelPath, fieldSeg('body'));
    }
    return new ElabEnv(
      appendPath(this.surfacePath, fieldSeg('body')),
      innerKernelPath,
      this.elabMap,
      this.patternNamedArgMap,
      this.appNamedArgLookup,
      this.value.body
    );
  }

  // ============================================================================
  // Navigation Methods - App
  // ============================================================================

  inAppFn(this: ElabEnv<TTerm & { tag: 'App' }>): ElabEnv<TTerm> {
    return new ElabEnv(
      appendPath(this.surfacePath, fieldSeg('fn')),
      appendPath(this.kernelPath, fieldSeg('fn')),
      this.elabMap,
      this.patternNamedArgMap,
      this.appNamedArgLookup,
      this.value.fn
    );
  }

  inAppArg(this: ElabEnv<TTerm & { tag: 'App' }>): ElabEnv<TTerm> {
    return new ElabEnv(
      appendPath(this.surfacePath, fieldSeg('arg')),
      appendPath(this.kernelPath, fieldSeg('arg')),
      this.elabMap,
      this.patternNamedArgMap,
      this.appNamedArgLookup,
      this.value.arg
    );
  }

  // ============================================================================
  // Navigation Methods - Annot
  // ============================================================================

  inAnnotTerm(this: ElabEnv<TTerm & { tag: 'Annot' }>): ElabEnv<TTerm> {
    return new ElabEnv(
      appendPath(this.surfacePath, fieldSeg('term')),
      appendPath(this.kernelPath, fieldSeg('term')),
      this.elabMap,
      this.patternNamedArgMap,
      this.appNamedArgLookup,
      this.value.term
    );
  }

  inAnnotType(this: ElabEnv<TTerm & { tag: 'Annot' }>): ElabEnv<TTerm> {
    return new ElabEnv(
      appendPath(this.surfacePath, fieldSeg('type')),
      appendPath(this.kernelPath, fieldSeg('type')),
      this.elabMap,
      this.patternNamedArgMap,
      this.appNamedArgLookup,
      this.value.type
    );
  }

  // ============================================================================
  // Navigation Methods - Match
  // ============================================================================

  inMatchScrutinee(this: ElabEnv<TTerm & { tag: 'Match' }>): ElabEnv<TTerm> {
    return new ElabEnv(
      appendPath(this.surfacePath, fieldSeg('scrutinee')),
      appendPath(this.kernelPath, fieldSeg('scrutinee')),
      this.elabMap,
      this.patternNamedArgMap,
      this.appNamedArgLookup,
      this.value.scrutinee
    );
  }

  /**
   * Navigate to a specific clause in a Match.
   * surfaceIndex and kernelIndex may differ due to absurd clause filtering.
   */
  inMatchClause(
    this: ElabEnv<TTerm & { tag: 'Match' }>,
    surfaceIndex: number,
    kernelIndex: number
  ): ElabEnv<{ patterns: TPattern[]; rhs: TTerm }> {
    return new ElabEnv(
      appendPath(this.surfacePath, fieldSeg('clauses'), arraySeg(surfaceIndex)),
      appendPath(this.kernelPath, fieldSeg('clauses'), arraySeg(kernelIndex)),
      this.elabMap,
      this.patternNamedArgMap,
      this.appNamedArgLookup,
      this.value.clauses[surfaceIndex]
    );
  }

  /**
   * Navigate to a pattern within a clause.
   */
  inClausePattern(
    this: ElabEnv<{ patterns: TPattern[]; rhs: TTerm }>,
    patternIndex: number
  ): ElabEnv<TPattern> {
    return new ElabEnv(
      appendPath(this.surfacePath, fieldSeg('patterns'), arraySeg(patternIndex)),
      appendPath(this.kernelPath, fieldSeg('patterns'), arraySeg(patternIndex)),
      this.elabMap,
      this.patternNamedArgMap,
      this.appNamedArgLookup,
      this.value.patterns[patternIndex]
    );
  }

  /**
   * Navigate to the RHS of a clause.
   */
  inClauseRhs(this: ElabEnv<{ patterns: TPattern[]; rhs: TTerm }>): ElabEnv<TTerm> {
    return new ElabEnv(
      appendPath(this.surfacePath, fieldSeg('rhs')),
      appendPath(this.kernelPath, fieldSeg('rhs')),
      this.elabMap,
      this.patternNamedArgMap,
      this.appNamedArgLookup,
      this.value.rhs
    );
  }

  // ============================================================================
  // Navigation Methods - Inductive Definition Parts
  // ============================================================================

  /**
   * Navigate to a constructor type within an inductive definition context.
   * Used when elaborating constructor types.
   */
  inConstructorType(ctorIndex: number, ctorType: TTerm): ElabEnv<TTerm> {
    return new ElabEnv(
      appendPath(this.surfacePath, fieldSeg('constructors'), arraySeg(ctorIndex), fieldSeg('type')),
      appendPath(this.kernelPath, fieldSeg('constructors'), arraySeg(ctorIndex), fieldSeg('type')),
      this.elabMap,
      this.patternNamedArgMap,
      this.appNamedArgLookup,
      ctorType
    );
  }

  // ============================================================================
  // Factory Methods
  // ============================================================================

  /**
   * Create an initial ElabEnv for elaborating a term.
   */
  static create(
    term: TTerm,
    elabMap: ElabMap,
    surfacePath: IndexPath = [],
    kernelPath: IndexPath = [],
    patternNamedArgMap?: NamedArgMap,
    appNamedArgLookup?: NamedArgMapLookup
  ): ElabEnv<TTerm> {
    return new ElabEnv(
      surfacePath,
      kernelPath,
      elabMap,
      patternNamedArgMap,
      appNamedArgLookup,
      term
    );
  }
}

// ============================================================================
// Constructor Parameter Names
// ============================================================================

/**
 * Information about a parameter for wildcard naming.
 * - name: the explicit binder name (empty if unnamed)
 * - typePrefix: lowercase first letter of type name (null if type is complex)
 */
export interface ParamInfo {
  name: string;
  typePrefix: string | null;
}

/**
 * Map from constructor name to its parameter info.
 * Used during pattern elaboration to generate meaningful wildcard names.
 *
 * For example, if VCons : (A : Type) -> (n : Nat) -> A -> Vec A n -> Vec A (Succ n)
 * then constructorParamNames.get("VCons") = [
 *   { name: "A", typePrefix: null },  // named param
 *   { name: "n", typePrefix: null },  // named param
 *   { name: "", typePrefix: "a" },    // unnamed, type is A (variable)
 *   { name: "", typePrefix: "v" },    // unnamed, type is Vec (head of application)
 * ]
 */
export type ConstructorParamNames = Map<string, ParamInfo[]>;

/**
 * Extract the type prefix for wildcard naming from a type term.
 * Returns lowercase first letter of type name, or null if type is complex.
 *
 * Simple cases we handle (no whnf needed):
 * - Const: use lowercase first letter of name
 * - Var: use lowercase first letter of name
 * - App: recurse into fn to find the head
 *
 * Complex cases we skip:
 * - Binder (Pi/Lambda types)
 * - Sort, Hole, Match, Annot
 */
function extractTypePrefix(type: TTKTerm): string | null {
  switch (type.tag) {
    case 'Const':
      return type.name.length > 0 ? type.name[0].toLowerCase() : null;
    case 'Var':
      // Var uses de Bruijn indices - we don't have access to the name here
      // Could potentially look it up in context, but for now skip
      return null;
    case 'App':
      // For applications like (Vec A n), recurse into fn to find Vec
      return extractTypePrefix(type.fn);
    default:
      // Binder, Sort, Hole, Match, Annot - too complex
      return null;
  }
}

/**
 * Extract parameter info from a constructor's type (a Pi type).
 *
 * For example, given:
 *   VCons : (A : Type) -> (n : Nat) -> A -> Vec A n -> Vec A (Succ n)
 *
 * Returns: [
 *   { name: "A", typePrefix: null },
 *   { name: "n", typePrefix: null },
 *   { name: "", typePrefix: "a" },    // from type A
 *   { name: "", typePrefix: "v" },    // from type Vec
 * ]
 *
 * This walks the Pi chain and collects binder names and type prefixes.
 */
export function extractConstructorParamNames(ctorType: TTKTerm): ParamInfo[] {
  const params: ParamInfo[] = [];
  let current = ctorType;

  while (current.tag === 'Binder' && current.binderKind.tag === 'BPi') {
    // Use the binder name, or empty string if it's "_" or empty
    const name = current.name === '_' || current.name === '' ? '' : current.name;
    // Extract type prefix for unnamed params
    const typePrefix = name === '' ? extractTypePrefix(current.domain) : null;
    params.push({ name, typePrefix });
    current = current.body;
  }

  return params;
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
// Named Argument Maps
// ============================================================================

/**
 * Map from named argument label to its 0-based position index.
 * Used during elaboration to reorder named arguments to positional.
 *
 * For example, for the type:
 *   { A : Type } -> Nat -> { B : Type } -> A -> B
 * The NamedArgMap would be:
 *   Map { "A" => 0, "B" => 2 }
 */
export type NamedArgMap = Map<string, number>;

/**
 * Extract a map of named argument positions from a surface type.
 * Walks the Pi chain and records positions of binders with `named: true`.
 *
 * @param surfaceType - The surface-level type (TTerm) to extract from
 * @returns Map from argument name to position index
 */
export function extractNamedArgMap(surfaceType: TTerm): NamedArgMap {
  const map: NamedArgMap = new Map();
  let index = 0;
  let current: TTerm = surfaceType;

  while (true) {
    if (current.tag === 'Binder' && current.binderKind.tag === 'BPiTT') {
      // Check if this is a named binder
      if (current.named && current.name !== '_') {
        map.set(current.name, index);
      }
      index++;
      current = current.body;
    } else if (current.tag === 'MultiBinder' && current.binderKind.tag === 'BPiTT') {
      // Handle MultiBinder - each name gets its own index
      if (current.named) {
        for (const name of current.names) {
          if (name !== '_') {
            map.set(name, index);
          }
          index++;
        }
      } else {
        index += current.names.length;
      }
      current = current.body;
    } else {
      // Not a Pi binder, stop walking
      break;
    }
  }

  return map;
}

/**
 * Count the total number of parameters in a type.
 * Walks the Pi chain and counts all binders.
 */
export function countParameters(surfaceType: TTerm): number {
  let count = 0;
  let current: TTerm = surfaceType;

  while (true) {
    if (current.tag === 'Binder' && current.binderKind.tag === 'BPiTT') {
      count++;
      current = current.body;
    } else if (current.tag === 'MultiBinder' && current.binderKind.tag === 'BPiTT') {
      count += current.names.length;
      current = current.body;
    } else {
      break;
    }
  }

  return count;
}

/**
 * Lookup function for getting a definition's named argument map.
 * Returns undefined if the definition doesn't exist or has no named args.
 */
export type NamedArgMapLookup = (name: string) => NamedArgMap | undefined;

/**
 * Info about named arguments and arity for a definition.
 */
export interface NamedArgInfo {
  namedArgMap: NamedArgMap;
  totalArity?: number;
}

/**
 * Lookup function for getting a definition's named argument info (map + arity).
 * Returns undefined if the definition doesn't exist or has no named args.
 */
export type NamedArgInfoLookup = (name: string) => NamedArgInfo | undefined;

/**
 * Represents an argument in an application spine.
 */
type SpineArg =
  | { kind: 'positional'; term: TTerm }
  | { kind: 'named'; name: string; term: TTerm };

/**
 * Collect an application spine from nested Apps.
 * Returns the function head and list of arguments (in application order, left to right).
 */
function collectAppSpine(term: TTerm): { head: TTerm; args: SpineArg[] } {
  const args: SpineArg[] = [];
  let current = term;

  while (current.tag === 'App') {
    const app = current as { tag: 'App'; fn: TTerm; arg: TTerm; argName?: string };
    if (app.argName) {
      args.unshift({ kind: 'named', name: app.argName, term: app.arg });
    } else {
      args.unshift({ kind: 'positional', term: app.arg });
    }
    current = app.fn;
  }

  return { head: current, args };
}

/**
 * Check if an application spine has any named arguments.
 */
function hasNamedArgs(term: TTerm): boolean {
  let current = term;
  while (current.tag === 'App') {
    const app = current as { tag: 'App'; fn: TTerm; arg: TTerm; argName?: string };
    if (app.argName) return true;
    current = app.fn;
  }
  return false;
}

/**
 * Reorder application arguments, placing named args at their correct positions.
 * Missing implicit (named) arguments are filled with Holes for type inference.
 *
 * @param args - Mixed list of positional and named arguments
 * @param namedMap - Map from name to position index
 * @param totalArity - Total number of parameters the function expects (optional)
 * @returns Ordered list of positional arguments, or error message
 */
function reorderArgs(
  args: SpineArg[],
  namedMap: NamedArgMap,
  totalArity?: number
): { ordered: TTerm[]; error?: undefined } | { ordered?: undefined; error: string } {
  // Separate named and positional arguments
  const named: Array<{ name: string; term: TTerm }> = [];
  const positional: TTerm[] = [];

  for (const arg of args) {
    if (arg.kind === 'named') {
      named.push({ name: arg.name, term: arg.term });
    } else {
      positional.push(arg.term);
    }
  }

  // Find indices for all named arguments
  const namedIndices: Array<{ idx: number; term: TTerm }> = [];
  for (const n of named) {
    const idx = namedMap.get(n.name);
    if (idx === undefined) {
      return { error: `Unknown named argument: ${n.name}` };
    }
    namedIndices.push({ idx, term: n.term });
  }

  // CRITICAL: Get set of all named parameter positions.
  // Positional arguments can ONLY fill non-named positions.
  const namedPositions = new Set(namedMap.values());

  // Determine result size
  const maxNamedIdx = namedIndices.length > 0
    ? Math.max(...namedIndices.map(ni => ni.idx))
    : -1;

  // Result array - we fill named args at their positions, then fill positional in gaps
  // If totalArity is provided, use it to ensure we have room for all arguments
  const estimatedSize = Math.max(maxNamedIdx + 1, positional.length + named.length);
  const resultSize = totalArity !== undefined ? Math.max(totalArity, estimatedSize) : estimatedSize;
  const result: (TTerm | null)[] = new Array(resultSize).fill(null);

  // Place named arguments at their positions
  for (const ni of namedIndices) {
    if (result[ni.idx] !== null) {
      return { error: `Duplicate argument at position ${ni.idx}` };
    }
    result[ni.idx] = ni.term;
  }

  // Determine if we should allow positional args to fill named positions.
  // This happens when a type/constructor has ONLY implicit/named parameters (e.g., Maybe, Nothing).
  // In such cases, writing `Maybe Nat` is sugar for `Maybe {A:=Nat}`.
  const hasAnyExplicitPositions = (() => {
    for (let i = 0; i < result.length; i++) {
      if (!namedPositions.has(i)) return true;
    }
    return false;
  })();

  let posIdx = 0;

  if (!hasAnyExplicitPositions && positional.length > 0) {
    // ALL positions are implicit/named, but we have positional args.
    // Fill them into named positions left-to-right (sugar for named syntax).
    // Example: `Maybe Nat` becomes `Maybe {A:=Nat}`
    for (let i = 0; i < result.length && posIdx < positional.length; i++) {
      if (result[i] === null && namedPositions.has(i)) {
        result[i] = positional[posIdx++];
      }
    }
  } else {
    // Normal case: fill positional arguments ONLY in non-named positions (from left to right)
    for (let i = 0; i < result.length && posIdx < positional.length; i++) {
      // Skip this position if it's a named parameter position
      if (namedPositions.has(i)) {
        continue;
      }
      if (result[i] === null) {
        result[i] = positional[posIdx++];
      }
    }
  }

  // Check if we have leftover positional arguments
  if (posIdx < positional.length) {
    const extraCount = positional.length - posIdx;
    return { error: `Too many positional arguments: ${extraCount} extra argument(s) cannot fill named parameter positions` };
  }

  // Check for unfilled gaps that precede filled positions
  let lastFilled = -1;
  for (let i = result.length - 1; i >= 0; i--) {
    if (result[i] !== null) {
      lastFilled = i;
      break;
    }
  }

  // When named arguments are used, we need to consider ALL named positions
  // as potentially needing to be filled, not just those up to lastFilled.
  // This handles cases like `refl {A:=Nat}` where A is at position 0 but
  // `a` at position 1 still needs a hole for inference.
  const maxNamedPosition = namedPositions.size > 0 ? Math.max(...namedPositions) : -1;
  const fillUpTo = Math.max(lastFilled, maxNamedPosition);

  for (let i = 0; i < fillUpTo; i++) {
    if (result[i] === null && !namedPositions.has(i)) {
      // Only error for unfilled NON-named positions
      return { error: `Missing argument at position ${i}` };
    }
  }

  // Fill missing named positions with Holes (implicit argument inference)
  // These will be resolved during type checking via unification
  // IMPORTANT: Use global counter to ensure hole IDs are unique across all elaborations.
  // Different elaborations (e.g., function type vs RHS) may create holes that get unified
  // during pattern matching. If they share IDs, fillHole will incorrectly replace all of them.
  for (let i = 0; i <= fillUpTo; i++) {
    if (result[i] === null && namedPositions.has(i)) {
      // Create a hole with a placeholder type - will be inferred during type checking
      result[i] = mkHoleTT(`_implicit${globalImplicitHoleCounter++}`, mkHoleTT('_implicit_type', mkPropTT()));
    }
  }

  // Trailing nulls are OK (partial application) - trim them
  const ordered = result.slice(0, fillUpTo + 1).filter((t): t is TTerm => t !== null);
  return { ordered };
}

/**
 * Error thrown during elaboration with named arguments.
 * Includes an optional surfacePath for source location mapping.
 */
export class NamedArgElabError extends Error {
  public readonly surfacePath?: IndexPath;

  constructor(message: string, surfacePath?: IndexPath) {
    super(message);
    this.name = 'NamedArgElabError';
    this.surfacePath = surfacePath;
  }
}

// ============================================================================
// Constructor Pattern Detection and RHS Fixing
// ============================================================================

/**
 * Check if a name is a constructor in the given definitions.
 */
function isConstructorName(name: string, definitions: DefinitionsMap): boolean {
  for (const inductive of definitions.inductiveTypes.values()) {
    for (const ctor of inductive.constructors) {
      if (ctor.name === name) {
        return true;
      }
    }
  }
  return false;
}

/**
 * Fix RHS de Bruijn indices for patterns that the parser thought were variables
 * but are actually constructors.
 *
 * The parser uses a heuristic: lowercase no-arg patterns are treated as variable bindings.
 * This is wrong for lowercase constructors like 'refl'. This function:
 * 1. Identifies such patterns by checking if they're constructors in definitions
 * 2. For each constructor pattern, replaces Var references in the RHS with Const
 * 3. Adjusts remaining Var indices to account for the removed bindings
 *
 * @param patterns - The clause patterns (surface syntax)
 * @param rhs - The clause RHS (surface syntax)
 * @param definitions - The definitions map to check for constructors
 * @returns The transformed RHS with constructor patterns properly handled
 */
export function fixRhsForConstructorPatterns(
  patterns: TPattern[],
  rhs: TTerm,
  definitions: DefinitionsMap
): TTerm {
  // Find patterns that the parser thought were variables but are actually constructors
  // These are PCtor patterns with no args and lowercase first letter
  const constructorPatternIndices: { index: number; name: string }[] = [];

  // Count pattern variables left-to-right (same order as parser's collectPatternVars)
  let varIndex = 0;
  for (const pattern of patterns) {
    if (pattern.tag === 'PCtor' && pattern.args.length === 0 &&
      (!pattern.namedArgs || pattern.namedArgs.length === 0)) {
      const firstChar = pattern.name[0];
      const isLowercase = firstChar === firstChar.toLowerCase() && firstChar !== firstChar.toUpperCase();
      const isSingleUppercase = pattern.name.length === 1 && firstChar === firstChar.toUpperCase();

      if (isLowercase || isSingleUppercase) {
        // Parser would have bound this as a variable
        // Check if it's actually a constructor
        if (isConstructorName(pattern.name, definitions)) {
          constructorPatternIndices.push({ index: varIndex, name: pattern.name });
        }
        varIndex++;
      }
    } else if (pattern.tag === 'PWild') {
      varIndex++;
    } else if (pattern.tag === 'PVar') {
      varIndex++;
    } else if (pattern.tag === 'PCtor') {
      // PCtor with args - count vars from sub-patterns
      varIndex += countPatternVars(pattern);
    }
  }

  if (constructorPatternIndices.length === 0) {
    // No constructor patterns that need fixing
    return rhs;
  }

  // The parser uses reversed context for de Bruijn indices
  // So index 0 = rightmost variable, index (total-1) = leftmost variable
  const totalVars = varIndex;

  // Convert to de Bruijn indices (reverse the order)
  // In de Bruijn, index 0 is the last-bound (rightmost) variable
  const constructorDeBruijnIndices = constructorPatternIndices.map(({ index, name }) => ({
    deBruijnIndex: totalVars - 1 - index,
    name
  })).sort((a, b) => b.deBruijnIndex - a.deBruijnIndex); // Sort descending for proper shifting

  // Transform the RHS
  return transformRhsForConstructorPatterns(rhs, constructorDeBruijnIndices);
}

/**
 * Transform RHS by replacing Var references to constructor patterns with Const,
 * and adjusting remaining Var indices.
 */
function transformRhsForConstructorPatterns(
  term: TTerm,
  constructorIndices: { deBruijnIndex: number; name: string }[]
): TTerm {
  function transform(t: TTerm, depth: number): TTerm {
    switch (t.tag) {
      case 'Var': {
        const adjustedIndex = t.index - depth;

        // Check if this Var refers to a constructor pattern
        const ctorMatch = constructorIndices.find(c => c.deBruijnIndex === adjustedIndex);
        if (ctorMatch) {
          // Replace with Const
          return { tag: 'Const', name: ctorMatch.name };
        }

        // Adjust index for removed bindings
        // Count how many constructor indices are below this one
        let shift = 0;
        for (const c of constructorIndices) {
          if (c.deBruijnIndex < adjustedIndex) {
            shift++;
          }
        }

        if (shift > 0) {
          return { tag: 'Var', index: t.index - shift };
        }
        return t;
      }

      case 'App':
        return {
          tag: 'App',
          fn: transform(t.fn, depth),
          arg: transform(t.arg, depth),
          ...(t.argName ? { argName: t.argName } : {})
        };

      case 'Binder':
        return {
          tag: 'Binder',
          name: t.name,
          binderKind: t.binderKind,
          domain: t.domain ? transform(t.domain, depth) : undefined,
          body: transform(t.body, depth + 1),
          ...(t.named !== undefined ? { named: t.named } : {})
        };

      case 'MultiBinder':
        return {
          tag: 'MultiBinder',
          names: t.names,
          binderKind: t.binderKind,
          domain: transform(t.domain, depth),
          body: transform(t.body, depth + t.names.length),
          ...(t.named !== undefined ? { named: t.named } : {})
        };

      case 'Match':
        return {
          tag: 'Match',
          scrutinee: transform(t.scrutinee, depth),
          clauses: t.clauses.map(c => ({
            ...c,
            rhs: transform(c.rhs, depth + countClausePatternVars(c.patterns))
          }))
        };

      case 'Annot':
        return {
          tag: 'Annot',
          term: transform(t.term, depth),
          type: transform(t.type, depth)
        };

      // Leaf nodes that don't contain Vars
      case 'Const':
      case 'Sort':
      case 'Hole':
      case 'ULevel':
        return t;

      default:
        return t;
    }
  }

  return transform(term, 0);
}

/**
 * Count the number of variables bound by a list of patterns.
 */
function countClausePatternVars(patterns: TPattern[]): number {
  return patterns.reduce((acc, p) => acc + countPatternVars(p), 0);
}

// ============================================================================
// Pattern Reordering for Named Patterns
// ============================================================================

/**
 * Check if a pattern list has any named patterns.
 */
export function hasNamedPatterns(patterns: TPattern[]): boolean {
  return patterns.some(p =>
    (p.tag === 'PVar' && p.named) || (p.tag === 'PWild' && p.named)
  );
}

/**
 * Represents a pattern in the reordering process.
 */
type PatternArg =
  | { kind: 'positional'; pattern: TPattern }
  | { kind: 'named'; name: string; pattern: TPattern }
  | { kind: 'namedWildcard'; pattern: TPattern };  // {_} syntax - can fill any named position

/**
 * Collect pattern information for reordering.
 * - `{name}` patterns go to their specific named position
 * - `{_}` patterns (named wildcards) can fill any unfilled named position
 * - Other patterns are positional and can only fill non-named positions
 */
function collectPatternArgs(patterns: TPattern[]): PatternArg[] {
  return patterns.map(p => {
    if (p.tag === 'PVar' && p.named) {
      return { kind: 'named', name: p.name, pattern: p };
    } else if (p.tag === 'PWild' && p.named) {
      // Named wildcard {_} - can fill any named position
      return { kind: 'namedWildcard', pattern: p };
    } else {
      // Regular positional patterns - can only fill non-named positions
      return { kind: 'positional', pattern: p };
    }
  });
}

/**
 * Count pattern variables in a pattern (for de Bruijn index calculation).
 */
function countPatternVars(pattern: TPattern): number {
  switch (pattern.tag) {
    case 'PVar':
      return 1;
    case 'PWild':
      return 1;
    case 'PCtor':
      return pattern.args.reduce((sum, p) => sum + countPatternVars(p), 0);
  }
}

/**
 * Apply a permutation to de Bruijn indices in a surface term.
 * Only affects Var nodes within the permutation range (pattern variables).
 *
 * @param term - The term to transform
 * @param permutation - Maps old indices to new indices
 * @param depth - Current binding depth (for adjusting which indices to transform)
 */
export function applyVarPermutation(term: TTerm, permutation: number[], depth: number = 0): TTerm {
  switch (term.tag) {
    case 'Var': {
      // Only apply permutation to pattern variables (indices within the permutation range)
      // adjusted for current depth
      const adjustedIndex = term.index - depth;
      if (adjustedIndex >= 0 && adjustedIndex < permutation.length) {
        return { tag: 'Var', index: permutation[adjustedIndex] + depth };
      }
      return term;
    }

    case 'Const':
    case 'Sort':
    case 'ULevel':
    case 'ULit':
    case 'UOmega':
    case 'Hole':
    case 'AbsurdMarker':
    case 'WithClause':
      return term;

    case 'Binder':
      return {
        ...term,
        domain: term.domain ? applyVarPermutation(term.domain, permutation, depth) : undefined,
        body: applyVarPermutation(term.body, permutation, depth + 1)
      };

    case 'MultiBinder':
      return {
        ...term,
        domain: applyVarPermutation(term.domain, permutation, depth),
        body: applyVarPermutation(term.body, permutation, depth + term.names.length)
      };

    case 'App':
      return {
        ...term,
        fn: applyVarPermutation(term.fn, permutation, depth),
        arg: applyVarPermutation(term.arg, permutation, depth)
      };

    case 'Annot':
      return {
        ...term,
        term: applyVarPermutation(term.term, permutation, depth),
        type: applyVarPermutation(term.type, permutation, depth)
      };

    case 'Match':
      return {
        ...term,
        scrutinee: applyVarPermutation(term.scrutinee, permutation, depth),
        clauses: term.clauses.map(c => ({
          ...c,
          // Patterns bind new variables, so increase depth by the number of pattern vars
          rhs: applyVarPermutation(c.rhs, permutation, depth + c.patterns.reduce((sum, p) => sum + countPatternVars(p), 0))
        }))
      };

    case 'TacticBlock':
      return term;

    default: {
      const _never: never = term;
      throw new Error(`Unreachable code: ${_never}`);
    }
  }
}

/**
 * Reorder clause patterns, placing named patterns at their correct positions.
 * Also computes a permutation for de Bruijn index transformation.
 *
 * @param patterns - Mixed list of positional and named patterns
 * @param namedMap - Map from name to position index
 * @param clauseNamedPatterns - Optional clause-level named patterns from {name := pattern} syntax
 * @returns Ordered list of positional patterns and de Bruijn permutation, or error message
 *
 * The varIndexPermutation maps old de Bruijn indices to new ones.
 * This is needed because pattern reordering changes the binding order.
 */
export function reorderPatterns(
  patterns: TPattern[],
  namedMap: NamedArgMap,
  clauseNamedPatterns?: Array<{ name: string; pattern: TPattern }>,
  totalArity?: number
): { ordered: TPattern[]; varIndexPermutation: number[]; sourceIndexMap: (number | null)[]; error?: undefined } | { ordered?: undefined; varIndexPermutation?: undefined; sourceIndexMap?: undefined; error: string } {
  const args = collectPatternArgs(patterns);

  // Separate named, namedWildcard, and positional patterns
  const named: Array<{ name: string; pattern: TPattern; originalIndex: number }> = [];
  const namedWildcards: Array<{ pattern: TPattern; originalIndex: number }> = [];
  const positional: Array<{ pattern: TPattern; originalIndex: number }> = [];

  for (let i = 0; i < args.length; i++) {
    const arg = args[i];
    if (arg.kind === 'named') {
      named.push({ name: arg.name, pattern: arg.pattern, originalIndex: i });
    } else if (arg.kind === 'namedWildcard') {
      namedWildcards.push({ pattern: arg.pattern, originalIndex: i });
    } else {
      positional.push({ pattern: arg.pattern, originalIndex: i });
    }
  }

  // Add clause-level named patterns ({name := pattern} syntax)
  // These come after the positional patterns in the original order
  if (clauseNamedPatterns) {
    for (let i = 0; i < clauseNamedPatterns.length; i++) {
      const np = clauseNamedPatterns[i];
      named.push({ name: np.name, pattern: np.pattern, originalIndex: patterns.length + i });
    }
  }

  // Find indices for all explicitly named patterns
  const namedIndices: Array<{ idx: number; pattern: TPattern; originalIndex: number }> = [];
  for (const n of named) {
    const idx = namedMap.get(n.name);
    if (idx === undefined) {
      return { error: `Unknown named pattern: ${n.name}` };
    }
    namedIndices.push({ idx, pattern: n.pattern, originalIndex: n.originalIndex });
  }

  // Determine result size
  // If totalArity is provided, use it; otherwise estimate from patterns
  const maxNamedIdx = namedIndices.length > 0
    ? Math.max(...namedIndices.map(ni => ni.idx))
    : -1;

  // Result array - we fill named patterns at their positions, then fill positional in gaps
  // Also track the original index for permutation computation
  const estimatedSize = Math.max(maxNamedIdx + 1, positional.length + named.length + namedWildcards.length);
  const resultSize = totalArity !== undefined ? totalArity : estimatedSize;
  const result: ({ pattern: TPattern; originalIndex: number } | null)[] = new Array(resultSize).fill(null);

  // CRITICAL: Get set of all named parameter positions.
  // Positional patterns can ONLY fill non-named positions.
  const namedPositions = new Set(namedMap.values());

  // Place explicitly named patterns at their positions
  for (const ni of namedIndices) {
    if (result[ni.idx] !== null) {
      return { error: `Duplicate pattern at position ${ni.idx}` };
    }
    result[ni.idx] = { pattern: ni.pattern, originalIndex: ni.originalIndex };
  }

  // Fill named wildcards ({_}) in unfilled named positions (in order)
  let wildcardIdx = 0;
  for (const pos of Array.from(namedPositions).sort((a, b) => a - b)) {
    if (wildcardIdx >= namedWildcards.length) break;
    if (result[pos] === null) {
      result[pos] = namedWildcards[wildcardIdx++];
    }
  }

  // Check for leftover named wildcards
  if (wildcardIdx < namedWildcards.length) {
    return { error: `Too many named wildcard patterns ({_}): ${namedWildcards.length - wildcardIdx} extra wildcard(s)` };
  }

  // Fill positional patterns ONLY in non-named positions (from left to right)
  let posIdx = 0;
  for (let i = 0; i < result.length && posIdx < positional.length; i++) {
    // Skip this position if it's a named parameter position
    if (namedPositions.has(i)) {
      continue;
    }
    if (result[i] === null) {
      result[i] = positional[posIdx++];
    }
  }

  // Check if we have leftover positional patterns (they would have gone into named positions)
  if (posIdx < positional.length) {
    const extraCount = positional.length - posIdx;
    // Find which named params were not provided
    const providedNamedParams = new Set(named.map(n => n.name));
    const missingNamedParams: string[] = [];
    for (const [name] of namedMap) {
      if (!providedNamedParams.has(name)) {
        missingNamedParams.push(name);
      }
    }

    if (missingNamedParams.length > 0) {
      const missingList = missingNamedParams.map(n => `'${n}'`).join(', ');
      return {
        error: `Missing required named pattern${missingNamedParams.length > 1 ? 's' : ''}: ${missingList}. ` +
          `Named parameters must be provided with {name := pattern} syntax, not positionally.`
      };
    }

    return { error: `Too many positional patterns: ${extraCount} extra pattern(s) cannot fill named parameter positions` };
  }

  // Fill missing named parameters with wildcards (implicit patterns)
  // Named positions that are NOT filled get a synthetic wildcard
  let syntheticWildcardIndex = patterns.length + (clauseNamedPatterns?.length ?? 0);
  for (const [_name, pos] of namedMap) {
    if (result[pos] === null) {
      // Insert a wildcard pattern for the missing named parameter
      result[pos] = { pattern: { tag: 'PWild' }, originalIndex: syntheticWildcardIndex++ };
    }
  }

  // Check for unfilled gaps that precede filled positions
  let lastFilled = -1;
  for (let i = result.length - 1; i >= 0; i--) {
    if (result[i] !== null) {
      lastFilled = i;
      break;
    }
  }

  for (let i = 0; i < lastFilled; i++) {
    if (result[i] === null) {
      return { error: `Missing pattern at position ${i}` };
    }
  }

  // Trailing nulls are OK (partial patterns) - trim them
  const finalResult = result.slice(0, lastFilled + 1).filter((t): t is { pattern: TPattern; originalIndex: number } => t !== null);
  const ordered = finalResult.map(r => r.pattern);

  // Build source index map: for each position in `ordered`, what's the original source index?
  // null means the pattern was synthetic (inserted wildcard for implicit param)
  const sourceIndexMap = finalResult.map(r => r.originalIndex < patterns.length ? r.originalIndex : null);

  // Compute de Bruijn index permutation
  // Pattern variables are collected left-to-right, then reversed for the context
  // Index 0 is the innermost (rightmost pattern's last var)

  // Step 1: Count vars per pattern position in original order
  // Include both positional patterns and clause-level named patterns
  const origVarCounts = patterns.map(p => countPatternVars(p));
  if (clauseNamedPatterns) {
    for (const np of clauseNamedPatterns) {
      origVarCounts.push(countPatternVars(np.pattern));
    }
  }
  const totalVars = origVarCounts.reduce((a, b) => a + b, 0);

  // Step 2: For each original pattern position, compute the de Bruijn index range
  // Pattern vars are collected left-to-right, reversed, so:
  // - Last pattern's vars get indices 0, 1, ...
  // - First pattern's vars get highest indices
  const origPatternStartIndex: number[] = [];
  let idx = totalVars - 1;
  for (let i = 0; i < origVarCounts.length; i++) {
    origPatternStartIndex.push(idx - origVarCounts[i] + 1);
    idx -= origVarCounts[i];
  }

  // Step 3: For reordered patterns, compute new de Bruijn index range
  // NOTE: Use newTotalVars, not totalVars, because synthetic wildcards add new vars
  const newVarCounts = ordered.map(p => countPatternVars(p));
  const newTotalVars = newVarCounts.reduce((a, b) => a + b, 0);
  const newPatternStartIndex: number[] = [];
  idx = newTotalVars - 1;
  for (let i = 0; i < ordered.length; i++) {
    newPatternStartIndex.push(idx - newVarCounts[i] + 1);
    idx -= newVarCounts[i];
  }

  // Step 4: Build the permutation
  // varIndexPermutation[oldIndex] = newIndex
  const varIndexPermutation: number[] = new Array(totalVars);
  for (let newPos = 0; newPos < finalResult.length; newPos++) {
    const origPos = finalResult[newPos].originalIndex;
    const varCount = origVarCounts[origPos];
    for (let v = 0; v < varCount; v++) {
      const oldIdx = origPatternStartIndex[origPos] + v;
      const newIdx = newPatternStartIndex[newPos] + v;
      varIndexPermutation[oldIdx] = newIdx;
    }
  }

  return { ordered, varIndexPermutation, sourceIndexMap };
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
 * Global counter for generating unique implicit hole IDs during elaboration.
 * Unlike wildcardCounter, this is NEVER reset because holes from different
 * elaborations (e.g., function type vs RHS) may be unified during pattern
 * matching. If they share IDs, fillHole will incorrectly replace all of them.
 */
let globalImplicitHoleCounter = 0;

/**
 * Current constructor parameter info context.
 * Set when elaborating patterns inside a constructor pattern.
 */
let currentCtorParamNames: ParamInfo[] | null = null;

/**
 * Current position within constructor arguments.
 * Tracks which parameter we're at when elaborating sub-patterns.
 */
let currentCtorParamIndex: number = 0;

/**
 * Current term parameter info for top-level pattern elaboration.
 * Set from the term's type signature before elaborating its value.
 */
let currentTermParamNames: ParamInfo[] | null = null;

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
 * Set the current term parameter info for top-level pattern elaboration.
 * Call this before elaborating a term's value, using param info from its type.
 */
export function setCurrentTermParamNames(params: ParamInfo[] | null): void {
  currentTermParamNames = params;
  currentTermParamIndex = 0;
}

/**
 * Generate a fresh unique name for a wildcard pattern within the current clause.
 *
 * The naming priority is:
 * 1. If we have an explicit parameter name (e.g., "A" from "(A : Type)"), use it
 * 2. If we have a type prefix (lowercase first letter of type), use it
 * 3. Fall back to "?"
 *
 * The counter ensures uniqueness within the clause.
 */
function freshWildcardName(): string {
  const counter = wildcardCounter++;

  // If we have constructor context (nested inside a constructor pattern)
  if (currentCtorParamNames !== null && currentCtorParamIndex < currentCtorParamNames.length) {
    const paramInfo = currentCtorParamNames[currentCtorParamIndex];
    // Priority 1: explicit parameter name
    if (paramInfo.name !== '') {
      return `${paramInfo.name}${counter}`;
    }
    // Priority 2: type-based prefix
    if (paramInfo.typePrefix !== null) {
      return `${paramInfo.typePrefix}${counter}`;
    }
  }

  // If we have term context (top-level patterns)
  if (currentTermParamNames !== null && currentTermParamIndex < currentTermParamNames.length) {
    const paramInfo = currentTermParamNames[currentTermParamIndex];
    // Priority 1: explicit parameter name
    if (paramInfo.name !== '') {
      return `${paramInfo.name}${counter}`;
    }
    // Priority 2: type-based prefix
    if (paramInfo.typePrefix !== null) {
      return `${paramInfo.typePrefix}${counter}`;
    }
  }

  // No parameter name or type prefix available, use "?"
  return `?${counter}`;
}

/**
 * Reset the wildcard counter and other global elaboration state (useful for testing).
 */
export function resetWildcardCounter(): void {
  wildcardCounter = 0;
  globalImplicitHoleCounter = 0;
  currentCtorParamNames = null;
  currentCtorParamIndex = 0;
  currentTermParamNames = null;
  currentTermParamIndex = 0;
}

// ============================================================================
// Level Elaboration: TLevel → TTKTerm (Legacy - for backward compatibility)
// ============================================================================

/**
 * Elaborate a surface-level level expression (TLevel) to a kernel term.
 *
 * NOTE: With the new term-based level representation, this function is mostly
 * deprecated. Prefer using TTerm-based levels in surface syntax and regular
 * term elaboration. This function exists for backward compatibility with
 * code that still uses the old TLevel type.
 *
 * @deprecated Use TTerm-based levels instead
 * @param level - Surface level expression (TLevel)
 * @param levelNameToIndex - Map from level variable names to de Bruijn indices
 * @returns Kernel level term (TTKTerm)
 */
export function elabLevelToKernel(level: TLevel, levelNameToIndex?: Map<string, number>): TTKTerm {
  switch (level.tag) {
    case 'LNum':
      return mkULit(level.n);
    case 'LName':
      // Level variable - look up de Bruijn index
      if (levelNameToIndex) {
        const index = levelNameToIndex.get(level.name);
        if (index !== undefined) {
          return mkVar(index);
        }
      }
      // If no index found, this is an error (undefined level variable)
      throw new Error(`Undefined level variable '${level.name}'`);
    case 'LSucc':
      return mkLSucc(elabLevelToKernel(level.pred, levelNameToIndex));
    case 'LMax':
      return mkLMax(elabLevelToKernel(level.left, levelNameToIndex), elabLevelToKernel(level.right, levelNameToIndex));
    case 'LIMax':
      return mkLIMax(elabLevelToKernel(level.left, levelNameToIndex), elabLevelToKernel(level.right, levelNameToIndex));
    case 'LOmega':
      return mkUOmega();
  }
}

// ============================================================================
// Term Elaboration: TT → TTK
// ============================================================================

/**
 * Reserved level operation names that are valid in level contexts.
 * These are built-in operations, not user-defined level variables.
 */
const RESERVED_LEVEL_OPS = new Set(['USucc', 'UMax', 'UIMax']);

/**
 * Validate that all Const nodes in a level term are valid level names in scope.
 * Throws NamedArgElabError if an undefined level variable is found.
 *
 * @param level - The elaborated level term to validate
 * @param levelNamesInScope - Set of valid level variable names
 * @param surfacePath - Path for error reporting (tracks position in the term)
 */
function validateLevelTerm(
  level: TTKTerm,
  levelNamesInScope: Set<string>,
  surfacePath: IndexPath
): void {
  switch (level.tag) {
    case 'Const':
      // Check if this is a valid level name in scope or a reserved level operation
      if (!levelNamesInScope.has(level.name) && !RESERVED_LEVEL_OPS.has(level.name)) {
        throw new NamedArgElabError(`Undefined level variable '${level.name}'`, surfacePath);
      }
      break;
    case 'App':
      // Recursively validate function and argument, tracking the path
      validateLevelTerm(level.fn, levelNamesInScope, appendPath(surfacePath, fieldSeg('fn')));
      validateLevelTerm(level.arg, levelNamesInScope, appendPath(surfacePath, fieldSeg('arg')));
      break;
    case 'ULit':
    case 'ULevel':
    case 'UOmega':
    case 'Var':
      // These are valid level terms
      break;
    default:
      // Other term types in a level are unusual but we don't error here
      break;
  }
}

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
  return elabToKernelWithScope(term, new Set());
}

/**
 * Internal helper that tracks level names in scope.
 * When a binder has domain ULevel, its name becomes a valid level name in the body.
 */
function elabToKernelWithScope(term: TTerm, levelNamesInScope: Set<string>): TTKTerm {
  switch (term.tag) {
    case 'Var':
      return { tag: 'Var', index: term.index };

    case 'Sort':
      // Level is now a term, elaborate it recursively
      return { tag: 'Sort', level: elabToKernelWithScope(term.level, levelNamesInScope) };

    case 'ULevel':
      return { tag: 'ULevel' };

    case 'ULit':
      return { tag: 'ULit', n: term.n };

    case 'UOmega':
      return { tag: 'UOmega' };

    case 'AbsurdMarker':
      // AbsurdMarker should only appear as clause RHS and is filtered out at the Match level
      throw new Error('AbsurdMarker should not be elaborated directly - it should be filtered at the clause level');

    case 'WithClause':
      // WithClause should be desugared to auxiliary functions before elaboration
      throw new Error('WithClause should be desugared before elaboration');

    case 'Const':
      return {
        tag: 'Const',
        name: term.name,
      };

    case 'Binder': {
      let binderKind: TTKBinderKind;
      let domain: TTKTerm;

      switch (term.binderKind.tag) {
        case 'BPiTT':
          binderKind = { tag: 'BPi' };
          // Pi binders must have a domain
          domain = elabToKernelWithScope(term.domain!, levelNamesInScope);
          break;
        case 'BLamTT':
          binderKind = { tag: 'BLam' };
          // Lambda binders must have a domain
          domain = elabToKernelWithScope(term.domain!, levelNamesInScope);
          break;
        case 'BLetTT':
          binderKind = { tag: 'BLet', defVal: elabToKernelWithScope(term.binderKind.defVal, levelNamesInScope) };
          // Let binders may have an implicit type (domain undefined in surface)
          // In this case, create a fresh meta for type inference
          domain = term.domain !== undefined
            ? elabToKernelWithScope(term.domain, levelNamesInScope)
            : freshImplicitLetTypeHole(term.name);
          break;
      }

      // If the domain is ULevel, the binder name becomes a valid level name in the body
      const bodyScope = domain.tag === 'ULevel'
        ? new Set([...levelNamesInScope, term.name])
        : levelNamesInScope;

      const body = elabToKernelWithScope(term.body, bodyScope);

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
        fn: elabToKernelWithScope(term.fn, levelNamesInScope),
        arg: elabToKernelWithScope(term.arg, levelNamesInScope)
      };

    case 'Hole':
      // Kernel holes are simple - type/context info from surface is discarded
      // Type checking will instantiate metas as needed
      return { tag: 'Hole', id: term.id };

    case 'Annot':
      return {
        tag: 'Annot',
        term: elabToKernelWithScope(term.term, levelNamesInScope),
        type: elabToKernelWithScope(term.type, levelNamesInScope)
      };

    case 'Match':
      // Filter out #absurd clauses - they are dropped during elaboration
      // and validated separately during type checking
      return {
        tag: 'Match',
        scrutinee: elabToKernelWithScope(term.scrutinee, levelNamesInScope),
        clauses: term.clauses
          .filter(c => c.rhs.tag !== 'AbsurdMarker')
          .map(c => {
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
              rhs: elabToKernelWithScope(c.rhs, levelNamesInScope)
            };
          })
      };

    case 'MultiBinder': {
      // Expand MultiBinder into nested single Binder terms
      // (a b c : T) -> B  becomes  (a : T) -> (b : T) -> (c : T) -> B
      //
      // IMPORTANT: The domain expression's de Bruijn indices refer to the context
      // BEFORE any of the MultiBinder's names are introduced. When we create
      // nested binders, each binder at position i has i binders above it,
      // so the domain needs to be shifted by i.
      const baseDomain = elabToKernelWithScope(term.domain, levelNamesInScope);

      // If the domain is ULevel, all names become valid level names in the body
      const bodyScope = baseDomain.tag === 'ULevel'
        ? new Set([...levelNamesInScope, ...term.names])
        : levelNamesInScope;

      let body = elabToKernelWithScope(term.body, bodyScope);

      // Convert surface binder kind to kernel binder kind
      let binderKindFactory: () => TTKBinderKind;
      if (term.binderKind.tag === 'BPiTT') {
        binderKindFactory = () => ({ tag: 'BPi' });
      } else if (term.binderKind.tag === 'BLamTT') {
        binderKindFactory = () => ({ tag: 'BLam' });
      } else {
        // BLetTT - MultiBinder with BLet doesn't really make sense semantically
        // but we handle it anyway
        const letDefVal = elabToKernelWithScope(term.binderKind.defVal, levelNamesInScope);
        binderKindFactory = () => ({
          tag: 'BLet',
          defVal: letDefVal
        });
      }

      // Build nested binders from inside out (reverse order)
      for (let i = term.names.length - 1; i >= 0; i--) {
        // Shift the domain by i to account for the i binders above position i
        const shiftedDomain = i > 0 ? shiftTerm(baseDomain, i, 0) : baseDomain;
        body = {
          tag: 'Binder',
          name: term.names[i],
          binderKind: binderKindFactory(),
          domain: shiftedDomain,
          body
        };
      }

      return body;
    }

    case 'TacticBlock':
      throw new Error('TacticBlock should be elaborated to a kernel term before reaching elabToKernel');

    default: {
      const _never: never = term;
      throw new Error(`Unreachable code: ${_never}`);
    }
  }
}

/**
 * Elaborate a surface term (TT) to a kernel term (TTK) with named argument resolution.
 *
 * This version handles named arguments in applications by:
 * 1. Collecting the entire app spine when named args are present
 * 2. Looking up the function's named arg map
 * 3. Reordering arguments to their correct positions
 *
 * @param term - Surface term (TT)
 * @param lookup - Function to look up named arg maps for definitions
 * @returns Kernel term (TTK) with named args resolved to positional
 * @throws NamedArgElabError if named arg resolution fails
 */
export function elabToKernelWithNamedArgs(term: TTerm, lookup: NamedArgInfoLookup): TTKTerm {
  // Helper to recursively elaborate with named arg support
  function elab(t: TTerm): TTKTerm {
    switch (t.tag) {
      case 'Var':
        return { tag: 'Var', index: t.index };

      case 'Sort':
        // Level is now a term, elaborate it recursively
        return { tag: 'Sort', level: elab(t.level) };

      case 'ULevel':
        return { tag: 'ULevel' };

      case 'ULit':
        return { tag: 'ULit', n: t.n };

      case 'UOmega':
        return { tag: 'UOmega' };

      case 'AbsurdMarker':
        throw new Error('AbsurdMarker should not be elaborated directly');

      case 'WithClause':
        throw new Error('WithClause should be desugared before elaboration');

      case 'Const':
        return { tag: 'Const', name: t.name };

      case 'Binder': {
        const body = elab(t.body);
        let binderKind: TTKBinderKind;
        let domain: TTKTerm;

        switch (t.binderKind.tag) {
          case 'BPiTT':
            binderKind = { tag: 'BPi' };
            domain = elab(t.domain!);
            break;
          case 'BLamTT':
            binderKind = { tag: 'BLam' };
            domain = elab(t.domain!);
            break;
          case 'BLetTT':
            binderKind = { tag: 'BLet', defVal: elab(t.binderKind.defVal) };
            domain = t.domain !== undefined
              ? elab(t.domain)
              : freshImplicitLetTypeHole(t.name);
            break;
        }

        return {
          tag: 'Binder',
          name: t.name,
          binderKind,
          domain,
          body
        };
      }

      case 'App': {
        // Collect the entire spine to check for named arguments
        const { head, args } = collectAppSpine(t);
        const hasNamed = hasNamedArgs(t);

        // Try to get the named arg info for the function
        let namedMap: NamedArgMap | undefined;
        let totalArity: number | undefined;
        if (head.tag === 'Const') {
          const info = lookup(head.name);
          if (info) {
            namedMap = info.namedArgMap;
            totalArity = info.totalArity;
          }
        }

        // If the application has named args, the function MUST have a named arg map
        if (hasNamed && (!namedMap || namedMap.size === 0)) {
          const funcName = head.tag === 'Const' ? head.name : '<expression>';
          throw new NamedArgElabError(
            `Cannot use named arguments: '${funcName}' has no named parameters`
          );
        }

        // If the application uses named arguments and the function has named parameters,
        // reorder and validate. Only enter this path when hasNamed is true — otherwise
        // positional-only applications (e.g., MkPair a (\(x : T) => body)) should not
        // be subject to named-argument position validation.
        if (hasNamed && namedMap && namedMap.size > 0) {
          // Reorder and validate arguments
          const reorderResult = reorderArgs(args, namedMap, totalArity);
          if ('error' in reorderResult && reorderResult.error !== undefined) {
            throw new NamedArgElabError(reorderResult.error);
          }

          // Build the elaborated application spine
          const orderedArgs = reorderResult.ordered!;
          let result = elab(head);
          for (const arg of orderedArgs) {
            result = {
              tag: 'App',
              fn: result,
              arg: elab(arg)
            };
          }
          return result;
        }

        // No named params on function - simple elaboration
        return {
          tag: 'App',
          fn: elab(t.fn),
          arg: elab(t.arg)
        };
      }

      case 'Hole':
        return { tag: 'Hole', id: t.id };

      case 'Annot':
        return {
          tag: 'Annot',
          term: elab(t.term),
          type: elab(t.type)
        };

      case 'Match':
        return {
          tag: 'Match',
          scrutinee: elab(t.scrutinee),
          clauses: t.clauses
            .filter(c => c.rhs.tag !== 'AbsurdMarker')
            .map(c => {
              wildcardCounter = 0;
              currentTermParamIndex = 0;
              return {
                patterns: c.patterns.map(p => {
                  const result = elabPatternToKernel(p);
                  currentTermParamIndex++;
                  return result;
                }),
                rhs: elab(c.rhs)
              };
            })
        };

      case 'MultiBinder': {
        // Expand MultiBinder into nested single Binder terms
        // (a b c : T) -> B  becomes  (a : T) -> (b : T') -> (c : T'') -> B
        // where T' = shift(T, 1), T'' = shift(T, 2), etc.
        const baseDomain = elab(t.domain);
        let body = elab(t.body);

        let binderKindFactory: () => TTKBinderKind;
        if (t.binderKind.tag === 'BPiTT') {
          binderKindFactory = () => ({ tag: 'BPi' });
        } else if (t.binderKind.tag === 'BLamTT') {
          binderKindFactory = () => ({ tag: 'BLam' });
        } else {
          const letDefVal = elab(t.binderKind.defVal);
          binderKindFactory = () => ({
            tag: 'BLet',
            defVal: letDefVal
          });
        }

        for (let i = t.names.length - 1; i >= 0; i--) {
          // Shift the domain by i to account for the i binders above position i
          const shiftedDomain = i > 0 ? shiftTerm(baseDomain, i, 0) : baseDomain;
          body = {
            tag: 'Binder',
            name: t.names[i],
            binderKind: binderKindFactory(),
            domain: shiftedDomain,
            body
          };
        }

        return body;
      }

      case 'TacticBlock':
        throw new Error('TacticBlock should be elaborated to a kernel term before reaching elabToKernelWithNamedArgs');

      default: {
        const _never: never = t;
        throw new Error(`Unreachable code: ${_never}`);
      }
    }
  }

  return elab(term);
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

      // Elaborate each positional argument with the appropriate parameter context
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

      // Elaborate named args if present (reordering happens in pattern checker)
      let elabNamedArgs: Array<{ name: string; pattern: TTKPattern }> | undefined;
      if (pattern.namedArgs && pattern.namedArgs.length > 0) {
        elabNamedArgs = pattern.namedArgs.map(na => ({
          name: na.name,
          pattern: elabPatternToKernel(na.pattern)
        }));
      }

      return {
        tag: 'PCtor',
        name: pattern.name,
        args: elabArgs,
        namedArgs: elabNamedArgs
      };
    }
  }
}

/**
 * Elaborate a surface context to kernel context.
 */
export function elabContextToKernel(ctx: TContext): TTKContext {
  return ctx.map((binding) => ({
    name: binding.name,
    type: elabToKernel(binding.type)
  }));
}

/**
 * Elaborate a surface binding to kernel binding.
 */
export function elabBindingToKernel(binding: TBinding): TTKContext[number] {
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
 * @param patternNamedArgMap - Optional map for reordering named patterns in Match clauses
 * @param appNamedArgLookup - Optional lookup for named arg maps of functions (for named arg applications)
 * @param patternTotalArity - Optional total arity for validating clause pattern count
 * @returns The elaborated kernel term
 */
export function elabToKernelWithMap(
  term: TTerm,
  elabMap: ElabMap,
  surfacePath: IndexPath = [],
  kernelPath: IndexPath = [],
  patternNamedArgMap?: NamedArgMap,
  appNamedArgLookup?: NamedArgInfoLookup,
  patternTotalArity?: number,
  levelNamesInScope: Set<string> = new Set()
): TTKTerm {
  // Record the correspondence between kernel and surface paths
  const kernelKey = serializeIndexPath(kernelPath);
  const surfaceKey = serializeIndexPath(surfacePath);
  elabMap.set(kernelKey, surfaceKey);

  // Recursively elaborate with path tracking
  switch (term.tag) {
    case 'Var':
      return { tag: 'Var', index: term.index };

    case 'Sort': {
      // Level is now a term - recursively elaborate it
      const levelSurfacePath = appendPath(surfacePath, fieldSeg('level'));
      const elaboratedLevel = elabToKernelWithMap(
        term.level,
        elabMap,
        levelSurfacePath,
        appendPath(kernelPath, fieldSeg('level')),
        patternNamedArgMap,
        appNamedArgLookup,
        patternTotalArity,
        levelNamesInScope
      );
      // Validate that any Const in the level is a valid level name in scope
      validateLevelTerm(elaboratedLevel, levelNamesInScope, levelSurfacePath);
      return { tag: 'Sort', level: elaboratedLevel };
    }

    case 'ULevel':
      return { tag: 'ULevel' };

    case 'ULit':
      return { tag: 'ULit', n: term.n };

    case 'UOmega':
      return { tag: 'UOmega' };

    case 'AbsurdMarker':
      // AbsurdMarker should only appear as clause RHS and is filtered out at the Match level
      throw new Error('AbsurdMarker should not be elaborated directly - it should be filtered at the clause level');

    case 'WithClause':
      // WithClause should be desugared to auxiliary functions before elaboration
      throw new Error('WithClause should be desugared before elaboration');

    case 'Const':
      return {
        tag: 'Const',
        name: term.name,
      };

    case 'Binder': {
      let binderKind: TTKBinderKind;
      let domain: TTKTerm;

      // Elaborate domain FIRST so we can check if it's ULevel
      switch (term.binderKind.tag) {
        case 'BPiTT':
          binderKind = { tag: 'BPi' };
          // Pi binders must have a domain
          domain = elabToKernelWithMap(
            term.domain!,
            elabMap,
            appendPath(surfacePath, fieldSeg('domain')),
            appendPath(kernelPath, fieldSeg('domain')),
            patternNamedArgMap,
            appNamedArgLookup,
            undefined,
            levelNamesInScope
          );
          break;
        case 'BLamTT':
          binderKind = { tag: 'BLam' };
          // Lambda binders must have a domain
          domain = elabToKernelWithMap(
            term.domain!,
            elabMap,
            appendPath(surfacePath, fieldSeg('domain')),
            appendPath(kernelPath, fieldSeg('domain')),
            patternNamedArgMap,
            appNamedArgLookup,
            undefined,
            levelNamesInScope
          );
          break;
        case 'BLetTT':
          binderKind = {
            tag: 'BLet',
            defVal: elabToKernelWithMap(
              term.binderKind.defVal,
              elabMap,
              appendPath(surfacePath, fieldSeg('binderKind'), fieldSeg('defVal')),
              appendPath(kernelPath, fieldSeg('binderKind'), fieldSeg('defVal')),
              patternNamedArgMap,
              appNamedArgLookup,
              undefined,
              levelNamesInScope
            )
          };
          // Let binders may have an implicit type (domain undefined in surface)
          domain = term.domain !== undefined
            ? elabToKernelWithMap(
              term.domain,
              elabMap,
              appendPath(surfacePath, fieldSeg('domain')),
              appendPath(kernelPath, fieldSeg('domain')),
              patternNamedArgMap,
              appNamedArgLookup,
              undefined,
              levelNamesInScope
            )
            : freshImplicitLetTypeHole(term.name);
          break;
      }

      // If the domain is ULevel, the binder name becomes a valid level name in the body
      const bodyScope = domain.tag === 'ULevel'
        ? new Set([...levelNamesInScope, term.name])
        : levelNamesInScope;

      const body = elabToKernelWithMap(
        term.body,
        elabMap,
        appendPath(surfacePath, fieldSeg('body')),
        appendPath(kernelPath, fieldSeg('body')),
        patternNamedArgMap,
        appNamedArgLookup,
        undefined,
        bodyScope
      );

      return {
        tag: 'Binder',
        name: term.name,
        binderKind,
        domain,
        body
      };
    }

    case 'App': {
      // Collect the entire spine to check for named arguments
      const { head, args } = collectAppSpine(term);
      const hasNamed = hasNamedArgs(term);

      // Try to get the named arg info for the function
      let namedArgInfo: NamedArgInfo | undefined;
      if (appNamedArgLookup && head.tag === 'Const') {
        namedArgInfo = appNamedArgLookup(head.name);
      }
      const namedMap = namedArgInfo?.namedArgMap;
      const totalArity = namedArgInfo?.totalArity;

      // If the application has named args, the function MUST have a named arg map
      if (hasNamed && (!namedMap || namedMap.size === 0)) {
        const funcName = head.tag === 'Const' ? head.name : '<expression>';
        throw new NamedArgElabError(
          `Cannot use named arguments: '${funcName}' has no named parameters`,
          surfacePath
        );
      }

      // If the function has named parameters, we MUST validate that positional
      // arguments don't overflow into named parameter positions
      if (namedMap && namedMap.size > 0) {
        // Reorder and validate arguments, passing totalArity for proper sizing
        const reorderResult = reorderArgs(args, namedMap, totalArity);
        if ('error' in reorderResult && reorderResult.error !== undefined) {
          throw new NamedArgElabError(reorderResult.error, surfacePath);
        }

        // Build the elaborated application spine
        const orderedArgs = reorderResult.ordered!;
        let result = elabToKernelWithMap(head, elabMap, surfacePath, kernelPath, patternNamedArgMap, appNamedArgLookup);
        for (const arg of orderedArgs) {
          result = {
            tag: 'App',
            fn: result,
            arg: elabToKernelWithMap(arg, elabMap, surfacePath, kernelPath, patternNamedArgMap, appNamedArgLookup)
          };
        }
        return result;
      }

      // No named params on function - simple elaboration
      return {
        tag: 'App',
        fn: elabToKernelWithMap(
          term.fn,
          elabMap,
          appendPath(surfacePath, fieldSeg('fn')),
          appendPath(kernelPath, fieldSeg('fn')),
          patternNamedArgMap,
          appNamedArgLookup
        ),
        arg: elabToKernelWithMap(
          term.arg,
          elabMap,
          appendPath(surfacePath, fieldSeg('arg')),
          appendPath(kernelPath, fieldSeg('arg')),
          patternNamedArgMap,
          appNamedArgLookup
        )
      };
    }

    case 'Hole':
      // Kernel holes are simple - type/context info from surface is discarded
      return { tag: 'Hole', id: term.id };

    case 'Annot':
      return {
        tag: 'Annot',
        term: elabToKernelWithMap(
          term.term,
          elabMap,
          appendPath(surfacePath, fieldSeg('term')),
          appendPath(kernelPath, fieldSeg('term')),
          patternNamedArgMap,
          appNamedArgLookup
        ),
        type: elabToKernelWithMap(
          term.type,
          elabMap,
          appendPath(surfacePath, fieldSeg('type')),
          appendPath(kernelPath, fieldSeg('type')),
          patternNamedArgMap,
          appNamedArgLookup
        )
      };

    case 'Match': {
      // Filter out #absurd clauses - they are dropped during elaboration
      // and validated separately during type checking
      const nonAbsurdClauses = term.clauses
        .map((clause, surfaceIndex) => ({ clause, surfaceIndex }))
        .filter(({ clause }) => clause.rhs.tag !== 'AbsurdMarker');

      return {
        tag: 'Match',
        scrutinee: elabToKernelWithMap(
          term.scrutinee,
          elabMap,
          appendPath(surfacePath, fieldSeg('scrutinee')),
          appendPath(kernelPath, fieldSeg('scrutinee')),
          patternNamedArgMap,
          appNamedArgLookup
        ),
        clauses: nonAbsurdClauses.map(({ clause, surfaceIndex }, kernelIndex) => {
          const clauseSurfacePath = appendPath(surfacePath, fieldSeg('clauses'), arraySeg(surfaceIndex));
          const clauseKernelPath = appendPath(kernelPath, fieldSeg('clauses'), arraySeg(kernelIndex));

          // Record the clause mapping
          elabMap.set(serializeIndexPath(clauseKernelPath), serializeIndexPath(clauseSurfacePath));

          // Reset wildcard counter for each clause so _w0 is the first wildcard in each clause
          wildcardCounter = 0;
          // Reset term param index for each clause
          currentTermParamIndex = 0;

          // Validate clause pattern count against function arity
          // If the function has named parameters, we need to validate that
          // the user isn't providing too many positional patterns
          const hasClauseNamedPatterns = clause.namedPatterns && clause.namedPatterns.length > 0;
          if (patternNamedArgMap && patternNamedArgMap.size > 0 && patternTotalArity !== undefined) {
            const positionalArity = patternTotalArity - patternNamedArgMap.size;
            // Count positional patterns (patterns without `named: true` flag)
            const positionalPatternCount = clause.patterns.filter(p => !(p.tag === 'PVar' && p.named) && !(p.tag === 'PWild' && p.named)).length;

            if (positionalPatternCount > positionalArity) {
              const namedNames = Array.from(patternNamedArgMap.keys()).join(', ');
              throw new NamedArgElabError(
                `Too many positional patterns: expected at most ${positionalArity} but got ${positionalPatternCount}. ` +
                `The function has ${patternNamedArgMap.size} named parameter${patternNamedArgMap.size === 1 ? '' : 's'} (${namedNames}) ` +
                `that must be matched with {name := pattern} syntax or omitted.`,
                clauseSurfacePath
              );
            }
          }

          // Reorder and validate patterns if we have a namedArgMap
          // This is needed to:
          // 1. Reorder patterns when using {name} or {name := pattern} syntax
          // 2. Validate that required named parameters are provided
          // We call this whenever the TYPE has named params, even if the clause doesn't provide any
          let patternsToElab = clause.patterns;
          let rhsToElab = clause.rhs;
          if (patternNamedArgMap && patternNamedArgMap.size > 0) {
            const reorderResult = reorderPatterns(clause.patterns, patternNamedArgMap, clause.namedPatterns, patternTotalArity);
            if ('error' in reorderResult && reorderResult.error !== undefined) {
              throw new NamedArgElabError(reorderResult.error, clauseSurfacePath);
            }
            patternsToElab = reorderResult.ordered!;
            // Apply the permutation to de Bruijn indices in the RHS
            // (no-op if no reordering happened)
            if (hasNamedPatterns(clause.patterns) || hasClauseNamedPatterns) {
              rhsToElab = applyVarPermutation(clause.rhs, reorderResult.varIndexPermutation!);
            }
          }

          return {
            patterns: patternsToElab.map((pattern, patternIndex) => {
              const patternSurfacePath = appendPath(clauseSurfacePath, fieldSeg('patterns'), arraySeg(patternIndex));
              const patternKernelPath = appendPath(clauseKernelPath, fieldSeg('patterns'), arraySeg(patternIndex));
              const result = elabPatternToKernelWithMap(pattern, elabMap, patternSurfacePath, patternKernelPath);
              // Increment term param index after each top-level pattern
              currentTermParamIndex++;
              return result;
            }),
            rhs: elabToKernelWithMap(
              rhsToElab,
              elabMap,
              appendPath(clauseSurfacePath, fieldSeg('rhs')),
              appendPath(clauseKernelPath, fieldSeg('rhs')),
              patternNamedArgMap,
              appNamedArgLookup
            )
          };
        })
      };
    }

    case 'MultiBinder': {
      // Expand MultiBinder into nested single Binder terms
      // (a b c : T) -> B  becomes  (a : T) -> (b : T') -> (c : T'') -> B
      // where T' = shift(T, 1), T'' = shift(T, 2), etc.
      //
      // The domain T is in the context BEFORE any of the MultiBinder's names.
      // When we create nested binders, binder at position i has i binders above it,
      // so the domain needs to be shifted by i.
      //
      // For path tracking, the domain maps to the first binder's domain
      // and the body maps to the innermost binder's body
      const baseDomain = elabToKernelWithMap(
        term.domain,
        elabMap,
        appendPath(surfacePath, fieldSeg('domain')),
        appendPath(kernelPath, fieldSeg('domain')),
        patternNamedArgMap,
        appNamedArgLookup
      );

      // Build the path to the innermost body - it will be nested under n-1 'body' segments
      let innerBodyKernelPath = kernelPath;
      for (let i = 0; i < term.names.length; i++) {
        innerBodyKernelPath = appendPath(innerBodyKernelPath, fieldSeg('body'));
      }

      let body = elabToKernelWithMap(
        term.body,
        elabMap,
        appendPath(surfacePath, fieldSeg('body')),
        innerBodyKernelPath,
        patternNamedArgMap,
        appNamedArgLookup
      );

      // Convert surface binder kind to kernel binder kind
      let binderKindFactory: () => TTKBinderKind;
      if (term.binderKind.tag === 'BPiTT') {
        binderKindFactory = () => ({ tag: 'BPi' });
      } else if (term.binderKind.tag === 'BLamTT') {
        binderKindFactory = () => ({ tag: 'BLam' });
      } else {
        // BLetTT
        const letDefVal = elabToKernel(term.binderKind.defVal);
        binderKindFactory = () => ({
          tag: 'BLet',
          defVal: letDefVal
        });
      }

      // Build nested binders from inside out (reverse order)
      for (let i = term.names.length - 1; i >= 0; i--) {
        // Shift the domain by i to account for the i binders above position i
        const shiftedDomain = i > 0 ? shiftTerm(baseDomain, i, 0) : baseDomain;
        body = {
          tag: 'Binder',
          name: term.names[i],
          binderKind: binderKindFactory(),
          domain: shiftedDomain,
          body
        };
      }

      return body;
    }

    case 'TacticBlock':
      throw new Error('TacticBlock should be elaborated to a kernel term before reaching elabToKernelWithMap');

    default: {
      const _never: never = term;
      throw new Error(`Unreachable code: ${_never}`);
    }
  }
}

/**
 * Elaborate a surface pattern (TPattern) to a kernel pattern (TTKPattern)
 * while tracking path correspondence in the elabMap.
 */
export function elabPatternToKernelWithMap(
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

      // Elaborate each positional argument with the appropriate parameter context
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

      // Elaborate named args if present (reordering happens in pattern checker)
      let elabNamedArgs: Array<{ name: string; pattern: TTKPattern }> | undefined;
      if (pattern.namedArgs && pattern.namedArgs.length > 0) {
        elabNamedArgs = pattern.namedArgs.map((na, naIndex) => {
          const naSurfacePath = appendPath(surfacePath, fieldSeg('namedArgs'), arraySeg(naIndex));
          const naKernelPath = appendPath(kernelPath, fieldSeg('namedArgs'), arraySeg(naIndex));
          return {
            name: na.name,
            pattern: elabPatternToKernelWithMap(na.pattern, elabMap, naSurfacePath, naKernelPath)
          };
        });
      }

      return {
        tag: 'PCtor',
        name: pattern.name,
        args: elabArgs,
        namedArgs: elabNamedArgs
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
    type: elabToKernel(field.type),
    implicit: field.implicit,
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
 * Get the default constructor name for a record.
 * Uses Mk${name} following standard conventions (like Lean's MkPoint, MkPair, etc.)
 */
export function defaultRecordConstructorName(recordName: string): string {
  return `Mk${recordName}`;
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
    constructorName: record.constructorName ?? defaultRecordConstructorName(record.name),
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
