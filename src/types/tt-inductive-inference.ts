/**
 * Parameter/Index Inference for Inductive Families
 *
 * This module implements an algorithm for classifying arguments to inductive type families
 * as either parameters (fixed across all constructors) or indices (varying across constructors).
 *
 * ## What are Parameters vs Indices?
 *
 * In an inductive type like `Vec : Type -> Nat -> Type`:
 * - **Parameters** are arguments that are uniform across all constructors (e.g., the element type)
 * - **Indices** are arguments that vary between constructors (e.g., the length)
 *
 * This distinction is important for generating strong eliminators (induction principles).
 * For example, equality can be given a J eliminator instead of a weaker 2-index eliminator.
 *
 * ## The Algorithm
 *
 * The algorithm has three phases:
 * 1. **Syntactic parameter detection**: Find positions that pass through a unique variable
 * 2. **Index promotion**: Detect indices that are always equal and promote one per equivalence class
 * 3. **Dependency validation**: Ensure parameters form a prefix (no parameter depends on an index)
 *
 * ## Examples
 *
 * ```
 * Vec : Type -> Nat -> Type
 *   nil  : (A : Type) -> Vec A 0
 *   cons : (A : Type) -> (n : Nat) -> A -> Vec A n -> Vec A (succ n)
 * Result: [1] (Type is param at position 0, Nat is index at position 1)
 *
 * Eq : (A : Type) -> A -> A -> Type
 *   refl : (A : Type) -> (x : A) -> Eq A x x
 * Result: [2] (A and x are params, last A is index - this gives J eliminator!)
 *
 * Fin : Nat -> Type
 *   fzero : (n : Nat) -> Fin (succ n)
 *   fsucc : (n : Nat) -> Fin n -> Fin (succ n)
 * Result: [0] (Nat is index because constructors use complex terms like 'succ n')
 * ```
 *
 * See docs/parameter-index-inference.md for the full specification.
 */

import { TTerm } from './tt-core';
import { InductiveTypeDef } from './tt-examples';

/**
 * Result of parameter/index inference.
 * Contains the indices of positions that are type indices (not parameters).
 * Parameters are all positions NOT in this set, and they form a prefix.
 *
 * Example: [2] means position 2 is an index, positions 0 and 1 are parameters.
 */
export type IndexPositions = number[];

/**
 * Infer which positions in an inductive type definition are indices vs parameters.
 *
 * @param def - The inductive type definition
 * @returns Array of position indices that are type indices (all other positions are parameters)
 *
 * @example
 * // For Vec : Type -> Nat -> Type
 * // Returns [1] - position 0 (Type) is parameter, position 1 (Nat) is index
 * inferParameterIndices(vecDef)
 *
 * @example
 * // For Eq : (A : Type) -> A -> A -> Type (with refl)
 * // Returns [2] - positions 0,1 are parameters, position 2 is index
 * inferParameterIndices(eqDef)
 */
export function inferParameterIndices(def: InductiveTypeDef): IndexPositions {
  // First, count how many arguments the type takes
  const numPositions = countPiArgs(def.type);

  if (numPositions === 0) {
    return []; // No arguments means no indices
  }

  // Phase 1: Syntactic parameter detection
  const syntacticParams = detectSyntacticParameters(def, numPositions);

  // Phase 2: Index promotion (equivalence classes)
  const afterPromotion = promoteIndices(def, numPositions, syntacticParams);

  // Phase 2.5: Dependency validation (enforce prefix property)
  const finalIndices = enforceParameterPrefix(afterPromotion, numPositions);

  return finalIndices;
}

// ============================================================================
// Phase 1: Syntactic Parameter Detection
// ============================================================================

/**
 * Detect positions that are syntactic parameters.
 * A position is a syntactic parameter if in every constructor:
 * - The term at that position is a single variable
 * - That variable is bound in the constructor's telescope
 * - That variable appears exactly once across all positions
 */
function detectSyntacticParameters(
  def: InductiveTypeDef,
  numPositions: number
): Set<number> {
  const params = new Set<number>();

  for (let pos = 0; pos < numPositions; pos++) {
    if (isSyntacticParameter(def, pos, numPositions)) {
      params.add(pos);
    }
  }

  return params;
}

/**
 * Check if a specific position is a syntactic parameter.
 */
function isSyntacticParameter(
  def: InductiveTypeDef,
  position: number,
  numPositions: number
): boolean {
  // Check all constructors
  for (const ctor of def.constructors) {
    // Extract the arguments to the inductive type in the constructor's return type
    const ctorArgs = extractInductiveArgs(ctor.type, def.name, numPositions);

    if (!ctorArgs) {
      // Constructor doesn't return the inductive type properly
      return false;
    }

    const termAtPos = ctorArgs[position];

    // Must be a variable
    if (termAtPos.tag !== 'Var') {
      return false;
    }

    // Check that this variable appears exactly once in all positions
    let appearances = 0;
    for (const arg of ctorArgs) {
      if (arg.tag === 'Var' && arg.index === termAtPos.index) {
        appearances++;
      }
    }

    if (appearances !== 1) {
      return false;
    }
  }

  return true;
}

// ============================================================================
// Phase 2: Index Promotion
// ============================================================================

/**
 * Promote indices to parameters when they're always equal across constructors.
 * This finds equivalence classes of index positions and promotes one per class.
 */
function promoteIndices(
  def: InductiveTypeDef,
  numPositions: number,
  syntacticParams: Set<number>
): Set<number> {
  // Start with all non-parameter positions as indices
  const indices = new Set<number>();
  for (let i = 0; i < numPositions; i++) {
    if (!syntacticParams.has(i)) {
      indices.add(i);
    }
  }

  if (indices.size <= 1) {
    return indices; // Nothing to promote
  }

  // Build global equivalence relation
  const equivalenceClasses = buildEquivalenceClasses(def, numPositions, indices);

  // For each equivalence class with more than one index, promote the leftmost
  const newIndices = new Set<number>();

  for (const eqClass of Array.from(equivalenceClasses)) {
    if (eqClass.size <= 1) {
      // No promotion needed - keep as index
      for (const pos of eqClass) {
        newIndices.add(pos);
      }
    } else {
      // Promote leftmost, keep others as indices
      const sorted = Array.from(eqClass).sort((a: number, b: number) => a - b);
      const toPromote = sorted[0];

      // Check if promotion is valid (must be variables in all constructors)
      if (canPromotePosition(def, toPromote, numPositions)) {
        // Don't add to newIndices - it's promoted to parameter
      } else {
        // Can't promote, keep as index
        newIndices.add(toPromote);
      }

      // Keep all others as indices
      for (let i = 1; i < sorted.length; i++) {
        newIndices.add(sorted[i]);
      }
    }
  }

  return newIndices;
}

/**
 * Build equivalence classes of positions that are always equal across all constructors.
 */
function buildEquivalenceClasses(
  def: InductiveTypeDef,
  numPositions: number,
  indices: Set<number>
): Set<Set<number>> {
  const indexArray = Array.from(indices);

  // Build equivalence relation: i ~ j iff they're equal in all constructors
  const equivalent = (i: number, j: number): boolean => {
    for (const ctor of def.constructors) {
      const args = extractInductiveArgs(ctor.type, def.name, numPositions);
      if (!args) return false;

      if (!termsEqual(args[i], args[j])) {
        return false;
      }
    }
    return true;
  };

  // Build equivalence classes using union-find
  const parent = new Map<number, number>();
  const find = (x: number): number => {
    if (!parent.has(x)) {
      parent.set(x, x);
      return x;
    }
    const p = parent.get(x)!;
    if (p === x) return x;
    const root = find(p);
    parent.set(x, root);
    return root;
  };

  const union = (x: number, y: number) => {
    const rootX = find(x);
    const rootY = find(y);
    if (rootX !== rootY) {
      parent.set(rootX, rootY);
    }
  };

  // Build equivalence classes
  for (let i = 0; i < indexArray.length; i++) {
    for (let j = i + 1; j < indexArray.length; j++) {
      if (equivalent(indexArray[i], indexArray[j])) {
        union(indexArray[i], indexArray[j]);
      }
    }
  }

  // Group by equivalence class
  const classes = new Map<number, Set<number>>();
  for (const idx of indexArray) {
    const root = find(idx);
    if (!classes.has(root)) {
      classes.set(root, new Set());
    }
    classes.get(root)!.add(idx);
  }

  return new Set(classes.values());
}

/**
 * Check if a position can be promoted (must be a variable in all constructors).
 */
function canPromotePosition(
  def: InductiveTypeDef,
  position: number,
  numPositions: number
): boolean {
  for (const ctor of def.constructors) {
    const args = extractInductiveArgs(ctor.type, def.name, numPositions);
    if (!args) return false;

    const term = args[position];
    if (term.tag !== 'Var') {
      return false; // Cannot promote complex terms
    }
  }
  return true;
}

// ============================================================================
// Phase 2.5: Dependency Validation
// ============================================================================

/**
 * Enforce that parameters form a prefix.
 * Any position after the first index must be demoted to an index.
 */
function enforceParameterPrefix(indices: Set<number>, numPositions: number): number[] {
  if (indices.size === 0) {
    return [];
  }

  const firstIndex = Math.min(...Array.from(indices));

  // All positions >= firstIndex must be indices
  const result: number[] = [];

  for (let i = firstIndex; i < numPositions; i++) {
    result.push(i);
  }

  return result.sort((a, b) => a - b);
}

// ============================================================================
// Helper Functions
// ============================================================================

/**
 * Count the number of Pi binders in a type.
 */
function countPiArgs(type: TTerm): number {
  let count = 0;
  let current = type;

  while (current.tag === 'Binder' && current.binderKind.tag === 'BPi') {
    count++;
    current = current.body;
  }

  return count;
}

/**
 * Extract the arguments to the inductive type from a constructor's type.
 * Returns the terms applied to the inductive type, or null if not found.
 *
 * Example: For `(A : Type) -> Vec A 0`, returns [A, 0]
 */
function extractInductiveArgs(
  ctorType: TTerm,
  inductiveName: string,
  expectedArgs: number
): TTerm[] | null {
  // Navigate to the return type (skip all Pi binders)
  let returnType = ctorType;
  while (returnType.tag === 'Binder' && returnType.binderKind.tag === 'BPi') {
    returnType = returnType.body;
  }

  // The return type should be applications of the inductive type
  // Extract arguments by peeling off applications
  const args: TTerm[] = [];
  let current = returnType;

  while (current.tag === 'App') {
    args.unshift(current.arg);
    current = current.fn;
  }

  // Current should now be the inductive type constant
  if (current.tag !== 'Const' || current.name !== inductiveName) {
    return null;
  }

  if (args.length !== expectedArgs) {
    return null;
  }

  return args;
}

/**
 * Check if two terms are structurally equal (definitional equality).
 * This is a simple syntactic check.
 */
function termsEqual(t1: TTerm, t2: TTerm): boolean {
  if (t1.tag !== t2.tag) return false;

  switch (t1.tag) {
    case 'Var':
      return t2.tag === 'Var' && t1.index === t2.index;

    case 'Sort':
      return t2.tag === 'Sort' && t1.level === t2.level;

    case 'Const':
      return t2.tag === 'Const' && t1.name === t2.name;

    case 'App':
      return (
        t2.tag === 'App' &&
        termsEqual(t1.fn, t2.fn) &&
        termsEqual(t1.arg, t2.arg)
      );

    case 'Binder':
      return (
        t2.tag === 'Binder' &&
        t1.binderKind.tag === t2.binderKind.tag &&
        termsEqual(t1.domain, t2.domain) &&
        termsEqual(t1.body, t2.body)
      );

    case 'Hole':
      // Holes are equal if they have the same ID
      return t2.tag === 'Hole' && t1.id === t2.id;

    case 'Annot':
      return (
        t2.tag === 'Annot' &&
        termsEqual(t1.term, t2.term) &&
        termsEqual(t1.type, t2.type)
      );

    case 'Match':
      // For simplicity, we won't compare match terms deeply
      // In practice, they shouldn't appear in inductive type arguments
      return false;

    default:
      const _exhaustive: never = t1;
      return false;
  }
}
