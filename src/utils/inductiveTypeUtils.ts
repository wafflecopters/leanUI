/**
 * Inductive Type Utilities
 *
 * Helper functions for working with inductive type definitions.
 */

import { TTerm, mkApp, mkConst, mkHole, mkType } from '../compiler/surface';
import { freshHoleId } from './termNavigation';

/**
 * Count the number of Pi binders (arguments) in a type.
 * For example:
 *   Type_0 -> 0
 *   Nat -> Type_0 -> 1
 *   Nat -> Type -> Type -> 2
 */
export function countPiArgs(type: TTerm): number {
  if (type.tag === 'Binder' && type.binderKind.tag === 'BPi') {
    return 1 + countPiArgs(type.body);
  }
  return 0;
}

/**
 * Get the domain types of all Pi binders in order.
 * For `(n: Nat) -> (A: Type) -> Type`, returns [Nat, Type]
 */
export function getPiDomains(type: TTerm): TTerm[] {
  const domains: TTerm[] = [];
  let current = type;

  while (current.tag === 'Binder' && current.binderKind.tag === 'BPi') {
    domains.push(current.domain);
    current = current.body;
  }

  return domains;
}

/**
 * Create a default constructor type for an inductive type.
 *
 * Given:
 *   - inductiveName: "Vec"
 *   - inductiveType: (n: Nat) -> (A: Type) -> Type
 *
 * Returns:
 *   Vec ?hole_0 ?hole_1
 *
 * The returned type is the inductive type applied to fresh holes for each argument.
 */
export function createDefaultConstructorType(
  inductiveName: string,
  inductiveType: TTerm
): TTerm {
  // Count how many Pi binders (arguments) the type has
  const argCount = countPiArgs(inductiveType);

  // Start with the inductive type constant
  // The type of the constant is the inductiveType itself
  let result: TTerm = mkConst(inductiveName, inductiveType);

  // Apply fresh holes for each argument
  for (let i = 0; i < argCount; i++) {
    const holeId = freshHoleId();
    // For simplicity, use Type_0 as the hole's type
    // In a real implementation, we'd use the actual domain type
    const hole = mkHole(holeId, mkType(0), []);
    result = mkApp(result, hole);
  }

  return result;
}

/**
 * Create a new constructor with a default type for the inductive type.
 */
export function createConstructorForInductive(
  inductiveName: string,
  inductiveType: TTerm,
  constructorBaseName: string
): { name: string; type: TTerm } {
  return {
    name: constructorBaseName,
    type: createDefaultConstructorType(inductiveName, inductiveType),
  };
}
