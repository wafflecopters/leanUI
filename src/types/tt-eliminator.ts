/**
 * Eliminator (Induction Principle) Generation
 *
 * This module generates the type signature for eliminators (induction principles)
 * of inductive type definitions.
 *
 * ## What is an Eliminator?
 *
 * An eliminator is the induction principle for an inductive type. It allows you to
 * prove properties about values of that type by case analysis and induction.
 *
 * ## Eliminator Structure (Simplified)
 *
 * For now, we generate eliminators in a simplified form suitable for simple inductive types.
 *
 * For an inductive type `D : Sort` with constructors `c₁, ..., cₖ`:
 *
 * ```
 * D-elim :
 *   (P : D → Sort)              -- motive (property to prove)
 *   → P c₁                       -- case for constructor 1
 *   → ...
 *   → P cₖ                       -- case for constructor k
 *   → (x : D)                    -- value to case-analyze
 *   → P x                        -- proof of property for x
 * ```
 *
 * ## Examples
 *
 * ### Bool
 * ```
 * Bool-elim :
 *   (P : Bool → Type)
 *   → P true
 *   → P false
 *   → (b : Bool)
 *   → P b
 * ```
 *
 * ### Nat (with inductive hypotheses)
 * ```
 * Nat-elim :
 *   (P : Nat → Type)
 *   → P zero
 *   → ((n : Nat) → P n → P (succ n))
 *   → (n : Nat)
 *   → P n
 * ```
 *
 * This is a simplified implementation. Full dependent eliminators with parameters
 * and indices will be added in future iterations.
 */

import { TTerm, mkPi, mkVar, mkApp, mkConst, mkType } from './tt-core';
import { InductiveTypeDef } from './tt-examples';

/**
 * Generate a simplified eliminator type for an inductive type.
 *
 * Currently supports:
 * - Simple types (Type_0)
 * - Non-indexed types
 * - Inductive hypotheses for recursive constructor arguments
 *
 * @param def - The inductive type definition
 * @returns The type of the eliminator
 *
 * @example
 * // For Bool : Type
 * generateEliminator(boolDef)
 * // Returns: (P : Bool → Type) → P true → P false → (b : Bool) → P b
 */
export function generateEliminator(def: InductiveTypeDef): TTerm {
  // For now, only handle simple types (no parameters/indices)
  const isSimpleType = isSimpleInductiveType(def.type);

  if (!isSimpleType) {
    // For complex types, return a placeholder
    // TODO: Implement full eliminator generation
    return mkType(0);
  }

  // Build the eliminator type from inside out:
  // 1. Result type: P x
  // 2. Target argument: (x : D)
  // 3. Constructor methods: one per constructor
  // 4. Motive: (P : D → Type)

  const inductiveConst = mkConst(def.name, def.type);

  // Start with result type: P x
  // P is at index 1 + num_constructors (from the target level)
  // x (target) is at index 0
  const numCtors = def.constructors.length;
  const P_index = numCtors + 1;
  const resultType = mkApp(mkVar(P_index), mkVar(0));

  // Add target argument: (x : D)
  let result = mkPi(inductiveConst, resultType, 'x');

  // Add constructor methods from right to left (last to first)
  for (let i = numCtors - 1; i >= 0; i--) {
    const ctor = def.constructors[i];
    const methodType = buildSimpleMethodType(def, ctor, numCtors - i);
    result = mkPi(methodType, result, `case_${ctor.name}`);
  }

  // Add motive: (P : D → Type)
  const motiveType = mkPi(inductiveConst, mkType(0), '_');
  result = mkPi(motiveType, result, 'P');

  return result;
}

// ============================================================================
// Helper Functions
// ============================================================================

/**
 * Check if an inductive type is "simple" (just Type_0, no parameters/indices).
 */
function isSimpleInductiveType(type: TTerm): boolean {
  return type.tag === 'Sort' && type.level === 0;
}

/**
 * Build the method type for a constructor in a simple eliminator.
 *
 * For a constructor like:
 * - `zero : Nat` → method type is `P zero`
 * - `succ : Nat → Nat` → method type is `(n : Nat) → P n → P (succ n)`
 *
 * @param def - The inductive type definition
 * @param ctor - The constructor
 * @param depth - How many binders we're under (for De Bruijn calculation)
 */
function buildSimpleMethodType(
  def: InductiveTypeDef,
  ctor: { name: string; type: TTerm },
  depth: number
): TTerm {
  const ctorConst = mkConst(ctor.name, ctor.type);
  const inductiveConst = mkConst(def.name, def.type);

  // Extract constructor arguments
  const ctorArgs = extractCtorArgs(ctor.type, def.name);

  if (ctorArgs.length === 0) {
    // Nullary constructor: method type is just P ctor
    // P is at depth + num_ctor_args (which is 0) + 1 (for target) + 1 (for P itself) = depth + 2
    const P_index = depth + 1;
    return mkApp(mkVar(P_index), ctorConst);
  }

  // Constructor with arguments: build method type with IHs
  // For now, simplified: bind all args, add IH for recursive args, then P (ctor args)

  // Build the result type: P (ctor arg₁ arg₂ ...)
  let ctorApp: TTerm = ctorConst;
  for (let i = 0; i < ctorArgs.length; i++) {
    // Arguments are bound in order, so arg 0 is at index (ctorArgs.length - 1), etc.
    ctorApp = mkApp(ctorApp, mkVar(ctorArgs.length - 1 - i));
  }

  // Count recursive arguments (those whose type is the inductive type)
  const recursiveArgs = ctorArgs.filter((arg) =>
    isInductiveType(arg.type, def.name)
  );

  // P is at: depth + ctorArgs.length (for the args) + recursiveArgs.length (for IHs) + 1 (target) + 1 (P)
  const P_index = depth + ctorArgs.length + recursiveArgs.length + 1;
  let result = mkApp(mkVar(P_index), ctorApp);

  // Add inductive hypotheses for recursive arguments (from right to left)
  let ihOffset = 0;
  for (let i = ctorArgs.length - 1; i >= 0; i--) {
    if (isInductiveType(ctorArgs[i].type, def.name)) {
      // Add IH: P arg_i
      // arg_i is at index (ctorArgs.length - 1 - i) + ihOffset
      const argIndex = ctorArgs.length - 1 - i + ihOffset;
      const ihType = mkApp(
        mkVar(P_index + ihOffset),
        mkVar(argIndex)
      );
      result = mkPi(ihType, result, `ih_${i}`);
      ihOffset++;
    }
  }

  // Add constructor arguments (from right to left)
  for (let i = ctorArgs.length - 1; i >= 0; i--) {
    const arg = ctorArgs[i];
    // Shift the type by the number of IHs and args we've already bound
    const shiftedType = shift(arg.type, ihOffset + (ctorArgs.length - 1 - i), 0);
    result = mkPi(shiftedType, result, arg.name);
  }

  return result;
}

/**
 * Extract constructor arguments (the telescope before the return type).
 */
function extractCtorArgs(
  ctorType: TTerm,
  inductiveName: string
): Array<{ name: string; type: TTerm }> {
  const args: Array<{ name: string; type: TTerm }> = [];
  let current = ctorType;

  // If the constructor type is just the inductive type (nullary constructor)
  if (current.tag === 'Const' && current.name === inductiveName) {
    return [];
  }

  // Otherwise, extract Pi binders
  while (current.tag === 'Binder' && current.binderKind.tag === 'BPi') {
    args.push({
      name: current.name,
      type: current.domain,
    });
    current = current.body;
  }

  return args;
}

/**
 * Check if a type is (or reduces to) the inductive type.
 */
function isInductiveType(type: TTerm, inductiveName: string): boolean {
  // Simple check: is it the constant for the inductive type?
  if (type.tag === 'Const' && type.name === inductiveName) {
    return true;
  }

  // Check if it's an application of the inductive type
  let current = type;
  while (current.tag === 'App') {
    current = current.fn;
  }

  return current.tag === 'Const' && current.name === inductiveName;
}

/**
 * Shift De Bruijn indices in a term.
 * Adds `amount` to all free variables with index >= `cutoff`.
 */
function shift(term: TTerm, amount: number, cutoff: number): TTerm {
  if (amount === 0) return term;

  switch (term.tag) {
    case 'Var':
      return term.index >= cutoff ? mkVar(term.index + amount) : term;

    case 'Sort':
    case 'Const':
    case 'Hole':
      return term;

    case 'App':
      return mkApp(shift(term.fn, amount, cutoff), shift(term.arg, amount, cutoff));

    case 'Binder': {
      const newDomain = shift(term.domain, amount, cutoff);
      const newBody = shift(term.body, amount, cutoff + 1);
      return {
        ...term,
        domain: newDomain,
        body: newBody,
      };
    }

    case 'Annot':
      return {
        tag: 'Annot',
        term: shift(term.term, amount, cutoff),
        type: shift(term.type, amount, cutoff),
      };

    case 'Match':
      // Don't handle match for now
      return term;

    default:
      const _exhaustive: never = term;
      return term;
  }
}
