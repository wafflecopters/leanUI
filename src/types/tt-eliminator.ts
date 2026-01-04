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
  // When building from inside out, method type i is used as domain where P is at index i
  // (zero's method is at index 0 after P, succ's method is at index 1, etc.)
  for (let i = numCtors - 1; i >= 0; i--) {
    const ctor = def.constructors[i];
    const methodType = buildSimpleMethodType(def, ctor, i);
    result = mkPi(methodType, result, `case_${ctor.name}`);
  }

  // Add motive: (P : D → Type)
  const motiveType = mkPi(inductiveConst, mkType(1), '_');
  result = mkPi(motiveType, result, 'P');

  return result;
}

// ============================================================================
// Helper Functions
// ============================================================================

/**
 * Check if an inductive type is "simple" (just a Sort, no parameters/indices).
 * Type = Sort level 1, Prop = Sort level 0.
 */
function isSimpleInductiveType(type: TTerm): boolean {
  return type.tag === 'Sort';
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
 * @param pIndex - The De Bruijn index at which P can be found from this method's position
 */
function buildSimpleMethodType(
  def: InductiveTypeDef,
  ctor: { name: string; type: TTerm },
  pIndex: number
): TTerm {
  const ctorConst = mkConst(ctor.name, ctor.type);

  // Extract constructor arguments
  const ctorArgs = extractCtorArgs(ctor.type, def.name);

  if (ctorArgs.length === 0) {
    // Nullary constructor: method type is just P ctor
    // P is directly at pIndex from this position
    return mkApp(mkVar(pIndex), ctorConst);
  }

  // Constructor with arguments: build method type with IHs
  // Structure: (arg0 : T0) -> ... -> (argN : TN) -> (ih0 : P arg_i) -> ... -> P (ctor args)

  // Count recursive arguments (those whose type is the inductive type)
  const recursiveArgs = ctorArgs.filter((arg) =>
    isInductiveType(arg.type, def.name)
  );
  const numIHs = recursiveArgs.length;

  // Inside the innermost part (after all args and IHs are bound):
  // P is at index pIndex + ctorArgs.length + numIHs
  const innerP = pIndex + ctorArgs.length + numIHs;

  // Build the result type: P (ctor arg₁ arg₂ ...)
  // Args are bound left-to-right, so arg 0 is at index (ctorArgs.length + numIHs - 1),
  // arg 1 is at (ctorArgs.length + numIHs - 2), etc.
  let ctorApp: TTerm = ctorConst;
  for (let i = 0; i < ctorArgs.length; i++) {
    const argIndex = ctorArgs.length + numIHs - 1 - i;
    ctorApp = mkApp(ctorApp, mkVar(argIndex));
  }
  let result = mkApp(mkVar(innerP), ctorApp);

  // Add inductive hypotheses for recursive arguments (from right to left)
  // We process args right-to-left and add an IH for each recursive arg.
  // When adding IH for arg i, from the domain position:
  // - We've already wrapped (numIHs - ihsRemaining) IHs and need to look past them
  // - P is at pIndex + ctorArgs.length (all args are above us, but IHs aren't bound yet in domain)
  // - arg_i is at position (ctorArgs.length - 1 - i) from the domain position
  let ihsAdded = 0;
  for (let i = ctorArgs.length - 1; i >= 0; i--) {
    if (isInductiveType(ctorArgs[i].type, def.name)) {
      // From the IH domain position:
      // - All ctorArgs.length arg binders are above us
      // - ihsAdded IH binders are above us (the ones we've already wrapped)
      // - P is at pIndex + ctorArgs.length + ihsAdded
      // - arg_i is at index (ctorArgs.length - 1 - i) + ihsAdded
      const pFromHere = pIndex + ctorArgs.length + ihsAdded;
      const argFromHere = ctorArgs.length - 1 - i + ihsAdded;
      const ihType = mkApp(mkVar(pFromHere), mkVar(argFromHere));
      result = mkPi(ihType, result, `ih_${ctorArgs[i].name}`);
      ihsAdded++;
    }
  }

  // Add constructor arguments (from right to left)
  for (let i = ctorArgs.length - 1; i >= 0; i--) {
    const arg = ctorArgs[i];
    // The arg type may reference earlier args, need to shift appropriately
    // At this point we've wrapped with all IHs (numIHs) and (ctorArgs.length - 1 - i) args
    const numWrapped = numIHs + (ctorArgs.length - 1 - i);
    const shiftedType = shift(arg.type, numWrapped, 0);
    result = mkPi(shiftedType, result, arg.name);
  }

  return result;
}

/**
 * Generate a name for a type (lowercase first letter, with counter if needed).
 * E.g., "Nat" -> "n", "Vec" -> "v", "List" -> "l"
 */
function generateNameForType(type: TTerm, usedNames: Set<string>): string {
  // Extract the base type name (unwrap applications)
  let baseType = type;
  while (baseType.tag === 'App') {
    baseType = baseType.fn;
  }

  let baseName: string;
  if (baseType.tag === 'Const') {
    // Use first letter lowercase
    baseName = baseType.name.charAt(0).toLowerCase();
  } else {
    baseName = 'x';
  }

  // Find a unique name
  let name = baseName;
  let counter = 2;
  while (usedNames.has(name)) {
    name = `${baseName}${counter}`;
    counter++;
  }
  usedNames.add(name);
  return name;
}

/**
 * Extract constructor arguments (the telescope before the return type).
 * Generates meaningful names for anonymous binders.
 */
function extractCtorArgs(
  ctorType: TTerm,
  inductiveName: string
): Array<{ name: string; type: TTerm }> {
  const args: Array<{ name: string; type: TTerm }> = [];
  const usedNames = new Set<string>();
  let current = ctorType;

  // If the constructor type is just the inductive type (nullary constructor)
  if (current.tag === 'Const' && current.name === inductiveName) {
    return [];
  }

  // Otherwise, extract Pi binders
  while (current.tag === 'Binder' && current.binderKind.tag === 'BPi') {
    let name = current.name;
    // Generate a meaningful name if anonymous
    if (name === '_' || name === '') {
      name = generateNameForType(current.domain, usedNames);
    } else {
      usedNames.add(name);
    }
    args.push({
      name,
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
