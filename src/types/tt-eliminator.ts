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
 * Extract parameters from an inductive type.
 * E.g., for `List : Type → Type`, extracts [{name: 'A', type: Type}]
 * For `Vec : Type → Nat → Type`, extracts [{name: 'A', type: Type}, {name: 'n', type: Nat}]
 */
interface TypeParam {
  name: string;
  type: TTerm;
}

function extractTypeParams(type: TTerm): { params: TypeParam[], resultSort: TTerm } {
  const params: TypeParam[] = [];
  const usedNames = new Set<string>();
  let current = type;

  while (current.tag === 'Binder' && current.binderKind.tag === 'BPi') {
    let name = current.name;
    if (name === '_' || name === '') {
      name = generateNameForType(current.domain, usedNames);
    } else {
      usedNames.add(name);
    }
    params.push({ name, type: current.domain });
    current = current.body;
  }

  return { params, resultSort: current };
}

/**
 * Build the fully applied inductive type: D p1 p2 ... pN
 * where params are at indices (numParams - 1), (numParams - 2), ..., 0 from innermost
 */
function buildFullyAppliedType(
  inductiveConst: TTerm,
  numParams: number,
  indexOffset: number = 0
): TTerm {
  let result = inductiveConst;
  for (let i = 0; i < numParams; i++) {
    // Params are bound outermost first, so from inside:
    // param 0 is at (numParams - 1 + indexOffset), param 1 at (numParams - 2 + indexOffset), etc.
    result = mkApp(result, mkVar(numParams - 1 - i + indexOffset));
  }
  return result;
}

/**
 * Generate an eliminator type for an inductive type.
 *
 * Supports:
 * - Simple types (e.g., Bool, Nat)
 * - Parameterized types (e.g., List A)
 * - Indexed types (e.g., Vec A n, Equal A x y)
 *
 * @param def - The inductive type definition
 * @returns The type of the eliminator
 */
export function generateEliminator(def: InductiveTypeDef): TTerm {
  const { params, resultSort } = extractTypeParams(def.type);
  const numParams = params.length;

  // Validate we end in a Sort
  if (resultSort.tag !== 'Sort') {
    // Malformed type, return placeholder
    return mkType(0);
  }

  const inductiveConst = mkConst(def.name, def.type);
  const numCtors = def.constructors.length;

  // Build the eliminator from inside out:
  // Structure: (params...) → (P : D params... → Type) → (cases...) → (x : D params...) → P x

  // 1. Start with result: P x
  // From innermost position (after all params, P, cases, x are bound):
  // - x is at index 0
  // - cases are at indices 1 to numCtors
  // - P is at index numCtors + 1
  // - params are at indices numCtors + 2 to numCtors + 1 + numParams
  const P_from_result = numCtors + 1;
  const resultType = mkApp(mkVar(P_from_result), mkVar(0));

  // 2. Add target: (x : D params...)
  // In the domain of (x : D params...), params are at indices numCtors + 1 onwards
  // (we have numCtors case binders + P above us, but not x yet)
  const targetType = buildFullyAppliedType(inductiveConst, numParams, numCtors + 1);
  let result = mkPi(targetType, resultType, 'x');

  // 3. Add constructor cases from right to left
  for (let i = numCtors - 1; i >= 0; i--) {
    const ctor = def.constructors[i];
    // From case i's domain position in the final structure:
    // - P is at index 0 (outermost after params)
    // - case_0 through case_{i-1} are at indices 1 through i
    // - So P is at index i when viewed from case_i's domain
    // Wait no: from case_i's domain, only case_0 through case_{i-1} have been entered
    // So P is at index i (i binders between us and P)
    const pIndex = i;
    const methodType = buildMethodType(def, ctor, pIndex, numParams);
    result = mkPi(methodType, result, `case_${ctor.name}`);
  }

  // 4. Add motive: (P : D params... → Type)
  // From P's position, params are at indices 0 to numParams-1
  const motiveTargetType = buildFullyAppliedType(inductiveConst, numParams, 0);
  const motiveType = mkPi(motiveTargetType, mkType(1), '_');
  result = mkPi(motiveType, result, 'P');

  // 5. Add parameters from right to left
  // The extracted param types already have correct De Bruijn indices for the
  // final structure because:
  // - Param i extracted at depth (i+1) has param j at index (i - j)
  // - In the final structure (A : ...) → (B : ...) → ..., from param i's domain,
  //   param j (j < i) is at index (i - 1 - j + 1) = (i - j)
  // So no adjustment is needed!
  for (let i = numParams - 1; i >= 0; i--) {
    const param = params[i];
    result = mkPi(param.type, result, param.name);
  }

  return result;
}

// ============================================================================
// Helper Functions
// ============================================================================

/**
 * Build the method type for a constructor in an eliminator.
 *
 * For a constructor like:
 * - `zero : Nat` → method type is `P zero`
 * - `succ : Nat → Nat` → method type is `(n : Nat) → P n → P (succ n)`
 * - `nil : (A : Type) → List A` → method type is `P nil` (params are implicit)
 * - `cons : (A : Type) → A → List A → List A` → method type is `(x : A) → (xs : List A) → P xs → P (cons x xs)`
 *
 * @param def - The inductive type definition
 * @param ctor - The constructor
 * @param pIndex - The De Bruijn index at which P can be found from this method's position
 * @param numTypeParams - Number of type parameters (to skip in constructor args)
 */
function buildMethodType(
  def: InductiveTypeDef,
  ctor: { name: string; type: TTerm },
  pIndex: number,
  numTypeParams: number
): TTerm {
  const ctorConst = mkConst(ctor.name, ctor.type);

  // Extract all constructor arguments
  const allCtorArgs = extractCtorArgs(ctor.type, def.name);

  // Count how many params the constructor actually takes
  // This may be less than numTypeParams if some are indices
  // E.g., for Vec, the type has params [A, n] but vnil only takes [A]
  // E.g., for Equal, the type has params [A, x, y] but refl only takes [A, x]
  const numCtorParams = Math.min(allCtorArgs.length, numTypeParams);

  // Skip type parameters - they're already bound in the eliminator
  // For `cons : (A : Type) → A → List A → List A`, skip the first (A : Type)
  const ctorArgs = allCtorArgs.slice(numCtorParams);

  // For building the result, we need to apply the constructor to:
  // 1. The type parameters (from the outer scope)
  // 2. The constructor's own arguments

  if (ctorArgs.length === 0) {
    // Nullary constructor (after removing params): method type is just P (ctor params...)
    // Build ctor applied to the params it actually takes
    // From method position, params are at pIndex + 1, pIndex + 2, ... (after P)
    let ctorApp = ctorConst;
    for (let i = 0; i < numCtorParams; i++) {
      // params are at indices (pIndex + numTypeParams - i) from here
      // (use numTypeParams for offset since all params are in scope, but only apply numCtorParams)
      ctorApp = mkApp(ctorApp, mkVar(pIndex + numTypeParams - i));
    }
    return mkApp(mkVar(pIndex), ctorApp);
  }

  // Constructor with arguments: build method type with IHs
  // Structure: (arg0 : T0) -> ... -> (argN : TN) -> (ih0 : P arg_i) -> ... -> P (ctor params args)

  // Count recursive arguments (those whose type is the inductive type)
  const recursiveArgs = ctorArgs.filter((arg) =>
    isInductiveType(arg.type, def.name)
  );
  const numIHs = recursiveArgs.length;

  // Inside the innermost part (after all args and IHs are bound):
  // - Local args are at indices 0 to (ctorArgs.length + numIHs - 1)
  // - P is at index pIndex + ctorArgs.length + numIHs
  // - Type params are at indices (pIndex + ctorArgs.length + numIHs + 1) to (pIndex + ctorArgs.length + numIHs + numTypeParams)
  const innerP = pIndex + ctorArgs.length + numIHs;
  const paramsOffset = innerP + 1;

  // Build the result type: P (ctor params args...)
  // First apply the params the constructor takes, then local args
  let ctorApp: TTerm = ctorConst;

  // Apply type parameters (only as many as the constructor takes)
  for (let i = 0; i < numCtorParams; i++) {
    // Use numTypeParams for offset calculation since all type params are in scope
    ctorApp = mkApp(ctorApp, mkVar(paramsOffset + numTypeParams - 1 - i));
  }

  // Apply constructor arguments
  // Args are bound left-to-right, so arg 0 is at index (ctorArgs.length + numIHs - 1), etc.
  for (let i = 0; i < ctorArgs.length; i++) {
    const argIndex = ctorArgs.length + numIHs - 1 - i;
    ctorApp = mkApp(ctorApp, mkVar(argIndex));
  }

  let result = mkApp(mkVar(innerP), ctorApp);

  // Add inductive hypotheses for recursive arguments (from right to left)
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
  // Need to adjust types to account for:
  // 1. The fact that constructor arg types reference params at position-dependent indices
  // 2. Shifting for any binders we're adding around the body
  //
  // Key insight: When we add a Pi binder, its domain is evaluated in the OUTER context,
  // not accounting for the binders we're about to add to the body.
  //
  // From the method type's position in the eliminator (as domain of case_CtorName):
  // - P is at index pIndex
  // - Params are at indices pIndex + 1, pIndex + 2, ..., pIndex + numTypeParams
  //
  // For ctorArgs[i], the original extraction was from depth (i + numTypeParams) in the constructor.
  // In that type, param j appears at index (i + numTypeParams - 1 - j) = (i) + (numTypeParams - 1 - j).
  for (let i = ctorArgs.length - 1; i >= 0; i--) {
    const arg = ctorArgs[i];

    // From the domain position of this arg in the method type:
    // - We're adding binders around our result, but domains are evaluated BEFORE entering those binders
    // - So from each domain position, the number of local binders above us = (ctorArgs.length - 1 - i) for args + numIHs for IHs
    // Wait no - we're building inside-out, so the result already has those binders.
    // But a Pi's domain is evaluated in the context OUTSIDE that Pi.
    //
    // Actually: when building (x : A) -> body, the domain A is evaluated in the current context,
    // then we enter the binder for the body. So domains don't see their own binder or later binders.
    //
    // From the domain of arg i: earlier args (j < i) are bound, providing (i) binders.
    // Plus there are pIndex binders above us for cases, then P, then params.
    // So params are at: pIndex + 1 + i, pIndex + 2 + i, ..., pIndex + numTypeParams + i
    // Wait that's not right either...

    // Let's think again. The method type being built is the domain of a Pi binder (case_cons).
    // Inside that domain (the method type itself), we add binders for args and IHs.
    // From any point inside the method type, the "outer" context is:
    //   [local binders in method type] + [case binders before us] + P + params
    //
    // For arg i's domain in the method type:
    // - Local binders above: args 0 to i-1 (there are i of them)
    // - Then: 0 cases (we're inside case_cons's domain), P, params
    // - So P is at index i + 0 = i? No wait...
    //
    // Ugh, I keep getting confused. Let me trace through a concrete example.
    //
    // For cons method: (x : A) → (l : List A) → (ih_l : P l) → P (cons A x l)
    //
    // Building inside out:
    // 1. result = P (cons A x l)  - inner, P at innerP
    // 2. result = (ih_l : P l) → result - ih domain at depth where P is at pFromHere
    // 3. result = (l : List A) → result - l domain at depth where A is at ?
    // 4. result = (x : A) → result - x domain at depth where A is at ?
    //
    // At step 4, from x's domain position:
    // - This is the outermost position of the method type
    // - The method type itself is the domain of case_cons's Pi
    // - Above case_cons: case_nil, P, A (for List)
    // - So from x's domain: case_nil at 0, P at 1, A at 2
    //
    // At step 3, from l's domain position:
    // - x is bound, so x is at index 0
    // - Above that: case_nil at 1, P at 2, A at 3
    //
    // So for arg i's domain, params are at indices pIndex + 1 + i onwards.
    const paramsBaseFromHere = pIndex + 1 + i;

    // The original type has param j at index (i) + (numCtorParams - 1 - j)
    // where i is the extraction depth offset (how many ctor args before this one)
    // Note: we use numCtorParams since constructors might only reference the params they take
    const extractionDepthOffset = i;

    // We don't need to shift for wrapped binders because domain types are evaluated
    // in the outer context (before entering the binder we're creating)
    const shiftedType = adjustCtorArgType(arg.type, 0, numCtorParams, extractionDepthOffset, paramsBaseFromHere);
    result = mkPi(shiftedType, result, arg.name);
  }

  return result;
}

/**
 * Adjust a constructor argument type for use in the eliminator.
 *
 * @param type - The original type extracted from the constructor
 * @param shiftAmount - How much to shift non-param references
 * @param numParams - Number of type parameters
 * @param depthOffset - How many ctor args were between params and this arg in the original
 * @param paramsBase - Base index for params in the new context
 */
function adjustCtorArgType(
  type: TTerm,
  shiftAmount: number,
  numParams: number,
  depthOffset: number,
  paramsBase: number
): TTerm {
  return adjustCtorArgTypeRec(type, shiftAmount, 0, numParams, depthOffset, paramsBase);
}

function adjustCtorArgTypeRec(
  term: TTerm,
  shiftAmount: number,
  cutoff: number,
  numParams: number,
  depthOffset: number,
  paramsBase: number
): TTerm {
  switch (term.tag) {
    case 'Var': {
      if (term.index < cutoff) {
        // Bound by a binder within the type we're processing
        return term;
      }
      // Free variable - was it a param ref or a ctor arg ref?
      const freeIndex = term.index - cutoff;

      // In the original type at extraction depth (numParams + depthOffset):
      // param j was at index (depthOffset + numParams - 1 - j)
      // So if freeIndex == depthOffset + numParams - 1 - j, then j = depthOffset + numParams - 1 - freeIndex

      // Check if this could be a param reference
      // Param 0 was at (depthOffset + numParams - 1)
      // Param (numParams-1) was at depthOffset
      // So param refs are in range [depthOffset, depthOffset + numParams - 1]
      if (freeIndex >= depthOffset && freeIndex < depthOffset + numParams) {
        // This is a param reference
        const paramIndex = depthOffset + numParams - 1 - freeIndex; // which param (0 = first)
        // Redirect to new location: paramsBase + numParams - 1 - paramIndex
        const newIndex = paramsBase + numParams - 1 - paramIndex + cutoff;
        return mkVar(newIndex);
      }

      // Not a param ref - shift for the binders we've added
      return mkVar(term.index + shiftAmount);
    }

    case 'Sort':
    case 'Const':
    case 'Hole':
      return term;

    case 'App':
      return mkApp(
        adjustCtorArgTypeRec(term.fn, shiftAmount, cutoff, numParams, depthOffset, paramsBase),
        adjustCtorArgTypeRec(term.arg, shiftAmount, cutoff, numParams, depthOffset, paramsBase)
      );

    case 'Binder': {
      const newDomain = adjustCtorArgTypeRec(term.domain, shiftAmount, cutoff, numParams, depthOffset, paramsBase);
      const newBody = adjustCtorArgTypeRec(term.body, shiftAmount, cutoff + 1, numParams, depthOffset, paramsBase);
      return {
        ...term,
        domain: newDomain,
        body: newBody,
      };
    }

    case 'Annot':
      return {
        tag: 'Annot',
        term: adjustCtorArgTypeRec(term.term, shiftAmount, cutoff, numParams, depthOffset, paramsBase),
        type: adjustCtorArgTypeRec(term.type, shiftAmount, cutoff, numParams, depthOffset, paramsBase),
      };

    case 'Match':
      return term;

    default:
      return term;
  }
}

/**
 * Generate a name for a type (lowercase first letter, with counter if needed).
 * E.g., "Nat" -> "n", "Vec" -> "v", "List" -> "l", "Type" -> "A"
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
  } else if (baseType.tag === 'Sort') {
    // Type parameters typically use uppercase letters starting with A
    baseName = 'A';
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
