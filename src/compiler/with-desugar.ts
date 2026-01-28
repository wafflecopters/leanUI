/**
 * With-clause desugaring following Agda's approach.
 *
 * Transforms with-clauses into auxiliary function definitions + calls.
 * This happens on the surface syntax BEFORE elaboration.
 *
 * Example:
 *   isZero : Nat -> Bool
 *   isZero n with n
 *     | Zero => True
 *     | Succ m => False
 *
 * Desugars to:
 *   isZero : Nat -> Bool
 *   isZero n = isZero-with-1 n n
 *
 *   isZero-with-1 : Nat -> Nat -> Bool
 *   isZero-with-1 n Zero = True
 *   isZero-with-1 n (Succ m) = False
 */

import { TTerm, TPattern, TClause, TWithClause, mkAppTT, mkVarTT, mkConstTT, mkHoleTT, mkPropTT, mkPiTT } from './surface';
import { ParsedDeclaration } from '../parser/parser';

/**
 * Result of desugaring a declaration that may contain with-clauses.
 */
export interface DesugarResult {
  /** The main declaration (with with-clauses replaced by calls) */
  mainDecl: ParsedDeclaration;
  /** Generated auxiliary function declarations */
  auxiliaries: ParsedDeclaration[];
}

/**
 * Counter for generating unique auxiliary function names.
 */
let withCounter = 0;

/**
 * Reset the counter (useful for testing).
 */
export function resetWithCounter(): void {
  withCounter = 0;
}

/**
 * Generate a fresh name for an auxiliary with-function.
 */
function freshWithName(baseName: string): string {
  withCounter++;
  return `${baseName}-with-${withCounter}`;
}

/**
 * Desugar with-clauses in a list of declarations.
 *
 * @param decls - The original declarations
 * @returns Desugared declarations with auxiliary functions appended
 */
export function desugarWithClauses(decls: ParsedDeclaration[]): ParsedDeclaration[] {
  const result: ParsedDeclaration[] = [];

  for (const decl of decls) {
    const desugared = desugarDeclaration(decl);
    result.push(desugared.mainDecl);
    result.push(...desugared.auxiliaries);
  }

  return result;
}

/**
 * Desugar with-clauses in a single declaration.
 */
function desugarDeclaration(decl: ParsedDeclaration): DesugarResult {
  if (decl.kind !== 'def' || !decl.value) {
    // Only term definitions can have with-clauses
    return { mainDecl: decl, auxiliaries: [] };
  }

  // Check if the value contains a WithClause
  if (!containsWithClause(decl.value)) {
    return { mainDecl: decl, auxiliaries: [] };
  }

  const baseName = decl.name || 'anon';
  const auxiliaries: ParsedDeclaration[] = [];

  // Desugar the value, collecting auxiliary definitions
  const newValue = desugarTerm(decl.value, baseName, decl.type, auxiliaries);

  return {
    mainDecl: { ...decl, value: newValue },
    auxiliaries,
  };
}

/**
 * Check if a term contains a WithClause.
 */
function containsWithClause(term: TTerm): boolean {
  switch (term.tag) {
    case 'WithClause':
      return true;
    case 'App':
      return containsWithClause(term.fn) || containsWithClause(term.arg);
    case 'Binder':
      return (term.domain ? containsWithClause(term.domain) : false) || containsWithClause(term.body);
    case 'MultiBinder':
      return containsWithClause(term.domain) || containsWithClause(term.body);
    case 'Match':
      return containsWithClause(term.scrutinee) ||
        term.clauses.some(c => containsWithClause(c.rhs));
    case 'Annot':
      return containsWithClause(term.term) || containsWithClause(term.type);
    default:
      return false;
  }
}

/**
 * Desugar with-clauses in a term.
 *
 * When we encounter a WithClause:
 * 1. Generate a fresh auxiliary function name
 * 2. Create the auxiliary function declaration
 * 3. Replace the WithClause with a call to the auxiliary
 */
function desugarTerm(
  term: TTerm,
  baseName: string,
  declType: TTerm | undefined,
  auxiliaries: ParsedDeclaration[]
): TTerm {
  switch (term.tag) {
    case 'WithClause':
      return desugarWithClause(term, baseName, declType, auxiliaries);

    case 'App': {
      const newFn = desugarTerm(term.fn, baseName, declType, auxiliaries);
      const newArg = desugarTerm(term.arg, baseName, declType, auxiliaries);
      if (newFn === term.fn && newArg === term.arg) return term;
      return { ...term, fn: newFn, arg: newArg };
    }

    case 'Binder': {
      const newDomain = term.domain ? desugarTerm(term.domain, baseName, declType, auxiliaries) : undefined;
      const newBody = desugarTerm(term.body, baseName, declType, auxiliaries);
      if (newDomain === term.domain && newBody === term.body) return term;
      return { ...term, domain: newDomain, body: newBody };
    }

    case 'MultiBinder': {
      const newDomain = desugarTerm(term.domain, baseName, declType, auxiliaries);
      const newBody = desugarTerm(term.body, baseName, declType, auxiliaries);
      if (newDomain === term.domain && newBody === term.body) return term;
      return { ...term, domain: newDomain, body: newBody };
    }

    case 'Match': {
      const newScrutinee = desugarTerm(term.scrutinee, baseName, declType, auxiliaries);
      const newClauses = term.clauses.map(c => ({
        ...c,
        rhs: desugarTerm(c.rhs, baseName, declType, auxiliaries),
      }));
      return { tag: 'Match', scrutinee: newScrutinee, clauses: newClauses };
    }

    case 'Annot': {
      const newTerm = desugarTerm(term.term, baseName, declType, auxiliaries);
      const newType = desugarTerm(term.type, baseName, declType, auxiliaries);
      if (newTerm === term.term && newType === term.type) return term;
      return { tag: 'Annot', term: newTerm, type: newType };
    }

    default:
      return term;
  }
}

/**
 * Desugar a single WithClause into an auxiliary function call.
 *
 * For: isZero n with n | Zero => True | Succ m => False
 *
 * Generates auxiliary:
 *   isZero-with-1 : Nat -> Nat -> Bool
 *   isZero-with-1 n Zero = True
 *   isZero-with-1 n (Succ m) = False
 *
 * Returns call: isZero-with-1 n n
 */
function desugarWithClause(
  withClause: TWithClause,
  baseName: string,
  declType: TTerm | undefined,
  auxiliaries: ParsedDeclaration[]
): TTerm {
  const auxName = freshWithName(baseName);
  const functionPatterns = withClause.functionPatterns;
  const scrutinees = withClause.scrutinees;

  // Create auxiliary function clauses
  // Each with-clause becomes: auxName functionPatterns... withPattern... = rhs
  const auxClauses: TClause[] = withClause.clauses.map(clause => ({
    patterns: [...functionPatterns, ...clause.patterns],
    rhs: clause.rhs,
    namedPatterns: withClause.functionNamedPatterns,
  }));

  // Compute the auxiliary function type from the main declaration's type
  // The auxiliary takes: (1) function pattern args, (2) scrutinee args
  // and returns the main function's return type
  const auxType = computeAuxiliaryType(declType, functionPatterns, scrutinees);

  // Create the auxiliary function definition
  const auxDecl: ParsedDeclaration = {
    kind: 'def',
    name: auxName,
    type: auxType,
    value: {
      tag: 'Match',
      scrutinee: mkHoleTT('_scrutinee', mkHoleTT('_scrutinee_type', mkPropTT())),
      clauses: auxClauses,
    },
  };

  auxiliaries.push(auxDecl);

  // Create the call to the auxiliary function
  // auxName arg1 arg2 ... scrutinee1 scrutinee2 ...
  //
  // The arguments are:
  // 1. Variables bound by functionPatterns (in de Bruijn order)
  // 2. The scrutinee expressions
  //
  // For pattern variables, we need to build Var references.
  // The functionPatterns bind variables that are in scope.
  // We need to pass these as arguments to the auxiliary.
  let call: TTerm = mkConstTT(auxName);

  // Count variables bound by function patterns
  const numPatternVars = countPatternVars(functionPatterns);

  // Add pattern variable arguments (in reverse de Bruijn order: highest index first)
  // Actually, we pass them in declaration order, which means index numPatternVars-1 down to 0
  for (let i = numPatternVars - 1; i >= 0; i--) {
    call = mkAppTT(call, mkVarTT(i));
  }

  // Add scrutinee arguments
  for (const scrutinee of scrutinees) {
    call = mkAppTT(call, scrutinee);
  }

  // Wrap the call in a Match to preserve the pattern bindings for the main function
  // This is essential because the patterns introduce variable bindings that the call uses
  const mainMatch: TTerm = {
    tag: 'Match',
    scrutinee: mkHoleTT('_scrutinee', mkHoleTT('_scrutinee_type', mkPropTT())),
    clauses: [{
      patterns: functionPatterns,
      namedPatterns: withClause.functionNamedPatterns,
      rhs: call
    }]
  };

  return mainMatch;
}

/**
 * Count the number of variables bound by a list of patterns.
 */
function countPatternVars(patterns: TPattern[]): number {
  let count = 0;
  for (const p of patterns) {
    count += countSinglePatternVars(p);
  }
  return count;
}

function countSinglePatternVars(p: TPattern): number {
  switch (p.tag) {
    case 'PVar':
      return 1;
    case 'PWild':
      return 1; // Wildcards also bind
    case 'PCtor':
      return p.args.reduce((acc, arg) => acc + countSinglePatternVars(arg), 0);
    default:
      return 0;
  }
}

/**
 * Compute the type for an auxiliary with-function.
 *
 * Given a main function type like `(n : Nat) -> Bool` and scrutinees,
 * compute the auxiliary function's type.
 *
 * Example:
 *   Main type: Nat -> Bool
 *   Function patterns: [n]
 *   Scrutinees: [n]
 *   Result: Nat -> Nat -> Bool
 *
 * The auxiliary takes:
 * 1. The function pattern arguments (extracted from main type)
 * 2. The scrutinee arguments (their types are looked up from pattern arg types)
 */
function computeAuxiliaryType(
  declType: TTerm | undefined,
  functionPatterns: TPattern[],
  scrutinees: TTerm[]
): TTerm | undefined {
  if (!declType) {
    return undefined;
  }

  // Extract argument types and return type from the main function type
  const { argTypes, returnType } = extractFunctionType(declType);

  // Count how many variables are bound by the function patterns
  const numPatternVars = countPatternVars(functionPatterns);

  // We need at least as many argument types as pattern variables
  if (argTypes.length < numPatternVars) {
    return undefined;
  }

  // The function pattern argument types (first numPatternVars args)
  const patternArgTypes = argTypes.slice(0, numPatternVars);

  // Compute scrutinee types
  // If a scrutinee is a Var referencing a pattern-bound variable, use that variable's type
  const scrutineeTypes: { name: string; type: TTerm }[] = [];
  for (let i = 0; i < scrutinees.length; i++) {
    const scrut = scrutinees[i];
    let scrutType: TTerm;

    if (scrut.tag === 'Var') {
      // Look up the type from the pattern argument types
      // scrut.index is relative to the current scope (pattern variables)
      // index 0 = most recently bound (last pattern var)
      // We need to map this to patternArgTypes which are in declaration order
      const patternVarIndex = numPatternVars - 1 - scrut.index;
      if (patternVarIndex >= 0 && patternVarIndex < patternArgTypes.length) {
        scrutType = patternArgTypes[patternVarIndex].type;
      } else {
        // Fallback: use a hole for unknown type
        scrutType = mkHoleTT(`_scrut${i}_type`, mkPropTT());
      }
    } else {
      // For non-variable scrutinees, use a hole (will be inferred)
      scrutType = mkHoleTT(`_scrut${i}_type`, mkPropTT());
    }

    scrutineeTypes.push({ name: `_scrut${i}`, type: scrutType });
  }

  // Build the auxiliary function type:
  // patternArg1 -> ... -> patternArgN -> scrutinee1 -> ... -> scrutineeM -> returnType
  let auxType = returnType;

  // Add scrutinee types (in reverse order since we're building from the end)
  for (let i = scrutineeTypes.length - 1; i >= 0; i--) {
    auxType = mkPiTT(scrutineeTypes[i].type, auxType, scrutineeTypes[i].name);
  }

  // Add pattern argument types (in reverse order)
  for (let i = patternArgTypes.length - 1; i >= 0; i--) {
    auxType = mkPiTT(patternArgTypes[i].type, auxType, patternArgTypes[i].name);
  }

  return auxType;
}

/**
 * Extract argument types and return type from a function type.
 * Returns { argTypes, returnType } where argTypes is a list of { name, type } pairs.
 */
function extractFunctionType(type: TTerm): {
  argTypes: { name: string; type: TTerm }[];
  returnType: TTerm;
} {
  const argTypes: { name: string; type: TTerm }[] = [];

  let current = type;
  while (current.tag === 'Binder' && current.binderKind.tag === 'BPiTT') {
    argTypes.push({
      name: current.name || '_',
      type: current.domain!,
    });
    current = current.body;
  }

  return { argTypes, returnType: current };
}
