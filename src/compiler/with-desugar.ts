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
    // Main decl first, auxiliaries after. The caller (compile.ts) handles
    // the correct processing order (pre-register main type, process auxiliaries first)
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
  // Note: function patterns may include constructors (e.g., Zero) from the parent
  // clause. This makes the auxiliary "partial" in that it only handles the specific
  // constructor case from the parent. Totality checking is skipped for auxiliaries.
  const auxClauses: TClause[] = withClause.clauses.map(clause => ({
    patterns: [...functionPatterns, ...clause.patterns],
    rhs: clause.rhs,
    namedPatterns: withClause.functionNamedPatterns,
  }));

  // Compute the auxiliary function type from the main declaration's type
  // The auxiliary takes: (1) bound variable args, (2) scrutinee args
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

  // Recursively desugar nested WithClauses in the auxiliary's clause RHS values.
  // This handles arbitrary nesting depth (with inside with inside with...).
  if (containsWithClause(auxDecl.value!)) {
    const nestedResult = desugarDeclaration(auxDecl);
    // Push nested auxiliaries FIRST so they are processed before callers
    auxiliaries.push(...nestedResult.auxiliaries);
    auxiliaries.push(nestedResult.mainDecl);
  } else {
    auxiliaries.push(auxDecl);
  }

  // Create the call to the auxiliary function
  // auxName patternArg1 patternArg2 ... scrutinee1 scrutinee2 ...
  //
  // Each function pattern is converted back to a term:
  //   PVar(n) → Var(index)
  //   PCtor("Zero", []) → Const("Zero")
  //   PCtor("Succ", [PVar(m)]) → App(Const("Succ"), Var(index))
  //   PWild → Var(index)
  let call: TTerm = mkConstTT(auxName);

  // Convert function patterns to terms for the call arguments
  const numPatternVars = countPatternVars(functionPatterns);
  let varIndex = numPatternVars; // Start from highest, counting down
  const patternArgs = patternsToTerms(functionPatterns, varIndex);
  for (const arg of patternArgs) {
    call = mkAppTT(call, arg);
  }

  // Add scrutinee arguments
  for (const scrutinee of scrutinees) {
    call = mkAppTT(call, scrutinee);
  }

  // Return the call directly. The WithClause is always nested inside a Match clause
  // (the parser wraps it), so the outer clause already provides pattern bindings.
  // The Var indices in `call` reference those same bindings.
  return call;
}

/**
 * Convert a list of patterns to a list of terms.
 * Used to generate arguments for the auxiliary function call.
 *
 * Variables are assigned de Bruijn indices counting down from `nextIndex`.
 * Constructor patterns become constructor applications.
 *
 * Returns the list of terms (one per top-level pattern position).
 */
function patternsToTerms(patterns: TPattern[], nextIndex: number): TTerm[] {
  const result: TTerm[] = [];
  // We need to assign de Bruijn indices to bound variables in left-to-right,
  // depth-first order. The first variable gets the highest index.
  let idx = nextIndex;
  for (const p of patterns) {
    const { term, newIdx } = patternToTerm(p, idx);
    result.push(term);
    idx = newIdx;
  }
  return result;
}

function patternToTerm(pattern: TPattern, nextIndex: number): { term: TTerm; newIdx: number } {
  switch (pattern.tag) {
    case 'PVar':
    case 'PWild': {
      // Variables are assigned de Bruijn indices counting down
      const idx = nextIndex - 1;
      return { term: mkVarTT(idx), newIdx: idx };
    }
    case 'PCtor': {
      // Constructor pattern: build App(App(Const(name), arg1), arg2) ...
      let term: TTerm = mkConstTT(pattern.name);
      let idx = nextIndex;
      for (const arg of pattern.args) {
        const { term: argTerm, newIdx } = patternToTerm(arg, idx);
        term = mkAppTT(term, argTerm);
        idx = newIdx;
      }
      return { term, newIdx: idx };
    }
    default:
      return { term: mkConstTT('_unknown'), newIdx: nextIndex };
  }
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
 * Uses a splice approach: walks the original type tree to find the splice point
 * (after consuming enough explicit args for the function patterns), then inserts
 * scrutinee types before the return type. This preserves all de Bruijn indices
 * in the prefix because we reuse the original type tree nodes.
 *
 * For variable scrutinees, we copy the type of the corresponding binder,
 * shifted to account for the binder depth difference.
 *
 * Example:
 *   Main type: {A : Type} -> List A -> Nat
 *   Function patterns: [xs] (1 explicit arg)
 *   Scrutinees: [xs]
 *   Result: {A : Type} -> List A -> List A -> Nat
 */
function computeAuxiliaryType(
  declType: TTerm | undefined,
  functionPatterns: TPattern[],
  scrutinees: TTerm[]
): TTerm | undefined {
  if (!declType) {
    return undefined;
  }

  // Use the number of PATTERNS (not bound vars) to determine how many
  // explicit type args to consume, since the auxiliary function takes
  // ALL function pattern args (including constructor patterns).
  const numPatterns = functionPatterns.length;
  const numPatternVars = countPatternVars(functionPatterns);

  // First, collect info about binders by walking the type
  const binderInfo = collectBinderInfo(declType, numPatterns);

  // Compute scrutinee types
  const scrutineeTypes: TTerm[] = [];
  for (let i = 0; i < scrutinees.length; i++) {
    const scrut = scrutinees[i];
    if (scrut.tag === 'Var') {
      // Look up the type from the explicit argument binders
      // scrut.index counts from most recently bound (0 = last pattern var)
      const patternVarIndex = numPatternVars - 1 - scrut.index;
      if (patternVarIndex >= 0 && patternVarIndex < binderInfo.explicitDomains.length) {
        const { domain, depth } = binderInfo.explicitDomains[patternVarIndex];
        // Shift the domain type to account for the binders between its
        // original position and the splice point (after all prefix binders)
        const shift = binderInfo.totalPrefixDepth - depth;
        scrutineeTypes.push(shiftVars(domain, shift));
      } else {
        scrutineeTypes.push(mkHoleTT(`_scrut${i}_type`, mkPropTT()));
      }
    } else {
      scrutineeTypes.push(mkHoleTT(`_scrut${i}_type`, mkPropTT()));
    }
  }

  // Splice scrutinee types into the original type at the splice point
  return spliceScrutineesIntoType(declType, numPatterns, scrutineeTypes);
}

/**
 * Collect information about binders in a Pi-type chain.
 * Returns the domains of explicit binders along with their depth,
 * plus the total depth of the prefix (all binders consumed).
 */
function collectBinderInfo(type: TTerm, numExplicitNeeded: number): {
  explicitDomains: { domain: TTerm; depth: number }[];
  totalPrefixDepth: number;
} {
  const explicitDomains: { domain: TTerm; depth: number }[] = [];
  let current = type;
  let depth = 0;
  let explicitCount = 0;

  while (explicitCount < numExplicitNeeded) {
    if (current.tag === 'Binder' && current.binderKind.tag === 'BPiTT') {
      const isNamed = !!(current as any).named;
      if (!isNamed) {
        explicitDomains.push({ domain: current.domain!, depth });
        explicitCount++;
      }
      depth++;
      current = current.body;
    } else if (current.tag === 'MultiBinder' && current.binderKind.tag === 'BPiTT') {
      const isNamed = !!(current as any).named;
      for (const _name of current.names) {
        if (!isNamed) {
          explicitDomains.push({ domain: current.domain, depth });
          explicitCount++;
        }
        depth++;
      }
      current = current.body;
    } else {
      break;
    }
  }

  return { explicitDomains, totalPrefixDepth: depth };
}

/**
 * Shift all free Var indices in a TTerm by the given amount.
 * Variables with index >= cutoff are shifted; those below cutoff are bound.
 */
function shiftVars(term: TTerm, amount: number, cutoff: number = 0): TTerm {
  if (amount === 0) return term;

  switch (term.tag) {
    case 'Var':
      if (term.index >= cutoff) {
        return { ...term, index: term.index + amount };
      }
      return term;

    case 'App': {
      const newFn = shiftVars(term.fn, amount, cutoff);
      const newArg = shiftVars(term.arg, amount, cutoff);
      if (newFn === term.fn && newArg === term.arg) return term;
      return { ...term, fn: newFn, arg: newArg };
    }

    case 'Binder': {
      const newDomain = term.domain ? shiftVars(term.domain, amount, cutoff) : undefined;
      const newBody = shiftVars(term.body, amount, cutoff + 1);
      if (newDomain === term.domain && newBody === term.body) return term;
      return { ...term, domain: newDomain, body: newBody };
    }

    case 'MultiBinder': {
      const newDomain = shiftVars(term.domain, amount, cutoff);
      const newBody = shiftVars(term.body, amount, cutoff + term.names.length);
      if (newDomain === term.domain && newBody === term.body) return term;
      return { ...term, domain: newDomain, body: newBody };
    }

    case 'Match': {
      const newScrutinee = shiftVars(term.scrutinee, amount, cutoff);
      const newClauses = term.clauses.map(c => ({
        ...c,
        rhs: shiftVars(c.rhs, amount, cutoff + countPatternVars(c.patterns)),
      }));
      return { tag: 'Match', scrutinee: newScrutinee, clauses: newClauses };
    }

    case 'Annot': {
      const newTerm = shiftVars(term.term, amount, cutoff);
      const newType = shiftVars(term.type, amount, cutoff);
      if (newTerm === term.term && newType === term.type) return term;
      return { tag: 'Annot', term: newTerm, type: newType };
    }

    case 'Hole': {
      const newType = shiftVars(term.type, amount, cutoff);
      if (newType === term.type) return term;
      return { ...term, type: newType };
    }

    default:
      // Const, Prop, ULevelLit, etc. have no variables
      return term;
  }
}

/**
 * Walk a Pi-type chain, counting explicit (non-implicit) binders consumed.
 * After consuming `numExplicit` explicit binders, splice in the given
 * scrutinee types as new Pi binders before the remaining return type.
 *
 * This preserves de Bruijn indices in the prefix because we reuse the
 * original type nodes - we only modify the "tail" of the Pi chain.
 */
function spliceScrutineesIntoType(
  type: TTerm,
  numExplicit: number,
  scrutineeTypes: TTerm[]
): TTerm {
  // Base case: we've consumed all required explicit args, splice here
  if (numExplicit <= 0) {
    // Shift free variables in the return type to account for the new scrutinee binders
    let result = shiftVars(type, scrutineeTypes.length);
    // Add in reverse so they appear in order
    for (let i = scrutineeTypes.length - 1; i >= 0; i--) {
      result = mkPiTT(scrutineeTypes[i], result, `_scrut${i}`);
    }
    return result;
  }

  // Recursive case: walk through Pi binders
  if (type.tag === 'Binder' && type.binderKind.tag === 'BPiTT') {
    const isNamed = !!(type as any).named;
    const consumed = isNamed ? 0 : 1;
    const newBody = spliceScrutineesIntoType(type.body, numExplicit - consumed, scrutineeTypes);
    if (newBody === type.body) return type;
    return { ...type, body: newBody };
  }

  if (type.tag === 'MultiBinder' && type.binderKind.tag === 'BPiTT') {
    const isNamed = !!(type as any).named;
    const consumed = isNamed ? 0 : type.names.length;
    const newBody = spliceScrutineesIntoType(type.body, numExplicit - consumed, scrutineeTypes);
    if (newBody === type.body) return type;
    return { ...type, body: newBody };
  }

  // If we run out of Pi binders before consuming enough explicit args,
  // just splice here (best effort)
  let result = shiftVars(type, scrutineeTypes.length);
  for (let i = scrutineeTypes.length - 1; i >= 0; i--) {
    result = mkPiTT(scrutineeTypes[i], result, `_scrut${i}`);
  }
  return result;
}
