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
/**
 * Check if all function patterns are "simple" for Agda-style desugaring:
 * each pattern is either a PVar/PWild, or a PCtor with exactly one PVar/PWild arg.
 * This ensures the number of inner vars equals the number of patterns (no binder count change).
 */
function hasOnlySimplePatterns(patterns: TPattern[]): boolean {
  return patterns.every(p =>
    p.tag === 'PVar' || p.tag === 'PWild' ||
    (p.tag === 'PCtor' && p.args.length === 1 &&
      (p.args[0].tag === 'PVar' || p.args[0].tag === 'PWild'))
  );
}

/**
 * Check if any function pattern is a constructor (not just a variable).
 */
function hasConstructorPatterns(patterns: TPattern[]): boolean {
  return patterns.some(p => p.tag === 'PCtor');
}

/**
 * Extract inner variable patterns from function patterns.
 * For PVar/PWild: returns the pattern as-is.
 * For PCtor with 1 arg: returns the inner PVar/PWild.
 * Only valid when hasOnlySimplePatterns is true.
 */
function extractInnerPatterns(patterns: TPattern[]): TPattern[] {
  return patterns.map(p => {
    if (p.tag === 'PCtor' && p.args.length === 1) {
      return p.args[0];
    }
    return p;
  });
}

function desugarWithClause(
  withClause: TWithClause,
  baseName: string,
  declType: TTerm | undefined,
  auxiliaries: ParsedDeclaration[]
): TTerm {
  const auxName = freshWithName(baseName);
  const functionPatterns = withClause.functionPatterns;
  const scrutinees = withClause.scrutinees;



  // Determine if we should use Agda-style desugaring for constructor function patterns.
  // When function patterns contain constructors (like Succ x) and the return type may
  // be dependent, we need to:
  // 1. Pass inner vars (x, y) instead of constructor-wrapped terms (Succ x, Succ y)
  // 2. Use PVar clause patterns instead of constructor patterns
  // 3. Substitute pattern reconstructions into the return type
  // This avoids a type mismatch between scrutinee type and auxiliary instantiation.
  const useAgdaStyle = hasConstructorPatterns(functionPatterns) && hasOnlySimplePatterns(functionPatterns);
  const effectiveClausePatterns = useAgdaStyle
    ? extractInnerPatterns(functionPatterns)
    : functionPatterns;

  // Create auxiliary function clauses
  // If a clause has refinedFunctionPatterns (Agda-style LHS refinement), use those
  // instead of the default effectiveClausePatterns.
  const auxClauses: TClause[] = withClause.clauses.map(clause => ({
    patterns: [...(clause.refinedFunctionPatterns ?? effectiveClausePatterns), ...clause.patterns],
    rhs: clause.rhs,
    namedPatterns: withClause.functionNamedPatterns,
  }));

  // Compute the auxiliary function type from the main declaration's type
  // The auxiliary takes: (1) bound variable args, (2) scrutinee args
  // and returns the main function's return type (with pattern reconstructions substituted)
  const auxType = computeAuxiliaryType(declType, functionPatterns, scrutinees, useAgdaStyle, baseName);

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
    withScrutineeCount: scrutinees.length,
    withScrutineeExprs: scrutinees,
    withFunctionPatterns: functionPatterns,
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
  let call: TTerm = mkConstTT(auxName);

  const numPatternVars = countPatternVars(functionPatterns);
  let varIndex = numPatternVars;

  if (useAgdaStyle) {
    // Agda-style: pass inner vars directly, not constructor-wrapped terms.
    // For PVar: same as before (just the var).
    // For PCtor("Succ", [PVar x]): pass x (the inner var), not Succ(x).
    // Since hasOnlySimplePatterns guarantees each pattern has exactly 1 inner var,
    // the var index assignment is the same as for PVar patterns.
    for (const _pat of functionPatterns) {
      const idx = varIndex - 1;
      call = mkAppTT(call, mkVarTT(idx));
      varIndex = idx;
    }
  } else {
    // Original style: pass reconstructed pattern terms
    const patternArgs = patternsToTerms(functionPatterns, varIndex);
    for (const arg of patternArgs) {
      call = mkAppTT(call, arg);
    }
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
/**
 * Check if a scrutinee expression is a self-recursive call to the function being defined.
 * Extracts the head of an application spine and checks if it's Const(declName).
 */
function isSelfRecursiveCall(scrut: TTerm, declName: string): boolean {
  let head = scrut;
  while (head.tag === 'App') {
    head = head.fn;
  }
  return head.tag === 'Const' && head.name === declName;
}

function computeAuxiliaryType(
  declType: TTerm | undefined,
  functionPatterns: TPattern[],
  scrutinees: TTerm[],
  useAgdaStyle: boolean = false,
  declName?: string
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
    } else if (declName && isSelfRecursiveCall(scrut, declName)) {
      // For self-recursive calls (e.g., `leqCanonical pleq qleq`), use the
      // function's own return type. This preserves the connection between the
      // scrutinee result and the pattern variables, enabling pattern refinement
      // (e.g., matching `refl` on `Equal p q` unifies p and q).
      scrutineeTypes.push(binderInfo.returnType);
    } else {
      // For other expression scrutinees (e.g., `leq x y`, `compare a b`),
      // use a Hole. The type checker infers the type from with-clause patterns.
      scrutineeTypes.push(mkHoleTT(`_scrut${i}_type`, mkPropTT()));
    }
  }

  // Build reconstruction map for Agda-style: maps de Bruijn index in return type
  // to the reconstruction term (e.g., Var 1 → App(Const("Succ"), Var 1))
  const reconstructionMap: Map<number, TTerm> | undefined = useAgdaStyle
    ? buildReconstructionMap(functionPatterns, binderInfo)
    : undefined;

  // Splice scrutinee types into the original type at the splice point
  return spliceScrutineesIntoType(declType, numPatterns, scrutineeTypes, scrutinees, reconstructionMap);
}

/**
 * Build a map from de Bruijn index (in the return type context) to reconstruction term.
 * Only creates entries for constructor patterns (PVar patterns are identity).
 *
 * For example, with patterns [Succ(PVar x), Succ(PVar y)] and totalPrefixDepth=2:
 *   Var 1 (first binder) → App(Const("Succ"), Var 1)
 *   Var 0 (second binder) → App(Const("Succ"), Var 0)
 */
function buildReconstructionMap(
  functionPatterns: TPattern[],
  binderInfo: { explicitDomains: { domain: TTerm; depth: number }[]; totalPrefixDepth: number }
): Map<number, TTerm> {
  const map = new Map<number, TTerm>();
  let explicitIdx = 0;

  for (const pattern of functionPatterns) {
    if (explicitIdx >= binderInfo.explicitDomains.length) break;
    const { depth } = binderInfo.explicitDomains[explicitIdx];
    // De Bruijn index of this binder from the return type perspective
    const varIdx = binderInfo.totalPrefixDepth - 1 - depth;

    if (pattern.tag === 'PCtor' && pattern.args.length === 1) {
      // Reconstruction: wrap the inner var in the constructor
      // The inner var has the same de Bruijn index (since binder count is preserved)
      let term: TTerm = mkConstTT(pattern.name);
      term = mkAppTT(term, mkVarTT(varIdx));
      map.set(varIdx, term);
    }
    // PVar/PWild: identity mapping, no entry needed

    explicitIdx++;
  }

  return map;
}

/**
 * Collect information about binders in a Pi-type chain.
 * Returns the domains of explicit binders along with their depth,
 * plus the total depth of the prefix (all binders consumed).
 */
function collectBinderInfo(type: TTerm, numExplicitNeeded: number): {
  explicitDomains: { domain: TTerm; depth: number }[];
  totalPrefixDepth: number;
  returnType: TTerm;
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

  return { explicitDomains, totalPrefixDepth: depth, returnType: current };
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
  scrutineeTypes: TTerm[],
  scrutinees: TTerm[],
  reconstructionMap?: Map<number, TTerm>
): TTerm {
  // Base case: we've consumed all required explicit args, splice here
  if (numExplicit <= 0) {
    let result = type;

    // Apply pattern reconstruction substitution for Agda-style desugaring.
    // This transforms the return type to use constructor-wrapped references
    // e.g., DecEq (Var 1) (Var 0) → DecEq (Succ (Var 1)) (Succ (Var 0))
    if (reconstructionMap && reconstructionMap.size > 0) {
      result = applySimultaneousSubst(result, reconstructionMap);
    }

    // WITH-ABSTRACTION: For each scrutinee, replace occurrences in the return type
    // Process in reverse order so indices remain correct
    for (let i = scrutineeTypes.length - 1; i >= 0; i--) {
      const scrut = scrutinees[i];
      const scrutType = scrutineeTypes[i];

      // Only abstract over variable scrutinees for now
      // (Complex expression abstraction is future work)
      if (scrut.tag === 'Var') {
        // Replace all occurrences of this variable with Var 0 (the fresh binder)
        // This also shifts other free variables
        result = replaceScrutineeInTTerm(result, scrut);
      } else {
        // For non-variable scrutinees, just shift free vars (no abstraction)
        result = shiftVars(result, 1);
      }

      // Add the scrutinee binder
      result = mkPiTT(scrutType, result, `_scrut${i}`);
    }

    return result;
  }

  // Recursive case: walk through Pi binders
  if (type.tag === 'Binder' && type.binderKind.tag === 'BPiTT') {
    const isNamed = !!(type as any).named;
    const consumed = isNamed ? 0 : 1;
    const newBody = spliceScrutineesIntoType(type.body, numExplicit - consumed, scrutineeTypes, scrutinees, reconstructionMap);
    if (newBody === type.body) return type;
    return { ...type, body: newBody };
  }

  if (type.tag === 'MultiBinder' && type.binderKind.tag === 'BPiTT') {
    const isNamed = !!(type as any).named;
    const consumed = isNamed ? 0 : type.names.length;
    const newBody = spliceScrutineesIntoType(type.body, numExplicit - consumed, scrutineeTypes, scrutinees, reconstructionMap);
    if (newBody === type.body) return type;
    return { ...type, body: newBody };
  }

  // If we run out of Pi binders before consuming enough explicit args,
  // just splice here (best effort)
  let result = type;
  if (reconstructionMap && reconstructionMap.size > 0) {
    result = applySimultaneousSubst(result, reconstructionMap);
  }

  // WITH-ABSTRACTION: same logic as base case
  for (let i = scrutineeTypes.length - 1; i >= 0; i--) {
    const scrut = scrutinees[i];
    const scrutType = scrutineeTypes[i];

    if (scrut.tag === 'Var') {
      result = replaceScrutineeInTTerm(result, scrut);
    } else {
      result = shiftVars(result, 1);
    }

    result = mkPiTT(scrutType, result, `_scrut${i}`);
  }

  return result;
}

/**
 * Apply a simultaneous substitution to a surface term.
 * The substMap maps de Bruijn indices to replacement terms.
 * Only substitutes exact Var matches; the replacement terms are NOT recursively substituted.
 */
function applySimultaneousSubst(
  term: TTerm,
  substMap: Map<number, TTerm>,
  cutoff: number = 0
): TTerm {
  switch (term.tag) {
    case 'Var': {
      if (term.index >= cutoff) {
        const replacement = substMap.get(term.index - cutoff);
        if (replacement !== undefined) {
          return shiftVars(replacement, cutoff);
        }
      }
      return term;
    }

    case 'App': {
      const newFn = applySimultaneousSubst(term.fn, substMap, cutoff);
      const newArg = applySimultaneousSubst(term.arg, substMap, cutoff);
      if (newFn === term.fn && newArg === term.arg) return term;
      return { ...term, fn: newFn, arg: newArg };
    }

    case 'Binder': {
      const newDomain = term.domain ? applySimultaneousSubst(term.domain, substMap, cutoff) : undefined;
      const newBody = applySimultaneousSubst(term.body, substMap, cutoff + 1);
      if (newDomain === term.domain && newBody === term.body) return term;
      return { ...term, domain: newDomain, body: newBody };
    }

    case 'MultiBinder': {
      const newDomain = applySimultaneousSubst(term.domain, substMap, cutoff);
      const newBody = applySimultaneousSubst(term.body, substMap, cutoff + term.names.length);
      if (newDomain === term.domain && newBody === term.body) return term;
      return { ...term, domain: newDomain, body: newBody };
    }

    case 'Annot': {
      const newTerm = applySimultaneousSubst(term.term, substMap, cutoff);
      const newType = applySimultaneousSubst(term.type, substMap, cutoff);
      if (newTerm === term.term && newType === term.type) return term;
      return { tag: 'Annot', term: newTerm, type: newType };
    }

    case 'Hole': {
      const newType = applySimultaneousSubst(term.type, substMap, cutoff);
      if (newType === term.type) return term;
      return { ...term, type: newType };
    }

    case 'Match': {
      const newScrutinee = applySimultaneousSubst(term.scrutinee, substMap, cutoff);
      const newClauses = term.clauses.map(c => ({
        ...c,
        rhs: applySimultaneousSubst(c.rhs, substMap, cutoff + countPatternVars(c.patterns)),
      }));
      return { tag: 'Match', scrutinee: newScrutinee, clauses: newClauses };
    }

    default:
      // Const, Prop, ULevelLit, etc.
      return term;
  }
}

/**
 * Check if two TTerms are structurally equal (for with-abstraction).
 * Used to find occurrences of scrutinee in the return type.
 */
function termsEqualTTerm(term1: TTerm, term2: TTerm, depth: number = 0): boolean {
  if (term1.tag !== term2.tag) return false;

  switch (term1.tag) {
    case 'Var':
      return term2.tag === 'Var' && term1.index === term2.index;

    case 'Const':
      return term2.tag === 'Const' && term1.name === term2.name;

    case 'App':
      return term2.tag === 'App' &&
        termsEqualTTerm(term1.fn, term2.fn, depth) &&
        termsEqualTTerm(term1.arg, term2.arg, depth);

    case 'Binder':
      if (term2.tag !== 'Binder') return false;
      // Simplified: just check binderKind tags match
      if (term1.binderKind.tag !== term2.binderKind.tag) return false;
      // Domain might be undefined for let without type annotation
      if (!term1.domain && !term2.domain) {
        return termsEqualTTerm(term1.body, term2.body, depth + 1);
      }
      if (!term1.domain || !term2.domain) {
        return false;
      }
      return termsEqualTTerm(term1.domain, term2.domain, depth) &&
        termsEqualTTerm(term1.body, term2.body, depth + 1);

    case 'MultiBinder':
      if (term2.tag !== 'MultiBinder') return false;
      if (term1.names.length !== term2.names.length) return false;
      if (term1.binderKind.tag !== term2.binderKind.tag) return false;
      return termsEqualTTerm(term1.domain, term2.domain, depth) &&
        termsEqualTTerm(term1.body, term2.body, depth + term1.names.length);

    case 'Sort':
    case 'ULevel':
    case 'UOmega':
      return true;

    case 'Hole':
      return term2.tag === 'Hole' && term1.id === term2.id;

    case 'Annot':
      return term2.tag === 'Annot' &&
        termsEqualTTerm(term1.term, term2.term, depth) &&
        termsEqualTTerm(term1.type, term2.type, depth);

    case 'Match':
      // Simplified: just check scrutinee
      return term2.tag === 'Match' && termsEqualTTerm(term1.scrutinee, term2.scrutinee, depth);

    case 'AbsurdMarker':
    case 'WithClause':
    case 'TacticBlock':
      // These shouldn't appear in return types, but handle them conservatively
      return false;

    // For other terms, conservatively return false
    default:
      return false;
  }
}

/**
 * Replace all occurrences of scrutinee with a fresh variable (Var 0),
 * and shift other free variables to account for the new binder.
 *
 * This implements with-abstraction for TTerm.
 */
function replaceScrutineeInTTerm(
  term: TTerm,
  scrutinee: TTerm,
  depth: number = 0
): TTerm {
  // Check if this term matches the scrutinee
  if (termsEqualTTerm(term, scrutinee, depth)) {
    // Replace with Var 0 (adjusted for depth)
    return mkVarTT(depth);
  }

  // Otherwise, recurse and shift free variables
  switch (term.tag) {
    case 'Var':
      // Shift free variables to account for new binder
      return mkVarTT(term.index + 1);

    case 'Const':
    case 'Sort':
    case 'ULevel':
    case 'ULit':
    case 'UOmega':
    case 'Hole':
    case 'AbsurdMarker':
      return term;

    case 'App': {
      const newFn = replaceScrutineeInTTerm(term.fn, scrutinee, depth);
      const newArg = replaceScrutineeInTTerm(term.arg, scrutinee, depth);
      if (newFn === term.fn && newArg === term.arg) return term;
      return mkAppTT(newFn, newArg);
    }

    case 'Binder': {
      const newDomain = term.domain ? replaceScrutineeInTTerm(term.domain, scrutinee, depth) : undefined;
      const newBody = replaceScrutineeInTTerm(term.body, scrutinee, depth + 1);
      if (newDomain === term.domain && newBody === term.body) return term;
      return { ...term, domain: newDomain, body: newBody };
    }

    case 'MultiBinder': {
      const newDomain = replaceScrutineeInTTerm(term.domain, scrutinee, depth);
      const newBody = replaceScrutineeInTTerm(term.body, scrutinee, depth + term.names.length);
      if (newDomain === term.domain && newBody === term.body) return term;
      return { ...term, domain: newDomain, body: newBody };
    }

    case 'Annot': {
      const newTerm = replaceScrutineeInTTerm(term.term, scrutinee, depth);
      const newType = replaceScrutineeInTTerm(term.type, scrutinee, depth);
      if (newTerm === term.term && newType === term.type) return term;
      return { tag: 'Annot', term: newTerm, type: newType };
    }

    case 'Match': {
      const newScrutinee = replaceScrutineeInTTerm(term.scrutinee, scrutinee, depth);
      const newClauses = term.clauses.map(c => ({
        ...c,
        rhs: replaceScrutineeInTTerm(c.rhs, scrutinee, depth + countPatternVars(c.patterns))
      }));
      return { tag: 'Match', scrutinee: newScrutinee, clauses: newClauses };
    }

    case 'WithClause':
    case 'TacticBlock':
      // These shouldn't appear in return types during with-desugaring
      return term;

    default:
      return term;
  }
}
