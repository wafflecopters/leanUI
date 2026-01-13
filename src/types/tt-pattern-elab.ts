/**
 * Pattern Elaboration for Dependent Type Checking
 *
 * This module implements pattern matching type-checking based on
 * "Pattern Matching Without K" (Cockx et al., ICFP 2014).
 *
 * Core algorithm:
 * 1. For each pattern, create fresh metavariables for unconstrained parts (wildcards)
 * 2. Unify the constructor's return type with the expected type
 * 3. This unification may solve metavariables and refine types
 * 4. After all patterns are elaborated, zonk to apply all solutions
 *
 * Key invariants:
 * - All wildcards become fresh metavariables
 * - Constructor pattern elaboration UNIFIES constructor return type with expected type
 * - The refined type may be more specific than the expected type (from index unification)
 */

import {
  TTKTerm,
  TTKContext,
  TTKPattern,
  TTKClause,
  TTKBinding,
  mkVar,
  mkApp,
  mkConst,
  mkType,
  mkPi,
  subst,
  shiftTerm,
  prettyPrint,
  replaceVars,
} from './tt-kernel';
import { MetaContext } from './tt-meta';
import { TypeCheckError, lookupConstByName, extendContext, inferType, DefinitionsMap } from './tt-typecheck';
import { unifyTerms, Substitution, varKey } from './tt-unify';
import { IndexPath, appendPath, fieldSeg, arraySeg } from './source-position';
import { TPattern } from './tt-core';
import { buildStepperEnvironment } from './stepper-utils';
import { PatternElabStepper } from './pattern-elab-stepper';

// Browser-safe debug flag (set to true to enable debug logging)
const DEBUG_PATTERN_ELAB = typeof process !== 'undefined' && process.env?.DEBUG_PATTERN_ELAB === '1';

// ============================================================================
// Types
// ============================================================================

export interface ConstructorInfo {
  name: string;
  fullType: TTKTerm;
  inductiveTypeName: string;
  numParams: number;
}

export interface PatternElabResult {
  /** Bindings introduced by this pattern (in order, leftmost/outermost first) */
  bindings: Array<{ name: string; type: TTKTerm }>;
  /** The refined type after unification (may be more specific than input) */
  refinedType: TTKTerm;
  /** The term this pattern elaborates to (Var for variables, constructor application for ctors, meta for wildcards) */
  patternTerm: TTKTerm;
  /**
   * Index refinements from dependent pattern matching.
   * When matching a constructor like VNil against Vec A a, we learn a = Zero.
   * Maps De Bruijn index (in the expected type at this point) to the refined term.
   */
  indexRefinements: Map<number, TTKTerm>;
  /**
   * Metas that need to be solved to variable bindings.
   * For constructor patterns like (Succ p), we create a meta for the 'p' position
   * that needs to be connected to the actual binding. The localBindingIdx is the
   * index into the bindings array (0 = first binding).
   */
  nestedVarMetas?: Array<{ meta: TTKTerm; localBindingIdx: number }>;
}

export interface ClauseElabResult {
  /** All bindings from all patterns */
  bindings: Array<{ name: string; type: TTKTerm }>;
  /** The return type (after zonking) */
  returnType: TTKTerm;
}

/** Result of checking a single clause (for external callers) */
export interface ClauseCheckResult {
  returnType: TTKTerm;
  solvedBindings: Array<{ name: string; type: TTKTerm }>;
  substitution: Substitution;
}

/**
 * Complete pattern elaboration data for stepper visualization.
 * Contains all pre-computed information needed for the stepper.
 */
export interface PatternElabData {
  /** Per-clause elaboration results (solved bindings, return types) */
  clauseResults: ClauseCheckResult[];
  /** Totality checking split tree (for pattern match visualization) */
  splitTree: import('./ttk-totality-check').SplitTree;
  /** Missing pattern cases (non-exhaustive patterns) */
  missingCases: import('./ttk-totality-check').MissingPattern[][];
  /** Indices of inaccessible clauses (unreachable patterns) */
  inaccessibleClauses: number[];
  /** Constructor environment for stepper (eagerly computed) */
  stepperEnv: Map<string, import('./pattern-elab-stepper').ConstructorInfo>;
}

/** Error from checking a single clause */
export interface ClauseCheckError {
  clauseIndex: number;
  message: string;
  path: IndexPath;
  term?: TTKTerm;
  context?: TTKContext;
}

/** Result of checking all function clauses */
export interface FunctionClausesResult {
  clauses: ClauseCheckResult[];
  substitution: Substitution;
  /** Errors from clauses that failed (allows checking all clauses) */
  errors: ClauseCheckError[];
  /** Constructor environment used by stepper (for building patternData) */
  stepperEnv?: Map<string, import('./pattern-elab-stepper').ConstructorInfo>;
}

// ============================================================================
// Helper Functions
// ============================================================================

/**
 * Look up constructor information from context.
 */
export function lookupConstructor(name: string, ctx: TTKContext): ConstructorInfo | null {
  const type = lookupConstByName(ctx, name);
  if (DEBUG_PATTERN_ELAB) {
    console.log(`[DEBUG] lookupConstructor(${name}): type=${type ? prettyPrint(type) : 'null'}`);
  }
  if (!type) return null;

  const { returnType } = unwrapPi(type);
  const headName = getHeadName(returnType);
  if (DEBUG_PATTERN_ELAB) {
    console.log(`[DEBUG] lookupConstructor(${name}): returnType=${prettyPrint(returnType)}, headName=${headName}`);
  }
  if (!headName) return null;

  return {
    name,
    fullType: type,
    inductiveTypeName: headName,
    numParams: countParams(type),
  };
}

/**
 * Unwrap Pi binders to get telescope and return type.
 */
function unwrapPi(type: TTKTerm): { args: Array<{ name: string; type: TTKTerm }>; returnType: TTKTerm } {
  const args: Array<{ name: string; type: TTKTerm }> = [];
  let curr = type;
  while (curr.tag === 'Binder' && curr.binderKind.tag === 'BPi') {
    args.push({ name: curr.name, type: curr.domain });
    curr = curr.body;
  }
  return { args, returnType: curr };
}

/**
 * Unwrap exactly `count` Pi binders. Returns args, remaining type, and whether we hit the limit.
 * Used for curried definitions where the clause has fewer patterns than the full function type.
 */
function unwrapPiN(type: TTKTerm, count: number): { args: Array<{ name: string; type: TTKTerm }>; returnType: TTKTerm } {
  const args: Array<{ name: string; type: TTKTerm }> = [];
  let curr = type;
  while (args.length < count && curr.tag === 'Binder' && curr.binderKind.tag === 'BPi') {
    args.push({ name: curr.name, type: curr.domain });
    curr = curr.body;
  }
  return { args, returnType: curr };
}

/**
 * Get the head constant name from an applied type.
 */
function getHeadName(type: TTKTerm): string | null {
  let curr = type;
  while (curr.tag === 'App') curr = curr.fn;
  return curr.tag === 'Const' ? curr.name : null;
}

/**
 * Get the arguments from an applied type (Vec A n -> [A, n]).
 */
function getArgs(type: TTKTerm): TTKTerm[] {
  const args: TTKTerm[] = [];
  let curr = type;
  while (curr.tag === 'App') {
    args.unshift(curr.arg);
    curr = curr.fn;
  }
  return args;
}

/**
 * Substitute a term for a variable at a specific index.
 * Unlike regular subst, this doesn't decrement other indices.
 * Used for applying index refinements from dependent pattern matching.
 */
function substVarIfPresent(term: TTKTerm, varIndex: number, replacement: TTKTerm): TTKTerm {
  // Use regular substitution - it will replace Var(varIndex) with replacement
  // and decrement higher indices. For refinements, this is what we want.
  return subst(varIndex, replacement, term);
}

/**
 * Count the number of parameters (vs indices) in a constructor type.
 * Parameters are those that appear exactly once in the return type indices,
 * in the same position as their Pi binder.
 */
function countParams(ctorType: TTKTerm): number {
  const { args, returnType } = unwrapPi(ctorType);
  const indices = getArgs(returnType);
  let n = 0;
  for (let i = 0; i < args.length && i < indices.length; i++) {
    const idx = indices[i];
    // Check if index[i] is Var(args.length - 1 - i), i.e., refers to args[i]
    const expected = args.length - 1 - i;
    if (idx.tag === 'Var' && idx.index === expected) {
      // Also check it only appears once
      if (indices.filter(x => x.tag === 'Var' && x.index === expected).length === 1) {
        n++;
      } else break;
    } else break;
  }
  return n;
}

/**
 * Parallel substitution for telescope types.
 * At telescope position i, Var(k) refers to telescope[i - 1 - k].
 * We replace each Var(k) with zonkedMetas[i - 1 - k].
 *
 * Unlike normal subst, this does NOT decrement higher indices
 * because we're replacing ALL telescope variables simultaneously.
 */
function parallelSubstTelescope(term: TTKTerm, position: number, zonkedMetas: TTKTerm[]): TTKTerm {
  return parallelSubstHelper(term, position, zonkedMetas, 0);
}

function parallelSubstHelper(term: TTKTerm, position: number, zonkedMetas: TTKTerm[], depth: number): TTKTerm {
  switch (term.tag) {
    case 'Var': {
      // Only substitute if this is a reference to a telescope variable
      const varIndex = term.index - depth;  // Adjust for binders we've gone under
      if (varIndex >= 0 && varIndex < position) {
        // This Var refers to telescope[position - 1 - varIndex]
        const metaIndex = position - 1 - varIndex;
        // Shift the replacement to account for binders we've gone under
        return shiftTerm(zonkedMetas[metaIndex], depth, 0);
      }
      // Not a telescope reference - keep as is (or adjust if needed)
      return term;
    }

    case 'Sort':
      return term;

    case 'Const':
      return {
        tag: 'Const',
        name: term.name,
        type: parallelSubstHelper(term.type, position, zonkedMetas, depth)
      };

    case 'Binder': {
      const domain = parallelSubstHelper(term.domain, position, zonkedMetas, depth);
      const body = parallelSubstHelper(term.body, position, zonkedMetas, depth + 1);
      let binderKind = term.binderKind;
      if (binderKind.tag === 'BLet') {
        binderKind = { tag: 'BLet', defVal: parallelSubstHelper(binderKind.defVal, position, zonkedMetas, depth) };
      }
      return { tag: 'Binder', name: term.name, binderKind, domain, body };
    }

    case 'App':
      return {
        tag: 'App',
        fn: parallelSubstHelper(term.fn, position, zonkedMetas, depth),
        arg: parallelSubstHelper(term.arg, position, zonkedMetas, depth)
      };

    case 'Hole':
      return {
        tag: 'Hole',
        id: term.id,
        type: parallelSubstHelper(term.type, position, zonkedMetas, depth),
        context: term.context.map(b => ({
          name: b.name,
          type: parallelSubstHelper(b.type, position, zonkedMetas, depth)
        }))
      };

    case 'Annot':
      return {
        tag: 'Annot',
        term: parallelSubstHelper(term.term, position, zonkedMetas, depth),
        type: parallelSubstHelper(term.type, position, zonkedMetas, depth)
      };

    case 'Match':
      return {
        tag: 'Match',
        scrutinee: parallelSubstHelper(term.scrutinee, position, zonkedMetas, depth),
        clauses: term.clauses.map(c => ({
          patterns: c.patterns,
          rhs: parallelSubstHelper(c.rhs, position, zonkedMetas, depth)
        }))
      };
  }
}

/**
 * Count pattern variables in a pattern.
 */
export function countPatternVars(pattern: TTKPattern): number {
  switch (pattern.tag) {
    case 'PVar':
      return 1;
    case 'PCtor':
      return pattern.args.reduce((sum, arg) => sum + countPatternVars(arg), 0);
  }
}

/**
 * Extract pattern variable names from a pattern (in order).
 */
export function extractPatternVarNames(pattern: TTKPattern): string[] {
  switch (pattern.tag) {
    case 'PVar':
      return [pattern.name];
    case 'PCtor':
      return pattern.args.flatMap(extractPatternVarNames);
  }
}

// ============================================================================
// Pattern Elaboration
// ============================================================================

/**
 * Elaborate a pattern against an expected type.
 *
 * For wildcards (PVar with name "_"): creates a fresh metavariable
 * For variables (PVar): creates a binding with the expected type
 * For constructors (PCtor): unifies constructor return type with expected type
 */
export function elaboratePattern(
  pattern: TTKPattern,
  expectedType: TTKTerm,
  ctx: TTKContext,
  mctx: MetaContext,
  path: IndexPath = [],
  defs?: DefinitionsMap
): PatternElabResult {
  // Normalize the expected type first
  const normType = expectedType;  // TODO: whnf if needed

  switch (pattern.tag) {
    case 'PVar': {
      // Both wildcards and named variables create a binding
      // For wildcards, the pattern term is a fresh meta
      // For named variables, the pattern term is a Var (index will be assigned by caller)
      // Wildcards can be '_' or unique names like '_w0', '_w1' (from uniform parsing)
      if (pattern.name === '_' || pattern.name.startsWith('_w')) {
        // Wildcard: the binding exists for de Bruijn indexing,
        // but its value is unconstrained (may be solved by unification)
        // Normalize the display name to '_' for user readability
        const meta = mctx.fresh(normType, ctx);
        return {
          bindings: [{ name: '_', type: normType }],
          refinedType: normType,
          patternTerm: meta,
          indexRefinements: new Map()
        };
      }
      // Named variable: pattern term will be set by the caller based on binding index
      // For now, use a placeholder that will be replaced
      return {
        bindings: [{ name: pattern.name, type: normType }],
        refinedType: normType,
        patternTerm: mkVar(0),  // Placeholder - caller will compute actual index
        indexRefinements: new Map()
      };
    }

    case 'PCtor': {
      const ctor = lookupConstructor(pattern.name, ctx);
      if (!ctor) {
        // Not a known constructor - treat as a variable binding
        // This handles the case where type parameters look like constructors
        if (pattern.args.length === 0) {
          return {
            bindings: [{ name: pattern.name, type: normType }],
            refinedType: normType,
            patternTerm: mkVar(0),  // Placeholder - caller will compute actual index
            indexRefinements: new Map()
          };
        }
        throw new TypeCheckError(
          `Unknown constructor '${pattern.name}'`,
          undefined, ctx, path
        );
      }

      // Check that constructor is for the right type
      const expectedHead = getHeadName(normType);
      if (expectedHead !== ctor.inductiveTypeName) {
        throw new TypeCheckError(
          `Constructor '${pattern.name}' is for type '${ctor.inductiveTypeName}' but expected '${expectedHead}'`,
          undefined, ctx, path
        );
      }

      return elaborateCtorPattern(pattern, ctor, normType, ctx, mctx, path, defs);
    }
  }
}

/**
 * Elaborate a constructor pattern.
 *
 * The key operation is unifying the constructor's return type with the expected type.
 * This may:
 * - Solve metavariables (wildcards get concrete values)
 * - Create variable equations (two pattern vars are equal)
 * - Fail with an error (constructor impossible for this type)
 */
function elaborateCtorPattern(
  pattern: { tag: 'PCtor'; name: string; args: TTKPattern[] },
  ctor: ConstructorInfo,
  expectedType: TTKTerm,
  ctx: TTKContext,
  mctx: MetaContext,
  path: IndexPath,
  defs?: DefinitionsMap
): PatternElabResult {
  const { args: telescope, returnType: ctorReturnType } = unwrapPi(ctor.fullType);

  if (pattern.args.length !== telescope.length) {
    throw new TypeCheckError(
      `Constructor '${pattern.name}' expects ${telescope.length} arguments but pattern has ${pattern.args.length}`,
      undefined, ctx, path
    );
  }

  const expectedIndices = getArgs(expectedType);

  // 1. Create fresh metas for each constructor argument
  // These represent "what values could fill these positions?"
  const argMetas: TTKTerm[] = [];
  let telescopeCtx = ctx;
  for (let i = 0; i < telescope.length; i++) {
    // The type of each telescope arg may depend on previous args
    let argType = telescope[i].type;
    // Substitute previous metas into the type
    for (let j = 0; j < i; j++) {
      argType = subst(i - 1 - j, argMetas[j], argType);
    }
    const meta = mctx.fresh(argType, telescopeCtx);
    argMetas.push(meta);
    telescopeCtx = extendContext(telescopeCtx, telescope[i].name, argType);
  }

  // 2. Build the instantiated return type: substitute metas into ctorReturnType
  let instantiatedReturn = ctorReturnType;
  for (let i = telescope.length - 1; i >= 0; i--) {
    instantiatedReturn = subst(0, argMetas[i], instantiatedReturn);
  }

  // 3. UNIFY instantiated return type with expected type
  // This is where the magic happens - unification may solve our metas
  if (DEBUG_PATTERN_ELAB) {
    console.log(`[DEBUG] Unifying: ${prettyPrint(instantiatedReturn)} =?= ${prettyPrint(expectedType)}`);
    console.log(`[DEBUG] argMetas:`, argMetas.map((m, i) => `${telescope[i].name}: ${prettyPrint(m)}`));
  }
  const unifyResult = unifyTerms(instantiatedReturn, expectedType, mkType(0), ctx, { definitions: defs });
  if (DEBUG_PATTERN_ELAB) {
    console.log(`[DEBUG] Unify result:`, unifyResult.tag);
    if (unifyResult.tag === 'success') {
      console.log(`[DEBUG] Substitution:`, Array.from(unifyResult.substitution.entries()).map(([k, v]) => `${k} -> ${prettyPrint(v)}`));
    }
  }
  if (unifyResult.tag === 'failure' || unifyResult.tag === 'stuck') {
    throw new TypeCheckError(
      `Constructor '${pattern.name}' cannot match expected type '${prettyPrint(expectedType)}': ${unifyResult.reason}`,
      undefined, ctx, path
    );
  }

  // 4. Apply unification substitution to solve metas and collect index refinements
  const indexRefinements = new Map<number, TTKTerm>();
  if (unifyResult.tag === 'success') {
    unifyResult.substitution.forEach((value, key) => {
      if (key.startsWith('var:')) {
        // Index refinement: var:N -> term means the variable at index N in expected type equals term
        const index = parseInt(key.slice(4), 10);
        indexRefinements.set(index, value);
      } else {
        // Metavariable solution
        mctx.solve(key, value);
      }
    });
  }

  // 5. Compute actual argument types by substituting solved metas into telescope types
  // The telescope types contain de Bruijn indices that refer to earlier telescope positions.
  // At position i, a Var(k) refers to telescope[i - 1 - k].
  //
  // We substitute these Var references with the corresponding zonked metas.
  const zonkedArgTypes: TTKTerm[] = [];

  // First, zonk all the argument metas
  const zonkedMetas = argMetas.map(m => mctx.zonk(m));

  for (let i = 0; i < telescope.length; i++) {
    // Start with the telescope type
    let argType = telescope[i].type;

    // Replace Var references with the corresponding zonked metas
    // At position i, Var(k) refers to telescope[i - 1 - k]
    // So we substitute Var(k) with zonkedMetas[i - 1 - k]
    //
    // We use a parallel substitution approach: replace all Var(k) references
    // without the index decrementing that normal subst does.
    argType = parallelSubstTelescope(argType, i, zonkedMetas);

    zonkedArgTypes.push(argType);
  }

  if (DEBUG_PATTERN_ELAB) {
    console.log(`[DEBUG] zonkedMetas:`, zonkedMetas.map((m, i) => `${telescope[i].name}: ${prettyPrint(m)}`));
    console.log(`[DEBUG] zonkedArgTypes:`, zonkedArgTypes.map((t, i) => `${telescope[i].name}: ${prettyPrint(t)}`));
  }

  // 6. Recursively elaborate each pattern argument
  const allBindings: Array<{ name: string; type: TTKTerm }> = [];
  const nestedVarMetas: Array<{ meta: TTKTerm; localBindingIdx: number }> = [];
  let currentCtx = ctx;
  for (let i = 0; i < pattern.args.length; i++) {
    const argPath = appendPath(path, fieldSeg('args'), arraySeg(i));
    const argResult = elaboratePattern(
      pattern.args[i],
      zonkedArgTypes[i],
      currentCtx,
      mctx,
      argPath,
      defs
    );

    // For simple variable patterns (not wildcards), track the argMeta so it can be
    // solved with the correct global index later by elaborateClause
    // Wildcards can be '_' or unique names like '_w0', '_w1' (from uniform parsing)
    const isWildcard = pattern.args[i].tag === 'PVar' &&
      (pattern.args[i].name === '_' || pattern.args[i].name.startsWith('_w'));
    if (pattern.args[i].tag === 'PVar' && !isWildcard &&
      argResult.bindings.length === 1) {
      const meta = argMetas[i];
      if (meta.tag === 'Hole' && meta.id) {
        nestedVarMetas.push({ meta, localBindingIdx: allBindings.length });
      }
    }

    for (const b of argResult.bindings) {
      allBindings.push(b);
      currentCtx = extendContext(currentCtx, b.name, b.type);
    }

    // Merge index refinements from nested patterns
    // Note: indices from nested patterns are in a different context, so we may need to shift
    // For now, just merge them directly (this may need adjustment for deeply nested patterns)
    argResult.indexRefinements.forEach((value, key) => {
      indexRefinements.set(key, value);
    });

    // Collect nested var metas from recursive patterns (with adjusted indices)
    if (argResult.nestedVarMetas) {
      for (const nvm of argResult.nestedVarMetas) {
        // Adjust the local binding index to account for bindings added before this arg
        const adjustedIdx = allBindings.length - argResult.bindings.length + nvm.localBindingIdx;
        nestedVarMetas.push({ meta: nvm.meta, localBindingIdx: adjustedIdx });
      }
    }
  }

  // 7. Build the constructor term: Ctor applied to zonked metas
  // Keep metas in the pattern term - they will be solved with correct global indices
  // by elaborateClause after all patterns are processed
  let ctorTerm: TTKTerm = mkConst(pattern.name, ctor.fullType);
  for (const m of zonkedMetas) {
    ctorTerm = mkApp(ctorTerm, mctx.zonk(m));
  }

  // 8. Return the refined type and the pattern term
  return {
    bindings: allBindings,
    refinedType: mctx.zonk(expectedType),
    patternTerm: ctorTerm,
    indexRefinements,
    nestedVarMetas: nestedVarMetas.length > 0 ? nestedVarMetas : undefined
  };
}

// ============================================================================
// Bidirectional Type Checking with Unification
// ============================================================================

/**
 * Check that a term has the expected type using bidirectional type checking
 * combined with unification (to solve metavariables).
 *
 * Key insight: when checking a lambda against a Pi type, we use the Pi's
 * domain as the bound variable's type, not the lambda's domain (which may
 * be a hole for unannotated lambdas).
 *
 * This is essential for curried function definitions like:
 *   swap A = \f => \(x: A) (y: A) => f y x
 * where \f has no type annotation but is checked against (f : A -> A -> A) -> ...
 */
function checkTypeWithUnification(
  term: TTKTerm,
  expectedType: TTKTerm,
  ctx: TTKContext,
  mctx: MetaContext,
  defs: DefinitionsMap | undefined,
  path: IndexPath
): void {
  // Check if term is a lambda and expected is Pi - use bidirectional rule
  if (term.tag === 'Binder' && term.binderKind.tag === 'BLam' &&
    expectedType.tag === 'Binder' && expectedType.binderKind.tag === 'BPi') {
    // Use the Pi's domain as the type for the bound variable
    // This is crucial for unannotated lambdas like \f => ...
    const varType = expectedType.domain;

    // If the lambda has an annotated domain (not a hole), unify with Pi's domain
    if (term.domain.tag !== 'Hole') {
      const unifyDomainResult = unifyTerms(term.domain, varType, mkType(0), ctx, { definitions: defs });
      if (unifyDomainResult.tag === 'failure' || unifyDomainResult.tag === 'stuck') {
        throw new TypeCheckError(
          `Lambda domain mismatch.\n  Expected: ${prettyPrint(varType)}\n  Got: ${prettyPrint(term.domain)}${unifyDomainResult.reason ? `: ${unifyDomainResult.reason}` : ''}`,
          term, ctx, appendPath(path, fieldSeg('domain'))
        );
      }
      // Apply any solutions from domain unification
      if (unifyDomainResult.tag === 'success') {
        unifyDomainResult.substitution.forEach((value, key) => {
          if (!key.startsWith('var:')) {
            mctx.solve(key, value);
          }
        });
      }
    }

    // Check body against the Pi's codomain, with the bound variable having the Pi's domain type
    const extCtx = extendContext(ctx, term.name, varType);
    const bodyPath = appendPath(path, fieldSeg('body'));
    checkTypeWithUnification(term.body, expectedType.body, extCtx, mctx, defs, bodyPath);
    return;
  }

  // For non-lambda terms: infer type and unify with expected
  const inferredType = inferType(term, ctx, path);

  if (DEBUG_PATTERN_ELAB) {
    console.log('[DEBUG] Inferred RHS type:', prettyPrint(inferredType));
  }

  // Unify inferred type with expected type (pass definitions for WHNF reduction)
  const unifyResult = unifyTerms(inferredType, expectedType, mkType(0), ctx, { definitions: defs });
  if (unifyResult.tag === 'failure' || unifyResult.tag === 'stuck') {
    throw new TypeCheckError(
      `Type mismatch.\n  Expected: ${prettyPrint(expectedType)}\n  Inferred: ${prettyPrint(inferredType)}${unifyResult.reason ? `: ${unifyResult.reason}` : ''}`,
      term, ctx, path
    );
  }

  // Apply any solutions from the unification
  if (unifyResult.tag === 'success') {
    unifyResult.substitution.forEach((value, key) => {
      if (!key.startsWith('var:')) {
        mctx.solve(key, value);
      }
    });
  }
}

// ============================================================================
// Clause Elaboration
// ============================================================================

/**
 * Elaborate a clause (patterns + RHS) against expected argument types and return type.
 *
 * Uses "Type Checking Through Unification" approach:
 * 1. Track patternTerms - what each pattern elaborates to (meta, var, or ctor application)
 * 2. Substitute patternTerms into subsequent arg types (handles dependent types)
 * 3. Substitute patternTerms into return type to get the refined return type
 * 4. Infer RHS type and unify with refined return type
 * 5. Success = all unifications succeed and no unsolved required metas
 */
export function elaborateClause(
  clause: TTKClause,
  argTypes: TTKTerm[],
  expectedReturn: TTKTerm,
  ctx: TTKContext,
  mctx: MetaContext,
  defs?: DefinitionsMap,
  path: IndexPath = []
): ClauseElabResult {
  if (clause.patterns.length !== argTypes.length) {
    throw new TypeCheckError(
      `Clause has ${clause.patterns.length} patterns but expected ${argTypes.length}`,
      undefined, ctx, path
    );
  }

  // Track what term each pattern position elaborates to
  // This is crucial for dependent types - later types may reference earlier patterns
  const patternTerms: TTKTerm[] = [];
  const allBindings: Array<{ name: string; type: TTKTerm }> = [];
  const bindingCountsPerPattern: number[] = [];  // Track actual bindings per pattern
  let bindingCount = 0;

  // Collect all index refinements from pattern matching
  // Each entry maps (pattern index, variable index in that pattern's expected type) -> refined term
  // We'll use these to refine the return type after pattern substitution
  const allIndexRefinements: Array<{ patternIdx: number; refinements: Map<number, TTKTerm> }> = [];

  // Collect nested var metas from constructor patterns (like ??m1 for 'p' in 'Succ p')
  // These need to be solved with correct global indices after all patterns are elaborated
  const allNestedVarMetas: Array<{ meta: TTKTerm; patternIdx: number; localBindingIdx: number }> = [];

  // Track metas created for variable patterns during expected type computation
  // These need to be solved with the actual pattern Vars after index fix-up
  const varPatternMetas: Array<{ meta: TTKTerm; patternIndex: number }> = [];

  // Track the meta created for each pattern index, so we can reuse/zonk it later
  // This ensures that references to the same pattern from different later patterns
  // are properly connected through unification
  const patternMetaMap = new Map<number, TTKTerm>();

  // Elaborate each pattern
  for (let i = 0; i < clause.patterns.length; i++) {
    const patPath = appendPath(path, fieldSeg('patterns'), arraySeg(i));

    // The expected type may reference earlier patterns via De Bruijn indices
    // De Bruijn index 0 in argTypes[i] refers to pattern i-1, index 1 to i-2, etc.
    //
    // We use PARALLEL substitution (replaceVars) to avoid index corruption.
    // Sequential subst would decrement indices after each substitution, breaking
    // the mapping when multiple patterns are involved.
    //
    // For variable patterns, we use metas instead of the placeholder Var indices.
    // We track and reuse these metas so that references to the same pattern
    // from multiple later patterns are properly unified.
    let expectedType = argTypes[i];
    const varMap = new Map<number, TTKTerm>();
    for (let j = 0; j < i; j++) {
      const patternIndex = i - 1 - j;
      let replacement = patternTerms[patternIndex];
      // For variable patterns (which have placeholder Var indices), use a meta.
      // If we've already created a meta for this pattern, zonk and reuse it.
      // This ensures that constraints from earlier pattern matching propagate.
      if (replacement.tag === 'Var') {
        const existingMeta = patternMetaMap.get(patternIndex);
        if (existingMeta) {
          // Reuse the existing meta (zonked to get any solutions)
          replacement = mctx.zonk(existingMeta);
        } else {
          // Create a new meta for this pattern
          // Get the type of this pattern position from argTypes
          // We need to substitute earlier patterns into this type as well
          let patternType = argTypes[patternIndex];
          // Apply earlier substitutions to patternType using metas we've already created
          const typeVarMap = new Map<number, TTKTerm>();
          for (let k = 0; k < patternIndex; k++) {
            const prevPatternIndex = patternIndex - 1 - k;
            if (patternTerms[prevPatternIndex].tag === 'Var') {
              const prevMeta = patternMetaMap.get(prevPatternIndex);
              typeVarMap.set(k, prevMeta ? mctx.zonk(prevMeta) : mctx.fresh(mkType(0), ctx));
            } else {
              typeVarMap.set(k, patternTerms[prevPatternIndex]);
            }
          }
          if (typeVarMap.size > 0) {
            patternType = replaceVars(typeVarMap, patternType);
          }
          replacement = mctx.fresh(patternType, ctx);
          // Store this meta for reuse by later patterns
          patternMetaMap.set(patternIndex, replacement);
          // Track this meta so we can solve it later with the correct Var
          varPatternMetas.push({ meta: replacement, patternIndex });
        }
      }
      varMap.set(j, replacement);
    }
    if (varMap.size > 0) {
      expectedType = replaceVars(varMap, expectedType);
    }
    expectedType = mctx.zonk(expectedType);

    if (DEBUG_PATTERN_ELAB) {
      console.log(`[DEBUG] Pattern ${i}: expected type (after subst): ${prettyPrint(expectedType)}`);
      console.log(`[DEBUG] Pattern ${i}: structure = ${JSON.stringify(clause.patterns[i])}`);
    }

    const result = elaboratePattern(
      clause.patterns[i],
      expectedType,
      ctx,  // Use base context - pattern context is separate
      mctx,
      patPath,
      defs
    );

    // For variable patterns, the patternTerm should be a Var with the correct index
    // The index counts from the end of all bindings (De Bruijn convention)
    let patternTerm = result.patternTerm;
    if (result.bindings.length === 1 && result.patternTerm.tag === 'Var') {
      // This is a simple variable binding - set the correct index
      // The index is relative to the final binding count
      // We'll fix this up after we know the total binding count
      patternTerm = mkVar(bindingCount);
    }
    patternTerms.push(patternTerm);

    // Collect index refinements from this pattern
    if (result.indexRefinements.size > 0) {
      allIndexRefinements.push({ patternIdx: i, refinements: result.indexRefinements });
    }

    // Collect nested var metas from constructor patterns
    // These need to be solved with correct global indices after fix-up
    if (result.nestedVarMetas) {
      for (const nvm of result.nestedVarMetas) {
        // localBindingIdx is relative to this pattern's bindings
        // cumulativeIdx is the global position of the first binding in this pattern
        allNestedVarMetas.push({
          meta: nvm.meta,
          patternIdx: i,
          localBindingIdx: nvm.localBindingIdx
        });
      }
    }

    // Track how many bindings this pattern actually contributed
    bindingCountsPerPattern.push(result.bindings.length);

    if (DEBUG_PATTERN_ELAB) {
      console.log(`[DEBUG] Pattern ${i} elaborates to: ${prettyPrint(patternTerm)}`);
      console.log(`[DEBUG] Pattern ${i} bindings: ${result.bindings.length}`);
      if (result.indexRefinements.size > 0) {
        console.log(`[DEBUG] Pattern ${i} index refinements:`,
          Array.from(result.indexRefinements.entries()).map(([k, v]) => `#${k} -> ${prettyPrint(v)}`));
      }
    }

    for (const b of result.bindings) {
      allBindings.push(b);
      bindingCount++;
    }
  }

  // Fix up pattern term indices now that we know the total binding count
  // During elaboration, we used mkVar(bindingCount) where bindingCount was the count at that point.
  // But in the final pattern context, the De Bruijn index should be (totalBindings - 1 - bindingIndex).
  // For pattern i which introduced binding at cumulative index p, the final index is (bindingCount - 1 - p).
  //
  // For constructor patterns like (Succ p), the patternTerm contains Vars with LOCAL indices
  // (relative to that pattern's bindings). We need to adjust these to GLOBAL indices.

  // Helper to adjust local Var indices in a pattern term to global indices
  // localBindingCount: number of bindings in this pattern
  // cumulativeStart: index of first binding from this pattern in global context
  // totalBindings: total number of bindings across all patterns
  const adjustLocalToGlobal = (term: TTKTerm, localBindingCount: number, cumulativeStart: number): TTKTerm => {
    switch (term.tag) {
      case 'Var':
        // Local index counts from end of local bindings
        // local index 0 = last binding in this pattern = binding at position (cumulativeStart + localBindingCount - 1)
        // In global context, this should be index (totalBindings - 1 - (cumulativeStart + localBindingCount - 1 - localIdx))
        // = totalBindings - 1 - cumulativeStart - localBindingCount + 1 + localIdx
        // = totalBindings - cumulativeStart - localBindingCount + localIdx
        const localIdx = term.index;
        const globalBindingPos = cumulativeStart + (localBindingCount - 1 - localIdx);
        const globalIdx = bindingCount - 1 - globalBindingPos;
        return mkVar(globalIdx);
      case 'App':
        return mkApp(
          adjustLocalToGlobal(term.fn, localBindingCount, cumulativeStart),
          adjustLocalToGlobal(term.arg, localBindingCount, cumulativeStart)
        );
      case 'Const':
        return term;
      case 'Hole':
        // Metas should stay as metas (they're not local bindings)
        return term;
      default:
        // Other term types shouldn't appear in pattern terms, but just return them
        return term;
    }
  };

  let cumulativeBindingIdx = 0;
  for (let i = 0; i < patternTerms.length; i++) {
    const pt = patternTerms[i];
    // Use actual bindings tracked during elaboration, not the pattern structure
    const bindingsForThisPattern = bindingCountsPerPattern[i];

    if (DEBUG_PATTERN_ELAB) {
      console.log(`[DEBUG] Fix-up pattern ${i}: actualBindings=${bindingsForThisPattern}, cumulative=${cumulativeBindingIdx}`);
    }

    if (pt.tag === 'Var') {
      // Simple variable pattern: fix the index
      const correctIndex = bindingCount - 1 - cumulativeBindingIdx;
      if (DEBUG_PATTERN_ELAB) {
        console.log(`[DEBUG]   patternTerms[${i}] is Var, correctIndex = ${bindingCount} - 1 - ${cumulativeBindingIdx} = ${correctIndex}`);
      }
      patternTerms[i] = mkVar(correctIndex);
    } else if (pt.tag === 'App') {
      // Constructor pattern: adjust local indices to global
      patternTerms[i] = adjustLocalToGlobal(pt, bindingsForThisPattern, cumulativeBindingIdx);
      if (DEBUG_PATTERN_ELAB) {
        console.log(`[DEBUG]   patternTerms[${i}] adjusted: ${prettyPrint(pt)} -> ${prettyPrint(patternTerms[i])}`);
      }
    }
    cumulativeBindingIdx += bindingsForThisPattern;
  }

  // Handle metas created for variable patterns.
  // During expected type computation, we created metas to stand in for variable patterns.
  // These metas may have been solved during unification (e.g., VNil tells us a = Zero).
  //
  // If a meta was already solved to something concrete, we should update the pattern term
  // with that value (this propagates index refinements like a = Zero).
  // If the meta wasn't solved, we solve it to the pattern's Var index.
  for (const { meta, patternIndex } of varPatternMetas) {
    if (meta.tag === 'Hole' && meta.id) {
      // Check if this meta was already solved during unification
      const zonked = mctx.zonk(meta);

      // If zonked is different from the original meta, it was solved
      const wasSolved = zonked.tag !== 'Hole' || (zonked.id !== meta.id);

      if (wasSolved) {
        // The meta was solved to something concrete (e.g., Zero from VNil matching).
        // Use this to refine the pattern term - this is how index refinements propagate!
        if (DEBUG_PATTERN_ELAB) {
          console.log(`[DEBUG] Meta ${meta.id} was solved during unification to ${prettyPrint(zonked)}`);
          console.log(`[DEBUG]   Updating patternTerms[${patternIndex}] from ${prettyPrint(patternTerms[patternIndex])} to ${prettyPrint(zonked)}`);
        }
        patternTerms[patternIndex] = zonked;
      } else {
        // Meta wasn't solved - solve it to the pattern's Var index
        const patternTerm = patternTerms[patternIndex];
        if (patternTerm.tag === 'Var') {
          mctx.solve(meta.id, patternTerm);
          if (DEBUG_PATTERN_ELAB) {
            console.log(`[DEBUG] Solved variable pattern meta ${meta.id} -> ${prettyPrint(patternTerm)}`);
          }
        }
      }
    }
  }

  // Solve nested var metas from constructor patterns with correct global indices
  // For (Succ p), we tracked that the argMeta for 'p' needs to be solved to the binding
  // Now that we know the global indices, we can solve them correctly
  {
    // First compute cumulative binding starts for each pattern
    const cumulativeStarts: number[] = [];
    let cumStart = 0;
    for (let i = 0; i < bindingCountsPerPattern.length; i++) {
      cumulativeStarts.push(cumStart);
      cumStart += bindingCountsPerPattern[i];
    }

    for (const { meta, patternIdx, localBindingIdx } of allNestedVarMetas) {
      if (meta.tag === 'Hole' && meta.id) {
        // Check if already solved during unification
        const zonked = mctx.zonk(meta);
        const wasSolved = zonked.tag !== 'Hole' || (zonked.id !== meta.id);

        if (!wasSolved) {
          // Compute the global index for this binding
          // localBindingIdx is the index within this pattern's bindings
          // cumulativeStarts[patternIdx] is where this pattern's bindings start
          const globalBindingPos = cumulativeStarts[patternIdx] + localBindingIdx;
          const globalIdx = bindingCount - 1 - globalBindingPos;
          mctx.solve(meta.id, mkVar(globalIdx));
          if (DEBUG_PATTERN_ELAB) {
            console.log(`[DEBUG] Solved nested var meta ${meta.id} from pattern ${patternIdx} -> #${globalIdx}`);
          }
        }
      }
    }
  }

  // Apply index refinements by updating pattern terms
  // When we match a constructor like VNil against Vec A a, we learn a = Zero.
  // The refinement var:N -> term tells us that variable at index N in pattern i's expected type
  // corresponds to an earlier pattern.
  //
  // Due to the way the substitution loop works (with index decrements), var:k after the loop
  // corresponds to the original telescope index k+1, which maps to pattern k+1.
  // This is because the substitution loop decrements indices, so original #1 becomes #0, etc.
  for (const { patternIdx, refinements } of allIndexRefinements) {
    refinements.forEach((refinedTerm, varIndex) => {
      // var:k in the expected type after substitution corresponds to pattern k+1
      // (due to index decrementing in the substitution loop)
      const targetPatternIdx = varIndex + 1;

      if (targetPatternIdx >= 0 && targetPatternIdx < patternTerms.length) {
        if (DEBUG_PATTERN_ELAB) {
          console.log(`[DEBUG] Refinement from pattern ${patternIdx}: var #${varIndex} in expected type`);
          console.log(`[DEBUG]   -> patternTerms[${targetPatternIdx}] was ${prettyPrint(patternTerms[targetPatternIdx])}, now ${prettyPrint(refinedTerm)}`);
        }
        // Update the pattern term with the refined value
        patternTerms[targetPatternIdx] = refinedTerm;
      } else {
        if (DEBUG_PATTERN_ELAB) {
          console.log(`[DEBUG] Refinement from pattern ${patternIdx}: var #${varIndex} -> ${prettyPrint(refinedTerm)} (no matching pattern term, idx=${targetPatternIdx})`);
        }
      }
    });
  }

  // Compute the refined return type using parallel substitution.
  // When bindingCount == arity, the indices in expectedReturn directly correspond
  // to the pattern context indices. We only need to apply refinements (like a = Zero).
  //
  // Build a mapping from function arg index -> pattern term
  // - Index k in expectedReturn corresponds to pattern (n-1-k)
  // - If the pattern term is just #k (identity), we can skip it
  // - If the pattern term is a refinement (like Zero), we must apply it
  if (DEBUG_PATTERN_ELAB) {
    console.log('[DEBUG] PatternTerms after fix-up:', patternTerms.map((t, i) => `[${i}]: ${prettyPrint(t)}`));
    console.log('[DEBUG] Original return type:', prettyPrint(expectedReturn));
  }

  const n = patternTerms.length;
  const refinementMap = new Map<number, TTKTerm>();

  // Build the refinement map: only include non-identity substitutions
  for (let i = 0; i < n; i++) {
    const targetIndex = n - 1 - i; // Index in the return type
    const patternTerm = patternTerms[i];
    // Check if this is NOT an identity (i.e., #targetIndex -> something other than #targetIndex)
    if (!(patternTerm.tag === 'Var' && patternTerm.index === targetIndex)) {
      refinementMap.set(targetIndex, patternTerm);
      if (DEBUG_PATTERN_ELAB) {
        console.log(`[DEBUG] Refinement: #${targetIndex} -> ${prettyPrint(patternTerm)}`);
      }
    }
  }

  // Apply the refinements using parallel substitution (no index shifting)
  let refinedReturn = replaceVars(refinementMap, expectedReturn);

  if (DEBUG_PATTERN_ELAB) {
    console.log(`[DEBUG] After replaceVars: ${prettyPrint(refinedReturn)}`);
  }

  // Recompute binding types using argTypes and the correct pattern context mapping.
  // The binding types computed during pattern elaboration have incorrect indices due to
  // sequential substitution with index decrementing. We need to translate argTypes directly
  // using the pattern context index mapping.
  //
  // For pattern i in a function with n patterns:
  // - argTypes[i] has De Bruijn indices relative to the function telescope at position i
  // - In argTypes[i], index k refers to pattern (i - 1 - k)
  // - In the pattern context, pattern j is at index (n - 1 - j)
  // - So we need to map: index k in argTypes[i] -> index (n - 1 - (i - 1 - k)) = (n - i + k)
  //
  // But we need to handle the complexity of which binding came from which pattern.
  // For simple variable patterns (1 binding each), binding i corresponds to argTypes[i].

  if (DEBUG_PATTERN_ELAB) {
    console.log('[DEBUG] Binding types before translation:', allBindings.map(b => `${b.name}: ${prettyPrint(b.type)}`));
  }

  // Build correct binding types
  // For variable patterns (1 binding): use argTypes[patIdx] with index translation
  // For constructor patterns (multiple bindings): use binding.type from elaboration
  //   (these types are already zonked and contain the correct values)
  const translatedBindings: Array<{ name: string; type: TTKTerm }> = [];

  // Compute cumulative binding indices for index translation
  const cumulativeBindings: number[] = [];
  let cumulative = 0;
  for (let patIdx = 0; patIdx < n; patIdx++) {
    cumulativeBindings.push(cumulative);
    cumulative += bindingCountsPerPattern[patIdx];
  }
  const totalBindings = cumulative;

  let bindingIdx = 0;
  for (let patIdx = 0; patIdx < n; patIdx++) {
    const bindingsForPattern = bindingCountsPerPattern[patIdx];

    for (let k = 0; k < bindingsForPattern; k++) {
      const binding = allBindings[bindingIdx];

      // For constructor patterns with multiple bindings, use the types from elaboration
      // These are already in terms of solved metas and need index translation
      if (bindingsForPattern > 1) {
        // Binding types from elaboration are in telescope context
        // We need to translate de Bruijn indices to pattern context indices
        // Build map: pattern position -> pattern context index
        const typeMap = new Map<number, TTKTerm>();
        for (let j = 0; j < patIdx; j++) {
          // Index j in the type refers to pattern (patIdx - 1 - j)
          // That pattern's first binding is at cumulative index cumulativeBindings[patIdx - 1 - j]
          // In the final context, that binding is at index (totalBindings - 1 - cumulativeBindings[patIdx - 1 - j])
          const refPatternIdx = patIdx - 1 - j;
          const refBindingCumIdx = cumulativeBindings[refPatternIdx];
          const patternCtxIdx = totalBindings - 1 - refBindingCumIdx;
          typeMap.set(j, mkVar(patternCtxIdx));
        }
        const translatedType = typeMap.size > 0 ? replaceVars(typeMap, binding.type) : binding.type;
        translatedBindings.push({
          name: binding.name,
          type: translatedType
        });
      } else {
        // Single binding pattern (variable): use argTypes with index translation
        // Build mapping for this pattern position
        const typeMap = new Map<number, TTKTerm>();
        for (let j = 0; j < patIdx; j++) {
          const refPatternIdx = patIdx - 1 - j;
          const refBindingCumIdx = cumulativeBindings[refPatternIdx];
          const patternCtxIdx = totalBindings - 1 - refBindingCumIdx;
          typeMap.set(j, mkVar(patternCtxIdx));
        }
        const originalType = argTypes[patIdx];
        const translatedType = typeMap.size > 0 ? replaceVars(typeMap, originalType) : originalType;
        translatedBindings.push({
          name: binding.name,
          type: translatedType
        });
      }
      bindingIdx++;
    }
  }

  if (DEBUG_PATTERN_ELAB) {
    console.log('[DEBUG] Binding types after translation:', translatedBindings.map(b => `${b.name}: ${prettyPrint(b.type)}`));
  }

  refinedReturn = mctx.zonk(refinedReturn);

  if (DEBUG_PATTERN_ELAB) {
    console.log(`[DEBUG] Refined return type: ${prettyPrint(refinedReturn)}`);
  }

  // Zonk bindings
  const zonkedBindings = translatedBindings.map(b => ({
    name: b.name,
    type: mctx.zonk(b.type)
  }));

  // Build pattern context for RHS type checking
  // De Bruijn convention: most recently bound variable is at index 0
  const patternCtx: TTKContext = [];
  for (let i = zonkedBindings.length - 1; i >= 0; i--) {
    patternCtx.push(zonkedBindings[i]);
  }
  // Add original context entries (they are at higher indices)
  for (const entry of ctx) {
    patternCtx.push(entry);
  }

  if (DEBUG_PATTERN_ELAB) {
    console.log('[DEBUG] Pattern context:', patternCtx.map(e => `${e.name}: ${prettyPrint(e.type)}`).join(', '));
  }

  // TYPE CHECK RHS USING BIDIRECTIONAL TYPE CHECKING WITH UNIFICATION
  // We use a custom bidirectional check that:
  // 1. For lambdas checked against Pi types, uses the Pi's domain as the bound variable's type
  //    (this handles unannotated lambdas like \f => ...)
  // 2. For other terms, infers the type and unifies with expected (to solve metavariables)
  const rhsPath = appendPath(path, fieldSeg('rhs'));
  const zonkedRhs = mctx.zonk(clause.rhs);

  if (DEBUG_PATTERN_ELAB) {
    console.log('[DEBUG] RHS:', prettyPrint(zonkedRhs));
    console.log('[DEBUG] Expected return:', prettyPrint(refinedReturn));
  }

  // Bidirectional check with unification
  checkTypeWithUnification(zonkedRhs, refinedReturn, patternCtx, mctx, defs, rhsPath);

  if (DEBUG_PATTERN_ELAB) {
    console.log('[DEBUG] RHS type check passed');
  }

  return {
    bindings: zonkedBindings,
    returnType: mctx.zonk(refinedReturn)
  };
}

// ============================================================================
// Function Clause Checking
// ============================================================================

/**
 * Check all clauses of a function definition.
 *
 * Handles curried definitions where the clause has fewer patterns than the full function type.
 * For example: `swap A = \f => ...` for type `(A : Type) -> (A -> A -> A) -> (A -> A -> A)`
 * Here we only match 1 pattern (A), and the expected return type is `(A -> A -> A) -> (A -> A -> A)`.
 */
export function checkFunctionClauses(
  fnType: TTKTerm,
  clauses: TTKClause[],
  ctx: TTKContext,
  _defs?: DefinitionsMap,  // Not used by stepper-based implementation
  path: IndexPath = []
): void {
  // Delegate to the result-returning version which now uses the stepper
  const result = checkFunctionClausesWithResult(fnType, clauses, ctx, path);

  // If there are any errors, throw the first one
  if (result.errors.length > 0) {
    const firstError = result.errors[0];
    throw new TypeCheckError(
      firstError.message,
      firstError.term,
      firstError.context,
      firstError.path
    );
  }
}

/**
 * Infer the type of a match expression.
 */
export function inferMatchType(
  scrutinee: TTKTerm,
  clauses: TTKClause[],
  ctx: TTKContext,
  expected?: TTKTerm,
  _defs?: DefinitionsMap,  // Not used by stepper-based implementation
  path: IndexPath = []
): TTKTerm {
  if (clauses.length === 0) {
    throw new TypeCheckError('Match expression must have at least one clause', undefined, ctx, path);
  }

  // Infer the type of the scrutinee
  const scrutineeType = inferType(scrutinee, ctx, appendPath(path, fieldSeg('scrutinee')));

  // Validate all clauses have exactly 1 pattern (for single scrutinee)
  for (let i = 0; i < clauses.length; i++) {
    if (clauses[i].patterns.length !== 1) {
      throw new TypeCheckError(
        `Match clause ${i + 1} must have exactly 1 pattern for single scrutinee`,
        undefined, ctx, appendPath(path, fieldSeg('clauses'), arraySeg(i))
      );
    }
  }

  // Build a function type for the match: scrutineeType -> returnType
  // We'll infer returnType from the first clause if not provided
  const mctx = new MetaContext();
  const returnTypeMeta = expected || mctx.fresh(mkType(0), ctx);
  const fnType = mkPi(scrutineeType, returnTypeMeta, '_scrutinee');

  // Build constructor environment and typing context for stepper
  const stepperEnv = buildStepperEnvironment(ctx);
  const typingContext = ctx.map(binding => ({
    name: binding.name,
    type: binding.type
  }));

  // Use the stepper to check each clause and infer return type
  let returnType: TTKTerm | undefined = expected;

  for (let i = 0; i < clauses.length; i++) {
    const clause = clauses[i];
    const cPath = appendPath(path, fieldSeg('clauses'), arraySeg(i));

    const stepper = new PatternElabStepper(clause, fnType, stepperEnv, typingContext);

    // Run stepper to completion
    while (!stepper.isDone()) {
      stepper.step();
    }

    const finalState = stepper.getState();

    if (finalState.phase.tag === 'Error') {
      const patternIndex = finalState.phase.patternIndex;
      const errorMsg = patternIndex !== undefined
        ? `In match clause ${i + 1}, pattern ${patternIndex + 1}: ${finalState.phase.message}`
        : `In match clause ${i + 1}: ${finalState.phase.message}`;

      throw new TypeCheckError(errorMsg, clause.rhs, ctx, cPath);
    } else if (finalState.phase.tag === 'Done') {
      if (!finalState.returnType) {
        throw new Error(`Internal error: stepper finished but returnType is null for match clause ${i + 1}`);
      }

      if (!returnType) {
        returnType = finalState.returnType;
      }
      // TODO: Check that all clauses have compatible return types
    } else {
      throw new Error(`Internal error: stepper finished but phase is ${finalState.phase.tag}`);
    }
  }

  return returnType!;
}

/**
 * Check function clauses and return detailed results.
 * Used by declaration checking for error reporting and type queries.
 */
export function checkFunctionClausesWithResult(
  fnType: TTKTerm,
  clauses: TTKClause[],
  ctx: TTKContext,
  path: IndexPath = [],
  _defs?: DefinitionsMap  // Not used by stepper-based implementation
): FunctionClausesResult {
  if (clauses.length === 0) {
    throw new TypeCheckError('Function must have at least one clause', undefined, ctx, path);
  }

  // Validate all clauses have the same arity
  const arity = clauses[0].patterns.length;
  for (let i = 1; i < clauses.length; i++) {
    if (clauses[i].patterns.length !== arity) {
      throw new TypeCheckError(
        `Clause ${i + 1} has ${clauses[i].patterns.length} patterns but expected ${arity}`,
        undefined, ctx, appendPath(path, fieldSeg('clauses'), arraySeg(i))
      );
    }
  }

  if (DEBUG_PATTERN_ELAB) {
    console.log('[DEBUG checkFunctionClausesWithResult] fnType:', prettyPrint(fnType));
    console.log('[DEBUG checkFunctionClausesWithResult] arity:', arity);
    console.log('[DEBUG checkFunctionClausesWithResult] ctx:', ctx.map(e => `${e.name}: ${prettyPrint(e.type)}`));
  }

  // Build constructor environment for pattern elaboration (EAGERLY)
  // This is the same environment the stepper modal uses
  const stepperEnv = buildStepperEnvironment(ctx);

  // Build typing context for the stepper (for looking up function/constant types during RHS checking)
  const typingContext = ctx.map(binding => ({
    name: binding.name,
    type: binding.type
  }));

  const results: ClauseCheckResult[] = [];
  const errors: ClauseCheckError[] = [];
  const combined: Substitution = new Map();

  // Use the stepper (CANONICAL implementation) to check each clause
  for (let i = 0; i < clauses.length; i++) {
    const clause = clauses[i];
    const cPath = appendPath(path, fieldSeg('clauses'), arraySeg(i));

    const stepper = new PatternElabStepper(clause, fnType, stepperEnv, typingContext);

    // Run stepper to completion
    while (!stepper.isDone()) {
      stepper.step();
    }

    const finalState = stepper.getState();

    if (finalState.phase.tag === 'Error') {
      // Stepper found an error - accumulate it
      const patternIndex = finalState.phase.patternIndex;
      const errorMsg = patternIndex !== undefined
        ? `In clause ${i + 1}, pattern ${patternIndex + 1}: ${finalState.phase.message}`
        : `In clause ${i + 1}: ${finalState.phase.message}`;

      errors.push({
        clauseIndex: i,
        message: errorMsg,
        path: cPath,
        term: clause.rhs,
        context: ctx
      });
    } else if (finalState.phase.tag === 'Done') {
      // Stepper succeeded - extract results
      if (!finalState.returnType) {
        throw new Error(`Internal error: stepper finished but returnType is null for clause ${i + 1}`);
      }

      results.push({
        returnType: finalState.returnType,
        solvedBindings: finalState.bindings.map((b: { name: string; type: TTKTerm }) => ({ name: b.name, type: b.type })),
        substitution: new Map()  // TODO: collect substitutions if needed
      });
    } else {
      throw new Error(`Internal error: stepper finished but phase is ${finalState.phase.tag}`);
    }
  }

  return { clauses: results, substitution: combined, errors, stepperEnv };
}
