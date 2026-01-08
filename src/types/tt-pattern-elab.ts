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
  subst,
  shiftTerm,
  prettyPrint,
} from './tt-kernel';
import { MetaContext } from './tt-meta';
import { TypeCheckError, lookupConstByName, extendContext, inferType, checkType, convertible, DefinitionsMap } from './tt-typecheck';
import { unifyTerms, Substitution, varKey } from './tt-unify';
import { IndexPath, appendPath, fieldSeg, arraySeg } from './source-position';
import { TPattern } from './tt-core';

// Browser-safe debug flag (set to true to enable debug logging)
const DEBUG_PATTERN_ELAB = false;

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

/** Result of checking all function clauses */
export interface FunctionClausesResult {
  clauses: ClauseCheckResult[];
  substitution: Substitution;
}

// ============================================================================
// Helper Functions
// ============================================================================

/**
 * Look up constructor information from context.
 */
export function lookupConstructor(name: string, ctx: TTKContext): ConstructorInfo | null {
  const type = lookupConstByName(ctx, name);
  if (!type) return null;

  const { returnType } = unwrapPi(type);
  const headName = getHeadName(returnType);
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
  path: IndexPath = []
): PatternElabResult {
  // Normalize the expected type first
  const normType = expectedType;  // TODO: whnf if needed

  switch (pattern.tag) {
    case 'PVar': {
      // Both wildcards and named variables create a binding
      // For wildcards, we also create a meta (though we may not need it)
      if (pattern.name === '_') {
        // Wildcard: the binding exists for de Bruijn indexing,
        // but its value is unconstrained (may be solved by unification)
        mctx.fresh(normType, ctx);
      }
      return {
        bindings: [{ name: pattern.name, type: normType }],
        refinedType: normType
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
            refinedType: normType
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

      return elaborateCtorPattern(pattern, ctor, normType, ctx, mctx, path);
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
  path: IndexPath
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
  const unifyResult = unifyTerms(instantiatedReturn, expectedType, mkType(0), ctx);
  if (DEBUG_PATTERN_ELAB) {
    console.log(`[DEBUG] Unify result:`, unifyResult.tag);
    if (unifyResult.tag === 'success') {
      console.log(`[DEBUG] Substitution:`, Array.from(unifyResult.substitution.entries()).map(([k, v]) => `${k} -> ${prettyPrint(v)}`));
    }
  }
  if (unifyResult.tag === 'failure') {
    throw new TypeCheckError(
      `Constructor '${pattern.name}' cannot match expected type '${prettyPrint(expectedType)}': ${unifyResult.reason}`,
      undefined, ctx, path
    );
  }

  // 4. Apply unification substitution to solve metas
  if (unifyResult.tag === 'success') {
    unifyResult.substitution.forEach((value, key) => {
      // If it's a hole solution, record it in mctx
      if (!key.startsWith('var:')) {
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
  let currentCtx = ctx;
  for (let i = 0; i < pattern.args.length; i++) {
    const argPath = appendPath(path, fieldSeg('args'), arraySeg(i));
    const argResult = elaboratePattern(
      pattern.args[i],
      zonkedArgTypes[i],
      currentCtx,
      mctx,
      argPath
    );
    for (const b of argResult.bindings) {
      allBindings.push(b);
      currentCtx = extendContext(currentCtx, b.name, b.type);
    }
  }

  // 7. Return the refined type (may have more specific indices now)
  return {
    bindings: allBindings,
    refinedType: mctx.zonk(expectedType)
  };
}

// ============================================================================
// Clause Elaboration
// ============================================================================

/**
 * Elaborate a clause (patterns + RHS) against expected argument types and return type.
 */
export function elaborateClause(
  clause: TTKClause,
  argTypes: TTKTerm[],
  expectedReturn: TTKTerm,
  ctx: TTKContext,
  mctx: MetaContext,
  _defs?: DefinitionsMap,
  path: IndexPath = []
): ClauseElabResult {
  if (clause.patterns.length !== argTypes.length) {
    throw new TypeCheckError(
      `Clause has ${clause.patterns.length} patterns but expected ${argTypes.length}`,
      undefined, ctx, path
    );
  }

  let currentCtx = ctx;
  const allBindings: Array<{ name: string; type: TTKTerm }> = [];

  // Elaborate each pattern
  for (let i = 0; i < clause.patterns.length; i++) {
    const patPath = appendPath(path, fieldSeg('patterns'), arraySeg(i));
    const result = elaboratePattern(
      clause.patterns[i],
      argTypes[i],
      currentCtx,
      mctx,
      patPath
    );
    for (const b of result.bindings) {
      allBindings.push(b);
      currentCtx = extendContext(currentCtx, b.name, b.type);
    }
  }

  // Zonk everything
  const zonkedBindings = allBindings.map(b => ({
    name: b.name,
    type: mctx.zonk(b.type)
  }));
  const zonkedReturn = mctx.zonk(expectedReturn);
  const zonkedRhs = mctx.zonk(clause.rhs);

  // Build zonked context for type checking
  // De Bruijn convention: most recently bound variable is at index 0
  // So we need to reverse the bindings - last pattern variable should be index 0
  const zonkedCtx: TTKContext = [];
  for (let i = zonkedBindings.length - 1; i >= 0; i--) {
    zonkedCtx.push(zonkedBindings[i]);
  }
  // Add original context entries (they are at higher indices)
  for (const entry of ctx) {
    zonkedCtx.push(entry);
  }

  // Type check RHS using bidirectional checking
  // This allows lambdas without type annotations to be checked against Pi types
  const rhsPath = appendPath(path, fieldSeg('rhs'));
  if (DEBUG_PATTERN_ELAB) {
    console.log('[DEBUG] zonkedRhs:', prettyPrint(zonkedRhs));
    console.log('[DEBUG] zonkedCtx:', zonkedCtx.map(e => `${e.name}: ${prettyPrint(e.type)}`).join(', '));
    console.log('[DEBUG] zonkedReturn:', prettyPrint(zonkedReturn));
  }

  // Use checkType for bidirectional type checking - this handles lambdas against Pi types
  checkType(zonkedRhs, zonkedReturn, zonkedCtx, rhsPath);

  return {
    bindings: zonkedBindings,
    returnType: zonkedReturn
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
  defs?: DefinitionsMap,
  path: IndexPath = []
): void {
  // Determine arity from the first clause
  const arity = clauses.length > 0 ? clauses[0].patterns.length : unwrapPi(fnType).args.length;

  // Extract only `arity` argument types and keep the rest in returnType
  const { args, returnType } = unwrapPiN(fnType, arity);
  const argTypes = args.map(a => a.type);

  if (DEBUG_PATTERN_ELAB) {
    console.log('[DEBUG checkFunctionClauses] fnType:', prettyPrint(fnType));
    console.log('[DEBUG checkFunctionClauses] arity:', arity);
    console.log('[DEBUG checkFunctionClauses] argTypes:', argTypes.map(t => prettyPrint(t)));
    console.log('[DEBUG checkFunctionClauses] returnType:', prettyPrint(returnType));
    console.log('[DEBUG checkFunctionClauses] ctx:', ctx.map(e => `${e.name}: ${prettyPrint(e.type)}`));
  }

  for (let i = 0; i < clauses.length; i++) {
    const clause = clauses[i];
    if (clause.patterns.length !== arity) {
      throw new TypeCheckError(
        `Clause ${i + 1} has ${clause.patterns.length} patterns but expected ${arity}`,
        undefined, ctx, appendPath(path, fieldSeg('clauses'), arraySeg(i))
      );
    }

    // Create a fresh MetaContext for each clause
    const mctx = new MetaContext();

    const cPath = appendPath(path, fieldSeg('clauses'), arraySeg(i));
    try {
      elaborateClause(clause, argTypes, returnType, ctx, mctx, defs, cPath);
    } catch (e) {
      if (e instanceof TypeCheckError) {
        throw new TypeCheckError(
          `In clause ${i + 1}: ${e.message}`,
          e.term,
          e.context || ctx,
          e.termPath || cPath
        );
      }
      throw e;
    }
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
  defs?: DefinitionsMap,
  path: IndexPath = []
): TTKTerm {
  if (clauses.length === 0) {
    throw new TypeCheckError('Match expression must have at least one clause', undefined, ctx, path);
  }

  // Infer the type of the scrutinee
  const scrutineeType = inferType(scrutinee, ctx, appendPath(path, fieldSeg('scrutinee')));

  // For each clause, elaborate and get the return type
  // All clauses must have the same return type
  let returnType: TTKTerm | undefined = expected;

  for (let i = 0; i < clauses.length; i++) {
    const clause = clauses[i];
    if (clause.patterns.length !== 1) {
      throw new TypeCheckError(
        `Match clause ${i + 1} must have exactly 1 pattern for single scrutinee`,
        undefined, ctx, appendPath(path, fieldSeg('clauses'), arraySeg(i))
      );
    }

    const mctx = new MetaContext();
    const cPath = appendPath(path, fieldSeg('clauses'), arraySeg(i));

    try {
      const result = elaborateClause(
        clause,
        [scrutineeType],
        returnType || mctx.fresh(mkType(0), ctx),
        ctx,
        mctx,
        defs,
        cPath
      );
      if (!returnType) {
        returnType = result.returnType;
      }
    } catch (e) {
      if (e instanceof TypeCheckError) {
        throw new TypeCheckError(
          `In match clause ${i + 1}: ${e.message}`,
          e.term,
          e.context || ctx,
          e.termPath || cPath
        );
      }
      throw e;
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
  defs?: DefinitionsMap
): FunctionClausesResult {
  if (clauses.length === 0) {
    throw new TypeCheckError('Function must have at least one clause', undefined, ctx, path);
  }

  // Determine arity from the first clause
  const arity = clauses[0].patterns.length;

  // Extract only `arity` argument types and keep the rest in returnType
  // This handles curried definitions where the clause has fewer patterns than the full function type
  const { args, returnType } = unwrapPiN(fnType, arity);
  const argTypes = args.map(a => a.type);

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
    console.log('[DEBUG checkFunctionClausesWithResult] argTypes:', argTypes.map(t => prettyPrint(t)));
    console.log('[DEBUG checkFunctionClausesWithResult] returnType:', prettyPrint(returnType));
    console.log('[DEBUG checkFunctionClausesWithResult] ctx:', ctx.map(e => `${e.name}: ${prettyPrint(e.type)}`));
  }

  const results: ClauseCheckResult[] = [];
  const combined: Substitution = new Map();

  for (let i = 0; i < clauses.length; i++) {
    const clause = clauses[i];
    const mctx = new MetaContext();
    const cPath = appendPath(path, fieldSeg('clauses'), arraySeg(i));

    try {
      const result = elaborateClause(clause, argTypes, returnType, ctx, mctx, defs, cPath);
      results.push({
        returnType: result.returnType,
        solvedBindings: result.bindings,
        substitution: new Map()  // TODO: collect substitutions from mctx if needed
      });
    } catch (e) {
      if (e instanceof TypeCheckError) {
        throw new TypeCheckError(
          `In clause ${i + 1}: ${e.message}`,
          e.term,
          e.context || ctx,
          e.termPath || cPath
        );
      }
      throw e;
    }
  }

  return { clauses: results, substitution: combined };
}
