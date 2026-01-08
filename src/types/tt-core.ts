/**
 * TT (Typed Terms) Core Layer
 *
 * This is the foundational layer for representing mathematical proofs as
 * properly typed terms with De Bruijn indices. This layer is separate from
 * the UI representation and serves as the "ground truth" for what we're proving.
 *
 * Key concepts:
 * - De Bruijn indices: Variables referenced by their binding distance, not names
 * - Dependent types: Types that can depend on values (Π-types, Σ-types)
 * - Eliminators: Induction principles (nat_elim, etc.)
 * - Holes: Unproven parts of the term (metavariables)
 *
 * Example: Induction proof for sum i 1 n i = (n*(n+1))/2
 *
 * The proof term might look like:
 *   nat_elim
 *     (λn. sum i 1 n i = (n*(n+1))/2)  -- motive (type being constructed)
 *     ?base                              -- hole for base case
 *     (λk. λIH. ?inductive)              -- hole for inductive step with IH
 *     n                                  -- value being inducted on
 */

// ============================================================================
// Core Term Language
// ============================================================================

/**
 * Binder kinds: distinguish between different ways to bind variables
 */
export type BinderKind =
  | { tag: 'BPi' }                    // Π-binder (dependent function type)
  | { tag: 'BLam' }                   // λ-binder (function abstraction)
  | { tag: 'BLet'; defVal: TTerm }    // let-binder (local definition with value)

// ============================================================================
// Pattern Matching
// ============================================================================

/**
 * Patterns for pattern matching.
 *
 * Patterns destructure values in pattern matching:
 * - PVar: binds a variable (e.g., 'n' in 'plus n b = ...')
 * - PCtor: constructor application pattern (e.g., 'Zero' or 'Succ n')
 *
 * Wildcards are represented as PVar with name "_".
 *
 * Examples:
 *   Zero           → PCtor("Zero", [])
 *   Succ n         → PCtor("Succ", [PVar("n")])
 *   Succ (Succ m)  → PCtor("Succ", [PCtor("Succ", [PVar("m")])])
 *   _              → PVar("_")
 *   x              → PVar("x")
 */
export type TPattern =
  | { tag: 'PVar'; name: string }                    // Variable pattern (binds) - "_" for wildcard
  | { tag: 'PCtor'; name: string; args: TPattern[] } // Constructor pattern

/**
 * A clause in pattern matching.
 *
 * Consists of:
 * - patterns: One pattern per scrutinee (for now just 1, but future: multi-arg)
 * - rhs: The right-hand side term to evaluate when patterns match
 *
 * Examples:
 *   | Zero => body         → TClause([PCtor("Zero", [])], body)
 *   | Succ n => body       → TClause([PCtor("Succ", [PVar("n")])], body)
 *
 * For function definitions with patterns:
 *   plus Zero b = b        → TClause([PCtor("Zero", []), PVar("b")], Var(0))
 *   plus (Succ a) b = ...  → TClause([PCtor("Succ", [PVar("a")]), PVar("b")], ...)
 *
 * The patterns bind variables in the RHS. Variables are bound left-to-right,
 * depth-first through the pattern tree, and accessible via De Bruijn indices.
 */
export interface TClause {
  patterns: TPattern[];  // Patterns to match (one per argument)
  rhs: TTerm;            // Right-hand side (body) when matched
}

/**
 * The core term language using De Bruijn indices.
 *
 * De Bruijn indices: A variable is represented by a number indicating how many
 * binders we need to traverse to find its binding. For example:
 *   λx. λy. x + y  becomes  λ. λ. 1 + 0
 *   (x is 1 level up, y is 0 levels up)
 *
 * UNIFIED BINDER DESIGN:
 * All binders (Π, λ, let) are represented with a single 'Binder' tag.
 * This allows us to:
 * - Store human-readable names for better pretty-printing
 * - Treat hypotheses as Pi-binders naturally: (a: R) -> (b: R) -> Goal
 * - Handle all binding constructs uniformly
 *
 * Example: A proof with hypotheses (a: R), (b: R) and goal K becomes:
 *   Binder("a", BPi, R, Binder("b", BPi, R, K))
 * Which reads as: (a: R) → (b: R) → K
 */

export type TTermApp = { tag: 'App'; fn: TTerm; arg: TTerm }
export type TTermConst = { tag: 'Const'; name: string; type: TTerm }

export type TTerm =
  | { tag: 'Var'; index: number }                          // De Bruijn variable
  | { tag: 'Sort'; level: number }                         // Type_i, Prop = Type_0
  | { tag: 'Binder'; name: string; binderKind: BinderKind; domain: TTerm; body: TTerm }  // Unified binder
  | TTermApp   // Function application (f a)
  | TTermConst // Named constant (nat_elim, eq, etc.)
  | { tag: 'Hole'; id: string; type: TTerm; context: TContext }  // Metavariable (unproven goal)
  | { tag: 'Annot'; term: TTerm; type: TTerm }            // Type annotation
  | { tag: 'Match'; scrutinee: TTerm; clauses: TClause[] } // Pattern matching (case/match)

export function mapTTerm<R>(
  term: TTerm,
  matchers: { [K in TTerm['tag']]: (term: Extract<TTerm, { tag: K }>) => R }
): R {
  const matcher = matchers[term.tag] as (term: TTerm) => R;
  return matcher(term);
}

/**
 * Named variable in context (for debugging/pretty-printing only)
 * Internally we use De Bruijn indices.
 */
export interface TBinding {
  name: string;      // Human-readable name (for display)
  type: TTerm;       // Type of the variable
}

/**
 * Type-checking context: list of bound variables
 * Index 0 is the most recently bound variable
 */
export type TContext = TBinding[];

/**
 * A hole (metavariable) represents a goal to be proven.
 * It has a type (what we need to prove) and a context (assumptions available).
 */
export interface THole {
  id: string;
  type: TTerm;          // Goal type
  context: TContext;    // Assumptions available
  description?: string; // Human-readable description
}

// ============================================================================
// Built-in Constants and Eliminators
// ============================================================================

/**
 * Built-in type constructors and eliminators
 * These are the primitive constants in our type theory
 */
export const TT_CONSTANTS = {
  // Natural numbers
  Nat: { tag: 'Const', name: 'ℕ', type: { tag: 'Sort', level: 0 } } as const,
  Zero: { tag: 'Const', name: '0', type: { tag: 'Const', name: 'ℕ', type: { tag: 'Sort', level: 0 } } } as const,
  Succ: (() => {
    // Succ : ℕ → ℕ
    const nat = { tag: 'Const', name: 'ℕ', type: { tag: 'Sort', level: 0 } } as TTerm;
    return { tag: 'Const', name: 'succ', type: mkPi(nat, nat, 'n') } as const;
  })(),

  // Real numbers (placeholder - would need proper construction)
  Real: { tag: 'Const', name: 'ℝ', type: { tag: 'Sort', level: 0 } } as const,

  // Equality type
  // eq : Π (A : Type), A → A → Prop
  Eq: (() => {
    const sort0 = { tag: 'Sort', level: 0 } as TTerm;
    const A = { tag: 'Var', index: 0 } as TTerm;
    // Build: Π (A : Type), A → A → Prop
    const type = mkPi(
      sort0,
      mkPi(A, mkPi(A, sort0, 'y'), 'x'),
      'A'
    );
    return { tag: 'Const', name: 'eq', type } as const;
  })(),
} as const satisfies Record<string, TTermConst>

export type TTConstantInfo =
  | { tag: 'binop', infixName?: string }

export const TT_CONSTANTS_INFO = {
  //  eq: { tag: 'binop', infixName: '=' }
} satisfies Partial<Record<typeof TT_CONSTANTS[keyof typeof TT_CONSTANTS]['name'], TTConstantInfo>>

export function ttconstInfo(term: TTermConst): TTConstantInfo | undefined {
  return TT_CONSTANTS_INFO[term.name as keyof typeof TT_CONSTANTS_INFO]
}

/**
 * Natural number eliminator (induction principle)
 *
 * For simplicity, we'll use a simplified version for now that works with
 * non-dependent predicates:
 *
 * nat_elim : Π (P : Prop), P → (P → P) → ℕ → P
 *
 * This is sufficient for testing and will be expanded to the full dependent version later.
 */
export function createNatElimType(): TTerm {
  const prop: TTerm = { tag: 'Sort', level: 0 };
  const nat = TT_CONSTANTS.Nat;

  // Simplified nat_elim for testing:
  // Π (P : Prop), P → (P → P) → ℕ → P

  const P = { tag: 'Var', index: 0 } as TTerm;

  // Build type step by step using mkPi:
  // Start from innermost: P (result)
  // Then: ℕ → P
  const natToP = mkPi(nat, { tag: 'Var', index: 3 }, 'n');

  // Then: (P → P) → (ℕ → P)
  const stepThenNat = mkPi(
    mkPi({ tag: 'Var', index: 1 }, { tag: 'Var', index: 2 }, 'ih'),
    natToP,
    'step'
  );

  // Then: P → ((P → P) → (ℕ → P))
  const baseToRest = mkPi(P, stepThenNat, 'base');

  // Finally: Π (P : Prop), ...
  return mkPi(prop, baseToRest, 'P');
}

export const NAT_ELIM: TTerm = {
  tag: 'Const',
  name: 'nat_elim',
  type: createNatElimType()
};

// ============================================================================
// Helper Functions for Term Construction
// ============================================================================

/**
 * Create a De Bruijn variable
 */
export function mkVar(index: number): TTerm {
  return { tag: 'Var', index };
}

/**
 * Create a Pi type (dependent function type)
 * If no name is provided, generates a default name
 */
export function mkPi(domain: TTerm, codomain: TTerm, name: string = 'x'): TTerm {
  return {
    tag: 'Binder',
    name,
    binderKind: { tag: 'BPi' },
    domain,
    body: codomain
  };
}

/**
 * Create a Lambda (function abstraction)
 * If no name is provided, generates a default name
 */
export function mkLambda(domain: TTerm, body: TTerm, name: string = 'x'): TTerm {
  return {
    tag: 'Binder',
    name,
    binderKind: { tag: 'BLam' },
    domain,
    body
  };
}

/**
 * Create a Let binding
 * Requires name for the bound variable and the value being bound
 */
export function mkLet(name: string, defType: TTerm, defVal: TTerm, body: TTerm): TTerm {
  return {
    tag: 'Binder',
    name,
    binderKind: { tag: 'BLet', defVal },
    domain: defType,
    body
  };
}

/**
 * Create a function application
 */
export function mkApp(fn: TTerm, arg: TTerm): TTerm {
  return { tag: 'App', fn, arg };
}

/**
 * Create a constant with a given name and type
 */
export function mkConst(name: string, type: TTerm): TTerm {
  return { tag: 'Const', name, type };
}

/**
 * Create a hole (metavariable to be filled)
 */
export function mkHole(id: string, type: TTerm, context: TContext = []): TTerm {
  return { tag: 'Hole', id, type, context };
}

/**
 * Create Prop (Type_0)
 */
export function mkProp(): TTerm {
  return { tag: 'Sort', level: 0 };
}

/**
 * Create Type_i
 */
export function mkType(level: number): TTerm {
  return { tag: 'Sort', level };
}

// ============================================================================
// Hole Replacement
// ============================================================================

/**
 * Replace all occurrences of a hole with a given term.
 * 
 * This is useful when filling in type holes or other metavariables.
 * For example, replacing ?type_a with ℝ throughout a term.
 * 
 * @param term - The term to search and replace in
 * @param holeId - ID of the hole to replace
 * @param replacement - Term to replace the hole with
 * @returns New term with all holes replaced
 */
export function replaceHole(term: TTerm, holeId: string, replacement: TTerm): TTerm {
  switch (term.tag) {
    case 'Var':
    case 'Sort':
    case 'Const':
      return term;

    case 'Hole':
      // If this is the hole we're looking for, replace it
      return term.id === holeId ? replacement : term;

    case 'Binder': {
      const newDomain = replaceHole(term.domain, holeId, replacement);
      const newBody = replaceHole(term.body, holeId, replacement);

      let newBinderKind: BinderKind;
      if (term.binderKind.tag === 'BLet') {
        const newDefVal = replaceHole(term.binderKind.defVal, holeId, replacement);
        newBinderKind = { tag: 'BLet', defVal: newDefVal };
      } else {
        newBinderKind = term.binderKind;
      }

      return {
        tag: 'Binder',
        name: term.name,
        binderKind: newBinderKind,
        domain: newDomain,
        body: newBody
      };
    }

    case 'App':
      return {
        tag: 'App',
        fn: replaceHole(term.fn, holeId, replacement),
        arg: replaceHole(term.arg, holeId, replacement)
      };

    case 'Annot':
      return {
        tag: 'Annot',
        term: replaceHole(term.term, holeId, replacement),
        type: replaceHole(term.type, holeId, replacement)
      };

    case 'Match':
      return {
        tag: 'Match',
        scrutinee: replaceHole(term.scrutinee, holeId, replacement),
        clauses: term.clauses.map(c => ({
          patterns: c.patterns,
          rhs: replaceHole(c.rhs, holeId, replacement)
        }))
      };
  }
}

// ============================================================================
// Definitional Equality & Term Extraction
// ============================================================================

/**
 * Check if two terms are definitionally equal.
 * 
 * For now, this implements structural equality (alpha-equivalence).
 * Later, this can be enhanced with:
 * - Beta-reduction: (λx. e) a ≡ e[a/x]
 * - Eta-conversion: λx. f x ≡ f (when x not free in f)
 * - Delta-reduction: unfold definitions
 * 
 * @param term1 - First term
 * @param term2 - Second term
 * @returns true if terms are definitionally equal
 */
export function isDefinitionallyEqual(term1: TTerm, term2: TTerm): boolean {
  // Structural equality check
  if (term1.tag !== term2.tag) return false;

  switch (term1.tag) {
    case 'Var':
      return term2.tag === 'Var' && term1.index === term2.index;

    case 'Sort':
      return term2.tag === 'Sort' && term1.level === term2.level;

    case 'Const':
      return term2.tag === 'Const' && term1.name === term2.name;

    case 'Hole':
      // Holes are only equal if they have the same ID
      return term2.tag === 'Hole' && term1.id === term2.id;

    case 'Binder': {
      if (term2.tag !== 'Binder') return false;

      // Check binder kind
      if (term1.binderKind.tag !== term2.binderKind.tag) return false;
      if (term1.binderKind.tag === 'BLet' && term2.binderKind.tag === 'BLet') {
        if (!isDefinitionallyEqual(term1.binderKind.defVal, term2.binderKind.defVal)) {
          return false;
        }
      }

      // Check domain and body (names don't matter for equality)
      return isDefinitionallyEqual(term1.domain, term2.domain) &&
        isDefinitionallyEqual(term1.body, term2.body);
    }

    case 'App': {
      if (term2.tag !== 'App') return false;
      return isDefinitionallyEqual(term1.fn, term2.fn) &&
        isDefinitionallyEqual(term1.arg, term2.arg);
    }

    case 'Annot': {
      if (term2.tag !== 'Annot') return false;
      return isDefinitionallyEqual(term1.term, term2.term) &&
        isDefinitionallyEqual(term1.type, term2.type);
    }

    case 'Match': {
      if (term2.tag !== 'Match') return false;
      // Check scrutinee
      if (!isDefinitionallyEqual(term1.scrutinee, term2.scrutinee)) return false;
      // Check same number of clauses
      if (term1.clauses.length !== term2.clauses.length) return false;
      // Check each clause (patterns and rhs)
      for (let i = 0; i < term1.clauses.length; i++) {
        const c1 = term1.clauses[i];
        const c2 = term2.clauses[i];
        // For now, just check RHS equality (pattern equality would need a separate function)
        if (!isDefinitionallyEqual(c1.rhs, c2.rhs)) return false;
      }
      return true;
    }
  }
}

/**
 * Get subterm at a given path (index path into the term tree).
 * 
 * Path indices navigate the term structure:
 * - For App: [0] = fn, [1] = arg
 * - For Binder: [0] = domain, [1] = body
 * - etc.
 * 
 * @param term - The term to navigate
 * @param path - Array of indices representing the path
 * @returns The subterm at the path, or null if path is invalid
 */
export function getSubtermAtPath(term: TTerm, path: number[]): TTerm | null {
  if (path.length === 0) return term;

  const [head, ...rest] = path;

  switch (term.tag) {
    case 'Var':
    case 'Sort':
    case 'Const':
    case 'Hole':
      // Leaf nodes have no children
      return null;

    case 'App':
      if (head === 0) return getSubtermAtPath(term.fn, rest);
      if (head === 1) return getSubtermAtPath(term.arg, rest);
      return null;

    case 'Binder':
      if (head === 0) return getSubtermAtPath(term.domain, rest);
      if (head === 1) return getSubtermAtPath(term.body, rest);
      if (head === 2 && term.binderKind.tag === 'BLet') {
        return getSubtermAtPath(term.binderKind.defVal, rest);
      }
      return null;

    case 'Annot':
      if (head === 0) return getSubtermAtPath(term.term, rest);
      if (head === 1) return getSubtermAtPath(term.type, rest);
      return null;

    case 'Match':
      // path[0] = 0 means scrutinee
      if (head === 0) return getSubtermAtPath(term.scrutinee, rest);
      // path[0] = 1, 2, 3, ... means clause index (0, 1, 2, ...)
      if (head >= 1 && head <= term.clauses.length) {
        const clauseIndex = head - 1;
        return getSubtermAtPath(term.clauses[clauseIndex].rhs, rest);
      }
      return null;
  }
}

/**
 * Replace subterm at a given path with a new term.
 * 
 * @param term - The term to modify
 * @param path - Array of indices representing the path
 * @param newSubterm - The new subterm to insert
 * @returns The modified term, or null if path is invalid
 */
export function replaceSubtermAtPath(term: TTerm, path: number[], newSubterm: TTerm): TTerm | null {
  if (path.length === 0) return newSubterm;

  const [head, ...rest] = path;

  switch (term.tag) {
    case 'Var':
    case 'Sort':
    case 'Const':
    case 'Hole':
      // Leaf nodes have no children
      return null;

    case 'App': {
      if (head === 0) {
        const newFn = replaceSubtermAtPath(term.fn, rest, newSubterm);
        return newFn ? { ...term, fn: newFn } : null;
      }
      if (head === 1) {
        const newArg = replaceSubtermAtPath(term.arg, rest, newSubterm);
        return newArg ? { ...term, arg: newArg } : null;
      }
      return null;
    }

    case 'Binder': {
      if (head === 0) {
        const newDomain = replaceSubtermAtPath(term.domain, rest, newSubterm);
        return newDomain ? { ...term, domain: newDomain } : null;
      }
      if (head === 1) {
        const newBody = replaceSubtermAtPath(term.body, rest, newSubterm);
        return newBody ? { ...term, body: newBody } : null;
      }
      if (head === 2 && term.binderKind.tag === 'BLet') {
        const newDefVal = replaceSubtermAtPath(term.binderKind.defVal, rest, newSubterm);
        return newDefVal ? {
          ...term,
          binderKind: { tag: 'BLet', defVal: newDefVal }
        } : null;
      }
      return null;
    }

    case 'Annot': {
      if (head === 0) {
        const newTerm = replaceSubtermAtPath(term.term, rest, newSubterm);
        return newTerm ? { ...term, term: newTerm } : null;
      }
      if (head === 1) {
        const newType = replaceSubtermAtPath(term.type, rest, newSubterm);
        return newType ? { ...term, type: newType } : null;
      }
      return null;
    }

    case 'Match': {
      // path[0] = 0 means scrutinee
      if (head === 0) {
        const newScrutinee = replaceSubtermAtPath(term.scrutinee, rest, newSubterm);
        return newScrutinee ? { ...term, scrutinee: newScrutinee } : null;
      }
      // path[0] = 1, 2, 3, ... means clause index (0, 1, 2, ...)
      if (head >= 1 && head <= term.clauses.length) {
        const clauseIndex = head - 1;
        const newRhs = replaceSubtermAtPath(term.clauses[clauseIndex].rhs, rest, newSubterm);
        if (!newRhs) return null;
        const newClauses = [...term.clauses];
        newClauses[clauseIndex] = { ...term.clauses[clauseIndex], rhs: newRhs };
        return { ...term, clauses: newClauses };
      }
      return null;
    }
  }
}

/**
 * Extract terms at given paths and create a lambda abstraction.
 * 
 * This implements the "beta-redux" view:
 * - Given term `a + b` with focus on `b`, produces `(λx. a + x) b`
 * - Given term `λy. (A -> y)` with focus on `A`, produces `(λx. λy. (x -> y)) A`
 * 
 * All subterms at the given paths must be definitionally equal, otherwise
 * this returns an error.
 * 
 * @param term - The term to extract from
 * @param paths - Array of index paths to the subterms to extract
 * @returns Object with lambda and extracted term, or error message
 */
export function asLambdaByExtractingTermAtIndexPaths(
  term: TTerm,
  paths: number[][]
): { lambda: TTerm; extracted: TTerm } | { error: string } {
  // Handle empty paths case
  if (paths.length === 0) {
    return { error: 'No paths provided for extraction' };
  }

  // Get the subterms at all paths
  const subterms = paths.map(path => getSubtermAtPath(term, path));

  // Check if any path is invalid
  if (subterms.some(t => t === null)) {
    return { error: 'Invalid path: one or more paths do not point to valid subterms' };
  }

  // Check that all subterms are definitionally equal
  const firstSubterm = subterms[0]!;
  for (let i = 1; i < subterms.length; i++) {
    if (!isDefinitionallyEqual(firstSubterm, subterms[i]!)) {
      return {
        error: `Subterms at paths are not definitionally equal:\n` +
          `  Path ${JSON.stringify(paths[0])}: ${prettyPrint(firstSubterm)}\n` +
          `  Path ${JSON.stringify(paths[i])}: ${prettyPrint(subterms[i]!)}`
      };
    }
  }

  // Create a fresh variable (De Bruijn index 0 in the new context)
  const varTerm: TTerm = { tag: 'Var', index: 0 };

  // Replace all occurrences of the subterm with the variable
  let lambdaBody = term;
  for (const path of paths) {
    const replaced = replaceSubtermAtPath(lambdaBody, path, varTerm);
    if (!replaced) {
      return { error: `Failed to replace subterm at path ${JSON.stringify(path)}` };
    }
    lambdaBody = replaced;
  }

  // Note: We should technically shift free variables in the lambda body to account for the new binder.
  // However, since we're working with terms that may come from ExpressionNodes (which don't use
  // De Bruijn indices yet), we'll skip this for now. A proper implementation would need to:
  // 1. Track which variables are free in the original term
  // 2. Increment their indices by 1 when wrapping with the lambda
  // For now, we assume the term doesn't have free De Bruijn variables that would conflict.

  // Create the lambda abstraction
  // Type inference will determine the type of x later
  const typeHole = mkHole('extracted-type', mkType(0));
  const lambda: TTerm = {
    tag: 'Binder',
    name: 'x',
    binderKind: { tag: 'BLam' },
    domain: typeHole,
    body: lambdaBody
  };

  return {
    lambda,
    extracted: firstSubterm
  };
}

// ============================================================================
// Usage Checking (for safe deletion)
// ============================================================================

/**
 * Check if a constant/variable name is referenced in a term
 * 
 * This traverses the entire term tree looking for:
 * - Const nodes with matching name
 * - Binders that bind the name (shadows it, so stops searching in body)
 * 
 * Important: This checks for FREE occurrences of the name. If a binder
 * shadows the name, we don't search in its body.
 * 
 * @param name - Variable/constant name to search for
 * @param term - Term to search in
 * @returns true if name is referenced (not shadowed)
 */
export function isNameUsed(name: string, term: TTerm): boolean {
  switch (term.tag) {
    case 'Var':
      // De Bruijn index - can't directly check by name
      return false;

    case 'Const':
      // Direct name match
      return term.name === name;

    case 'Sort':
      // No names to check
      return false;

    case 'Hole':
      // Holes don't contain the name itself, but check their type
      return isNameUsed(name, term.type);

    case 'Binder':
      // Check domain
      if (isNameUsed(name, term.domain)) return true;

      // Check let-binding value if present
      if (term.binderKind.tag === 'BLet') {
        if (isNameUsed(name, term.binderKind.defVal)) return true;
      }

      // Check body - BUT if this binder binds our name, it shadows it
      if (term.name === name) {
        // Name is shadowed in the body, don't search there
        return false;
      }
      return isNameUsed(name, term.body);

    case 'App':
      return isNameUsed(name, term.fn) || isNameUsed(name, term.arg);

    case 'Annot':
      return isNameUsed(name, term.term) || isNameUsed(name, term.type);

    case 'Match':
      // Check scrutinee
      if (isNameUsed(name, term.scrutinee)) return true;
      // Check all clause RHS terms
      for (const clause of term.clauses) {
        if (isNameUsed(name, clause.rhs)) return true;
      }
      return false;
  }
}

// ============================================================================
// Substitution (for De Bruijn indices)
// ============================================================================

/**
 * Substitute term s for variable with index n in term t
 * This is the core operation for beta-reduction and let-expansion
 *
 * subst(n, s, t) replaces variable n in t with s, adjusting indices
 */
export function subst(index: number, replacement: TTerm, term: TTerm): TTerm {
  return substHelper(index, replacement, term, 0);
}

/**
 * Helper for substitution that tracks the current binding depth
 *
 * @param targetIndex - The De Bruijn index we're replacing
 * @param replacement - The term to substitute in
 * @param term - The term we're substituting into
 * @param depth - Current binding depth (how many binders we've gone under)
 */
function substHelper(targetIndex: number, replacement: TTerm, term: TTerm, depth: number): TTerm {
  switch (term.tag) {
    case 'Var':
      // If this is the variable we're replacing
      if (term.index === targetIndex + depth) {
        // Shift the replacement term by depth (it's going under 'depth' binders)
        return shift(depth, replacement, 0);
      }
      return term;

    case 'Sort':
    case 'Const':
      return term;

    case 'Binder': {
      // Handle all binder types uniformly
      const newDomain = substHelper(targetIndex, replacement, term.domain, depth);
      const newBody = substHelper(targetIndex, replacement, term.body, depth + 1);

      // For BLet, also substitute in the definition value
      let newBinderKind: BinderKind;
      if (term.binderKind.tag === 'BLet') {
        const newDefVal = substHelper(targetIndex, replacement, term.binderKind.defVal, depth);
        newBinderKind = { tag: 'BLet', defVal: newDefVal };
      } else {
        newBinderKind = term.binderKind;
      }

      return {
        tag: 'Binder',
        name: term.name,
        binderKind: newBinderKind,
        domain: newDomain,
        body: newBody
      };
    }

    case 'App':
      return {
        tag: 'App',
        fn: substHelper(targetIndex, replacement, term.fn, depth),
        arg: substHelper(targetIndex, replacement, term.arg, depth)
      };

    case 'Hole':
      return {
        tag: 'Hole',
        id: term.id,
        type: substHelper(targetIndex, replacement, term.type, depth),
        context: term.context  // Context doesn't change
      };

    case 'Annot':
      return {
        tag: 'Annot',
        term: substHelper(targetIndex, replacement, term.term, depth),
        type: substHelper(targetIndex, replacement, term.type, depth)
      };

    case 'Match':
      return {
        tag: 'Match',
        scrutinee: substHelper(targetIndex, replacement, term.scrutinee, depth),
        clauses: term.clauses.map(c => ({
          patterns: c.patterns,
          // TODO: when we implement proper pattern binding, we need to account for
          // variables bound by patterns when substituting in the RHS
          rhs: substHelper(targetIndex, replacement, c.rhs, depth)
        }))
      };
  }
}

/**
 * Shift De Bruijn indices in a term
 * Used when moving a term under binders
 *
 * @param amount - How much to shift by
 * @param term - The term to shift
 * @param cutoff - Only shift variables >= cutoff
 */
function shift(amount: number, term: TTerm, cutoff: number): TTerm {
  switch (term.tag) {
    case 'Var':
      return term.index >= cutoff
        ? { tag: 'Var', index: term.index + amount }
        : term;

    case 'Sort':
    case 'Const':
      return term;

    case 'Binder': {
      // Handle all binder types uniformly
      const newDomain = shift(amount, term.domain, cutoff);
      const newBody = shift(amount, term.body, cutoff + 1);

      // For BLet, also shift the definition value
      let newBinderKind: BinderKind;
      if (term.binderKind.tag === 'BLet') {
        const newDefVal = shift(amount, term.binderKind.defVal, cutoff);
        newBinderKind = { tag: 'BLet', defVal: newDefVal };
      } else {
        newBinderKind = term.binderKind;
      }

      return {
        tag: 'Binder',
        name: term.name,
        binderKind: newBinderKind,
        domain: newDomain,
        body: newBody
      };
    }

    case 'App':
      return {
        tag: 'App',
        fn: shift(amount, term.fn, cutoff),
        arg: shift(amount, term.arg, cutoff)
      };

    case 'Hole':
      return {
        tag: 'Hole',
        id: term.id,
        type: shift(amount, term.type, cutoff),
        context: term.context
      };

    case 'Annot':
      return {
        tag: 'Annot',
        term: shift(amount, term.term, cutoff),
        type: shift(amount, term.type, cutoff)
      };

    case 'Match':
      return {
        tag: 'Match',
        scrutinee: shift(amount, term.scrutinee, cutoff),
        clauses: term.clauses.map(c => ({
          patterns: c.patterns,
          // TODO: when we implement proper pattern binding, we need to account for
          // variables bound by patterns when shifting in the RHS
          rhs: shift(amount, c.rhs, cutoff)
        }))
      };
  }
}

// ============================================================================
// Pretty Printing (De Bruijn to Named Variables)
// ============================================================================

/**
 * Terse pretty-printing for TT terms - compact S-expression style
 * Example: (eq (plus a a) (mul 2 a)) instead of ((a : ℝ) → ...)
 */
export function prettyPrintTerse(term: TTerm, context: string[] = []): string {
  switch (term.tag) {
    case 'Var':
      // Context is prepended, so index directly into it
      if (term.index < context.length) {
        return context[term.index];
      }
      return `_${term.index}`;

    case 'Sort':
      // Sort(0) = Prop, Sort(1) = Type, Sort(n+1) = Type n
      if (term.level === 0) {
        return 'Prop';
      }
      const typeLevel = term.level - 1;
      return typeLevel === 0 ? 'Type' : `Type ${typeLevel}`;

    case 'Const':
      // Try to extract just the meaningful name from verbose strings
      return term.name;

    case 'Binder': {
      const newContext = [term.name, ...context];
      const body = prettyPrintTerse(term.body, newContext);
      const domain = prettyPrintTerse(term.domain, context);
      const isAnonymous = term.name === '_' || term.name === '';

      switch (term.binderKind.tag) {
        case 'BPi':
          // Check if non-dependent (function type) or anonymous
          if (!occursIn(0, term.body) || isAnonymous) {
            return `(${domain} -> ${body})`;
          }
          return `((${term.name} : ${domain}) -> ${body})`;

        case 'BLam':
          if (isAnonymous) {
            return `(\\${domain} => ${body})`;
          }
          return `(\\${term.name} => ${body})`;

        case 'BLet':
          const defVal = prettyPrintTerse(term.binderKind.defVal, context);
          return `(let ${term.name} = ${defVal} in ${body})`;
      }
    }

    case 'App': {
      const fn = prettyPrintTerse(term.fn, context);
      const arg = prettyPrintTerse(term.arg, context);

      // Get function name for cleaner output
      const fnName = term.fn.tag === 'Const' ? term.fn.name : fn;

      // Special handling for known operators
      if (fnName === 'eq' || fnName === 'plus' || fnName === 'mul' || fnName === 'minus') {
        return `(${fnName} ${fn === fnName ? '' : fn} ${arg})`.replace(/\s+/g, ' ').trim();
      }

      return `(${fn} ${arg})`;
    }

    case 'Hole':
      return '?';

    case 'Annot':
      return prettyPrintTerse(term.term, context);

    case 'Match': {
      const scrutinee = prettyPrintTerse(term.scrutinee, context);
      const clauses = term.clauses.map(c => {
        // TODO: when we implement proper pattern binding, we need to extend context with pattern vars
        const patternStr = c.patterns.map(p => prettyPrintPattern(p)).join(' ');
        const rhsStr = prettyPrintTerse(c.rhs, context);
        return `${patternStr} => ${rhsStr}`;
      }).join(' | ');
      return `(match ${scrutinee} | ${clauses})`;
    }
  }
}

/**
 * Pretty-print a pattern (helper for Match)
 */
function prettyPrintPattern(pattern: TPattern): string {
  switch (pattern.tag) {
    case 'PVar':
      return pattern.name;  // "_" for wildcards
    case 'PCtor':
      if (pattern.args.length === 0) {
        return pattern.name;
      }
      const args = pattern.args.map(prettyPrintPattern).join(' ');
      return `(${pattern.name} ${args})`;
  }
}

// Helper to strip outer parentheses from a string
function stripOuterParens(s: string): string {
  if (s.startsWith('(') && s.endsWith(')')) {
    return s.slice(1, -1);
  }
  return s;
}

/**
 * Convert a term with De Bruijn indices to a human-readable string
 * Now uses the names stored in binders for better readability
 */
export function prettyPrint(term: TTerm, context: string[] = []): string {
  switch (term.tag) {
    case 'Var':
      // Look up the name from context (context is prepended, so index directly)
      if (term.index < context.length) {
        return context[term.index];
      }
      return `#${term.index}`;  // Free variable

    case 'Sort':
      // Sort(0) = Prop, Sort(1) = Type (or Type 0), Sort(n+1) = Type n
      // Following Lean's convention where Type = Sort 1, Type 1 = Sort 2, etc.
      if (term.level === 0) {
        return 'Prop';
      }
      const typeLevel = term.level - 1;
      return typeLevel === 0 ? 'Type' : `Type ${typeLevel}`;

    case 'Const':
      return term.name;

    case 'Binder': {
      const newContext = [term.name, ...context];
      const isAnonymous = term.name === '_' || term.name === '';

      switch (term.binderKind.tag) {
        case 'BPi': {
          // Collect all arrow parts: A -> B -> C -> D becomes [A, B, C, D]
          const parts: string[] = [];
          let current: TTerm = term;
          let ctx = context;
          while (current.tag === 'Binder' && current.binderKind.tag === 'BPi') {
            const currentAnon = current.name === '_' || current.name === '';
            const domain = stripOuterParens(prettyPrint(current.domain, ctx));
            if (currentAnon) {
              parts.push(domain);
            } else {
              parts.push(`(${current.name} : ${domain})`);
            }
            ctx = [current.name, ...ctx];
            current = current.body;
          }
          parts.push(prettyPrint(current, ctx));
          return `(${parts.join(' -> ')})`;
        }

        case 'BLam': {
          const domain = stripOuterParens(prettyPrint(term.domain, context));
          const body = prettyPrint(term.body, newContext);
          if (isAnonymous) {
            return `(\\${domain} => ${body})`;
          }
          return `(\\(${term.name} : ${domain}) => ${body})`;
        }

        case 'BLet': {
          const domain = stripOuterParens(prettyPrint(term.domain, context));
          const body = prettyPrint(term.body, newContext);
          const defVal = prettyPrint(term.binderKind.defVal, context);
          return `(let ${term.name} : ${domain} := ${defVal} in ${body})`;
        }
      }
    }

    case 'App': {
      // Collect all arguments from nested applications: ((f a) b) c -> [f, a, b, c]
      const parts: string[] = [];
      let current: TTerm = term;
      while (current.tag === 'App') {
        parts.unshift(prettyPrint(current.arg, context));
        current = current.fn;
      }
      parts.unshift(prettyPrint(current, context));
      return `(${parts.join(' ')})`;
    }

    case 'Hole':
      return `?${term.id}`;

    case 'Annot': {
      const termStr = prettyPrint(term.term, context);
      const typeStr = stripOuterParens(prettyPrint(term.type, context));
      return `(${termStr} : ${typeStr})`;
    }

    case 'Match': {
      const scrutinee = prettyPrint(term.scrutinee, context);
      const clauses = term.clauses.map(c => {
        // TODO: when we implement proper pattern binding, we need to extend context with pattern vars
        const patternStr = c.patterns.map(p => prettyPrintPattern(p)).join(' ');
        const rhsStr = prettyPrint(c.rhs, context);
        return `${patternStr} => ${rhsStr}`;
      }).join(' | ');
      return `(match ${scrutinee} | ${clauses})`;
    }
  }
}

// ============================================================================
// LaTeX Pretty Printing
// ============================================================================

/**
 * Options for LaTeX pretty printing
 */
export interface LatexPrintOptions {
  /** If true, show type subscript on equality: x =_A y. If false, just x = y */
  showEqTypeSubscript?: boolean;
}

const defaultLatexOptions: LatexPrintOptions = {
  showEqTypeSubscript: true,
};

/**
 * Try to match a term against the pattern: Eq A x y
 * Returns { typeArg, lhs, rhs } if matched, otherwise null
 */
function matchEqApp(term: TTerm): { typeArg: TTerm; lhs: TTerm; rhs: TTerm } | null {
  // Eq A x y is App(App(App(Eq, A), x), y)
  if (term.tag !== 'App') return null;
  const rhs = term.arg;
  const app2 = term.fn;

  if (app2.tag !== 'App') return null;
  const lhs = app2.arg;
  const app1 = app2.fn;

  if (app1.tag !== 'App') return null;
  const typeArg = app1.arg;
  const eqConst = app1.fn;

  if (eqConst.tag !== 'Const' || eqConst.name !== 'Eq') return null;

  return { typeArg, lhs, rhs };
}

/**
 * Convert a TT term to a LaTeX string for mathematical rendering
 */
export function prettyPrintLatex(
  term: TTerm,
  context: string[] = [],
  options: LatexPrintOptions = defaultLatexOptions
): string {
  const opts = { ...defaultLatexOptions, ...options };

  // Check for Eq pattern first
  const eqMatch = matchEqApp(term);
  if (eqMatch) {
    const lhs = prettyPrintLatex(eqMatch.lhs, context, opts);
    const rhs = prettyPrintLatex(eqMatch.rhs, context, opts);
    if (opts.showEqTypeSubscript) {
      const typeArg = prettyPrintLatex(eqMatch.typeArg, context, opts);
      return `${lhs} =_{${typeArg}} ${rhs}`;
    } else {
      return `${lhs} = ${rhs}`;
    }
  }

  switch (term.tag) {
    case 'Var':
      if (term.index < context.length) {
        return context[term.index];
      }
      return `\\#${term.index}`;

    case 'Sort':
      // Sort(0) = Prop, Sort(1) = Type, Sort(n+1) = Type n
      if (term.level === 0) {
        return '\\text{Prop}';
      }
      const typeLevelLatex = term.level - 1;
      return typeLevelLatex === 0 ? '\\text{Type}' : `\\text{Type}_{${typeLevelLatex}}`;

    case 'Const':
      // Escape special LaTeX characters in names
      return term.name.replace(/_/g, '\\_');

    case 'Binder': {
      const domain = prettyPrintLatex(term.domain, context, opts);
      const newContext = [term.name, ...context];
      const body = prettyPrintLatex(term.body, newContext, opts);
      const isAnonymous = term.name === '_' || term.name === '';

      switch (term.binderKind.tag) {
        case 'BPi':
          if (isAnonymous || !occursIn(0, term.body)) {
            return `(${domain} \\to ${body})`;
          }
          return `(\\Pi\\, (${term.name} : ${domain}),\\, ${body})`;

        case 'BLam':
          if (isAnonymous) {
            return `(\\lambda\\, ${domain},\\, ${body})`;
          }
          return `(\\lambda\\, (${term.name} : ${domain}),\\, ${body})`;

        case 'BLet':
          const defVal = prettyPrintLatex(term.binderKind.defVal, context, opts);
          return `(\\text{let } ${term.name} : ${domain} := ${defVal} \\text{ in } ${body})`;
      }
    }

    case 'App': {
      const fn = prettyPrintLatex(term.fn, context, opts);
      const arg = prettyPrintLatex(term.arg, context, opts);
      return `(${fn}\\; ${arg})`;
    }

    case 'Hole':
      return `?_{${term.id}}`;

    case 'Annot':
      return `(${prettyPrintLatex(term.term, context, opts)} : ${prettyPrintLatex(term.type, context, opts)})`;

    case 'Match': {
      const scrutinee = prettyPrintLatex(term.scrutinee, context, opts);
      const clauses = term.clauses.map(c => {
        // TODO: when we implement proper pattern binding, we need to extend context with pattern vars
        const patternStr = c.patterns.map(p => prettyPrintPatternLatex(p)).join('\\; ');
        const rhsStr = prettyPrintLatex(c.rhs, context, opts);
        return `${patternStr} \\Rightarrow ${rhsStr}`;
      }).join(' \\mid ');
      return `\\text{match}\\; ${scrutinee}\\; \\{\\, ${clauses} \\,\\}`;
    }
  }
}

/**
 * Pretty-print a pattern in LaTeX format (helper for Match)
 */
function prettyPrintPatternLatex(pattern: TPattern): string {
  switch (pattern.tag) {
    case 'PVar':
      // Escape underscores for LaTeX (including "_" wildcards)
      return pattern.name.replace(/_/g, '\\_');
    case 'PCtor':
      if (pattern.args.length === 0) {
        return pattern.name.replace(/_/g, '\\_');
      }
      const args = pattern.args.map(prettyPrintPatternLatex).join('\\; ');
      return `(${pattern.name.replace(/_/g, '\\_')}\\; ${args})`;
  }
}

// ============================================================================
// Helper: Convert Hypotheses to Pi Binders
// ============================================================================

/**
 * Convert a list of hypotheses (assumptions) into a nested Pi type.
 *
 * This is the key helper for making hypotheses part of the AST!
 *
 * Given hypotheses [(a: R), (b: R)] and goal K, produces:
 *   (a: R) → (b: R) → K
 *
 * Which is represented as:
 *   Binder("a", BPi, R, Binder("b", BPi, R, K))
 *
 * @param hypotheses - List of (name, type) pairs
 * @param goal - The goal/conclusion type
 * @returns A nested Pi type representing the theorem to prove
 *
 * Example:
 *   hypothesesToPi([["a", Real], ["b", Real]], goal)
 *   // Returns: (a: ℝ) → (b: ℝ) → goal
 */
export function hypothesesToPi(hypotheses: Array<[string, TTerm]>, goal: TTerm): TTerm {
  // Build from right to left (innermost first)
  let result = goal;
  for (let i = hypotheses.length - 1; i >= 0; i--) {
    const [name, type] = hypotheses[i];
    result = mkPi(type, result, name);
  }
  return result;
}

/**
 * Convert a list of hypotheses into nested Lambda abstractions.
 *
 * This is used to construct proof terms that take hypotheses as arguments.
 *
 * Given hypotheses [(a: R), (b: R)] and body term t, produces:
 *   λ(a: R). λ(b: R). t
 *
 * @param hypotheses - List of (name, type) pairs
 * @param body - The proof term body
 * @returns A nested Lambda term
 */
export function hypothesesToLambda(hypotheses: Array<[string, TTerm]>, body: TTerm): TTerm {
  let result = body;
  for (let i = hypotheses.length - 1; i >= 0; i--) {
    const [name, type] = hypotheses[i];
    result = mkLambda(type, result, name);
  }
  return result;
}

// ============================================================================
// Equality Type Constructors
// ============================================================================

/**
 * Construct an equality type: a = b
 * 
 * In type theory, equality is represented as a type constructor:
 *   Eq : ∀ (α : Type) (a b : α), Prop
 * 
 * For now, we simplify and just use a constant "Eq" applied to two terms.
 * 
 * @param a - Left side of equality
 * @param b - Right side of equality
 * @returns Term representing the type (a = b)
 */
export function mkEq(a: TTerm, b: TTerm): TTerm {
  // Eq a b : Prop
  return mkApp(mkApp(mkConst('Eq', mkProp()), a), b);
}

/**
 * Construct a reflexivity proof: refl a : a = a
 * 
 * Reflexivity states that everything is equal to itself.
 * 
 * @param a - The term
 * @returns Proof term for (a = a)
 */
export function mkRefl(a: TTerm): TTerm {
  // refl : ∀ {α : Type} (a : α), a = a
  return mkApp(mkConst('refl', mkProp()), a);
}

/**
 * Construct a symmetry proof: sym h : b = a (given h : a = b)
 * 
 * Symmetry states that if a = b, then b = a.
 * 
 * @param proof - Proof of (a = b)
 * @returns Proof term for (b = a)
 */
export function mkSym(proof: TTerm): TTerm {
  // sym : ∀ {α : Type} {a b : α}, (a = b) → (b = a)
  return mkApp(mkConst('sym', mkProp()), proof);
}

/**
 * Construct a transitivity proof: trans h1 h2 : a = c (given h1 : a = b, h2 : b = c)
 * 
 * Transitivity states that if a = b and b = c, then a = c.
 * 
 * @param proof1 - Proof of (a = b)
 * @param proof2 - Proof of (b = c)
 * @returns Proof term for (a = c)
 */
export function mkTrans(proof1: TTerm, proof2: TTerm): TTerm {
  // trans : ∀ {α : Type} {a b c : α}, (a = b) → (b = c) → (a = c)
  return mkApp(mkApp(mkConst('trans', mkProp()), proof1), proof2);
}

/**
 * Construct a congruence proof: cong f h : f a = f b (given h : a = b)
 * 
 * Congruence states that if a = b, then applying any function f gives f a = f b.
 * 
 * @param f - The function to apply
 * @param proof - Proof of (a = b)
 * @returns Proof term for (f a = f b)
 */
export function mkCong(f: TTerm, proof: TTerm): TTerm {
  // cong : ∀ {α β : Type} (f : α → β) {a b : α}, (a = b) → (f a = f b)
  return mkApp(mkApp(mkConst('cong', mkProp()), f), proof);
}

// ============================================================================
// Term Definitions
// ============================================================================

/**
 * A term definition separates the declaration from the definition.
 * This is the natural way to represent top-level theorems/constants:
 * 
 * Declaration: _root : (a: R) → (b: R) → P
 * Definition:  _root = ?proof
 * 
 * This matches how Lean works and avoids the awkward wrapper:
 *   let _root : ... := ?proof in _root
 */
export interface TermDefinition {
  name: string;      // Name of the term (e.g., "_root", "my_theorem")
  type: TTerm;       // The type (e.g., the proposition we're proving)
  value: TTerm;      // The definition (starts as a hole, gets filled in)
}

/**
 * Create a term definition for a proof.
 * 
 * This creates:
 *   name : (a: R) → (b: R) → goal
 *   name = ?proofHoleId
 * 
 * @param name - Name for the term definition (e.g., "_root", "commutativity")
 * @param hypotheses - List of (name, type) pairs for assumptions
 * @param goal - The goal type we're trying to prove
 * @param proofHoleId - ID for the initial proof hole
 * @param context - Type context for the hole
 * @returns A term definition with type and initial hole
 * 
 * Example:
 *   createRootTermDefinition("comm", [["a", Real], ["b", Real]], equalityGoal)
 *   // Returns:
 *   //   { name: "comm",
 *   //     type: (a: ℝ) → (b: ℝ) → (a + b = b + a),
 *   //     value: ?proof }
 */
export function createRootTermDefinition(
  name: string,
  hypotheses: Array<[string, TTerm]>,
  goal: TTerm,
  proofHoleId: string = 'proof',
  context: TContext = []
): TermDefinition {
  // Build the theorem type: (a: R) → (b: R) → goal
  const theoremType = hypothesesToPi(hypotheses, goal);

  // Create the initial proof hole
  const proofHole = mkHole(proofHoleId, theoremType, context);

  return {
    name,
    type: theoremType,
    value: proofHole
  };
}

/**
 * @deprecated Use createRootTermDefinition instead. This uses the OLD let-wrapper architecture.
 * 
 * Create the root proof term structure (OLD let-wrapper architecture).
 *
 * This creates a single unified term that represents the entire proof workspace:
 *
 *   let _root : (a: R) → (b: R) → P = ?PROOF in _root
 *
 * Where:
 * - The type is a Pi-type formed from hypotheses ending with the goal type P
 * - The value is a proof hole (which will contain nested lets)
 *
 * NEW ARCHITECTURE:
 * Use TermDefinition instead, which separates declaration and definition:
 *   { name: "_root", type: (a: R) → (b: R) → P, value: ?PROOF }
 *
 * @param hypotheses - List of (name, type) pairs for assumptions
 * @param goal - The goal type we're trying to prove (e.g., an equality)
 * @param proofHoleId - ID for the proof term hole (default: "proof")
 * @param context - Type context for the holes
 * @returns The root let-binding term
 *
 * Example:
 *   createRootProofTerm([["a", Real], ["b", Real]], someEquality)
 *   // Returns:
 *   //   let _root : (a: ℝ) → (b: ℝ) → (x = y)
 *   //            = ?proof in _root
 */
export function createRootProofTerm(
  hypotheses: Array<[string, TTerm]>,
  goal: TTerm,
  proofHoleId: string = 'proof',
  context: TContext = []
): TTerm {
  // Build the theorem type: (a: R) → (b: R) → goal
  const theoremType = hypothesesToPi(hypotheses, goal);

  // Create the proof hole (how we prove it)
  // The proof hole's type is the full theorem type
  const proofHole = mkHole(proofHoleId, theoremType, context);

  // Create the root let-binding
  return mkLet('_root', theoremType, proofHole, mkVar(0));
}

/**
 * @deprecated Use insertLetBinding or fillHoleWith on TermDefinition.value instead.
 * 
 * Add a let-binding into the proof term (inside the root's value).
 *
 * This takes an existing proof term and wraps the innermost hole with a new let-binding.
 *
 * @param rootTerm - The root proof term
 * @param letName - Name for the new let-binding
 * @param letType - Type of the bound value
 * @param letValue - Value being bound
 * @returns Updated root term with the new let-binding
 */
export function addLetToProof(
  rootTerm: TTerm,
  letName: string,
  letType: TTerm,
  letValue: TTerm
): TTerm {
  // This will need to navigate to the proof hole and wrap it
  // For now, let's create a helper that replaces a hole with a let+hole
  return fillHoleWithLet(rootTerm, 'proof', letName, letType, letValue);
}

/**
 * Helper: Replace a hole with a let-binding that contains a new hole
 */
function fillHoleWithLet(
  term: TTerm,
  holeId: string,
  letName: string,
  letType: TTerm,
  letValue: TTerm
): TTerm {
  switch (term.tag) {
    case 'Hole':
      if (term.id === holeId) {
        // Replace this hole with: let letName = letValue in ?newHole
        const newHole = mkHole(holeId, term.type, term.context);
        return mkLet(letName, letType, letValue, newHole);
      }
      return term;

    case 'Var':
    case 'Sort':
    case 'Const':
      return term;

    case 'Binder': {
      const newDomain = fillHoleWithLet(term.domain, holeId, letName, letType, letValue);
      const newBody = fillHoleWithLet(term.body, holeId, letName, letType, letValue);

      let newBinderKind: BinderKind;
      if (term.binderKind.tag === 'BLet') {
        const newDefVal = fillHoleWithLet(term.binderKind.defVal, holeId, letName, letType, letValue);
        newBinderKind = { tag: 'BLet', defVal: newDefVal };
      } else {
        newBinderKind = term.binderKind;
      }

      return {
        tag: 'Binder',
        name: term.name,
        binderKind: newBinderKind,
        domain: newDomain,
        body: newBody
      };
    }

    case 'App':
      return {
        tag: 'App',
        fn: fillHoleWithLet(term.fn, holeId, letName, letType, letValue),
        arg: fillHoleWithLet(term.arg, holeId, letName, letType, letValue)
      };

    case 'Annot':
      return {
        tag: 'Annot',
        term: fillHoleWithLet(term.term, holeId, letName, letType, letValue),
        type: fillHoleWithLet(term.type, holeId, letName, letType, letValue)
      };

    case 'Match':
      return {
        tag: 'Match',
        scrutinee: fillHoleWithLet(term.scrutinee, holeId, letName, letType, letValue),
        clauses: term.clauses.map(c => ({
          patterns: c.patterns,
          rhs: fillHoleWithLet(c.rhs, holeId, letName, letType, letValue)
        }))
      };
  }
}

/**
 * @deprecated Use flattenPiBinders on TermDefinition.type instead.
 * 
 * Extract hypotheses from the root proof term (OLD let-wrapper architecture).
 *
 * Extracts the list of (name, type) pairs from the Pi-type in the root let's type.
 *
 * @param rootTerm - The root proof term
 * @returns List of hypotheses as (name, type) pairs
 */
export function extractHypothesesFromRoot(rootTerm: TTerm): Array<[string, TTerm]> {
  // Root should be: let _root : (a: R) → (b: R) → ?goal = ...
  if (rootTerm.tag !== 'Binder' || rootTerm.binderKind.tag !== 'BLet') {
    throw new Error('Expected root to be a let-binding');
  }

  // Extract from the type (which is the theorem type)
  return flattenPiBinders(rootTerm.domain);
}

/**
 * @deprecated Use insertPiBinder on TermDefinition.type instead.
 * 
 * Add a hypothesis to the root proof term (OLD let-wrapper architecture).
 *
 * Updates the root's type to include the new hypothesis in the Pi-type chain.
 *
 * @param rootTerm - The root proof term
 * @param hypName - Name of the new hypothesis
 * @param hypType - Type of the new hypothesis
 * @returns Updated root term
 */
export function addHypothesisToRoot(rootTerm: TTerm, hypName: string, hypType: TTerm): TTerm {
  if (rootTerm.tag !== 'Binder' || rootTerm.binderKind.tag !== 'BLet') {
    throw new Error('Expected root to be a let-binding');
  }

  // Extract current hypotheses
  const hypotheses = extractHypothesesFromRoot(rootTerm);

  // Add new hypothesis
  hypotheses.push([hypName, hypType]);

  // Get the goal (last thing in the Pi chain)
  const goal = getFinalReturnType(rootTerm.domain);

  // Rebuild the theorem type
  const newTheoremType = hypothesesToPi(hypotheses, goal);

  // Create updated root
  return {
    tag: 'Binder',
    name: rootTerm.name,
    binderKind: { tag: 'BLet', defVal: rootTerm.binderKind.defVal },
    domain: newTheoremType,
    body: rootTerm.body
  };
}

/**
 * @deprecated Use getFinalReturnType on TermDefinition.type instead.
 * 
 * Get the goal from the root proof term (OLD let-wrapper architecture).
 *
 * Extracts the goal type (the conclusion) from the end of the Pi-type chain.
 *
 * @param rootTerm - The root proof term
 * @returns The goal type
 */
export function getGoalFromRoot(rootTerm: TTerm): TTerm {
  if (rootTerm.tag !== 'Binder' || rootTerm.binderKind.tag !== 'BLet') {
    throw new Error('Expected root to be a let-binding');
  }

  return getFinalReturnType(rootTerm.domain);
}

/**
 * @deprecated Use setFinalReturnType on TermDefinition.type instead.
 * 
 * Set the goal in the root proof term (OLD let-wrapper architecture).
 *
 * Updates the goal type (conclusion) at the end of the Pi-type chain.
 *
 * @param rootTerm - The root proof term
 * @param newGoal - The new goal type
 * @returns Updated root term
 */
export function setGoalInRoot(rootTerm: TTerm, newGoal: TTerm): TTerm {
  if (rootTerm.tag !== 'Binder' || rootTerm.binderKind.tag !== 'BLet') {
    throw new Error('Expected root to be a let-binding');
  }

  // Extract current hypotheses
  const hypotheses = extractHypothesesFromRoot(rootTerm);

  // Rebuild the theorem type with new goal
  const newTheoremType = hypothesesToPi(hypotheses, newGoal);

  // Create updated root
  return {
    tag: 'Binder',
    name: rootTerm.name,
    binderKind: { tag: 'BLet', defVal: rootTerm.binderKind.defVal },
    domain: newTheoremType,
    body: rootTerm.body
  };
}

// ============================================================================
// Helper: Check Variable Occurrence
// ============================================================================

/**
 * Check if variable with De Bruijn index occurs in term
 */
export function occursIn(index: number, term: TTerm): boolean {
  switch (term.tag) {
    case 'Var':
      return term.index === index;
    case 'Sort':
    case 'Const':
      return false;
    case 'Binder': {
      // Check in domain and body (going under binder for body)
      const inDomain = occursIn(index, term.domain);
      const inBody = occursIn(index + 1, term.body);

      // For BLet, also check in the definition value
      if (term.binderKind.tag === 'BLet') {
        return inDomain || occursIn(index, term.binderKind.defVal) || inBody;
      }
      return inDomain || inBody;
    }
    case 'App':
      return occursIn(index, term.fn) || occursIn(index, term.arg);
    case 'Hole':
      return occursIn(index, term.type);
    case 'Annot':
      return occursIn(index, term.term) || occursIn(index, term.type);

    case 'Match':
      // Check scrutinee
      if (occursIn(index, term.scrutinee)) return true;
      // Check all clause RHS terms
      // TODO: when we implement proper pattern binding, adjust index for pattern-bound vars
      for (const clause of term.clauses) {
        if (occursIn(index, clause.rhs)) return true;
      }
      return false;
  }
}

// ============================================================================
// TT Engine Helpers: Working with Binders
// ============================================================================

/**
 * Flatten Pi-binders from a type signature into an array.
 * 
 * Given: (a: R) → (b: R) → (c: R) → Goal
 * Returns: [['a', R], ['b', R], ['c', R]]
 * 
 * This extracts all the Pi-binders at the top level until we hit a non-Pi term.
 * 
 * @param term - The type signature (typically a nested Pi-type)
 * @returns Array of [name, type] pairs for each Pi-binder
 */
export function flattenPiBinders(term: TTerm): Array<[string, TTerm]> {
  const binders: Array<[string, TTerm]> = [];
  let current = term;

  while (current.tag === 'Binder' && current.binderKind.tag === 'BPi') {
    binders.push([current.name, current.domain]);
    current = current.body;
  }

  return binders;
}

/**
 * Get the final return type after stripping all Pi-binders.
 * 
 * Given: (a: R) → (b: R) → Goal
 * Returns: Goal
 * 
 * @param term - The type signature
 * @returns The final return type (goal)
 */
export function getFinalReturnType(term: TTerm): TTerm {
  let current = term;

  while (current.tag === 'Binder' && current.binderKind.tag === 'BPi') {
    current = current.body;
  }

  return current;
}

/**
 * Insert a Pi-binder at a specific position in the type signature.
 * 
 * @param term - The type signature
 * @param position - Where to insert (0 = first, length = last)
 * @param name - Name of the new binder
 * @param binderType - Type of the new binder
 * @returns Updated type signature with new binder inserted
 */
export function insertPiBinder(
  term: TTerm,
  position: number,
  name: string,
  binderType: TTerm
): TTerm {
  // Extract current binders
  const binders = flattenPiBinders(term);
  const goal = getFinalReturnType(term);

  // Insert new binder at position
  binders.splice(position, 0, [name, binderType]);

  // Rebuild Pi-type
  return hypothesesToPi(binders, goal);
}

/**
 * Remove a Pi-binder at a specific position in the type signature.
 * 
 * @param term - The type signature
 * @param position - Which binder to remove (0-indexed)
 * @returns Updated type signature with binder removed
 */
export function removePiBinder(term: TTerm, position: number): TTerm {
  // Extract current binders
  const binders = flattenPiBinders(term);
  const goal = getFinalReturnType(term);

  // Remove binder at position
  binders.splice(position, 1);

  // Rebuild Pi-type
  return hypothesesToPi(binders, goal);
}

/**
 * Update the final return type (goal) in a type signature.
 * 
 * @param term - The type signature
 * @param newGoal - New goal type
 * @returns Updated type signature with new goal
 */
export function setFinalReturnType(term: TTerm, newGoal: TTerm): TTerm {
  const binders = flattenPiBinders(term);
  return hypothesesToPi(binders, newGoal);
}

/**
 * Check if a binder (by name) is used "downstream" in a term.
 * 
 * This checks if the binder name appears freely in:
 * - The body of the binder
 * - Any subsequent binders
 * 
 * This is useful for deletion safety: you can only delete a binder if it's not used downstream.
 * 
 * @param term - The term to check
 * @param binderName - Name of the binder to look for
 * @param position - Position of the binder (for Pi-chains, check from this position onward)
 * @returns True if the binder is used downstream
 */
export function isBinderUsedDownstream(term: TTerm, binderName: string, position: number = 0): boolean {
  // For Pi-binders, check if the name is used in bodies after this position
  const binders = flattenPiBinders(term);
  const goal = getFinalReturnType(term);

  // Check in subsequent binder types
  for (let i = position + 1; i < binders.length; i++) {
    if (isNameUsed(binderName, binders[i][1])) {
      return true;
    }
  }

  // Check in the goal
  if (isNameUsed(binderName, goal)) {
    return true;
  }

  return false;
}

/**
 * Flatten let-bindings from a term into an array.
 * 
 * Given: let a = 1 in let b = 2 in let c = 3 in body
 * Returns: [['a', type_a, 1], ['b', type_b, 2], ['c', type_c, 3]]
 * 
 * @param term - The term containing let-bindings
 * @returns Array of [name, type, value] triples for each let-binding
 */
export function flattenLetBindings(term: TTerm): Array<[string, TTerm, TTerm]> {
  const lets: Array<[string, TTerm, TTerm]> = [];
  let current = term;

  while (current.tag === 'Binder' && current.binderKind.tag === 'BLet') {
    lets.push([current.name, current.domain, current.binderKind.defVal]);
    current = current.body;
  }

  return lets;
}

/**
 * Get the final body after stripping all let-bindings.
 * 
 * @param term - The term
 * @returns The final body (after all lets)
 */
export function getFinalLetBody(term: TTerm): TTerm {
  let current = term;

  while (current.tag === 'Binder' && current.binderKind.tag === 'BLet') {
    current = current.body;
  }

  return current;
}

/**
 * Insert a let-binding at a specific position.
 * 
 * @param term - The term
 * @param position - Where to insert (0 = outermost, length = innermost)
 * @param name - Name of the let-binding
 * @param letType - Type of the bound value
 * @param letValue - Value being bound
 * @returns Updated term with new let-binding inserted
 */
export function insertLetBinding(
  term: TTerm,
  position: number,
  name: string,
  letType: TTerm,
  letValue: TTerm
): TTerm {
  // Extract current lets
  const lets = flattenLetBindings(term);
  const body = getFinalLetBody(term);

  // Insert new let at position
  lets.splice(position, 0, [name, letType, letValue]);

  // Rebuild let-chain
  let result = body;
  for (let i = lets.length - 1; i >= 0; i--) {
    const [n, t, v] = lets[i];
    result = mkLet(n, t, v, result);
  }

  return result;
}

/**
 * Remove a let-binding at a specific position.
 * 
 * @param term - The term
 * @param position - Which let to remove (0-indexed)
 * @returns Updated term with let-binding removed
 */
export function removeLetBinding(term: TTerm, position: number): TTerm {
  // Extract current lets
  const lets = flattenLetBindings(term);
  const body = getFinalLetBody(term);

  // Remove let at position
  lets.splice(position, 1);

  // Rebuild let-chain
  let result = body;
  for (let i = lets.length - 1; i >= 0; i--) {
    const [n, t, v] = lets[i];
    result = mkLet(n, t, v, result);
  }

  return result;
}

/**
 * Check if a let-binding (by name) is used downstream.
 * 
 * @param term - The term to check
 * @param letName - Name of the let-binding
 * @param position - Position of the let (check from this position onward)
 * @returns True if the let is used downstream
 */
export function isLetUsedDownstream(term: TTerm, letName: string, position: number = 0): boolean {
  const lets = flattenLetBindings(term);
  const body = getFinalLetBody(term);

  // Check in subsequent let values and types
  for (let i = position + 1; i < lets.length; i++) {
    const [, type, value] = lets[i];
    if (isNameUsed(letName, type) || isNameUsed(letName, value)) {
      return true;
    }
  }

  // Check in the final body
  if (isNameUsed(letName, body)) {
    return true;
  }

  return false;
}

/**
 * Index path for navigating term structure.
 * Each element is either:
 * - 'domain' | 'body' | 'defVal' - to navigate into binders
 * - 'fn' | 'arg' - to navigate into applications
 * - 'scrutinee' | 'clauses' | 'rhs' - to navigate into pattern matching
 * - 'type' | 'term' - to navigate into type/term containers
 * - number - to navigate into a specific let/pi-binder (indexed from outermost) or clause index
 */
export type TermPath = Array<'domain' | 'body' | 'defVal' | 'fn' | 'arg' | 'type' | 'term' | 'scrutinee' | 'clauses' | 'rhs' | number>;

/**
 * Get the term at a specific path.
 * 
 * @param term - The root term
 * @param path - Path to navigate
 * @returns The term at that path, or null if path is invalid
 */
export function getAtPath(term: TTerm, path: TermPath): TTerm | null {
  let current: TTerm | null = term;

  for (const step of path) {
    if (!current) return null;

    if (typeof step === 'number') {
      // Navigate to nth binder
      if (current.tag === 'Binder') {
        let index = step;
        while (index > 0 && current && current.tag === 'Binder') {
          current = current.body;
          index--;
        }
        if (index > 0) return null;
      } else {
        return null;
      }
    } else {
      // Navigate by field name
      switch (step) {
        case 'domain':
          if (current.tag === 'Binder') {
            current = current.domain;
          } else {
            return null;
          }
          break;
        case 'body':
          if (current.tag === 'Binder') {
            current = current.body;
          } else {
            return null;
          }
          break;
        case 'defVal':
          if (current.tag === 'Binder' && current.binderKind.tag === 'BLet') {
            current = current.binderKind.defVal;
          } else {
            return null;
          }
          break;
        case 'fn':
          if (current.tag === 'App') {
            current = current.fn;
          } else {
            return null;
          }
          break;
        case 'arg':
          if (current.tag === 'App') {
            current = current.arg;
          } else {
            return null;
          }
          break;
        case 'type':
          if (current.tag === 'Hole' || current.tag === 'Annot') {
            current = current.type;
          } else {
            return null;
          }
          break;
        case 'term':
          if (current.tag === 'Annot') {
            current = current.term;
          } else {
            return null;
          }
          break;
        default:
          return null;
      }
    }
  }

  return current;
}

/**
 * Update the term at a specific path.
 * 
 * @param term - The root term
 * @param path - Path to the term to update
 * @param newTerm - New term to put at that path
 * @returns Updated root term with change applied
 */
export function updateAtPath(term: TTerm, path: TermPath, newTerm: TTerm): TTerm {
  if (path.length === 0) {
    return newTerm;
  }

  const [step, ...rest] = path;

  if (typeof step === 'number') {
    // Navigate to nth binder
    if (term.tag !== 'Binder') {
      throw new Error('Cannot navigate by index into non-binder term');
    }

    if (step === 0) {
      // Update this binder's body
      return {
        ...term,
        body: updateAtPath(term.body, rest, newTerm)
      };
    } else {
      // Recurse into body
      return {
        ...term,
        body: updateAtPath(term.body, [step - 1, ...rest], newTerm)
      };
    }
  }

  // Navigate by field name
  switch (step) {
    case 'domain':
      if (term.tag !== 'Binder') {
        throw new Error('Cannot access domain of non-binder term');
      }
      return {
        ...term,
        domain: updateAtPath(term.domain, rest, newTerm)
      };

    case 'body':
      if (term.tag !== 'Binder') {
        throw new Error('Cannot access body of non-binder term');
      }
      return {
        ...term,
        body: updateAtPath(term.body, rest, newTerm)
      };

    case 'defVal':
      if (term.tag !== 'Binder' || term.binderKind.tag !== 'BLet') {
        throw new Error('Cannot access defVal of non-let term');
      }
      return {
        ...term,
        binderKind: {
          tag: 'BLet',
          defVal: updateAtPath(term.binderKind.defVal, rest, newTerm)
        }
      };

    case 'fn':
      if (term.tag !== 'App') {
        throw new Error('Cannot access fn of non-app term');
      }
      return {
        ...term,
        fn: updateAtPath(term.fn, rest, newTerm)
      };

    case 'arg':
      if (term.tag !== 'App') {
        throw new Error('Cannot access arg of non-app term');
      }
      return {
        ...term,
        arg: updateAtPath(term.arg, rest, newTerm)
      };

    case 'type':
      if (term.tag !== 'Hole' && term.tag !== 'Annot') {
        throw new Error('Cannot access type of this term');
      }
      if (term.tag === 'Hole') {
        return {
          ...term,
          type: updateAtPath(term.type, rest, newTerm)
        };
      } else {
        return {
          ...term,
          type: updateAtPath(term.type, rest, newTerm)
        };
      }

    case 'term':
      if (term.tag !== 'Annot') {
        throw new Error('Cannot access term of non-annot');
      }
      return {
        ...term,
        term: updateAtPath(term.term, rest, newTerm)
      };

    default:
      throw new Error(`Unknown path step: ${step}`);
  }
}

// ============================================================================
// EditableTerm: Immutable wrapper for editing term definitions
// ============================================================================

// ============================================================================
// Record Types (Structures)
// ============================================================================

/**
 * A field in a record type.
 *
 * Fields can depend on previous fields (dependent records), but for simplicity
 * we start with non-dependent fields where each field type is a closed term.
 */
export interface RecordField {
  name: string;
  type: TTerm;
}

/**
 * A record type definition (structure).
 *
 * Records are special single-constructor types with named projections.
 * In Lean, this would be:
 *
 *   structure Magma (A : Type) where
 *     op : A → A → A
 *
 * We represent this as:
 * - type: The kind of the record (e.g., Type → Type for Magma)
 * - fields: The named fields with their types
 * - extends: (optional) Names of records to extend (inherit fields from)
 *
 * A record implicitly has:
 * - A constructor: Record.mk : field1_type → field2_type → ... → Record
 * - Projections: Record.field1 : Record → field1_type, etc.
 *
 * When a record extends other records:
 * - All fields from extended records are inlined during elaboration
 * - Field name clashes cause an error
 * - This is a surface-level feature - the kernel sees the inlined version
 *
 * Parameters:
 * - Records can have parameters (like `A : Type` for `Magma A`)
 * - Field types are interpreted in a context where params are bound
 * - param[0] is at De Bruijn index 0 (first param is innermost)
 *
 * Example: Magma (A : Type) with op : A → A → A
 * - params: [{ name: 'A', type: Type_0 }]
 * - In field context: A is at index 0
 * - op.type = Π(_ : Var(0)). Π(_ : Var(1)). Var(2)
 */
export interface RecordParam {
  name: string;
  type: TTerm;
}

export interface RecordDef {
  name: string;
  type: TTerm;           // The kind of the record type (e.g., Type_0 → Type_0)
  params: RecordParam[]; // Parameters that scope over all fields
  fields: RecordField[]; // Named fields (types are in param context)
  extends?: string[];    // Names of records to extend (optional)
}

/**
 * Create a record projection constant.
 *
 * A projection extracts a field from a record instance.
 * E.g., Magma.op : Magma A → (A → A → A)
 *
 * @param recordName - Name of the record type
 * @param fieldName - Name of the field
 * @param recordType - The record type (applied to any parameters)
 * @param fieldType - The type of the field
 * @returns A Const term representing the projection
 */
export function mkProjection(
  recordName: string,
  fieldName: string,
  recordType: TTerm,
  fieldType: TTerm
): TTerm {
  // Projection : Record → FieldType
  return mkConst(
    `${recordName}.${fieldName}`,
    mkPi(recordType, fieldType, 'self')
  );
}

/**
 * Create the constructor type for a record.
 *
 * The constructor takes all field values and produces a record instance.
 * E.g., Magma.mk : (A : Type) → (A → A → A) → Magma A
 *
 * @param recordRef - A reference to the record type constant
 * @param fields - The record fields
 * @param params - Parameter binders (e.g., [(A, Type)] for polymorphic records)
 * @returns The type of the constructor
 */
export function mkRecordConstructorType(
  recordRef: TTerm,
  fields: RecordField[],
  params: Array<[string, TTerm]> = []
): TTerm {
  // Build from inside out: last field → ... → first field → params → Record
  // The record type is applied to all params
  let appliedRecord = recordRef;
  for (let i = 0; i < params.length; i++) {
    // Apply record to Var(params.length - 1 - i) - the parameter at this position
    // Since we're building the constructor type where params are the outermost binders
    appliedRecord = mkApp(appliedRecord, mkVar(params.length - 1 - i + fields.length));
  }

  // Start with the applied record as the return type
  let result = appliedRecord;

  // Add field types as arguments (innermost to outermost)
  for (let i = fields.length - 1; i >= 0; i--) {
    const field = fields[i];
    result = mkPi(field.type, result, field.name);
  }

  // Add parameter types as outermost binders
  for (let i = params.length - 1; i >= 0; i--) {
    const [paramName, paramType] = params[i];
    result = mkPi(paramType, result, paramName);
  }

  return result;
}

/**
 * Create a record constructor constant.
 *
 * @param recordName - Name of the record type
 * @param recordRef - Reference to the record type
 * @param fields - The record fields
 * @param params - Parameter binders for polymorphic records
 * @returns A Const term representing the constructor
 */
export function mkRecordConstructor(
  recordName: string,
  recordRef: TTerm,
  fields: RecordField[],
  params: Array<[string, TTerm]> = []
): TTerm {
  const ctorType = mkRecordConstructorType(recordRef, fields, params);
  return mkConst(`${recordName}.mk`, ctorType);
}

/**
 * Create an application of a projection to a record instance.
 *
 * @param projection - The projection term
 * @param instance - The record instance
 * @returns Application term: projection instance
 */
export function mkFieldAccess(projection: TTerm, instance: TTerm): TTerm {
  return mkApp(projection, instance);
}

/**
 * EditableTerm provides an immutable, structured interface for editing
 * a term definition (proof workspace).
 *
 * The term definition is decomposed into:
 * - hypotheses: Array of Pi-binders from the type signature
 * - goal: The final return type of the signature
 * - body: The proof term (definition value)
 *
 * Example term definition:
 *   name: theorem
 *   type: (a: ℝ) → (b: ℝ) → (a + b = b + a)
 *   value: ?proof
 *
 * Becomes EditableTerm with:
 *   hypotheses: [["a", ℝ], ["b", ℝ]]
 *   goal: (a + b = b + a)
 *   body: ?proof
 */
export class EditableTerm {
  readonly name: string;
  readonly hypotheses: ReadonlyArray<[string, TTerm]>;
  readonly goal: TTerm;
  readonly body: TTerm;

  constructor(
    name: string,
    hypotheses: ReadonlyArray<[string, TTerm]>,
    goal: TTerm,
    body: TTerm
  ) {
    this.name = name;
    this.hypotheses = hypotheses;
    this.goal = goal;
    this.body = body;
  }

  /**
   * Create an EditableTerm from a TermDefinition by destructuring the type.
   */
  static fromTermDefinition(def: TermDefinition): EditableTerm {
    const hypotheses = flattenPiBinders(def.type);
    const goal = getFinalReturnType(def.type);
    return new EditableTerm(def.name, hypotheses, goal, def.value);
  }

  /**
   * Convert back to a TermDefinition by reconstructing the type.
   */
  toTermDefinition(): TermDefinition {
    return {
      name: this.name,
      type: hypothesesToPi(this.hypotheses as Array<[string, TTerm]>, this.goal),
      value: this.body
    };
  }

  /**
   * Add a hypothesis (Pi-binder) at the specified position.
   *
   * @param index - Position to insert (0 = first, hypotheses.length = last)
   * @param name - Name of the hypothesis
   * @param type - Type of the hypothesis
   * @returns New EditableTerm with hypothesis added
   */
  addHypothesis(index: number, name: string, type: TTerm): EditableTerm {
    const newHypotheses = [...this.hypotheses];
    newHypotheses.splice(index, 0, [name, type]);
    return new EditableTerm(this.name, newHypotheses, this.goal, this.body);
  }

  /**
   * Remove a hypothesis at the specified position.
   * Checks if the hypothesis is used before removing.
   *
   * @param index - Position of hypothesis to remove
   * @returns New EditableTerm with hypothesis removed
   * @throws Error if hypothesis is used in goal or body
   */
  removeHypothesis(index: number): EditableTerm {
    if (index < 0 || index >= this.hypotheses.length) {
      throw new Error(`Invalid hypothesis index: ${index}`);
    }

    const [name] = this.hypotheses[index];

    // Check if used in remaining hypotheses' types
    for (let i = index + 1; i < this.hypotheses.length; i++) {
      if (isNameUsed(name, this.hypotheses[i][1])) {
        throw new Error(`Cannot remove hypothesis "${name}": used in hypothesis "${this.hypotheses[i][0]}"`);
      }
    }

    // Check if used in goal
    if (isNameUsed(name, this.goal)) {
      throw new Error(`Cannot remove hypothesis "${name}": used in goal`);
    }

    // Check if used in body
    if (isNameUsed(name, this.body)) {
      throw new Error(`Cannot remove hypothesis "${name}": used in body`);
    }

    const newHypotheses = [...this.hypotheses];
    newHypotheses.splice(index, 1);
    return new EditableTerm(this.name, newHypotheses, this.goal, this.body);
  }

  /**
   * Update a hypothesis at the specified position.
   *
   * @param index - Position of hypothesis to update
   * @param name - New name (or undefined to keep current)
   * @param type - New type (or undefined to keep current)
   * @returns New EditableTerm with hypothesis updated
   */
  updateHypothesis(
    index: number,
    name?: string,
    type?: TTerm
  ): EditableTerm {
    if (index < 0 || index >= this.hypotheses.length) {
      throw new Error(`Invalid hypothesis index: ${index}`);
    }

    const newHypotheses = [...this.hypotheses];
    const [currentName, currentType] = this.hypotheses[index];
    newHypotheses[index] = [
      name !== undefined ? name : currentName,
      type !== undefined ? type : currentType
    ];
    return new EditableTerm(this.name, newHypotheses, this.goal, this.body);
  }

  /**
   * Update the goal (final return type).
   *
   * @param newGoal - New goal term
   * @returns New EditableTerm with updated goal
   */
  updateGoal(newGoal: TTerm): EditableTerm {
    return new EditableTerm(this.name, this.hypotheses, newGoal, this.body);
  }

  /**
   * Update the body (proof term).
   *
   * @param newBody - New body term
   * @returns New EditableTerm with updated body
   */
  updateBody(newBody: TTerm): EditableTerm {
    return new EditableTerm(this.name, this.hypotheses, this.goal, newBody);
  }

  /**
   * Update body at a specific path.
   *
   * @param path - Path to the subterm to update
   * @param newTerm - New term to put at that path
   * @returns New EditableTerm with updated body
   */
  updateBodyAt(path: TermPath, newTerm: TTerm): EditableTerm {
    const newBody = updateAtPath(this.body, path, newTerm);
    return new EditableTerm(this.name, this.hypotheses, this.goal, newBody);
  }

  /**
   * Get hypothesis by index.
   */
  getHypothesis(index: number): [string, TTerm] | undefined {
    return this.hypotheses[index];
  }

  /**
   * Get hypothesis by name.
   */
  getHypothesisByName(name: string): [string, TTerm] | undefined {
    return this.hypotheses.find(([n]) => n === name);
  }

  /**
   * Get hypothesis index by name.
   */
  getHypothesisIndex(name: string): number {
    return this.hypotheses.findIndex(([n]) => n === name);
  }
}
