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
      if (term.index < context.length) {
        return context[context.length - 1 - term.index];
      }
      return `_${term.index}`;

    case 'Sort':
      return term.level === 0 ? 'Prop' : `Type`;

    case 'Const':
      // Try to extract just the meaningful name from verbose strings
      return term.name;

    case 'Binder': {
      const newContext = [term.name, ...context];
      const body = prettyPrintTerse(term.body, newContext);
      const domain = prettyPrintTerse(term.domain, context);

      switch (term.binderKind.tag) {
        case 'BPi':
          // Check if non-dependent (function type)
          if (!occursIn(0, term.body)) {
            return `(${domain} → ${body})`;
          }
          return `(Π ${term.name} : ${domain}, ${body})`;

        case 'BLam':
          return `(λ ${term.name}, ${body})`;

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
  }
}

/**
 * Convert a term with De Bruijn indices to a human-readable string
 * Now uses the names stored in binders for better readability
 */
export function prettyPrint(term: TTerm, context: string[] = []): string {
  switch (term.tag) {
    case 'Var':
      // Look up the name from context
      if (term.index < context.length) {
        return context[context.length - 1 - term.index];
      }
      return `#${term.index}`;  // Free variable

    case 'Sort':
      return term.level === 0 ? 'Prop' : `Type_${term.level}`;

    case 'Const':
      return term.name;

    case 'Binder': {
      const domain = prettyPrint(term.domain, context);
      const newContext = [term.name, ...context];
      const body = prettyPrint(term.body, newContext);

      switch (term.binderKind.tag) {
        case 'BPi':
          // Always show binder name for clarity: (a : R) → B
          return `((${term.name} : ${domain}) → ${body})`;

        case 'BLam':
          return `(λ (${term.name} : ${domain}), ${body})`;

        case 'BLet':
          const defVal = prettyPrint(term.binderKind.defVal, context);
          return `(let ${term.name} : ${domain} := ${defVal} in ${body})`;
      }
    }

    case 'App': {
      const fn = prettyPrint(term.fn, context);
      const arg = prettyPrint(term.arg, context);
      return `(${fn} ${arg})`;
    }

    case 'Hole':
      return `?${term.id}`;

    case 'Annot':
      return `(${prettyPrint(term.term, context)} : ${prettyPrint(term.type, context)})`;
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
 * - number - to navigate into a specific let/pi-binder (indexed from outermost)
 */
export type TermPath = Array<'domain' | 'body' | 'defVal' | 'fn' | 'arg' | 'type' | 'term' | number>;

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
