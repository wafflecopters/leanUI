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
 * The core term language using De Bruijn indices.
 *
 * De Bruijn indices: A variable is represented by a number indicating how many
 * binders we need to traverse to find its binding. For example:
 *   λx. λy. x + y  becomes  λ. λ. 1 + 0
 *   (x is 1 level up, y is 0 levels up)
 */
export type TTerm =
  | { tag: 'Var'; index: number }                          // De Bruijn variable
  | { tag: 'Sort'; level: number }                         // Type_i, Prop = Type_0
  | { tag: 'Pi'; domain: TTerm; codomain: TTerm }          // Dependent function type (Π x : A, B x)
  | { tag: 'Lambda'; domain: TTerm; body: TTerm }          // Function abstraction (λ x : A, t)
  | { tag: 'App'; fn: TTerm; arg: TTerm }                  // Function application (f a)
  | { tag: 'Let'; defType: TTerm; defVal: TTerm; body: TTerm }  // Let binding
  | { tag: 'Const'; name: string; type: TTerm }            // Named constant (nat_elim, eq, etc.)
  | { tag: 'Hole'; id: string; type: TTerm; context: TContext }  // Metavariable (unproven goal)
  | { tag: 'Annot'; term: TTerm; type: TTerm }            // Type annotation

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
  Nat: { tag: 'Const', name: 'ℕ', type: { tag: 'Sort', level: 0 } } as TTerm,
  Zero: { tag: 'Const', name: '0', type: { tag: 'Const', name: 'ℕ', type: { tag: 'Sort', level: 0 } } } as TTerm,
  Succ: (() => {
    // Succ : ℕ → ℕ
    const nat = { tag: 'Const', name: 'ℕ', type: { tag: 'Sort', level: 0 } } as TTerm;
    return { tag: 'Const', name: 'succ', type: { tag: 'Pi', domain: nat, codomain: nat } } as TTerm;
  })(),

  // Real numbers (placeholder - would need proper construction)
  Real: { tag: 'Const', name: 'ℝ', type: { tag: 'Sort', level: 0 } } as TTerm,

  // Equality type
  // eq : Π (A : Type), A → A → Prop
  Eq: (() => {
    const sort0 = { tag: 'Sort', level: 0 } as TTerm;
    const A = { tag: 'Var', index: 0 } as TTerm;
    // A → A → Prop
    const type = {
      tag: 'Pi',
      domain: sort0,
      codomain: {
        tag: 'Pi',
        domain: A,
        codomain: {
          tag: 'Pi',
          domain: A,
          codomain: sort0
        }
      }
    } as TTerm;
    return { tag: 'Const', name: 'eq', type } as TTerm;
  })(),
};

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

  // Build type: Π (P : Prop), P → (P → P) → ℕ → P
  return {
    tag: 'Pi',
    domain: prop,                                    // P : Prop
    codomain: {
      tag: 'Pi',
      domain: { tag: 'Var', index: 0 },             // P (base case)
      codomain: {
        tag: 'Pi',
        domain: {                                    // P → P (step)
          tag: 'Pi',
          domain: { tag: 'Var', index: 1 },
          codomain: { tag: 'Var', index: 2 }
        },
        codomain: {
          tag: 'Pi',
          domain: nat,                               // ℕ (value)
          codomain: { tag: 'Var', index: 3 }        // P (result)
        }
      }
    }
  };
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
 */
export function mkPi(domain: TTerm, codomain: TTerm): TTerm {
  return { tag: 'Pi', domain, codomain };
}

/**
 * Create a Lambda (function abstraction)
 */
export function mkLambda(domain: TTerm, body: TTerm): TTerm {
  return { tag: 'Lambda', domain, body };
}

/**
 * Create a function application
 */
export function mkApp(fn: TTerm, arg: TTerm): TTerm {
  return { tag: 'App', fn, arg };
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

    case 'Pi':
      return {
        tag: 'Pi',
        domain: substHelper(targetIndex, replacement, term.domain, depth),
        // Going under a binder, so increment depth
        codomain: substHelper(targetIndex, replacement, term.codomain, depth + 1)
      };

    case 'Lambda':
      return {
        tag: 'Lambda',
        domain: substHelper(targetIndex, replacement, term.domain, depth),
        body: substHelper(targetIndex, replacement, term.body, depth + 1)
      };

    case 'App':
      return {
        tag: 'App',
        fn: substHelper(targetIndex, replacement, term.fn, depth),
        arg: substHelper(targetIndex, replacement, term.arg, depth)
      };

    case 'Let':
      return {
        tag: 'Let',
        defType: substHelper(targetIndex, replacement, term.defType, depth),
        defVal: substHelper(targetIndex, replacement, term.defVal, depth),
        body: substHelper(targetIndex, replacement, term.body, depth + 1)
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

    case 'Pi':
      return {
        tag: 'Pi',
        domain: shift(amount, term.domain, cutoff),
        codomain: shift(amount, term.codomain, cutoff + 1)
      };

    case 'Lambda':
      return {
        tag: 'Lambda',
        domain: shift(amount, term.domain, cutoff),
        body: shift(amount, term.body, cutoff + 1)
      };

    case 'App':
      return {
        tag: 'App',
        fn: shift(amount, term.fn, cutoff),
        arg: shift(amount, term.arg, cutoff)
      };

    case 'Let':
      return {
        tag: 'Let',
        defType: shift(amount, term.defType, cutoff),
        defVal: shift(amount, term.defVal, cutoff),
        body: shift(amount, term.body, cutoff + 1)
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
 * Convert a term with De Bruijn indices to a human-readable string
 * Uses a context to map indices back to names
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

    case 'Pi': {
      const varName = `x${context.length}`;
      const domain = prettyPrint(term.domain, context);
      const codomain = prettyPrint(term.codomain, [varName, ...context]);

      // Check if it's a non-dependent function (A → B)
      if (!occursIn(0, term.codomain)) {
        return `(${domain} → ${codomain})`;
      }
      return `(Π (${varName} : ${domain}), ${codomain})`;
    }

    case 'Lambda': {
      const varName = `x${context.length}`;
      const domain = prettyPrint(term.domain, context);
      const body = prettyPrint(term.body, [varName, ...context]);
      return `(λ (${varName} : ${domain}), ${body})`;
    }

    case 'App': {
      const fn = prettyPrint(term.fn, context);
      const arg = prettyPrint(term.arg, context);
      return `(${fn} ${arg})`;
    }

    case 'Let': {
      const varName = `let${context.length}`;
      const defType = prettyPrint(term.defType, context);
      const defVal = prettyPrint(term.defVal, context);
      const body = prettyPrint(term.body, [varName, ...context]);
      return `(let ${varName} : ${defType} := ${defVal} in ${body})`;
    }

    case 'Hole':
      return `?${term.id}`;

    case 'Annot':
      return `(${prettyPrint(term.term, context)} : ${prettyPrint(term.type, context)})`;
  }
}

/**
 * Check if variable with De Bruijn index occurs in term
 */
function occursIn(index: number, term: TTerm): boolean {
  switch (term.tag) {
    case 'Var':
      return term.index === index;
    case 'Sort':
    case 'Const':
      return false;
    case 'Pi':
      return occursIn(index, term.domain) || occursIn(index + 1, term.codomain);
    case 'Lambda':
      return occursIn(index, term.domain) || occursIn(index + 1, term.body);
    case 'App':
      return occursIn(index, term.fn) || occursIn(index, term.arg);
    case 'Let':
      return occursIn(index, term.defType) || occursIn(index, term.defVal) || occursIn(index + 1, term.body);
    case 'Hole':
      return occursIn(index, term.type);
    case 'Annot':
      return occursIn(index, term.term) || occursIn(index, term.type);
  }
}
