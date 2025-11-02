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
export type TTerm =
  | { tag: 'Var'; index: number }                          // De Bruijn variable
  | { tag: 'Sort'; level: number }                         // Type_i, Prop = Type_0
  | { tag: 'Binder'; name: string; binderKind: BinderKind; domain: TTerm; body: TTerm }  // Unified binder
  | { tag: 'App'; fn: TTerm; arg: TTerm }                  // Function application (f a)
  | { tag: 'Const'; name: string; type: TTerm }            // Named constant (nat_elim, eq, etc.)
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
  Nat: { tag: 'Const', name: 'ℕ', type: { tag: 'Sort', level: 0 } } as TTerm,
  Zero: { tag: 'Const', name: '0', type: { tag: 'Const', name: 'ℕ', type: { tag: 'Sort', level: 0 } } } as TTerm,
  Succ: (() => {
    // Succ : ℕ → ℕ
    const nat = { tag: 'Const', name: 'ℕ', type: { tag: 'Sort', level: 0 } } as TTerm;
    return { tag: 'Const', name: 'succ', type: mkPi(nat, nat, 'n') } as TTerm;
  })(),

  // Real numbers (placeholder - would need proper construction)
  Real: { tag: 'Const', name: 'ℝ', type: { tag: 'Sort', level: 0 } } as TTerm,

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
 * Create the root proof term structure.
 *
 * @deprecated Use createRootTermDefinition instead.
 * This creates a single unified term that represents the entire proof workspace:
 *
 *   let _root : (a: R) → (b: R) → P = ?PROOF
 *
 * Where:
 * - The type is a Pi-type formed from hypotheses ending with the goal type P
 * - The value is a proof hole (which will contain nested lets)
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
 *   //            = ?proof
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
 * Extract hypotheses from the root proof term.
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
  return extractHypothesesFromPi(rootTerm.domain);
}

/**
 * Helper: Extract hypotheses from a Pi-type chain
 */
function extractHypothesesFromPi(term: TTerm): Array<[string, TTerm]> {
  const hypotheses: Array<[string, TTerm]> = [];

  let current = term;
  while (current.tag === 'Binder' && current.binderKind.tag === 'BPi') {
    hypotheses.push([current.name, current.domain]);
    current = current.body;
  }

  return hypotheses;
}

/**
 * Add a hypothesis to the root proof term.
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
  const goal = getGoalFromPi(rootTerm.domain);

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
 * Get the goal from the root proof term.
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

  return getGoalFromPi(rootTerm.domain);
}

/**
 * Set the goal in the root proof term.
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

/**
 * Helper: Get the goal from the end of a Pi-type chain
 */
function getGoalFromPi(term: TTerm): TTerm {
  let current = term;
  while (current.tag === 'Binder' && current.binderKind.tag === 'BPi') {
    current = current.body;
  }
  return current;
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
