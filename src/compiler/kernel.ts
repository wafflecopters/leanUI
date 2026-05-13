/**
 * TTK (Typed Terms - Kernel) Core Types and Utilities
 *
 * This is the kernel-level representation of terms, used for type-checking
 * and verification. This is the "elaborated" form of terms - the ground truth.
 *
 * The surface syntax (TT) is converted to kernel syntax (TTK) by the elaborator.
 * This separation allows:
 * - Surface syntax to have sugar like record extension
 * - Kernel to remain simple and easy to type-check
 *
 * Key differences from TT:
 * - No record extension (inlined during elaboration)
 * - No sugar - everything is explicit
 * - This is what gets type-checked
 */

// ============================================================================
// Universe Levels (Term-based representation)
// ============================================================================

/**
 * Universe levels are now represented as terms.
 *
 * Level expressions:
 * - ULit(n): Numeric literal level (0, 1, 2, ...)
 * - UOmega: The first infinite ordinal ω
 * - Var(n): Level variable (de Bruijn index, bound by Pi with ULevel domain)
 * - Meta(id): Level metavariable (for inference)
 * - App(USucc, l): Successor level (l + 1)
 * - App(App(UMax, l1), l2): Maximum of two levels
 * - App(App(UIMax, l1), l2): Impredicative max (0 if l2 = 0)
 *
 * This representation unifies level expressions with the term language,
 * enabling automatic de Bruijn scoping for level variables.
 */

// Level term constructors are defined below with TTKTerm

// ============================================================================
// Core Kernel Term Language
// ============================================================================

/**
 * Binder kinds in the kernel: distinguish between different ways to bind variables
 */
export type TTKBinderKind =
  | { tag: 'BPi' }                      // Π-binder (dependent function type)
  | { tag: 'BLam' }                     // λ-binder (function abstraction)
  | { tag: 'BLet'; defVal: TTKTerm }    // let-binder (local definition with value)

/**
 * The kernel term language using De Bruijn indices.
 *
 * This is structurally identical to TTerm, but semantically represents
 * the elaborated/desugared form of terms.
 */

export type TTKTermApp = { tag: 'App'; fn: TTKTerm; arg: TTKTerm }
export type TTKTermConst = { tag: 'Const'; name: string }

/**
 * TTK Pattern - kernel-level patterns
 *
 * - PVar: binds a named variable (user-written identifier like x, n, default)
 * - PWild: binds a wildcard variable with generated name (from surface `_`)
 * - PCtor: matches a constructor with sub-patterns
 *
 * PWild exists at kernel level (with generated name) to distinguish wildcards
 * from user-named variables. This enables proper pretty-printing (show `_` for
 * wildcards) and IDE features like inlay hints showing the generated names.
 */
/**
 * A named pattern argument: { Name := pattern }
 * Used in constructor patterns to specify which parameter receives which pattern.
 */
export interface TTKNamedPatternArg {
  name: string;
  pattern: TTKPattern;
}

export type TTKPattern =
  | { tag: 'PVar'; name: string }
  | { tag: 'PWild'; name: string }
  | { tag: 'PCtor'; name: string; args: TTKPattern[]; namedArgs?: TTKNamedPatternArg[] };

export type TTKClause = {
  patterns: TTKPattern[];  // Positional patterns
  namedPatterns?: TTKNamedPatternArg[];  // Named patterns: {name := pattern} at clause level
  rhs: TTKTerm;
  /** Elaborated arguments from LHS unification - shows the solved values for pattern positions */
  elabArgs?: TTKTerm[];
  /** Context variable names for printing (in de Bruijn order: index 0 first) */
  contextNames?: string[];
  /** Meta variable solutions for printing solved terms in this clause */
  metaVars?: PrettyPrintMetaVars;
};

export type TTKTerm =
  | { tag: 'Var'; index: number }                          // De Bruijn variable
  | { tag: 'Sort'; level: TTKTerm }                        // Sort l (Type l, Prop = Sort 0) - level is now a term
  | { tag: 'ULevel' }                                      // The type of universe levels
  | { tag: 'ULit'; n: number }                             // Numeric level literal (0, 1, 2, ...)
  | { tag: 'UOmega' }                                      // The first infinite ordinal ω
  | { tag: 'Binder'; name: string; binderKind: TTKBinderKind; domain: TTKTerm; body: TTKTerm }  // Unified binder
  | TTKTermApp   // Function application (f a)
  | TTKTermConst // Named constant (nat_elim, eq, etc.) - includes USucc, UMax, UIMax for levels
  | { tag: 'Hole'; id: string }                            // Unelaborated hole (becomes Meta during type checking)
  | { tag: 'Meta'; id: string }                            // Metavariable (instantiated during type checking)
  | { tag: 'Annot'; term: TTKTerm; type: TTKTerm }          // Type annotation
  | { tag: 'Match'; scrutinee: TTKTerm; clauses: TTKClause[] } // Pattern matching
  | { tag: 'NatLit'; value: bigint }                       // Natural number literal (e.g., 1784) — Phase 1: inert primitive
  | { tag: 'RatLit'; num: bigint; den: bigint }            // Rational literal (decimals): num/den, gcd-reduced, den > 0. e.g., 1.5 = {num:3, den:2}.

export function prettyPrintPattern(pattern: TTKPattern, updatedNames: string[] = []): string {
  const [updatedName, ...rest] = updatedNames

  switch (pattern.tag) {
    case 'PVar': {
      const name = updatedName ?? pattern.name;
      return name;
    }
    case 'PWild':
      // Display wildcards with their generated name visible
      const usefulPatternName = pattern.name && pattern.name !== '_';
      return usefulPatternName ? pattern.name : '_';
    case 'PCtor': {
      const name = updatedName ?? pattern.name;
      if (pattern.args.length === 0) {
        return name;
      }
      return `(${name} ${pattern.args.map(p => prettyPrintPattern(p, rest)).join(' ')})`;
    }
  }
}

export function prettyPrintPatternList(patterns: TTKPattern[]): string {
  return patterns.map(p => prettyPrintPattern(p)).join(' ');
}

/**
 * Type-checking context: list of bound variables with optional values.
 * Index 0 is the most recently bound variable.
 */
export type TTKContext = { name: string; type: TTKTerm; value?: TTKTerm }[];


// ============================================================================
// Helper Functions for Term Construction
// ============================================================================

/**
 * Create a De Bruijn variable
 */
export function mkVar(index: number): TTKTerm {
  return { tag: 'Var', index };
}

/**
 * Create a Pi type (dependent function type)
 */
export function mkPi(domain: TTKTerm, codomain: TTKTerm, name: string = 'x'): TTKTerm {
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
 */
export function mkLambda(domain: TTKTerm, body: TTKTerm, name: string = 'x'): TTKTerm {
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
 */
export function mkLet(name: string, defType: TTKTerm, defVal: TTKTerm, body: TTKTerm): TTKTerm {
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
export function mkApp(fn: TTKTerm, arg: TTKTerm): TTKTerm {
  return { tag: 'App', fn, arg };
}

/**
 * Apply a function to multiple arguments (left-associative)
 */
export function mkAppSpine(fn: TTKTerm, args: TTKTerm[]): TTKTerm {
  return args.reduce((acc, arg) => mkApp(acc, arg), fn);
}

/**
 * Create a constant with a given name and type
 */
export function mkConst(name: string): TTKTerm {
  return { tag: 'Const', name };
}

/**
 * Create a hole (unelaborated placeholder)
 */
export function mkHole(id: string): TTKTerm {
  return { tag: 'Hole', id };
}

/**
 * Create a metavariable (instantiated during type checking)
 */
export function mkMeta(id: string): TTKTerm {
  return { tag: 'Meta', id };
}

/**
 * Create a canonicalized rational literal. Reduces num/den by gcd and
 * normalizes sign so den > 0. Returns NatLit if the result is integral
 * (den == 1) — a RatLit invariant: num/den is in lowest terms with den >= 2,
 * or it's a NatLit. This ensures structural equality coincides with
 * mathematical equality for rationals.
 *
 * Throws if den == 0.
 */
export function mkRatLit(num: bigint, den: bigint): TTKTerm {
  if (den === 0n) throw new Error('RatLit: division by zero');
  if (den < 0n) { num = -num; den = -den; }
  const g = bigintGcd(num < 0n ? -num : num, den);
  num = num / g;
  den = den / g;
  if (den === 1n && num >= 0n) return { tag: 'NatLit', value: num };
  return { tag: 'RatLit', num, den };
}

function bigintGcd(a: bigint, b: bigint): bigint {
  while (b !== 0n) { [a, b] = [b, a % b]; }
  return a;
}

// ============================================================================
// Level Term Constructors
// ============================================================================

/**
 * Create a numeric level literal
 */
export function mkULit(n: number): TTKTerm {
  return { tag: 'ULit', n };
}

/**
 * Create the omega level (first infinite ordinal)
 */
export function mkUOmega(): TTKTerm {
  return { tag: 'UOmega' };
}

/**
 * Create a level successor: USucc l
 */
export function mkLSucc(level: TTKTerm): TTKTerm {
  return mkApp(mkConst('USucc'), level);
}

/**
 * Create level max: UMax l1 l2
 */
export function mkLMax(left: TTKTerm, right: TTKTerm): TTKTerm {
  return mkApp(mkApp(mkConst('UMax'), left), right);
}

/**
 * Create level imax (impredicative max): UIMax l1 l2
 */
export function mkLIMax(left: TTKTerm, right: TTKTerm): TTKTerm {
  return mkApp(mkApp(mkConst('UIMax'), left), right);
}

// Backwards compatibility aliases
export const mkLZero = () => mkULit(0);
export const mkLOmega = mkUOmega;

/**
 * Create a level from a number (convenience)
 */
export function mkLevelNum(n: number): TTKTerm {
  return mkULit(n);
}

/**
 * Create Prop (Sort 0)
 */
export function mkProp(): TTKTerm {
  return { tag: 'Sort', level: mkULit(0) };
}

/**
 * Create Type_i (Sort (i+1) in our convention)
 * Type = Type_0 = Sort 1
 * Type 1 = Sort 2
 * etc.
 */
export function mkType(n: number = 0): TTKTerm {
  return { tag: 'Sort', level: mkLSucc(mkULit(n)) };
}

/**
 * Create Sort with explicit level (level is now a TTKTerm)
 */
export function mkSort(level: TTKTerm): TTKTerm {
  return { tag: 'Sort', level };
}

/**
 * Create ULevel (the type of universe levels)
 */
export function mkULevel(): TTKTerm {
  return { tag: 'ULevel' };
}

// ============================================================================
// Level Term Utilities
// ============================================================================

/**
 * Check if a term is the USucc constant applied to an argument.
 * Returns the argument if so, undefined otherwise.
 */
export function matchUSucc(term: TTKTerm): TTKTerm | undefined {
  if (term.tag === 'App' && term.fn.tag === 'Const' && term.fn.name === 'USucc') {
    return term.arg;
  }
  return undefined;
}

/**
 * Check if a term is UMax applied to two arguments.
 * Returns [left, right] if so, undefined otherwise.
 */
export function matchUMax(term: TTKTerm): [TTKTerm, TTKTerm] | undefined {
  if (term.tag === 'App' && term.fn.tag === 'App' &&
    term.fn.fn.tag === 'Const' && term.fn.fn.name === 'UMax') {
    return [term.fn.arg, term.arg];
  }
  return undefined;
}

/**
 * Check if a term is UIMax applied to two arguments.
 * Returns [left, right] if so, undefined otherwise.
 */
export function matchUIMax(term: TTKTerm): [TTKTerm, TTKTerm] | undefined {
  if (term.tag === 'App' && term.fn.tag === 'App' &&
    term.fn.fn.tag === 'Const' && term.fn.fn.name === 'UIMax') {
    return [term.fn.arg, term.arg];
  }
  return undefined;
}

/**
 * Try to convert a level term to a concrete number.
 * Returns undefined if the level contains variables, metas, or omega.
 */
export function levelToNumber(level: TTKTerm): number | undefined {
  if (level.tag === 'ULit') {
    return level.n;
  }
  if (level.tag === 'UOmega') {
    return undefined;  // ω is infinite, not a finite number
  }
  const succArg = matchUSucc(level);
  if (succArg !== undefined) {
    const pred = levelToNumber(succArg);
    return pred !== undefined ? pred + 1 : undefined;
  }
  const maxArgs = matchUMax(level);
  if (maxArgs !== undefined) {
    const left = levelToNumber(maxArgs[0]);
    const right = levelToNumber(maxArgs[1]);
    return left !== undefined && right !== undefined ? Math.max(left, right) : undefined;
  }
  const imaxArgs = matchUIMax(level);
  if (imaxArgs !== undefined) {
    const left = levelToNumber(imaxArgs[0]);
    const right = levelToNumber(imaxArgs[1]);
    if (right === 0) return 0;  // imax(_, 0) = 0
    return left !== undefined && right !== undefined ? Math.max(left, right) : undefined;
  }
  return undefined;  // Var, Meta, or other terms
}

/**
 * Check if two level terms are structurally equal.
 * This is just structural term equality.
 */
export function levelsEqual(l1: TTKTerm, l2: TTKTerm): boolean {
  // First try to compare as concrete numbers (handles USucc(ULit(1)) == USucc(USucc(ULit(0))))
  const n1 = levelToNumber(l1);
  const n2 = levelToNumber(l2);
  if (n1 !== undefined && n2 !== undefined) {
    return n1 === n2;
  }

  // If not both concrete, simplify and compare structurally
  const s1 = simplifyLevel(l1);
  const s2 = simplifyLevel(l2);
  return levelsEqualStructural(s1, s2);
}

/**
 * Simplify a level term (basic simplifications).
 */
export function simplifyLevel(level: TTKTerm): TTKTerm {
  if (level.tag === 'ULit' || level.tag === 'UOmega' || level.tag === 'Var' || level.tag === 'Meta') {
    return level;
  }

  const succArg = matchUSucc(level);
  if (succArg !== undefined) {
    return mkLSucc(simplifyLevel(succArg));
  }

  const maxArgs = matchUMax(level);
  if (maxArgs !== undefined) {
    const left = simplifyLevel(maxArgs[0]);
    const right = simplifyLevel(maxArgs[1]);

    // max(0, l) = l, max(l, 0) = l
    if (left.tag === 'ULit' && left.n === 0) return right;
    if (right.tag === 'ULit' && right.n === 0) return left;

    // max(l, l) = l
    if (levelsEqual(left, right)) return left;

    // If both are concrete, compute the max
    const leftNum = levelToNumber(left);
    const rightNum = levelToNumber(right);
    if (leftNum !== undefined && rightNum !== undefined) {
      return mkULit(Math.max(leftNum, rightNum));
    }

    return mkLMax(left, right);
  }

  const imaxArgs = matchUIMax(level);
  if (imaxArgs !== undefined) {
    const left = simplifyLevel(imaxArgs[0]);
    const right = simplifyLevel(imaxArgs[1]);

    // imax(_, 0) = 0
    if (right.tag === 'ULit' && right.n === 0) return mkULit(0);

    // If right is definitely not zero, imax = max
    const rightNum = levelToNumber(right);
    if (rightNum !== undefined && rightNum > 0) {
      return simplifyLevel(mkLMax(left, right));
    }

    return mkLIMax(left, right);
  }

  return level;
}

/**
 * Check if a level term contains any level variables (Var nodes).
 * Used to detect when a Pi type needs level ω because its
 * codomain level depends on a bound level variable.
 */
export function levelContainsVar(level: TTKTerm): boolean {
  if (level.tag === 'Var') return true;
  if (level.tag === 'ULit' || level.tag === 'UOmega' || level.tag === 'Meta' || level.tag === 'Const') {
    return false;
  }
  if (level.tag === 'App') {
    return levelContainsVar(level.fn) || levelContainsVar(level.arg);
  }
  return false;
}

// Alias for backwards compatibility
export const levelContainsParam = levelContainsVar;

// ============================================================================
// Symbolic Level Comparison
// ============================================================================

/**
 * Collect all level variables (Var indices) in a level term.
 * Used to check if a result universe covers all constructor argument universes.
 */
export function collectLevelVars(level: TTKTerm): Set<number> {
  const vars = new Set<number>();
  collectLevelVarsHelper(level, vars);
  return vars;
}

function collectLevelVarsHelper(level: TTKTerm, vars: Set<number>): void {
  switch (level.tag) {
    case 'Var':
      vars.add(level.index);
      return;
    case 'ULit':
    case 'UOmega':
    case 'Meta':
    case 'Const':
      return;
    case 'App':
      collectLevelVarsHelper(level.fn, vars);
      collectLevelVarsHelper(level.arg, vars);
      return;
    default:
      return;
  }
}

/**
 * Check if l1 ≤ l2 symbolically.
 *
 * Returns:
 * - true: l1 is definitely ≤ l2
 * - false: l1 is definitely > l2
 * - 'unknown': cannot determine (e.g., comparing unrelated variables)
 *
 * Based on Lean's level comparison algorithm.
 */
export function levelLeq(l1: TTKTerm, l2: TTKTerm): boolean | 'unknown' {
  return levelLeqWithOffset(l1, l2, 0);
}

/**
 * Check if l1 ≥ l2 (convenience wrapper for levelLeq(l2, l1)).
 */
export function levelGeq(l1: TTKTerm, l2: TTKTerm): boolean | 'unknown' {
  return levelLeq(l2, l1);
}

/**
 * Internal helper for level comparison with an offset.
 * offset > 0 means we're checking l1 ≤ l2 + offset
 * offset < 0 means we're checking l1 + |offset| ≤ l2
 */
function levelLeqWithOffset(l1: TTKTerm, l2: TTKTerm, offset: number): boolean | 'unknown' {
  // Simplify both levels first
  const s1 = simplifyLevel(l1);
  const s2 = simplifyLevel(l2);

  // If both are concrete numbers, compare directly
  const n1 = levelToNumber(s1);
  const n2 = levelToNumber(s2);
  if (n1 !== undefined && n2 !== undefined) {
    return n1 <= n2 + offset;
  }

  // Zero is the smallest level
  if (s1.tag === 'ULit' && s1.n === 0 && offset >= 0) {
    return true;
  }

  // If l1 = l2 structurally and offset >= 0, then l1 ≤ l2 + offset
  if (offset >= 0 && levelsEqualStructural(s1, s2)) {
    return true;
  }

  // Handle Succ on left: Succ(a) ≤ b iff a ≤ b with offset-1
  const succArg1 = matchUSucc(s1);
  if (succArg1 !== undefined) {
    return levelLeqWithOffset(succArg1, s2, offset - 1);
  }

  // Handle Succ on right: a ≤ Succ(b) iff a ≤ b with offset+1
  const succArg2 = matchUSucc(s2);
  if (succArg2 !== undefined) {
    return levelLeqWithOffset(s1, succArg2, offset + 1);
  }

  // Handle Max on left: Max(a, b) ≤ c iff a ≤ c AND b ≤ c
  const maxArgs1 = matchUMax(s1);
  if (maxArgs1 !== undefined) {
    const leftResult = levelLeqWithOffset(maxArgs1[0], s2, offset);
    const rightResult = levelLeqWithOffset(maxArgs1[1], s2, offset);

    if (leftResult === false || rightResult === false) {
      return false;
    }
    if (leftResult === true && rightResult === true) {
      return true;
    }
    return 'unknown';
  }

  // Handle Max on right: a ≤ Max(b, c) iff a ≤ b OR a ≤ c
  const maxArgs2 = matchUMax(s2);
  if (maxArgs2 !== undefined) {
    const leftResult = levelLeqWithOffset(s1, maxArgs2[0], offset);
    const rightResult = levelLeqWithOffset(s1, maxArgs2[1], offset);

    if (leftResult === true || rightResult === true) {
      return true;
    }
    if (leftResult === false && rightResult === false) {
      return false;
    }
    return 'unknown';
  }

  // Handle IMax on left: IMax(a, b) ≤ c
  // IMax(a, b) = 0 if b = 0, else Max(a, b)
  const imaxArgs1 = matchUIMax(s1);
  if (imaxArgs1 !== undefined) {
    const [a, b] = imaxArgs1;
    const bNum = levelToNumber(b);

    // If b is concretely 0, IMax(a, b) = 0
    if (bNum === 0) {
      return levelLeqWithOffset(mkULit(0), s2, offset);
    }

    // If b is concretely > 0, IMax(a, b) = Max(a, b)
    if (bNum !== undefined && bNum > 0) {
      return levelLeqWithOffset(mkLMax(a, b), s2, offset);
    }

    // If b = Succ(something), b is definitively non-zero, so IMax(a, b) = Max(a, b)
    const bSuccArg = matchUSucc(b);
    if (bSuccArg !== undefined) {
      return levelLeqWithOffset(mkLMax(a, b), s2, offset);
    }

    // b is a variable - need to check both cases
    // Case 1: b = 0 => IMax(a, b) = 0, check 0 ≤ c
    // Case 2: b > 0 => IMax(a, b) = Max(a, b), check Max(a, b) ≤ c
    const case0 = levelLeqWithOffset(mkULit(0), s2, offset);
    const caseSucc = levelLeqWithOffset(mkLMax(a, b), s2, offset);

    // Both cases must hold (we don't know which b is)
    if (case0 === true && caseSucc === true) {
      return true;
    }
    // If either case is definitely false, we can't prove the constraint
    // But actually, if b ends up being the right value, it might be true
    // So we return 'unknown' unless both are true
    return 'unknown';
  }

  // Handle IMax on right: a ≤ IMax(b, c)
  const imaxArgs2 = matchUIMax(s2);
  if (imaxArgs2 !== undefined) {
    const [b, c] = imaxArgs2;
    const cNum = levelToNumber(c);

    // If c is concretely 0, IMax(b, c) = 0
    if (cNum === 0) {
      return levelLeqWithOffset(s1, mkULit(0), offset);
    }

    // If c is concretely > 0, IMax(b, c) = Max(b, c)
    if (cNum !== undefined && cNum > 0) {
      return levelLeqWithOffset(s1, mkLMax(b, c), offset);
    }

    // If c = Succ(something), c is definitively non-zero, so IMax(b, c) = Max(b, c)
    const cSuccArg = matchUSucc(c);
    if (cSuccArg !== undefined) {
      return levelLeqWithOffset(s1, mkLMax(b, c), offset);
    }

    // c is a variable - in the worst case c = 0, so IMax(b, c) = 0
    // We need a ≤ IMax(b, c) to hold for all possible c values
    // This is tricky - return 'unknown' to be conservative
    return 'unknown';
  }

  // Both are variables or complex expressions we can't simplify further
  // Check if they're the same variable
  if (s1.tag === 'Var' && s2.tag === 'Var') {
    if (s1.index === s2.index) {
      return offset >= 0;
    }
    // Different variables - can't determine
    return 'unknown';
  }

  // Concrete vs variable
  if (n1 !== undefined && s2.tag === 'Var') {
    // n1 ≤ Var(i) + offset ?
    // If n1 = 0 and offset >= 0, true (0 is smallest)
    if (n1 === 0 && offset >= 0) {
      return true;
    }
    // Otherwise unknown
    return 'unknown';
  }

  if (s1.tag === 'Var' && n2 !== undefined) {
    // Var(i) ≤ n2 + offset ?
    // We don't know the value of Var(i), so unknown
    // (unless n2 + offset is very large, but we don't have a max level)
    return 'unknown';
  }

  // Can't determine
  return 'unknown';
}

/**
 * Check if a level variable is "contained" in another level.
 * A variable v is contained in level l if:
 * - l is exactly v
 * - l is Max(a, b) and v is contained in a or b
 * - l is IMax(a, b) and v is contained in a or b (conservative)
 * - l is Succ(a) and v is contained in a
 *
 * This is used to check if a result universe covers all argument variables.
 */
export function levelVarContainedIn(varIndex: number, level: TTKTerm): boolean {
  const s = simplifyLevel(level);

  if (s.tag === 'Var') {
    return s.index === varIndex;
  }

  const succArg = matchUSucc(s);
  if (succArg !== undefined) {
    return levelVarContainedIn(varIndex, succArg);
  }

  const maxArgs = matchUMax(s);
  if (maxArgs !== undefined) {
    return levelVarContainedIn(varIndex, maxArgs[0]) || levelVarContainedIn(varIndex, maxArgs[1]);
  }

  const imaxArgs = matchUIMax(s);
  if (imaxArgs !== undefined) {
    return levelVarContainedIn(varIndex, imaxArgs[0]) || levelVarContainedIn(varIndex, imaxArgs[1]);
  }

  return false;
}

/**
 * Structural equality check for level terms (after simplification).
 */
function levelsEqualStructural(l1: TTKTerm, l2: TTKTerm): boolean {
  if (l1.tag !== l2.tag) return false;
  switch (l1.tag) {
    case 'ULit':
      return l2.tag === 'ULit' && l1.n === l2.n;
    case 'UOmega':
      return l2.tag === 'UOmega';
    case 'Var':
      return l2.tag === 'Var' && l1.index === l2.index;
    case 'Meta':
      return l2.tag === 'Meta' && l1.id === l2.id;
    case 'App':
      return l2.tag === 'App' && levelsEqualStructural(l1.fn, l2.fn) && levelsEqualStructural(l1.arg, l2.arg);
    case 'Const':
      return l2.tag === 'Const' && l1.name === l2.name;
    default:
      return false;
  }
}

/**
 * Pretty print a level term.
 * @param level - The level term to print
 * @param context - Optional context for looking up variable names (index 0 = innermost binder)
 */
export function prettyPrintLevel(level: TTKTerm, context: string[] = []): string {
  // Try to get a concrete number first
  const num = levelToNumber(level);
  if (num !== undefined) {
    return num.toString();
  }

  if (level.tag === 'ULit') {
    return level.n.toString();
  }
  if (level.tag === 'UOmega') {
    return 'ω';
  }
  if (level.tag === 'Var') {
    // Look up the name from context if available
    if (level.index < context.length) {
      return context[level.index];
    }
    return `#${level.index}`;
  }
  if (level.tag === 'Meta') {
    return `?${level.id}`;
  }

  const succArg = matchUSucc(level);
  if (succArg !== undefined) {
    return `(${prettyPrintLevel(succArg, context)} + 1)`;
  }

  const maxArgs = matchUMax(level);
  if (maxArgs !== undefined) {
    return `max(${prettyPrintLevel(maxArgs[0], context)}, ${prettyPrintLevel(maxArgs[1], context)})`;
  }

  const imaxArgs = matchUIMax(level);
  if (imaxArgs !== undefined) {
    return `imax(${prettyPrintLevel(imaxArgs[0], context)}, ${prettyPrintLevel(imaxArgs[1], context)})`;
  }

  // Fallback for unknown level term structures
  return `<level:${level.tag}>`;
}

// ============================================================================
// Definitional Equality
// ============================================================================

/**
 * Check if two kernel terms are definitionally equal (structural).
 */
export function isDefinitionallyEqual(term1: TTKTerm, term2: TTKTerm): boolean {
  if (term1.tag !== term2.tag) return false;

  switch (term1.tag) {
    case 'Var':
      return term2.tag === 'Var' && term1.index === term2.index;

    case 'Sort':
      return term2.tag === 'Sort' && levelsEqual(term1.level, term2.level);

    case 'ULevel':
      return term2.tag === 'ULevel';

    case 'Const':
      return term2.tag === 'Const' && term1.name === term2.name;

    case 'Hole':
      return term2.tag === 'Hole' && term1.id === term2.id;

    case 'Meta':
      return term2.tag === 'Meta' && term1.id === term2.id;

    case 'Binder': {
      if (term2.tag !== 'Binder') return false;
      if (term1.binderKind.tag !== term2.binderKind.tag) return false;
      if (term1.binderKind.tag === 'BLet' && term2.binderKind.tag === 'BLet') {
        if (!isDefinitionallyEqual(term1.binderKind.defVal, term2.binderKind.defVal)) {
          return false;
        }
      }
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
      if (!isDefinitionallyEqual(term1.scrutinee, term2.scrutinee)) return false;
      if (term1.clauses.length !== term2.clauses.length) return false;
      for (let i = 0; i < term1.clauses.length; i++) {
        if (!patternsStructurallyEqual(term1.clauses[i].patterns, term2.clauses[i].patterns)) return false;
        if (!namedPatternsStructurallyEqual(term1.clauses[i].namedPatterns, term2.clauses[i].namedPatterns)) return false;
        if (!isDefinitionallyEqual(term1.clauses[i].rhs, term2.clauses[i].rhs)) return false;
      }
      return true;
    }

    case 'ULit':
      return term2.tag === 'ULit' && term1.n === term2.n;

    case 'UOmega':
      return term2.tag === 'UOmega';

    case 'NatLit':
      return term2.tag === 'NatLit' && term1.value === term2.value;
    case 'RatLit':
      return term2.tag === 'RatLit' && term1.num === term2.num && term1.den === term2.den;
  }
}

// ============================================================================
// Pretty Printing
// ============================================================================

// Helper to strip outer parentheses from a string
function stripOuterParens(s: string): string {
  if (s.startsWith('(') && s.endsWith(')')) {
    return s.slice(1, -1);
  }
  return s;
}

/** Optional meta variable solutions for pretty printing solved terms */
export type PrettyPrintMetaVars = Map<string, { solution?: TTKTerm }>;

/**
 * Convert a kernel term to a human-readable string.
 * If metaVars is provided, Meta nodes will be printed as their solutions.
 */
export function prettyPrint(term: TTKTerm, context: string[] = [], metaVars?: PrettyPrintMetaVars): string {
  switch (term.tag) {
    case 'Var':
      // Context is prepended, so index directly into it
      if (term.index < context.length) {
        return context[term.index];
      }
      return `#${term.index}`;

    case 'Sort': {
      // Sort 0 = Prop, Sort (l+1) = Type l
      // Following Lean's convention where Type = Sort 1, Type 1 = Sort 2, etc.
      if (term.level.tag === 'ULit' && term.level.n === 0) {
        return 'Prop';
      }
      // Check for USucc pattern
      const succArg = matchUSucc(term.level);
      if (succArg !== undefined) {
        // Sort (l+1) = Type l
        const innerNum = levelToNumber(succArg);
        if (innerNum !== undefined) {
          return innerNum === 0 ? 'Type' : `Type ${innerNum}`;
        }
        // Non-numeric inner level (contains ω, variables, metas)
        return `Type ${prettyPrintLevel(succArg, context)}`;
      }
      // Fallback for other level forms (shouldn't happen in well-formed terms)
      return `Sort ${prettyPrintLevel(term.level, context)}`;
    }

    case 'ULit':
      return `${term.n}`;

    case 'UOmega':
      return 'ω';

    case 'ULevel':
      return 'ULevel';

    case 'Const':
      return term.name;

    case 'Binder': {
      const newContext = [term.name, ...context];
      const isAnonymous = term.name === '_' || term.name === '';

      switch (term.binderKind.tag) {
        case 'BPi': {
          // Collect all arrow parts: A -> B -> C -> D becomes [A, B, C, D]
          const parts: string[] = [];
          let current: TTKTerm = term;
          let ctx = context;
          while (current.tag === 'Binder' && current.binderKind.tag === 'BPi') {
            const currentAnon = current.name === '_' || current.name === '';
            const domainStr = prettyPrint(current.domain, ctx, metaVars);
            // Don't strip parens for function type domains - they indicate grouping
            const domain = current.domain.tag === 'Binder' && current.domain.binderKind.tag === 'BPi'
              ? domainStr
              : stripOuterParens(domainStr);
            if (currentAnon) {
              parts.push(domain);
            } else {
              parts.push(`(${current.name} : ${domain})`);
            }
            ctx = [current.name, ...ctx];
            current = current.body;
          }
          parts.push(prettyPrint(current, ctx, metaVars));
          return `(${parts.join(' -> ')})`;
        }

        case 'BLam': {
          const domain = stripOuterParens(prettyPrint(term.domain, context, metaVars));
          const body = prettyPrint(term.body, newContext, metaVars);
          if (isAnonymous) {
            return `(\\${domain} => ${body})`;
          }
          return `(\\(${term.name} : ${domain}) => ${body})`;
        }

        case 'BLet': {
          const domain = stripOuterParens(prettyPrint(term.domain, context, metaVars));
          const body = prettyPrint(term.body, newContext, metaVars);
          const defVal = prettyPrint(term.binderKind.defVal, context, metaVars);
          return `(let ${term.name} : ${domain} = ${defVal} in ${body})`;
        }
      }
    }

    case 'App': {
      // Collect all arguments from nested applications: ((f a) b) c -> [f, a, b, c]
      const parts: string[] = [];
      let current: TTKTerm = term;
      while (current.tag === 'App') {
        parts.unshift(prettyPrint(current.arg, context, metaVars));
        current = current.fn;
      }
      parts.unshift(prettyPrint(current, context, metaVars));
      return `(${parts.join(' ')})`;
    }

    case 'Hole':
      return `?${term.id}`;

    case 'Meta': {
      // If we have meta solutions, print the solved value instead
      const solution = metaVars?.get(term.id)?.solution;
      if (solution) {
        return prettyPrint(solution, context, metaVars);
      }
      return `?${term.id}`;
    }

    case 'Annot': {
      const termStr = prettyPrint(term.term, context, metaVars);
      const typeStr = stripOuterParens(prettyPrint(term.type, context, metaVars));
      return `(${termStr} : ${typeStr})`;
    }

    case 'Match': {
      // Omit the placeholder scrutinee (_scrutinee) since patterns provide the match structure
      const scrutineeStr = term.scrutinee.tag === 'Hole' && term.scrutinee.id === '_scrutinee'
        ? '_'
        : prettyPrint(term.scrutinee, context, metaVars);
      const scrutinee = scrutineeStr;
      const clauses = term.clauses.map(c => {
        // Use stored context names if available (from checking), otherwise derive from patterns
        const clauseContext = c.contextNames
          ? [...c.contextNames, ...context]
          : [...collectClausePatternVars(c).reverse(), ...context];
        // Use clause's metaVars if available (for solved terms), otherwise fall back to outer metaVars
        const clauseMetaVars = c.metaVars ?? metaVars;

        // If elabArgs are available, show them (the solved elaboration); otherwise show patterns
        const lhsStr = c.elabArgs
          ? c.elabArgs.map(arg => prettyPrint(arg, clauseContext, clauseMetaVars)).join(' ')
          : [
            ...c.patterns.map(p => prettyPrintPatternInternal(p)),
            ...(c.namedPatterns ?? []).map(np => `${np.name} := ${prettyPrintPatternInternal(np.pattern)}`),
          ].join(' ');

        const rhsStr = prettyPrint(c.rhs, clauseContext, clauseMetaVars);
        return `${lhsStr} => ${rhsStr}`;
      }).join(' | ');
      return `(match ${scrutinee} | ${clauses})`;
    }

    case 'NatLit':
      return term.value.toString();
    case 'RatLit':
      // Canonical RatLit: den=1 only for signed-negative integers (positive
      // collapse to NatLit); den≥2 for true rationals.
      return term.den === 1n ? term.num.toString() : `${term.num}/${term.den}`;
  }
}

/**
 * NamedArgMap maps parameter names to their positions.
 * Used to identify which arguments are implicit/named.
 */
export type NamedArgMap = Map<string, number>;

/**
 * Lookup function to get named arg info for a function/constructor.
 * Returns a map of parameter name -> position index.
 */
export type NamedArgLookup = (name: string) => NamedArgMap | undefined;

/**
 * Pretty print options for formatted output
 */
export interface PrettyPrintOptions {
  /** Current indentation level (number of spaces) */
  indent?: number;
  /** Number of spaces per indentation level */
  indentSize?: number;
  /** Optional lookup function to get named argument info for functions/constructors */
  namedArgLookup?: NamedArgLookup;
  /**
   * Show implicit/named args with labels like {A:=Nat}.
   * Default: true. When false, all args rendered as positional.
   */
  showNamedArgsWithLabels?: boolean;
  /**
   * Named arg map for the current signature being rendered.
   * When provided, params at positions in this map are rendered with {braces} instead of (parens).
   */
  signatureNamedArgMap?: NamedArgMap;
}

/**
 * Convert a kernel term to a formatted, human-readable string with proper indentation.
 * Match statements and let bodies are printed on new lines.
 */
export function prettyPrintFormatted(
  term: TTKTerm,
  context: string[] = [],
  metaVars?: PrettyPrintMetaVars,
  options: PrettyPrintOptions = {}
): string {
  const indent = options.indent ?? 0;
  const indentSize = options.indentSize ?? 2;
  const nextIndent = indent + indentSize;

  switch (term.tag) {
    case 'Var':
      if (term.index < context.length) {
        return context[term.index];
      }
      return `#${term.index}`;

    case 'Sort': {
      // Sort 0 = Prop, Sort (l+1) = Type l
      if (term.level.tag === 'ULit' && term.level.n === 0) {
        return 'Prop';
      }
      const succArg = matchUSucc(term.level);
      if (succArg !== undefined) {
        const innerNum = levelToNumber(succArg);
        if (innerNum !== undefined) {
          return innerNum === 0 ? 'Type' : `Type ${innerNum}`;
        }
        return `Type ${prettyPrintLevel(succArg, context)}`;
      }
      return `Sort ${prettyPrintLevel(term.level, context)}`;
    }

    case 'ULevel':
      return 'ULevel';

    case 'ULit':
      return `${term.n}`;

    case 'UOmega':
      return 'ω';

    case 'Const':
      return term.name;

    case 'Binder': {
      const newContext = [term.name, ...context];
      const isAnonymous = term.name === '_' || term.name === '';

      switch (term.binderKind.tag) {
        case 'BPi': {
          const parts: string[] = [];
          let current: TTKTerm = term;
          let ctx = context;
          let positionIndex = 0;

          // Build position -> name map from signatureNamedArgMap if provided
          const namedPositions = new Set<number>();
          if (options.signatureNamedArgMap) {
            for (const [, pos] of options.signatureNamedArgMap) {
              namedPositions.add(pos);
            }
          }

          while (current.tag === 'Binder' && current.binderKind.tag === 'BPi') {
            const currentAnon = current.name === '_' || current.name === '';
            const domainStr = prettyPrintFormatted(current.domain, ctx, metaVars, options);
            // Don't strip parens for function type domains - they indicate grouping
            const domain = current.domain.tag === 'Binder' && current.domain.binderKind.tag === 'BPi'
              ? domainStr
              : stripOuterParens(domainStr);
            const isNamedParam = namedPositions.has(positionIndex);
            if (currentAnon) {
              parts.push(domain);
            } else if (isNamedParam) {
              // Use braces for named/implicit parameters
              parts.push(`{${current.name} : ${domain}}`);
            } else {
              parts.push(`(${current.name} : ${domain})`);
            }
            ctx = [current.name, ...ctx];
            current = current.body;
            positionIndex++;
          }
          parts.push(prettyPrintFormatted(current, ctx, metaVars, options));
          return `(${parts.join(' -> ')})`;
        }

        case 'BLam': {
          const domain = stripOuterParens(prettyPrintFormatted(term.domain, context, metaVars, options));
          const body = prettyPrintFormatted(term.body, newContext, metaVars, options);
          if (isAnonymous) {
            return `(\\${domain} => ${body})`;
          }
          return `(\\(${term.name} : ${domain}) => ${body})`;
        }

        case 'BLet': {
          const domain = stripOuterParens(prettyPrintFormatted(term.domain, context, metaVars, options));
          const defVal = prettyPrintFormatted(term.binderKind.defVal, context, metaVars, options);
          const nextPad = ' '.repeat(nextIndent);
          const body = prettyPrintFormatted(term.body, newContext, metaVars, { ...options, indent: nextIndent });
          return `(let ${term.name} : ${domain} = ${defVal} in\n${nextPad}${body})`;
        }
      }
    }

    case 'App': {
      // Collect all arguments from nested applications: ((f a) b) c -> fn=f, args=[a, b, c]
      const args: TTKTerm[] = [];
      let current: TTKTerm = term;
      while (current.tag === 'App') {
        args.unshift(current.arg);
        current = current.fn;
      }
      const fn = current;

      // Try to get named arg info if the function is a Const
      let namedArgMap: NamedArgMap | undefined;
      if (fn.tag === 'Const' && options.namedArgLookup) {
        namedArgMap = options.namedArgLookup(fn.name);
      }

      // Build position -> name map for implicit args
      const positionToName = new Map<number, string>();
      if (namedArgMap) {
        for (const [name, pos] of namedArgMap) {
          positionToName.set(pos, name);
        }
      }

      // Format each argument, adding labels for named positions if enabled
      const fnStr = prettyPrintFormatted(fn, context, metaVars, options);
      const showLabels = options.showNamedArgsWithLabels !== false; // Default true
      const argStrs = args.map((arg, idx) => {
        const argStr = prettyPrintFormatted(arg, context, metaVars, options);
        const paramName = positionToName.get(idx);
        if (paramName && showLabels) {
          // This is a named/implicit argument - print with label
          return `{${paramName}:=${argStr}}`;
        }
        return argStr;
      });

      return `(${[fnStr, ...argStrs].join(' ')})`;
    }

    case 'Hole':
      return `?${term.id}`;

    case 'Meta': {
      const solution = metaVars?.get(term.id)?.solution;
      if (solution) {
        return prettyPrintFormatted(solution, context, metaVars, options);
      }
      return `?${term.id}`;
    }

    case 'Annot': {
      const termStr = prettyPrintFormatted(term.term, context, metaVars, options);
      const typeStr = stripOuterParens(prettyPrintFormatted(term.type, context, metaVars, options));
      return `(${termStr} : ${typeStr})`;
    }

    case 'Match': {
      // Omit the placeholder scrutinee (_scrutinee) since patterns provide the match structure
      const scrutineeStr = term.scrutinee.tag === 'Hole' && term.scrutinee.id === '_scrutinee'
        ? '_'
        : prettyPrintFormatted(term.scrutinee, context, metaVars, options);
      const scrutinee = scrutineeStr;
      const nextPad = ' '.repeat(nextIndent);

      const clauses = term.clauses.map(c => {
        const clauseContext = c.contextNames
          ? [...c.contextNames, ...context]
          : [...collectClausePatternVars(c).reverse(), ...context];
        const clauseMetaVars = c.metaVars ?? metaVars;

        const lhsStr = c.elabArgs
          ? c.elabArgs.map(arg => prettyPrintFormatted(arg, clauseContext, clauseMetaVars, options)).join(' ')
          : [
            ...c.patterns.map(p => prettyPrintPatternInternal(p)),
            ...(c.namedPatterns ?? []).map(np => `${np.name} := ${prettyPrintPatternInternal(np.pattern)}`),
          ].join(' ');

        const rhsStr = prettyPrintFormatted(c.rhs, clauseContext, clauseMetaVars, { ...options, indent: nextIndent });
        return `${nextPad}| ${lhsStr} => ${rhsStr}`;
      }).join('\n');

      return `(match ${scrutinee}\n${clauses})`;
    }

    case 'NatLit':
      return term.value.toString();
    case 'RatLit':
      // Canonical RatLit: den=1 only for signed-negative integers (positive
      // collapse to NatLit); den≥2 for true rationals.
      return term.den === 1n ? term.num.toString() : `${term.num}/${term.den}`;
  }
}

function prettyPrintPatternInternal(pattern: TTKPattern): string {
  switch (pattern.tag) {
    case 'PVar':
      return pattern.name;
    case 'PWild':
      // Display wildcards with their generated name visible
      return `_[${pattern.name}]`;
    case 'PCtor': {
      const parts = [
        ...pattern.args.map(prettyPrintPatternInternal),
        ...(pattern.namedArgs ?? []).map(na => `${na.name} := ${prettyPrintPatternInternal(na.pattern)}`),
      ];
      if (parts.length === 0) {
        return pattern.name;
      }
      return `(${pattern.name} ${parts.join(' ')})`;
    }
  }
}

/** Collect variable names from a clause in left-to-right order */
function collectClausePatternVars(clause: Pick<TTKClause, 'patterns' | 'namedPatterns'>): string[] {
  const vars: string[] = [];
  for (const p of clause.patterns) {
    collectPatternVarsHelper(p, vars);
  }
  for (const namedPattern of clause.namedPatterns ?? []) {
    collectPatternVarsHelper(namedPattern.pattern, vars);
  }
  return vars;
}

function collectPatternVarsHelper(pattern: TTKPattern, vars: string[]): void {
  switch (pattern.tag) {
    case 'PVar':
      vars.push(pattern.name);
      break;
    case 'PWild':
      break;
    case 'PCtor':
      for (const arg of pattern.args) {
        collectPatternVarsHelper(arg, vars);
      }
      for (const namedArg of pattern.namedArgs ?? []) {
        collectPatternVarsHelper(namedArg.pattern, vars);
      }
      break;
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

function escapeLatexName(name: string): string {
  return name.replace(/_/g, '\\_');
}

/**
 * Try to match a term against the pattern: Eq A x y
 * Returns { typeArg, lhs, rhs } if matched, otherwise null
 */
function matchEqApp(term: TTKTerm): { typeArg: TTKTerm; lhs: TTKTerm; rhs: TTKTerm } | null {
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
 * Convert a TTK term to a LaTeX string for mathematical rendering
 */
export function prettyPrintLatex(
  term: TTKTerm,
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
        return escapeLatexName(context[term.index]);
      }
      return `\\#${term.index}`;

    case 'Sort': {
      // Sort 0 = Prop, Sort (l+1) = Type l
      if (term.level.tag === 'ULit' && term.level.n === 0) {
        return '\\text{Prop}';
      }
      const succArg = matchUSucc(term.level);
      if (succArg !== undefined) {
        const innerNum = levelToNumber(succArg);
        if (innerNum !== undefined) {
          return innerNum === 0 ? '\\text{Type}' : `\\text{Type}_{${innerNum}}`;
        }
        return `\\text{Type}_{${prettyPrintLevel(succArg)}}`;
      }
      return `\\text{Sort}\\; ${prettyPrintLevel(term.level)}`;
    }

    case 'ULit':
      return `${term.n}`;

    case 'UOmega':
      return '\\omega';

    case 'Const':
      // Escape special LaTeX characters in names
      return escapeLatexName(term.name);

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
          return `(\\Pi\\, (${escapeLatexName(term.name)} : ${domain}),\\, ${body})`;

        case 'BLam':
          if (isAnonymous) {
            return `(\\lambda\\, ${domain},\\, ${body})`;
          }
          return `(\\lambda\\, (${escapeLatexName(term.name)} : ${domain}),\\, ${body})`;

        case 'BLet':
          const defVal = prettyPrintLatex(term.binderKind.defVal, context, opts);
          return `(\\text{let } ${escapeLatexName(term.name)} : ${domain} = ${defVal} \\text{ in } ${body})`;
      }
    }

    case 'App': {
      const fn = prettyPrintLatex(term.fn, context, opts);
      const arg = prettyPrintLatex(term.arg, context, opts);
      return `(${fn}\\; ${arg})`;
    }

    case 'Hole':
      return `?_{${term.id}}`;

    case 'Meta':
      return `?_{${term.id}}`;

    case 'Annot':
      return `(${prettyPrintLatex(term.term, context, opts)} : ${prettyPrintLatex(term.type, context, opts)})`;

    case 'Match': {
      // Omit the placeholder scrutinee (_scrutinee) since patterns provide the match structure
      const scrutineeStr = term.scrutinee.tag === 'Hole' && term.scrutinee.id === '_scrutinee'
        ? '\\_'
        : prettyPrintLatex(term.scrutinee, context, opts);
      const scrutinee = scrutineeStr;
      const clauses = term.clauses.map(c => {
        // Collect pattern variable names and add to context for RHS and elabArgs
        const patternVars = collectClausePatternVars(c);
        const clauseContext = [...patternVars.reverse(), ...context];

        // If elabArgs are available, show them (the solved elaboration); otherwise show patterns
        const lhsStr = c.elabArgs
          ? c.elabArgs.map(arg => prettyPrintLatex(arg, clauseContext, opts)).join('\\; ')
          : [
            ...c.patterns.map(p => prettyPrintPatternLatex(p)),
            ...(c.namedPatterns ?? []).map(np => `${escapeLatexName(np.name)} := ${prettyPrintPatternLatex(np.pattern)}`),
          ].join('\\; ');

        const rhsStr = prettyPrintLatex(c.rhs, clauseContext, opts);
        return `${lhsStr} \\Rightarrow ${rhsStr}`;
      }).join(' \\mid ');
      return `\\text{match}\\; ${scrutinee}\\; \\{\\, ${clauses} \\,\\}`;
    }

    case 'ULevel':
      return '\\text{Level}';

    case 'NatLit':
      return term.value.toString();
    case 'RatLit':
      // Canonical RatLit: den=1 only for signed-negative integers (positive
      // collapse to NatLit); den≥2 for true rationals.
      return term.den === 1n ? term.num.toString() : `${term.num}/${term.den}`;
  }
}

function prettyPrintPatternLatex(pattern: TTKPattern): string {
  switch (pattern.tag) {
    case 'PVar':
      return escapeLatexName(pattern.name);
    case 'PWild':
      // Display wildcards with their generated name visible
      return `\\_{[${escapeLatexName(pattern.name)}]}`;
    case 'PCtor': {
      const parts = [
        ...pattern.args.map(prettyPrintPatternLatex),
        ...(pattern.namedArgs ?? []).map(na => `${escapeLatexName(na.name)} := ${prettyPrintPatternLatex(na.pattern)}`),
      ];
      if (parts.length === 0) {
        return escapeLatexName(pattern.name);
      }
      return `(${escapeLatexName(pattern.name)}\\; ${parts.join('\\; ')})`;
    }
  }
}

// ============================================================================
// Variable Occurrence Checking
// ============================================================================

/**
 * Check if variable with De Bruijn index occurs in term
 */
export function occursIn(index: number, term: TTKTerm): boolean {
  switch (term.tag) {
    case 'Var':
      return term.index === index;
    case 'Sort':
      // Level is now a term, so check if the variable occurs in the level
      return occursIn(index, term.level);
    case 'Const':
    case 'ULit':
    case 'UOmega':
      return false;
    case 'Binder': {
      const inDomain = occursIn(index, term.domain);
      const inBody = occursIn(index + 1, term.body);
      if (term.binderKind.tag === 'BLet') {
        return inDomain || occursIn(index, term.binderKind.defVal) || inBody;
      }
      return inDomain || inBody;
    }
    case 'App':
      return occursIn(index, term.fn) || occursIn(index, term.arg);
    case 'Hole':
    case 'Meta':
      return false;
    case 'Annot':
      return occursIn(index, term.term) || occursIn(index, term.type);

    case 'Match':
      if (occursIn(index, term.scrutinee)) return true;
      for (const clause of term.clauses) {
        if (occursIn(index + collectClausePatternVars(clause).length, clause.rhs)) return true;
      }
      return false;

    case 'ULevel':
      return false;

    case 'NatLit':
    case 'RatLit':
      return false;
  }
}

// ============================================================================
// Kernel Record Types (Structures) - Elaborated Form
// ============================================================================

/**
 * A parameter to a kernel record type.
 */
export interface TTKRecordParam {
  name: string;
  type: TTKTerm;
  implicit?: boolean;  // true for implicit parameters {A : Type}
}

/**
 * A field in a kernel record type.
 * This is the elaborated form - no extensions, just plain fields.
 */
export interface TTKRecordField {
  name: string;
  type: TTKTerm;
  implicit?: boolean;  // true for implicit fields
}

/**
 * A kernel record type definition (structure).
 * This is the elaborated form with all extensions inlined.
 *
 * Field types are in a context where params are bound:
 * - param[0] is at De Bruijn index 0
 */
export interface TTKRecordDef {
  name: string;
  constructorName: string;  // Constructor name (defaults to Mk#${name})
  type: TTKTerm;
  params: TTKRecordParam[];
  fields: TTKRecordField[];
}

// ============================================================================
// Type Check Error
// ============================================================================

import { IndexPath } from '../types/source-position';

export class TypeCheckError extends Error {
  constructor(
    message: string,
    public term?: TTKTerm,
    public context?: TTKContext,
    public termPath?: IndexPath,
  ) {
    super(message);
    this.name = 'TypeCheckError';
  }
}

// ============================================================================
// Hole Utility Functions
// ============================================================================

/**
 * Find a hole by ID in a term
 */
export function findHole(term: TTKTerm, holeId: string): TTKTerm | null {
  switch (term.tag) {
    case 'Hole':
      return term.id === holeId ? term : null;

    case 'Meta':
    case 'Var':
    case 'Const':
    case 'ULevel':
    case 'ULit':
    case 'UOmega':
      return null;

    case 'Sort':
      // Level is now a term, so search in the level
      return findHole(term.level, holeId);

    case 'Binder': {
      const inDomain = findHole(term.domain, holeId);
      if (inDomain) return inDomain;
      const inBody = findHole(term.body, holeId);
      if (inBody) return inBody;
      if (term.binderKind.tag === 'BLet') {
        const inDefVal = findHole(term.binderKind.defVal, holeId);
        if (inDefVal) return inDefVal;
      }
      return null;
    }

    case 'App': {
      const inFn = findHole(term.fn, holeId);
      if (inFn) return inFn;
      return findHole(term.arg, holeId);
    }

    case 'Annot': {
      const inTerm = findHole(term.term, holeId);
      if (inTerm) return inTerm;
      return findHole(term.type, holeId);
    }

    case 'Match': {
      const inScrutinee = findHole(term.scrutinee, holeId);
      if (inScrutinee) return inScrutinee;
      for (const clause of term.clauses) {
        const inRhs = findHole(clause.rhs, holeId);
        if (inRhs) return inRhs;
      }
      return null;
    }

    case 'NatLit':
    case 'RatLit':
      return null;
  }
}

/**
 * Fill a hole with a proof term
 */
export function fillHole(term: TTKTerm, holeId: string, proofTerm: TTKTerm): TTKTerm {
  switch (term.tag) {
    case 'Hole':
      return term.id === holeId ? proofTerm : term;

    case 'Meta':
    case 'Var':
    case 'Const':
    case 'ULevel':
    case 'ULit':
    case 'UOmega':
    case 'NatLit':
    case 'RatLit':
      return term;

    case 'Sort':
      // Level is now a term, so fill holes in the level
      return { tag: 'Sort', level: fillHole(term.level, holeId, proofTerm) };

    case 'Binder': {
      const newDomain = fillHole(term.domain, holeId, proofTerm);
      const newBody = fillHole(term.body, holeId, proofTerm);
      let newBinderKind: TTKBinderKind;
      if (term.binderKind.tag === 'BLet') {
        const newDefVal = fillHole(term.binderKind.defVal, holeId, proofTerm);
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
        fn: fillHole(term.fn, holeId, proofTerm),
        arg: fillHole(term.arg, holeId, proofTerm)
      };

    case 'Annot':
      return {
        tag: 'Annot',
        term: fillHole(term.term, holeId, proofTerm),
        type: fillHole(term.type, holeId, proofTerm)
      };

    case 'Match':
      return {
        tag: 'Match',
        scrutinee: fillHole(term.scrutinee, holeId, proofTerm),
        clauses: term.clauses.map(c => ({
          ...c,
          rhs: fillHole(c.rhs, holeId, proofTerm)
        }))
      };
  }
}

function patternsStructurallyEqual(left: readonly TTKPattern[], right: readonly TTKPattern[]): boolean {
  return left.length === right.length && left.every((pattern, index) => patternStructurallyEqual(pattern, right[index]));
}

function namedPatternsStructurallyEqual(
  left?: readonly TTKNamedPatternArg[],
  right?: readonly TTKNamedPatternArg[],
): boolean {
  const leftPatterns = left ?? [];
  const rightPatterns = right ?? [];
  return leftPatterns.length === rightPatterns.length &&
    leftPatterns.every((pattern, index) =>
      pattern.name === rightPatterns[index].name &&
      patternStructurallyEqual(pattern.pattern, rightPatterns[index].pattern));
}

function patternStructurallyEqual(left: TTKPattern, right: TTKPattern): boolean {
  if (left.tag !== right.tag) return false;
  switch (left.tag) {
    case 'PVar':
    case 'PWild':
      return left.name === (right as typeof left).name;
    case 'PCtor': {
      const rightCtor = right as typeof left;
      return left.name === rightCtor.name &&
        patternsStructurallyEqual(left.args, rightCtor.args) &&
        namedPatternsStructurallyEqual(left.namedArgs, rightCtor.namedArgs);
    }
  }
}
