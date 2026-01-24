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

export function prettyPrintPattern(pattern: TTKPattern, updatedNames: string[] = []): string {
  const [updatedName, ...rest] = updatedNames

  switch (pattern.tag) {
    case 'PVar': {
      const name = updatedName ?? pattern.name;
      return name;
    }
    case 'PWild':
      // Display wildcards with their generated name visible
      return `_[${pattern.name}]`;
    case 'PCtor': {
      const name = updatedName ?? pattern.name;
      if (pattern.args.length === 0) {
        return name;
      }
      return `(${name} ${pattern.args.map(p => prettyPrintPattern(p, rest)).join(' ')})`;
    }
  }
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
      // For other term types (Sort, Binder, etc.), which shouldn't appear in levels
      return false;
  }
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

/**
 * Pretty print a level term.
 */
export function prettyPrintLevel(level: TTKTerm): string {
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
    return `#${level.index}`;
  }
  if (level.tag === 'Meta') {
    return `?${level.id}`;
  }

  const succArg = matchUSucc(level);
  if (succArg !== undefined) {
    return `(${prettyPrintLevel(succArg)} + 1)`;
  }

  const maxArgs = matchUMax(level);
  if (maxArgs !== undefined) {
    return `max(${prettyPrintLevel(maxArgs[0])}, ${prettyPrintLevel(maxArgs[1])})`;
  }

  const imaxArgs = matchUIMax(level);
  if (imaxArgs !== undefined) {
    return `imax(${prettyPrintLevel(imaxArgs[0])}, ${prettyPrintLevel(imaxArgs[1])})`;
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
        if (!isDefinitionallyEqual(term1.clauses[i].rhs, term2.clauses[i].rhs)) return false;
      }
      return true;
    }

    case 'ULit':
      return term2.tag === 'ULit' && term1.n === term2.n;

    case 'UOmega':
      return term2.tag === 'UOmega';
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
        return `Type ${prettyPrintLevel(succArg)}`;
      }
      // Fallback for other level forms (shouldn't happen in well-formed terms)
      return `Sort ${prettyPrintLevel(term.level)}`;
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
            const domain = stripOuterParens(prettyPrint(current.domain, ctx, metaVars));
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
      const scrutinee = prettyPrint(term.scrutinee, context, metaVars);
      const clauses = term.clauses.map(c => {
        // Use stored context names if available (from checking), otherwise derive from patterns
        const clauseContext = c.contextNames
          ? [...c.contextNames, ...context]
          : [...collectPatternVars(c.patterns).reverse(), ...context];
        // Use clause's metaVars if available (for solved terms), otherwise fall back to outer metaVars
        const clauseMetaVars = c.metaVars ?? metaVars;

        // If elabArgs are available, show them (the solved elaboration); otherwise show patterns
        const lhsStr = c.elabArgs
          ? c.elabArgs.map(arg => prettyPrint(arg, clauseContext, clauseMetaVars)).join(' ')
          : c.patterns.map(p => prettyPrintPatternInternal(p)).join(' ');

        const rhsStr = prettyPrint(c.rhs, clauseContext, clauseMetaVars);
        return `${lhsStr} => ${rhsStr}`;
      }).join(' | ');
      return `(match ${scrutinee} | ${clauses})`;
    }
  }
}

/**
 * Pretty print options for formatted output
 */
export interface PrettyPrintOptions {
  /** Current indentation level (number of spaces) */
  indent?: number;
  /** Number of spaces per indentation level */
  indentSize?: number;
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
        return `Type ${prettyPrintLevel(succArg)}`;
      }
      return `Sort ${prettyPrintLevel(term.level)}`;
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
          while (current.tag === 'Binder' && current.binderKind.tag === 'BPi') {
            const currentAnon = current.name === '_' || current.name === '';
            const domain = stripOuterParens(prettyPrintFormatted(current.domain, ctx, metaVars, options));
            if (currentAnon) {
              parts.push(domain);
            } else {
              parts.push(`(${current.name} : ${domain})`);
            }
            ctx = [current.name, ...ctx];
            current = current.body;
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
      const parts: string[] = [];
      let current: TTKTerm = term;
      while (current.tag === 'App') {
        parts.unshift(prettyPrintFormatted(current.arg, context, metaVars, options));
        current = current.fn;
      }
      parts.unshift(prettyPrintFormatted(current, context, metaVars, options));
      return `(${parts.join(' ')})`;
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
      const scrutinee = prettyPrintFormatted(term.scrutinee, context, metaVars, options);
      const nextPad = ' '.repeat(nextIndent);

      const clauses = term.clauses.map(c => {
        const clauseContext = c.contextNames
          ? [...c.contextNames, ...context]
          : [...collectPatternVars(c.patterns).reverse(), ...context];
        const clauseMetaVars = c.metaVars ?? metaVars;

        const lhsStr = c.elabArgs
          ? c.elabArgs.map(arg => prettyPrintFormatted(arg, clauseContext, clauseMetaVars, options)).join(' ')
          : c.patterns.map(p => prettyPrintPatternInternal(p)).join(' ');

        const rhsStr = prettyPrintFormatted(c.rhs, clauseContext, clauseMetaVars, { ...options, indent: nextIndent });
        return `${nextPad}| ${lhsStr} => ${rhsStr}`;
      }).join('\n');

      return `(match ${scrutinee}\n${clauses})`;
    }
  }
}

function prettyPrintPatternInternal(pattern: TTKPattern): string {
  switch (pattern.tag) {
    case 'PVar':
      return pattern.name;
    case 'PWild':
      // Display wildcards with their generated name visible
      return `_[${pattern.name}]`;
    case 'PCtor':
      if (pattern.args.length === 0) {
        return pattern.name;
      }
      const args = pattern.args.map(prettyPrintPatternInternal).join(' ');
      return `(${pattern.name} ${args})`;
  }
}

/** Collect variable names from patterns in left-to-right order */
function collectPatternVars(patterns: TTKPattern[]): string[] {
  const vars: string[] = [];
  for (const p of patterns) {
    collectPatternVarsHelper(p, vars);
  }
  return vars;
}

function collectPatternVarsHelper(pattern: TTKPattern, vars: string[]): void {
  switch (pattern.tag) {
    case 'PVar':
      vars.push(pattern.name);
      break;
    case 'PWild':
      vars.push(pattern.name);
      break;
    case 'PCtor':
      for (const arg of pattern.args) {
        collectPatternVarsHelper(arg, vars);
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
        return context[term.index];
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
          return `(\\text{let } ${term.name} : ${domain} = ${defVal} \\text{ in } ${body})`;
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
      const scrutinee = prettyPrintLatex(term.scrutinee, context, opts);
      const clauses = term.clauses.map(c => {
        // Collect pattern variable names and add to context for RHS and elabArgs
        const patternVars = collectPatternVars(c.patterns);
        const clauseContext = [...patternVars.reverse(), ...context];

        // If elabArgs are available, show them (the solved elaboration); otherwise show patterns
        const lhsStr = c.elabArgs
          ? c.elabArgs.map(arg => prettyPrintLatex(arg, clauseContext, opts)).join('\\; ')
          : c.patterns.map(p => prettyPrintPatternLatex(p)).join('\\; ');

        const rhsStr = prettyPrintLatex(c.rhs, clauseContext, opts);
        return `${lhsStr} \\Rightarrow ${rhsStr}`;
      }).join(' \\mid ');
      return `\\text{match}\\; ${scrutinee}\\; \\{\\, ${clauses} \\,\\}`;
    }

    case 'ULevel':
      return '\\text{Level}';
  }
}

function prettyPrintPatternLatex(pattern: TTKPattern): string {
  const escapeName = (name: string) => name.replace(/_/g, '\\_');

  switch (pattern.tag) {
    case 'PVar':
      return escapeName(pattern.name);
    case 'PWild':
      // Display wildcards with their generated name visible
      return `\\_{[${escapeName(pattern.name)}]}`;
    case 'PCtor':
      if (pattern.args.length === 0) {
        return escapeName(pattern.name);
      }
      const args = pattern.args.map(prettyPrintPatternLatex).join('\\; ');
      return `(${escapeName(pattern.name)}\\; ${args})`;
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
        if (occursIn(index, clause.rhs)) return true;
      }
      return false;

    case 'ULevel':
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
}

/**
 * A field in a kernel record type.
 * This is the elaborated form - no extensions, just plain fields.
 */
export interface TTKRecordField {
  name: string;
  type: TTKTerm;
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
// Type Inference Stub (TODO: Integrate with compiler/checker.ts)
// ============================================================================

export type InferResult =
  | { ok: true; type: TTKTerm }
  | { ok: false; error: string };

/**
 * Type inference stub. In the future, this should integrate with the
 * proper type checker in compiler/checker.ts.
 */
export function inferType(_term: TTKTerm, _context: TTKContext): InferResult {
  // TODO: Implement proper type inference using compiler/checker.ts
  return { ok: false, error: 'Type inference not yet implemented in new compiler' };
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
          patterns: c.patterns,
          rhs: fillHole(c.rhs, holeId, proofTerm)
        }))
      };
  }
}

