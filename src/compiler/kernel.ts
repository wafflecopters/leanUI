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
// Universe Levels
// ============================================================================

/**
 * Universe levels for the type hierarchy.
 *
 * - LZero: The zero level (Prop)
 * - LSucc: Successor level (l + 1)
 * - LMax: Maximum of two levels (for Pi types)
 * - LIMax: Impredicative max - max(l1, l2) but 0 if l2 = 0 (for Prop)
 * - LParam: Level parameter (for universe-polymorphic definitions)
 * - LMVar: Level metavariable (for inference)
 */
export type Level =
  | { tag: 'LZero' }
  | { tag: 'LSucc'; pred: Level }
  | { tag: 'LMax'; left: Level; right: Level }
  | { tag: 'LIMax'; left: Level; right: Level }
  | { tag: 'LParam'; name: string }
  | { tag: 'LMVar'; id: string }

// Level constructors
export const mkLZero = (): Level => ({ tag: 'LZero' });
export const mkLSucc = (pred: Level): Level => ({ tag: 'LSucc', pred });
export const mkLMax = (left: Level, right: Level): Level => ({ tag: 'LMax', left, right });
export const mkLIMax = (left: Level, right: Level): Level => ({ tag: 'LIMax', left, right });
export const mkLParam = (name: string): Level => ({ tag: 'LParam', name });
export const mkLMVar = (id: string): Level => ({ tag: 'LMVar', id });

// Convenience: create a concrete level from a number
export function mkLevelNum(n: number): Level {
  let level: Level = mkLZero();
  for (let i = 0; i < n; i++) {
    level = mkLSucc(level);
  }
  return level;
}

// Try to convert a level to a concrete number, returns undefined if it contains variables/metas
export function levelToNumber(level: Level): number | undefined {
  switch (level.tag) {
    case 'LZero':
      return 0;
    case 'LSucc': {
      const pred = levelToNumber(level.pred);
      return pred !== undefined ? pred + 1 : undefined;
    }
    case 'LMax': {
      const left = levelToNumber(level.left);
      const right = levelToNumber(level.right);
      return left !== undefined && right !== undefined ? Math.max(left, right) : undefined;
    }
    case 'LIMax': {
      const left = levelToNumber(level.left);
      const right = levelToNumber(level.right);
      if (right === 0) return 0;  // imax(_, 0) = 0
      return left !== undefined && right !== undefined ? Math.max(left, right) : undefined;
    }
    case 'LParam':
    case 'LMVar':
      return undefined;
  }
}

// Simplify a level (basic simplifications)
export function simplifyLevel(level: Level): Level {
  switch (level.tag) {
    case 'LZero':
    case 'LParam':
    case 'LMVar':
      return level;

    case 'LSucc':
      return mkLSucc(simplifyLevel(level.pred));

    case 'LMax': {
      const left = simplifyLevel(level.left);
      const right = simplifyLevel(level.right);

      // max(0, l) = l, max(l, 0) = l
      if (left.tag === 'LZero') return right;
      if (right.tag === 'LZero') return left;

      // max(l, l) = l
      if (levelsEqual(left, right)) return left;

      // If both are concrete, compute the max
      const leftNum = levelToNumber(left);
      const rightNum = levelToNumber(right);
      if (leftNum !== undefined && rightNum !== undefined) {
        return mkLevelNum(Math.max(leftNum, rightNum));
      }

      return mkLMax(left, right);
    }

    case 'LIMax': {
      const left = simplifyLevel(level.left);
      const right = simplifyLevel(level.right);

      // imax(_, 0) = 0
      if (right.tag === 'LZero') return mkLZero();

      // If right is definitely not zero, imax = max
      const rightNum = levelToNumber(right);
      if (rightNum !== undefined && rightNum > 0) {
        return simplifyLevel(mkLMax(left, right));
      }

      return mkLIMax(left, right);
    }
  }
}

// Check if two levels are structurally equal
export function levelsEqual(l1: Level, l2: Level): boolean {
  if (l1.tag !== l2.tag) return false;

  switch (l1.tag) {
    case 'LZero':
      return true;
    case 'LSucc':
      return levelsEqual(l1.pred, (l2 as typeof l1).pred);
    case 'LMax':
    case 'LIMax':
      return levelsEqual(l1.left, (l2 as typeof l1).left) &&
             levelsEqual(l1.right, (l2 as typeof l1).right);
    case 'LParam':
      return l1.name === (l2 as typeof l1).name;
    case 'LMVar':
      return l1.id === (l2 as typeof l1).id;
  }
}

// Pretty print a level
export function prettyPrintLevel(level: Level): string {
  // Try to get a concrete number first
  const num = levelToNumber(level);
  if (num !== undefined) {
    return num.toString();
  }

  switch (level.tag) {
    case 'LZero':
      return '0';
    case 'LSucc':
      return `(${prettyPrintLevel(level.pred)} + 1)`;
    case 'LMax':
      return `max(${prettyPrintLevel(level.left)}, ${prettyPrintLevel(level.right)})`;
    case 'LIMax':
      return `imax(${prettyPrintLevel(level.left)}, ${prettyPrintLevel(level.right)})`;
    case 'LParam':
      return level.name;
    case 'LMVar':
      return `?${level.id}`;
  }
}

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
export type TTKPattern =
  | { tag: 'PVar'; name: string }
  | { tag: 'PWild'; name: string }
  | { tag: 'PCtor'; name: string; args: TTKPattern[] };

export type TTKClause = {
  patterns: TTKPattern[];
  rhs: TTKTerm;
};

export type TTKTerm =
  | { tag: 'Var'; index: number }                          // De Bruijn variable
  | { tag: 'Sort'; level: Level }                          // Sort l (Type l, Prop = Sort 0)
  | { tag: 'ULevel' }                                      // The type of universe levels
  | { tag: 'Binder'; name: string; binderKind: TTKBinderKind; domain: TTKTerm; body: TTKTerm }  // Unified binder
  | TTKTermApp   // Function application (f a)
  | TTKTermConst // Named constant (nat_elim, eq, etc.)
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
      // Display wildcards as _ (the generated name is hidden but available for inlays)
      return '_';
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

/**
 * Create Prop (Sort 0)
 */
export function mkProp(): TTKTerm {
  return { tag: 'Sort', level: mkLZero() };
}

/**
 * Create Type_i (Sort (i+1) in our convention)
 * Type = Type_0 = Sort 1
 * Type 1 = Sort 2
 * etc.
 */
export function mkType(n: number = 0): TTKTerm {
  return { tag: 'Sort', level: mkLSucc(mkLevelNum(n)) };
}

/**
 * Create Sort with explicit level
 */
export function mkSort(level: Level): TTKTerm {
  return { tag: 'Sort', level };
}

/**
 * Create ULevel (the type of universe levels)
 */
export function mkULevel(): TTKTerm {
  return { tag: 'ULevel' };
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

/**
 * Convert a kernel term to a human-readable string
 */
export function prettyPrint(term: TTKTerm, context: string[] = []): string {
  switch (term.tag) {
    case 'Var':
      // Context is prepended, so index directly into it
      if (term.index < context.length) {
        return context[term.index];
      }
      return `#${term.index}`;

    case 'Sort': {
      // Sort 0 = Prop, Sort 1 = Type, Sort (n+1) = Type n
      // Following Lean's convention where Type = Sort 1, Type 1 = Sort 2, etc.
      const levelNum = levelToNumber(term.level);
      if (levelNum !== undefined) {
        if (levelNum === 0) return 'Prop';
        const typeLevel = levelNum - 1;
        return typeLevel === 0 ? 'Type' : `Type ${typeLevel}`;
      }
      // Level contains variables/metas, show as Sort l
      return `Sort ${prettyPrintLevel(term.level)}`;
    }

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
          return `(let ${term.name} : ${domain} = ${defVal} in ${body})`;
        }
      }
    }

    case 'App': {
      // Collect all arguments from nested applications: ((f a) b) c -> [f, a, b, c]
      const parts: string[] = [];
      let current: TTKTerm = term;
      while (current.tag === 'App') {
        parts.unshift(prettyPrint(current.arg, context));
        current = current.fn;
      }
      parts.unshift(prettyPrint(current, context));
      return `(${parts.join(' ')})`;
    }

    case 'Hole':
      return `?${term.id}`;

    case 'Meta':
      return `?${term.id}`;

    case 'Annot': {
      const termStr = prettyPrint(term.term, context);
      const typeStr = stripOuterParens(prettyPrint(term.type, context));
      return `(${termStr} : ${typeStr})`;
    }

    case 'Match': {
      const scrutinee = prettyPrint(term.scrutinee, context);
      const clauses = term.clauses.map(c => {
        const patternStr = c.patterns.map(p => prettyPrintPatternInternal(p)).join(' ');
        // Collect pattern variable names and add to context for RHS
        const patternVars = collectPatternVars(c.patterns);
        const rhsContext = [...patternVars.reverse(), ...context];
        const rhsStr = prettyPrint(c.rhs, rhsContext);
        return `${patternStr} => ${rhsStr}`;
      }).join(' | ');
      return `(match ${scrutinee} | ${clauses})`;
    }
  }
}

function prettyPrintPatternInternal(pattern: TTKPattern): string {
  switch (pattern.tag) {
    case 'PVar':
      return pattern.name;
    case 'PWild':
      return '_';
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
      // Sort 0 = Prop, Sort 1 = Type, Sort (n+1) = Type n
      const levelNum = levelToNumber(term.level);
      if (levelNum !== undefined) {
        if (levelNum === 0) return '\\text{Prop}';
        const typeLevel = levelNum - 1;
        return typeLevel === 0 ? '\\text{Type}' : `\\text{Type}_{${typeLevel}}`;
      }
      // Level contains variables/metas
      return `\\text{Sort}\\; ${prettyPrintLevel(term.level)}`;
    }

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
        const patternStr = c.patterns.map(p => prettyPrintPatternLatex(p)).join('\\; ');
        const rhsStr = prettyPrintLatex(c.rhs, context, opts);
        return `${patternStr} \\Rightarrow ${rhsStr}`;
      }).join(' \\mid ');
      return `\\text{match}\\; ${scrutinee}\\; \\{\\, ${clauses} \\,\\}`;
    }
  }
}

function prettyPrintPatternLatex(pattern: TTKPattern): string {
  const escapeName = (name: string) => name.replace(/_/g, '\\_');

  switch (pattern.tag) {
    case 'PVar':
      return escapeName(pattern.name);
    case 'PWild':
      return '\\_';
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
    case 'Const':
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
    case 'Sort':
    case 'Const':
      return null;

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
    case 'Sort':
    case 'Const':
      return term;

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

