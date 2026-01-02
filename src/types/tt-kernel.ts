/**
 * TTK (Typed Terms - Kernel) Core Layer
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
export type TTKTermConst = { tag: 'Const'; name: string; type: TTKTerm }

export type TTKTerm =
  | { tag: 'Var'; index: number }                          // De Bruijn variable
  | { tag: 'Sort'; level: number }                         // Type_i, Prop = Type_0
  | { tag: 'Binder'; name: string; binderKind: TTKBinderKind; domain: TTKTerm; body: TTKTerm }  // Unified binder
  | TTKTermApp   // Function application (f a)
  | TTKTermConst // Named constant (nat_elim, eq, etc.)
  | { tag: 'Hole'; id: string; type: TTKTerm; context: TTKContext }  // Metavariable (unproven goal)
  | { tag: 'Annot'; term: TTKTerm; type: TTKTerm }          // Type annotation

/**
 * Named variable in context (for debugging/pretty-printing only)
 */
export interface TTKBinding {
  name: string;
  type: TTKTerm;
}

/**
 * Type-checking context: list of bound variables
 * Index 0 is the most recently bound variable
 */
export type TTKContext = TTKBinding[];

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
 * Create a constant with a given name and type
 */
export function mkConst(name: string, type: TTKTerm): TTKTerm {
  return { tag: 'Const', name, type };
}

/**
 * Create a hole (metavariable to be filled)
 */
export function mkHole(id: string, type: TTKTerm, context: TTKContext = []): TTKTerm {
  return { tag: 'Hole', id, type, context };
}

/**
 * Create Prop (Type_0)
 */
export function mkProp(): TTKTerm {
  return { tag: 'Sort', level: 0 };
}

/**
 * Create Type_i
 */
export function mkType(level: number): TTKTerm {
  return { tag: 'Sort', level };
}

// ============================================================================
// Substitution (for De Bruijn indices)
// ============================================================================

/**
 * Substitute term s for variable with index n in term t
 * This is the core operation for beta-reduction and let-expansion
 */
export function subst(index: number, replacement: TTKTerm, term: TTKTerm): TTKTerm {
  return substHelper(index, replacement, term, 0);
}

function substHelper(targetIndex: number, replacement: TTKTerm, term: TTKTerm, depth: number): TTKTerm {
  switch (term.tag) {
    case 'Var':
      if (term.index === targetIndex + depth) {
        return shift(depth, replacement, 0);
      }
      return term;

    case 'Sort':
    case 'Const':
      return term;

    case 'Binder': {
      const newDomain = substHelper(targetIndex, replacement, term.domain, depth);
      const newBody = substHelper(targetIndex, replacement, term.body, depth + 1);

      let newBinderKind: TTKBinderKind;
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
        context: term.context
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
 */
function shift(amount: number, term: TTKTerm, cutoff: number): TTKTerm {
  switch (term.tag) {
    case 'Var':
      return term.index >= cutoff
        ? { tag: 'Var', index: term.index + amount }
        : term;

    case 'Sort':
    case 'Const':
      return term;

    case 'Binder': {
      const newDomain = shift(amount, term.domain, cutoff);
      const newBody = shift(amount, term.body, cutoff + 1);

      let newBinderKind: TTKBinderKind;
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
      return term2.tag === 'Sort' && term1.level === term2.level;

    case 'Const':
      return term2.tag === 'Const' && term1.name === term2.name;

    case 'Hole':
      return term2.tag === 'Hole' && term1.id === term2.id;

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
  }
}

// ============================================================================
// Pretty Printing
// ============================================================================

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

    case 'Sort':
      // Sort(0) = Prop, Sort(1) = Type, Sort(n+1) = Type n
      // Following Lean's convention where Type = Sort 1, Type 1 = Sort 2, etc.
      if (term.level === 0) {
        return 'Prop';
      }
      const typeLevel = term.level - 1;
      return typeLevel === 0 ? 'Type' : `Type ${typeLevel}`;

    case 'Const':
      return term.name;

    case 'Binder': {
      const domain = prettyPrint(term.domain, context);
      const newContext = [term.name, ...context];
      const body = prettyPrint(term.body, newContext);
      const isAnonymous = term.name === '_' || term.name === '';

      switch (term.binderKind.tag) {
        case 'BPi':
          // If anonymous binder, just show: domain -> body
          // Otherwise show: (name : domain) -> body
          if (isAnonymous) {
            return `(${domain} -> ${body})`;
          }
          return `((${term.name} : ${domain}) -> ${body})`;

        case 'BLam':
          if (isAnonymous) {
            return `(λ ${domain} => ${body})`;
          }
          return `(λ (${term.name} : ${domain}) => ${body})`;

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
      return occursIn(index, term.type);
    case 'Annot':
      return occursIn(index, term.term) || occursIn(index, term.type);
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

