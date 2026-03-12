/**
 * latex-converter.ts — Convert CompiledDeclaration[] into structured LaTeX for rendering.
 *
 * Pure functions, no React. Produces LatexDocument which the LaTeXPanel renders.
 */

import { CompiledDeclaration, CompiledBlock, CompileResult } from './compile';
import { TTKTerm, TTKPattern, TTKClause } from './kernel';
import { extractAppSpine, extractPiSpine, AppSpine } from './term';
import { occursIn } from './kernel';
import { shiftTerm } from './subst';

// ============================================================================
// Carrier Type Suppression
// ============================================================================
// "Carrier types" are bundled algebraic structures (like Real = DPair Type
// CompleteOrderedField) where the binding variable is an implementation detail.
// In math, you write f,g : ℝ → ℝ, not ∀R:ℝ, f,g : R → R.
//
// When a Pi/Lambda binder has a carrier type, we:
// 1. Suppress the binder from rendered output
// 2. Push the carrier's LaTeX into the context so references resolve to it
//    (e.g., Carrier R → transparent → Var(R) → ℝ)

const CARRIER_TYPES: Record<string, string> = {
  'Real': '\\mathbb{R}',
};

/** Sentinel prefix for raw LaTeX entries in the rendering context. */
const LATEX_PREFIX = '\x00latex:';

/**
 * Set of user-defined type names whose bodies are propositional.
 * Built in convertToLatex() before processing declarations, so that
 * looksLikeProp can recognize e.g. EpsDeltaWitness as propositional.
 */
let _knownPropNames: Set<string> = new Set();

/** Check if a term is a carrier type. Returns the LaTeX string or null. */
function isCarrierType(type: TTKTerm): string | null {
  if (type.tag === 'Const' && CARRIER_TYPES[type.name]) {
    return CARRIER_TYPES[type.name];
  }
  return null;
}

/** Check if a context entry is a carrier substitution. */
function isCarrierEntry(name: string): boolean {
  return name.startsWith(LATEX_PREFIX);
}

/** Find which binder positions in a Pi-type are carrier types. */
function getCarrierPositions(type: TTKTerm): Map<number, string> {
  const positions = new Map<number, string>();
  const { binders } = extractPiSpine(type);
  for (let i = 0; i < binders.length; i++) {
    const cl = isCarrierType(binders[i].type);
    if (cl) positions.set(i, cl);
  }
  return positions;
}

// ============================================================================
// Greek Letters & Variable Name Cleanup
// ============================================================================

const GREEK_MAP: Record<string, string> = {
  'eps': '\\varepsilon',
  'epsilon': '\\varepsilon',
  'delta': '\\delta',
  'alpha': '\\alpha',
  'beta': '\\beta',
  'gamma': '\\gamma',
  'sigma': '\\sigma',
  'tau': '\\tau',
  'mu': '\\mu',
  'nu': '\\nu',
  'phi': '\\varphi',
  'psi': '\\psi',
  'omega': '\\omega',
  'theta': '\\theta',
  'eta': '\\eta',
  'rho': '\\rho',
  'xi': '\\xi',
  'zeta': '\\zeta',
};

/**
 * Clean up internal variable names for display.
 * _pad0 → f, _pad1 → g, etc. (elaborator renames)
 * _implicit... → suppress
 */
function cleanVarName(name: string): string {
  // _padN → letter from alphabet
  const padMatch = name.match(/^_pad(\d+)$/);
  if (padMatch) {
    const idx = parseInt(padMatch[1]);
    const letters = 'fghpqrstuvw';
    return idx < letters.length ? letters[idx] : `f_{${idx}}`;
  }
  return name;
}

/**
 * Check if a variable name looks like a proof/hypothesis variable (Lean convention).
 * Short h-prefixed names (hab, hbc, hle, hlt, heps, hx, hne) are hypothesis names.
 * Short ne-prefixed names (neab, nebc) are negation hypothesis names.
 * Also catches single-letter proof vars like 'h' and short names like 'eq'.
 */
function isHypothesisName(name: string): boolean {
  if (/^h[a-z]{0,5}$/.test(name)) return true;  // h, hab, hbc, hle, hlt, heps, hx
  if (/^ne[a-z]{1,3}$/.test(name)) return true;  // neab, nebc
  if (name === 'eq') return true;                 // equality from pattern matching
  return false;
}

/**
 * Render a variable name as LaTeX, applying Greek letter mapping and cleanup.
 * If the name is a carrier substitution (LATEX_PREFIX), return raw LaTeX.
 */
function renderVarName(name: string): string {
  if (name.startsWith(LATEX_PREFIX)) {
    return name.slice(LATEX_PREFIX.length);
  }
  const cleaned = cleanVarName(name);
  const greek = GREEK_MAP[cleaned];
  if (greek) return greek;
  // Subscript detection: single letter + digits → letter_{digits}
  const subscriptMatch = cleaned.match(/^([a-zA-Z])(\d+)$/);
  if (subscriptMatch) {
    return `${subscriptMatch[1]}_{${subscriptMatch[2]}}`;
  }
  // Single letter → math italic (standard math convention)
  // Multi-letter → \text{} to avoid rendering as product of variables
  if (cleaned.length === 1) return escapeLaTeX(cleaned);
  return `\\text{${escapeLaTeX(cleaned)}}`;
}

// ============================================================================
// Output Types
// ============================================================================

export interface LatexSection {
  name: string;
  category: 'inductive' | 'record' | 'definition' | 'theorem' | 'postulate';
  checkSuccess: boolean;
  errors: string[];
  blocks: LatexBlock[];
}

export type LatexBlock =
  | { kind: 'header'; latex: string }
  | { kind: 'rule'; latex: string }
  | { kind: 'comment'; latex: string };

export interface LatexDocument {
  sections: LatexSection[];
}

// ============================================================================
// Notation Table
// ============================================================================

export type NotationEntry =
  | { kind: 'const'; latex: string }                                // 0-arity constant: Nat → ℕ
  | { kind: 'prefix'; latex: string; arity: number; skipArgs: number[] }  // prefix function: S(x)
  | { kind: 'infix'; latex: string; arity: number; skipArgs: number[] }   // infix: x + y
  | { kind: 'custom'; arity?: number; render: (args: TTKTerm[], ctx: string[], n: NotationTable) => string };

export type NotationTable = Map<string, NotationEntry>;

/**
 * Render a function argument as a summand expression.
 * If fn is a lambda `\i => body`, render body with indexVar as the bound name.
 * If fn is a variable or other term, render as `fn(indexVar)`.
 */
function renderSummand(fn: TTKTerm, indexVar: string, ctx: string[], notations: NotationTable): string {
  if (fn.tag === 'Binder' && fn.binderKind.tag === 'BLam') {
    // Lambda: render the body with the index variable name
    const bodyCtx = [indexVar, ...ctx];
    return termToLatex(fn.body, bodyCtx, notations);
  }
  // Variable or named function: render as f(i)
  const fnStr = termToLatex(fn, ctx, notations);
  return `${fnStr}(${indexVar})`;
}

/**
 * Default notation table for the nat-math-tactics preset.
 */
export function makeDefaultNotations(): NotationTable {
  const table: NotationTable = new Map();

  // Types
  table.set('Nat', { kind: 'const', latex: '\\mathbb{N}' });
  table.set('Void', { kind: 'const', latex: '\\bot' });

  // Constructors
  table.set('Zero', { kind: 'const', latex: '0' });
  table.set('Succ', { kind: 'prefix', latex: 'S', arity: 1, skipArgs: [] });

  // Arithmetic
  table.set('plus', { kind: 'infix', latex: '+', arity: 2, skipArgs: [] });
  table.set('mul', { kind: 'infix', latex: '\\cdot', arity: 2, skipArgs: [] });

  // Relations — Equal has 3 args: {A} x y, skip the type arg
  table.set('Equal', { kind: 'infix', latex: '=', arity: 3, skipArgs: [0] });
  table.set('Leq', { kind: 'infix', latex: '\\le', arity: 2, skipArgs: [] });
  table.set('LessThan', { kind: 'infix', latex: '<', arity: 2, skipArgs: [] });

  // Constructors for Leq
  table.set('LeqZero', { kind: 'custom', render: (_args, _ctx, _n) => '\\text{LeqZero}' });
  table.set('LeqSucc', { kind: 'custom', render: (args, ctx, n) => {
    if (args.length >= 3) {
      // {n} {m} proof — skip implicits, show proof
      return `\\text{LeqSucc}\\;${termToLatex(args[args.length - 1], ctx, n)}`;
    }
    return '\\text{LeqSucc}';
  }});

  // refl constructor — Equal.refl has implicit {A} {a}, so 0 visible args
  table.set('refl', { kind: 'custom', render: (args, ctx, n) => {
    if (args.length === 0) return '\\text{refl}';
    // If applied to visible args, render them
    const visibleArgs = args.slice(2); // skip {A} {a}
    if (visibleArgs.length === 0) return '\\text{refl}';
    return '\\text{refl}\\;' + visibleArgs.map(a => termToLatex(a, ctx, n)).join('\\;');
  }});

  // Either — use "or" for propositional disjunction, ⊕ for sum types
  table.set('Either', { kind: 'custom', render: (args, ctx, n) => {
    if (args.length === 2) {
      const a = termToLatex(args[0], ctx, n);
      const b = termToLatex(args[1], ctx, n);
      if (looksLikeProp(args[0], 0) || looksLikeProp(args[1], 0)) {
        return `${a} \\text{ or } ${b}`;
      }
      return `${a} \\oplus ${b}`;
    }
    return '\\text{Either}';
  }});
  table.set('inl', { kind: 'custom', render: (args, ctx, n) => {
    // {L} {R} val
    const val = args.length >= 3 ? args[2] : args[args.length - 1];
    if (val) return `\\text{inl}\\;${termToLatex(val, ctx, n)}`;
    return '\\text{inl}';
  }});
  table.set('inr', { kind: 'custom', render: (args, ctx, n) => {
    const val = args.length >= 3 ? args[2] : args[args.length - 1];
    if (val) return `\\text{inr}\\;${termToLatex(val, ctx, n)}`;
    return '\\text{inr}';
  }});

  // eitherElim: {A} {B} {C} f g e — skip types, show match
  table.set('eitherElim', { kind: 'custom', render: (args, ctx, n) => {
    if (args.length >= 6) {
      const f = termToLatex(args[3], ctx, n);
      const g = termToLatex(args[4], ctx, n);
      const e = termToLatex(args[5], ctx, n);
      return `\\text{match}\\;${e}\\;\\{\\text{inl} \\Rightarrow ${f},\\; \\text{inr} \\Rightarrow ${g}\\}`;
    }
    // Partial application — show what we have
    const visible = args.slice(3);
    if (visible.length > 0) {
      const argsStr = visible.map(a => termToLatex(a, ctx, n)).join(',\\, ');
      return `\\text{eitherElim}(${argsStr})`;
    }
    return '\\text{eitherElim}';
  }});

  // replace: {A} x y P proof px — flatten nested chains, suppress motive
  table.set('replace', { kind: 'custom', render: (args, ctx, n) => {
    if (args.length >= 6) {
      // Flatten nested replace chains: replace(P, eq, replace(P', eq', base))
      // → base (by eq', eq)
      const rewrites: string[] = [];
      let curArgs = args;
      // eslint-disable-next-line no-constant-condition
      while (true) {
        if (curArgs.length >= 6) {
          rewrites.push(termToLatex(curArgs[4], ctx, n));
          const inner = curArgs[5];
          const innerSpine = extractAppSpine(inner);
          if (innerSpine.fn.tag === 'Const' && innerSpine.fn.name === 'replace' && innerSpine.args.length >= 6) {
            curArgs = innerSpine.args;
            continue;
          }
          // Base case
          const base = termToLatex(inner, ctx, n);
          const parts = rewrites.reverse().map(r => `\\text{by } ${r}`).join(',\\, ');
          return `${base}\\;(${parts})`;
        }
        break;
      }
    }
    return '\\text{replace}';
  }});

  // trans: {A} x y z proof1 proof2 — skip type+values, show proofs
  table.set('trans', { kind: 'custom', render: (args, ctx, n) => {
    if (args.length >= 6) {
      const p1 = termToLatex(args[4], ctx, n);
      const p2 = termToLatex(args[5], ctx, n);
      return `\\text{trans}(${p1},\\, ${p2})`;
    }
    return '\\text{trans}';
  }});

  // sym: {A} {x} {y} proof — skip type+values, show proof
  table.set('sym', { kind: 'custom', render: (args, ctx, n) => {
    if (args.length >= 4) {
      const inner = termToLatex(args[3], ctx, n);
      return `\\text{sym}(${inner})`;
    }
    return '\\text{sym}';
  }});

  // cong: {A} {B} x y f proof — show function and proof
  table.set('cong', { kind: 'custom', render: (args, ctx, n) => {
    if (args.length >= 6) {
      const f = termToLatex(args[4], ctx, n);
      const proof = termToLatex(args[5], ctx, n);
      return `\\text{cong}(${f},\\, ${proof})`;
    }
    return '\\text{cong}';
  }});

  // DecEq
  table.set('DecEq', { kind: 'custom', render: (args, ctx, n) => {
    // {A} a b
    if (args.length >= 3) {
      return `\\text{DecEq}\\;${termToLatex(args[1], ctx, n)}\\;${termToLatex(args[2], ctx, n)}`;
    }
    return '\\text{DecEq}';
  }});
  table.set('Yes', { kind: 'custom', render: (args, ctx, n) => {
    // {A} {a} {b} proof
    const proof = args[args.length - 1];
    if (proof) return `\\text{Yes}\\;${termToLatex(proof, ctx, n)}`;
    return '\\text{Yes}';
  }});
  table.set('No', { kind: 'custom', render: (args, ctx, n) => {
    const proof = args[args.length - 1];
    if (proof) return `\\text{No}\\;${termToLatex(proof, ctx, n)}`;
    return '\\text{No}';
  }});

  // DPair — has 4 params: u, v, A, B
  // Renders as ∃x ∈ ℝ such that ... (carrier sets) or ∃(x : A), ... (other)
  table.set('DPair', { kind: 'custom', render: (args, ctx, n) => {
    if (args.length >= 4) {
      const A = args[2];
      const B = args[3];

      // Helper: format the ∃ binder + body
      const formatDPair = (varName: string, aStr: string, bodyStr: string) => {
        const isCarrier = CARRIER_LATEX_VALUES.has(aStr);
        const nameStr = renderVarName(varName);
        if (isCarrier) {
          return `\\exists ${nameStr} \\in ${aStr} \\text{ such that } ${bodyStr}`;
        }
        return `\\exists\\,(${nameStr} : ${aStr}),\\, ${bodyStr}`;
      };

      // If B is a lambda, render as ∃(x : A), body
      if (B.tag === 'Binder' && B.binderKind.tag === 'BLam') {
        const varName = B.name || 'x';
        const aStr = termToLatex(A, ctx, n);
        const bodyCtx = [varName, ...ctx];
        const bodyStr = termToLatex(B.body, bodyCtx, n);
        return formatDPair(varName, aStr, bodyStr);
      }
      // Not a lambda — B is a function (A -> Type). Apply to a fresh var: ∃(x : A), B(x)
      // Lift B's free variables by 1 to account for the new binding
      // Detect EpsDeltaWitness to use 'delta' as the binder name
      const bSpine = extractAppSpine(B);
      const varName = (bSpine.fn.tag === 'Const' && bSpine.fn.name === 'EpsDeltaWitness') ? 'delta' : 'x';
      const aStr = termToLatex(A, ctx, n);
      const liftedB = shiftTerm(B, 1, 0);
      const bApp: TTKTerm = { tag: 'App', fn: liftedB, arg: { tag: 'Var', index: 0 } };
      const bodyCtx = [varName, ...ctx];
      const bodyStr = termToLatex(bApp, bodyCtx, n);
      return formatDPair(varName, aStr, bodyStr);
    }
    // 2-arg form (legacy)
    if (args.length === 2) {
      return `\\exists\\,(${termToLatex(args[0], ctx, n)})\\,(${termToLatex(args[1], ctx, n)})`;
    }
    return '\\exists';
  }});
  // MkDPair — 4 implicit params (u, v, A, B), then fst, snd
  table.set('MkDPair', { kind: 'custom', render: (args, ctx, n) => {
    const visible = args.slice(4);
    if (visible.length >= 2) {
      return `\\langle ${termToLatex(visible[0], ctx, n)},\\, ${termToLatex(visible[1], ctx, n)} \\rangle`;
    }
    // Fallback: try skip 2 (older calling convention)
    if (args.length >= 4 && visible.length < 2) {
      const vis2 = args.slice(2);
      if (vis2.length >= 2) {
        return `\\langle ${termToLatex(vis2[0], ctx, n)},\\, ${termToLatex(vis2[1], ctx, n)} \\rangle`;
      }
    }
    return '\\text{MkDPair}';
  }});
  // DPair.fst — skip 4 params (u, v, A, B), show projection of 5th arg
  table.set('DPair.fst', { kind: 'custom', arity: 5, render: (args, ctx, n) => {
    if (args.length >= 5) {
      return `\\pi_1(${termToLatex(args[4], ctx, n)})`;
    }
    return '\\pi_1';
  }});
  // DPair.snd — skip 4 params (u, v, A, B), show projection of 5th arg
  table.set('DPair.snd', { kind: 'custom', arity: 5, render: (args, ctx, n) => {
    if (args.length >= 5) {
      return `\\pi_2(${termToLatex(args[4], ctx, n)})`;
    }
    return '\\pi_2';
  }});

  // sigmaSumStartCount(start, count, fn) sums fn(start+0) .. fn(start+count-1)
  // Render as: ∑_{i=start}^{start+count-1} body
  table.set('sigmaSumStartCount', { kind: 'custom', render: (args, ctx, n) => {
    if (args.length === 3) {
      const start = termToLatex(args[0], ctx, n);
      const count = termToLatex(args[1], ctx, n);
      const summand = renderSummand(args[2], 'i', ctx, n);
      // Upper bound is start + count - 1; render compactly
      const upper = start === '0' ? `${count} - 1` : `${start} + ${count} - 1`;
      return `\\sum_{i=${start}}^{${upper}} ${summand}`;
    }
    return '\\sum';
  }});

  // sigmaSum(start, end, fn) — user-facing sum from start to end
  table.set('sigmaSum', { kind: 'custom', render: (args, ctx, n) => {
    if (args.length === 3) {
      const start = termToLatex(args[0], ctx, n);
      const end = termToLatex(args[1], ctx, n);
      const summand = renderSummand(args[2], 'i', ctx, n);
      return `\\sum_{i=${start}}^{${end}} ${summand}`;
    }
    return '\\sum';
  }});

  // sum(n) = 1 + 2 + ... + n = ∑_{i=1}^{n} i
  table.set('sum', { kind: 'custom', render: (args, ctx, n) => {
    if (args.length === 1) {
      const bound = termToLatex(args[0], ctx, n);
      return `\\sum_{i=1}^{${bound}} i`;
    }
    return '\\sum';
  }});

  // one
  table.set('one', { kind: 'const', latex: '1' });

  // ---- Pair / product types ----
  table.set('Pair', { kind: 'custom', render: (args, ctx, n) => {
    if (args.length >= 2) {
      return `${termToLatex(args[0], ctx, n)} \\times ${termToLatex(args[1], ctx, n)}`;
    }
    return '\\text{Pair}';
  }});
  // MkPair({A}, {B}, a, b) → (a, b)
  table.set('MkPair', { kind: 'custom', render: (args, ctx, n) => {
    const visible = args.slice(2);
    if (visible.length >= 2) {
      return `(${termToLatex(visible[0], ctx, n)},\\, ${termToLatex(visible[1], ctx, n)})`;
    }
    return '\\text{MkPair}';
  }});
  // Pair.fst({A}, {B}, p) → π₁(p)
  table.set('Pair.fst', { kind: 'custom', arity: 3, render: (args, ctx, n) => {
    if (args.length >= 3) {
      return `\\pi_1(${termToLatex(args[2], ctx, n)})`;
    }
    return '\\pi_1';
  }});
  // Pair.snd({A}, {B}, p) → π₂(p)
  table.set('Pair.snd', { kind: 'custom', arity: 3, render: (args, ctx, n) => {
    if (args.length >= 3) {
      return `\\pi_2(${termToLatex(args[2], ctx, n)})`;
    }
    return '\\pi_2';
  }});

  // ---- Real Analysis notations ----
  // All operations take (R : Real) as first arg — skip it in rendering.

  // Carrier(R) → R (transparent: the carrier type IS R for display purposes)
  table.set('Carrier', { kind: 'custom', render: (args, ctx, n) => {
    if (args.length >= 1) return termToLatex(args[0], ctx, n);
    return '\\text{Carrier}';
  }});
  // field(R) → just the record; usually invisible in math
  table.set('field', { kind: 'custom', render: (args, ctx, n) => {
    if (args.length >= 1) return `\\text{field}(${termToLatex(args[0], ctx, n)})`;
    return '\\text{field}';
  }});
  // Real type
  table.set('Real', { kind: 'const', latex: '\\mathbb{R}' });

  // Field operations on reals: radd R x y → x + y
  table.set('radd', { kind: 'infix', latex: '+', arity: 3, skipArgs: [0] });
  table.set('rmul', { kind: 'infix', latex: '\\cdot', arity: 3, skipArgs: [0] });
  table.set('rsub', { kind: 'infix', latex: '-', arity: 3, skipArgs: [0] });
  table.set('rzero', { kind: 'prefix', latex: '0', arity: 1, skipArgs: [0] });
  table.set('rone', { kind: 'prefix', latex: '1', arity: 1, skipArgs: [0] });
  table.set('rneg', { kind: 'prefix', latex: '-', arity: 2, skipArgs: [0] });
  // rtwo(R) → 2, rhalf(R) → ½, rinv(R, x) → x⁻¹
  table.set('rtwo', { kind: 'prefix', latex: '2', arity: 1, skipArgs: [0] });
  table.set('rhalf', { kind: 'custom', render: (_args, _ctx, _n) => {
    return '\\tfrac{1}{2}';
  }});
  table.set('rinv', { kind: 'custom', render: (args, ctx, n) => {
    if (args.length >= 2) {
      const x = termToLatex(args[1], ctx, n);
      // Wrap in parens if it's a compound expression
      if (x.includes('+') || x.includes('-') || x.includes('\\cdot')) {
        return `(${x})^{-1}`;
      }
      return `${x}^{-1}`;
    }
    return '\\text{inv}';
  }});

  // Order relations on reals: rle R x y → x ≤ y
  table.set('rle', { kind: 'infix', latex: '\\le', arity: 3, skipArgs: [0] });
  table.set('rlt', { kind: 'infix', latex: '<', arity: 3, skipArgs: [0] });

  // Absolute value: rabs x → |x| (R is implicit)
  table.set('rabs', { kind: 'custom', render: (args, ctx, n) => {
    if (args.length >= 2) {
      return `\\left|${termToLatex(args[1], ctx, n)}\\right|`;
    }
    return '|\\cdot|';
  }});

  // Limit: Limit R f x0 L → lim_{x → x0} f(x) = L
  table.set('Limit', { kind: 'custom', render: (args, ctx, n) => {
    if (args.length >= 4) {
      const f = args[1];
      const x0 = termToLatex(args[2], ctx, n);
      const lVal = termToLatex(args[3], ctx, n);
      // If f is a lambda, render its body directly with the bound var
      if (f.tag === 'Binder' && f.binderKind.tag === 'BLam') {
        const varName = f.name || 'x';
        const bodyCtx = [varName, ...ctx];
        const body = termToLatex(f.body, bodyCtx, n);
        // Parenthesize infix bodies: lim (f(x) + g(x)) not lim f(x) + g(x)
        const bodyHead = extractAppSpine(f.body);
        const needsParens = bodyHead.fn.tag === 'Const' &&
          n.has(bodyHead.fn.name) && n.get(bodyHead.fn.name)!.kind === 'infix';
        const bodyStr = needsParens ? `(${body})` : body;
        return `\\lim_{${renderVarName(varName)} \\to ${x0}} ${bodyStr} = ${lVal}`;
      }
      // Named function: render as f(x) = L
      const fStr = termToLatex(f, ctx, n);
      return `\\lim_{x \\to ${x0}} ${fStr}(x) = ${lVal}`;
    }
    return '\\text{Limit}';
  }});
  // Limit.eps_delta — record projection: R, f, x0, L (4 params), then instance, eps, epsProof
  // Use function name as subscript (εδ_f) so the reader knows which limit is being applied.
  // Suppress epsProof (positivity argument) — a mathematician leaves this implicit.
  table.set('Limit.eps_delta', { kind: 'custom', arity: 7, render: (args, ctx, n) => {
    if (args.length >= 7) {
      const fRendered = termToLatex(args[1], ctx, n);
      const epsArg = termToLatex(args[5], ctx, n);
      // Use function name as subscript when short (simple variable)
      if (fRendered.length <= 3) {
        return `\\varepsilon\\delta_{${fRendered}}(${epsArg})`;
      }
      // Complex function: fall back to showing the instance name
      const limitProof = termToLatex(args[4], ctx, n);
      return `${limitProof}.\\varepsilon\\delta(${epsArg})`;
    }
    if (args.length >= 5) {
      return `${termToLatex(args[4], ctx, n)}.\\varepsilon\\delta`;
    }
    return '\\text{eps\\_delta}';
  }});
  // MkLimit — record constructor: R, f, x0, L (4 params), then eps_delta field
  table.set('MkLimit', { kind: 'custom', render: (args, ctx, n) => {
    // Skip params, just show it as a proof construction
    if (args.length >= 5) {
      return `\\langle ${termToLatex(args[4], ctx, n)} \\rangle`;
    }
    return '\\langle \\ldots \\rangle';
  }});

  // EpsDeltaWitness R f x0 L eps delta
  // = Pair (0 < delta) (∀x, |x - x0| < delta → |f(x) - L| < eps)
  table.set('EpsDeltaWitness', { kind: 'custom', render: (args, ctx, n) => {
    // Full 6-arg form: render the actual math
    if (args.length >= 6) {
      const f = args[1];
      const x0Str = termToLatex(args[2], ctx, n);
      const LStr = termToLatex(args[3], ctx, n);
      const epsStr = termToLatex(args[4], ctx, n);
      const deltaStr = termToLatex(args[5], ctx, n);
      // Render f(x) by applying function to fresh variable
      const fxStr = renderSummand(f, 'x', ctx, n);
      // Wrap RHS in parens if compound (contains + or -) to avoid ambiguity: |a - (b + c)|
      // LHS doesn't need wrapping since subtraction is left-associative: |a + b - X| = |(a + b) - X|
      const fxWrap = fxStr;
      const LWrap = (LStr.includes('+') || LStr.includes('-')) ? `(${LStr})` : LStr;
      return `0 < ${deltaStr} \\text{ and } \\forall x,\\, 0 < \\left|x - ${x0Str}\\right| < ${deltaStr} \\implies \\left|${fxWrap} - ${LWrap}\\right| < ${epsStr}`;
    }
    // 5 args — partial application (no delta yet)
    if (args.length >= 5) {
      const visible = args.slice(1); // skip R
      const argsStr = visible.map(a => termToLatex(a, ctx, n)).join(',\\, ');
      return `\\text{Witness}(${argsStr})`;
    }
    return '\\text{Witness}';
  }});

  // ---- CompleteOrderedField projections ----
  // All take (A : Type) and (inst : CompleteOrderedField A) as first 2 args — skip them.
  // Operations: render with math symbols
  table.set('CompleteOrderedField.add', { kind: 'infix', latex: '+', arity: 4, skipArgs: [0, 1] });
  table.set('CompleteOrderedField.mul', { kind: 'infix', latex: '\\cdot', arity: 4, skipArgs: [0, 1] });
  table.set('CompleteOrderedField.zero', { kind: 'prefix', latex: '0', arity: 2, skipArgs: [0, 1] });
  table.set('CompleteOrderedField.one', { kind: 'prefix', latex: '1', arity: 2, skipArgs: [0, 1] });
  table.set('CompleteOrderedField.neg', { kind: 'prefix', latex: '-', arity: 3, skipArgs: [0, 1] });
  table.set('CompleteOrderedField.le', { kind: 'infix', latex: '\\le', arity: 4, skipArgs: [0, 1] });
  table.set('CompleteOrderedField.inv', { kind: 'custom', render: (args, ctx, n) => {
    if (args.length >= 3) {
      const x = termToLatex(args[2], ctx, n);
      if (x.includes('+') || x.includes('-') || x.includes('\\cdot')) {
        return `(${x})^{-1}`;
      }
      return `${x}^{-1}`;
    }
    return '\\text{inv}';
  }});
  // Proof projections: skip 2 params, render as \text{name}(visible_args...)
  const proofProjections = [
    'addAssoc', 'addComm', 'addZeroRight', 'negRight',
    'mulAssoc', 'mulOneLeft', 'mulOneRight', 'mulComm',
    'distribLeft', 'distribRight',
    'leRefl', 'leAntisym', 'leTrans', 'leTotal',
    'addLeLeft', 'mulNonneg',
    'zeroLeOne', 'zeroNeOne', 'invPos', 'mulInvRight',
    'supUpperBound', 'supLeast',
  ];
  for (const fieldName of proofProjections) {
    table.set(`CompleteOrderedField.${fieldName}`, { kind: 'custom', render: (args, ctx, n) => {
      const visible = args.slice(2);
      if (visible.length === 0) return `\\text{${fieldName}}`;
      const argsStr = visible.map(a => termToLatex(a, ctx, n)).join(',\\, ');
      return `\\text{${fieldName}}(${argsStr})`;
    }});
  }

  // ---- Other record projections with same pattern (skip 2 params) ----
  // For records in the hierarchy: AbelianGroup, Ring, Field, OrderedField
  const recordHierarchy = [
    'AbelianGroup', 'Ring', 'CommRing', 'Field', 'OrderedField',
  ];
  for (const recName of recordHierarchy) {
    // Register the same operations for each ancestor record
    table.set(`${recName}.add`, { kind: 'infix', latex: '+', arity: 4, skipArgs: [0, 1] });
    table.set(`${recName}.mul`, { kind: 'infix', latex: '\\cdot', arity: 4, skipArgs: [0, 1] });
    table.set(`${recName}.zero`, { kind: 'prefix', latex: '0', arity: 2, skipArgs: [0, 1] });
    table.set(`${recName}.one`, { kind: 'prefix', latex: '1', arity: 2, skipArgs: [0, 1] });
    table.set(`${recName}.neg`, { kind: 'prefix', latex: '-', arity: 3, skipArgs: [0, 1] });
    table.set(`${recName}.le`, { kind: 'infix', latex: '\\le', arity: 4, skipArgs: [0, 1] });
  }

  return table;
}

// ============================================================================
// Term-to-LaTeX Rendering (notation-aware)
// ============================================================================

/**
 * Try to match Succ(Succ(...(Zero))) and return the numeric value.
 */
function matchNatLiteral(term: TTKTerm): number | null {
  let n = 0;
  let current = term;
  while (current.tag === 'App') {
    if (current.fn.tag === 'Const' && current.fn.name === 'Succ') {
      n++;
      current = current.arg;
    } else {
      return null;
    }
  }
  if (current.tag === 'Const' && current.name === 'Zero') {
    return n;
  }
  return null;
}

/**
 * Convert a kernel term to a LaTeX string with notation support.
 */
export function termToLatex(
  term: TTKTerm,
  context: string[],
  notations: NotationTable,
): string {
  // Try numeric literal first
  const natLit = matchNatLiteral(term);
  if (natLit !== null) return `${natLit}`;

  // Try notation-aware App spine matching
  if (term.tag === 'App' || term.tag === 'Const') {
    const spine = extractAppSpine(term);
    if (spine.fn.tag === 'Const') {
      const entry = notations.get(spine.fn.name);
      if (entry) {
        return renderNotation(entry, spine.fn.name, spine.args, context, notations);
      }
    }
  }

  // Structural rendering
  switch (term.tag) {
    case 'Var':
      if (term.index < context.length) {
        return renderVarName(context[term.index]);
      }
      return `\\#${term.index}`;

    case 'Sort': {
      if (term.level.tag === 'ULit' && term.level.n === 0) {
        return '\\text{Prop}';
      }
      if (term.level.tag === 'ULit') {
        const n = term.level.n - 1;
        return n === 0 ? '\\text{Type}' : `\\text{Type}_{${n}}`;
      }
      // USucc pattern
      if (term.level.tag === 'App' && term.level.fn.tag === 'Const' && term.level.fn.name === 'USucc') {
        const inner = termToLatex(term.level.arg, context, notations);
        return `\\text{Type}_{${inner}}`;
      }
      return `\\text{Sort}\\;${termToLatex(term.level, context, notations)}`;
    }

    case 'ULit':
      return `${term.n}`;

    case 'UOmega':
      return '\\omega';

    case 'ULevel':
      return '\\text{Level}';

    case 'Const': {
      const entry = notations.get(term.name);
      if (entry && entry.kind === 'const') {
        return entry.latex;
      }
      return `\\text{${escapeLaTeX(term.name)}}`;
    }

    case 'Binder': {
      // For Lambda/Pi with carrier domain, skip the binder and render body with substitution
      const carrierLatex = isCarrierType(term.domain);
      if (carrierLatex && (term.binderKind.tag === 'BLam' || term.binderKind.tag === 'BPi')) {
        const carrierCtx = [LATEX_PREFIX + carrierLatex, ...context];
        const body = termToLatex(term.body, carrierCtx, notations);
        return body;
      }

      const domain = termToLatex(term.domain, context, notations);
      const newCtx = [term.name, ...context];
      const body = termToLatex(term.body, newCtx, notations);
      const isAnon = term.name === '_' || term.name === '';
      const nameStr = renderVarName(term.name);

      switch (term.binderKind.tag) {
        case 'BPi':
          if (isAnon || !occursIn(0, term.body)) {
            // Equal X Y -> Void  →  X ≠ Y
            if (term.body.tag === 'Const' && term.body.name === 'Void') {
              const eqSpine = extractAppSpine(term.domain);
              if (eqSpine.fn.tag === 'Const' && eqSpine.fn.name === 'Equal' && eqSpine.args.length >= 3) {
                const x = termToLatex(eqSpine.args[1], context, notations);
                const y = termToLatex(eqSpine.args[2], context, notations);
                return `${x} \\neq ${y}`;
              }
            }
            // Use ⟹ for propositional implications, → for function types
            if (looksLikeProp(term.domain, 0) && looksLikeProp(term.body, 0)) {
              return `${domain} \\implies ${body}`;
            }
            return `${domain} \\to ${body}`;
          }
          // Use ∀ for propositional bodies, Π otherwise
          if (looksLikeProp(term.body, 1)) {
            const isCS = CARRIER_LATEX_VALUES.has(domain);
            const sep = isCS ? ' \\in ' : ' : ';
            return `\\forall ${nameStr}${sep}${domain},\\, ${body}`;
          }
          return `\\Pi\\, (${nameStr} : ${domain}),\\, ${body}`;

        case 'BLam':
          if (isAnon) {
            return `\\lambda\\, \\_ .\\, ${body}`;
          }
          return `${nameStr} \\mapsto ${body}`;

        case 'BLet': {
          const defVal = termToLatex(term.binderKind.defVal, context, notations);
          return `\\text{let } ${nameStr} := ${defVal} \\text{ in } ${body}`;
        }
      }
      break; // unreachable but satisfies TS
    }

    case 'App': {
      // Render as f(a, b, c) math-style, filtering out carrier variables
      const spine = extractAppSpine(term);
      const fnStr = termToLatex(spine.fn, context, notations);
      const visibleArgs = spine.args.filter(a =>
        !(a.tag === 'Var' && a.index < context.length && isCarrierEntry(context[a.index]))
      );
      if (visibleArgs.length === 0) return fnStr;
      const argsStr = visibleArgs.map(a => termToLatex(a, context, notations)).join(',\\, ');
      return `${fnStr}(${argsStr})`;
    }

    case 'Hole':
      return '?';

    case 'Meta':
      return '?';

    case 'Annot':
      return `(${termToLatex(term.term, context, notations)} : ${termToLatex(term.type, context, notations)})`;

    case 'Match': {
      const scrutinee = term.scrutinee.tag === 'Hole' && term.scrutinee.id === '_scrutinee'
        ? '\\_'
        : termToLatex(term.scrutinee, context, notations);
      const clauses = term.clauses.map(c => {
        const patVars = collectPatternVars(c.patterns);
        const clauseCtx = [...patVars.reverse(), ...context];
        const lhs = c.elabArgs
          ? c.elabArgs.map(a => termToLatex(a, clauseCtx, notations)).join('\\;')
          : c.patterns.map(p => patternToLatex(p, notations)).join('\\;');
        const rhs = termToLatex(c.rhs, clauseCtx, notations);
        return `${lhs} \\Rightarrow ${rhs}`;
      }).join(' \\mid ');
      return `\\text{match}\\; ${scrutinee}\\; \\{\\, ${clauses} \\,\\}`;
    }
  }

  return '?'; // fallback
}

/**
 * Check if a term is an "effective variable reference" — renders as just a name
 * in describeJustification (no function call syntax). This includes:
 * 1. Plain Var (non-carrier)
 * 2. Var applied to args that are all Vars/carrier-filtered (Var-function suppression)
 */
function isEffectiveVarRef(term: TTKTerm, context: string[]): boolean {
  if (term.tag === 'Var' && term.index < context.length && !isCarrierEntry(context[term.index])) {
    return true;
  }
  if (term.tag !== 'App') return false;
  const spine = extractAppSpine(term);
  if (spine.fn.tag !== 'Var' || spine.fn.index >= context.length) return false;
  if (isCarrierEntry(context[spine.fn.index])) return false;
  const visibleArgs = spine.args.filter(a =>
    a.tag !== 'Meta' && a.tag !== 'Hole' && a.tag !== 'Sort' &&
    !(a.tag === 'Var' && a.index < context.length && isCarrierEntry(context[a.index]))
  );
  return visibleArgs.length === 0 || visibleArgs.every(a => a.tag === 'Var');
}

/**
 * Strip DPair/Pair projections from a term, returning the base expression
 * and the chain of projections applied. E.g.:
 *   Pair.fst(DPair.snd(X)) → { base: X, projections: ['dsnd', 'pfst'] }
 *   DPair.fst(X) → { base: X, projections: ['dfst'] }
 */
function stripProjections(term: TTKTerm): { base: TTKTerm, projections: string[] } {
  const projections: string[] = [];
  let current = term;
  for (;;) {
    const spine = extractAppSpine(current);
    if (spine.fn.tag !== 'Const') break;
    if (spine.fn.name === 'DPair.fst' && spine.args.length >= 5) {
      projections.unshift('dfst');
      current = spine.args[4];
    } else if (spine.fn.name === 'DPair.snd' && spine.args.length >= 5) {
      projections.unshift('dsnd');
      current = spine.args[4];
    } else if (spine.fn.name === 'Pair.fst' && spine.args.length >= 3) {
      projections.unshift('pfst');
      current = spine.args[2];
    } else if (spine.fn.name === 'Pair.snd' && spine.args.length >= 3) {
      projections.unshift('psnd');
      current = spine.args[2];
    } else {
      break;
    }
  }
  return { base: current, projections };
}

/** Structural key for a term — used for grouping without any display suppression. */
function termStructuralKey(term: TTKTerm): string {
  switch (term.tag) {
    case 'Var': return `V${term.index}`;
    case 'Const': return `C:${term.name}`;
    case 'App': return `(${termStructuralKey(term.fn)} ${termStructuralKey(term.arg)})`;
    case 'Sort': return 'S';
    case 'Binder': return `B(${termStructuralKey(term.domain)},${termStructuralKey(term.body)})`;
    case 'Meta': return `M${term.id}`;
    case 'Hole': return `H${term.id}`;
    default: return '?';
  }
}

/**
 * Detect DPair/Pair destructuring patterns in function application args.
 * When the same base expression X appears as:
 *   DPair.fst(X), Pair.fst(DPair.snd(X)), Pair.snd(DPair.snd(X))
 * introduce "Let (δ, h, bound) = X" and replace projection args with short names.
 *
 * Returns null if no pattern found.
 */
function detectDestructuringLets(
  args: TTKTerm[],
  context: string[],
  notations: NotationTable,
  fnName: string,
): { lets: string[], mainExpr: string } | null {
  // 1. Strip projections from each arg and group by base (structural equality)
  const argInfos = args.map(arg => {
    const result = stripProjections(arg);
    return {
      projections: result.projections,
      base: result.projections.length > 0 ? result.base : null,
      baseKey: result.projections.length > 0
        ? termStructuralKey(result.base)
        : '',
    };
  });

  const groups = new Map<string, { base: TTKTerm, argIndices: number[] }>();
  for (let i = 0; i < argInfos.length; i++) {
    const info = argInfos[i];
    if (!info.base) continue;
    if (!groups.has(info.baseKey)) {
      groups.set(info.baseKey, { base: info.base, argIndices: [] });
    }
    groups.get(info.baseKey)!.argIndices.push(i);
  }

  // Only extract bases with 2+ projection usages
  const extractable = [...groups.values()].filter(g => g.argIndices.length >= 2);
  if (extractable.length === 0) return null;

  // 2. Generate let-bindings and track replacements
  const lets: string[] = [];
  const replacements = new Map<number, string>(); // argIdx → replacement LaTeX
  // Track string replacements for nested occurrences (e.g., π₁(X) inside leTotal)
  const stringReplacements: [string, string][] = [];

  for (let gi = 0; gi < extractable.length; gi++) {
    const group = extractable[gi];
    const sub = extractable.length > 1 ? `_{${gi + 1}}` : '';
    // Use termToLatex for the let RHS — keeps record dot notation (limF.εδ(...))
    // where describeJustification would suppress the instance as a var-ref
    const baseLatex = termToLatex(group.base, context, notations);

    // Collect projection names used for this base
    const projNames = new Map<string, string>(); // projKey → LaTeX name
    for (const idx of group.argIndices) {
      const projs = argInfos[idx].projections;
      const projKey = projs.join('.');

      if (!projNames.has(projKey)) {
        if (projKey === 'dfst') {
          projNames.set(projKey, `\\delta${sub}`);
        } else if (projKey === 'dsnd.pfst') {
          projNames.set(projKey, `h${sub}`);
        } else if (projKey === 'dsnd.psnd') {
          projNames.set(projKey, `\\text{bnd}${sub}`);
        } else if (projKey === 'pfst') {
          projNames.set(projKey, `\\pi_1${sub}`);
        } else if (projKey === 'psnd') {
          projNames.set(projKey, `\\pi_2${sub}`);
        } else {
          // Unknown projection chain — skip this group
          continue;
        }
      }
      replacements.set(idx, projNames.get(projKey)!);
    }

    if (projNames.size === 0) continue;

    // Build string replacements for nested occurrences in other args
    // e.g., leTotal(π₁(baseLatex), ...) → leTotal(δ₁, ...)
    for (const [projKey, name] of projNames) {
      let pattern: string | undefined;
      if (projKey === 'dfst') {
        pattern = `\\pi_1(${baseLatex})`;
      } else if (projKey === 'dsnd.pfst') {
        pattern = `\\pi_1(\\pi_2(${baseLatex}))`;
      } else if (projKey === 'dsnd.psnd') {
        pattern = `\\pi_2(\\pi_2(${baseLatex}))`;
      } else if (projKey === 'pfst') {
        pattern = `\\pi_1(${baseLatex})`;
      } else if (projKey === 'psnd') {
        pattern = `\\pi_2(${baseLatex})`;
      }
      if (pattern) stringReplacements.push([pattern, name]);
    }

    // Sort projection names in canonical order: dfst, dsnd.pfst, dsnd.psnd
    const order = ['dfst', 'dsnd.pfst', 'dsnd.psnd', 'pfst', 'psnd'];
    const sortedNames = [...projNames.entries()]
      .sort(([a], [b]) => order.indexOf(a) - order.indexOf(b))
      .map(([_, name]) => name);

    lets.push(`\\text{Let } (${sortedNames.join(',\\, ')}) = ${baseLatex}`);
  }

  if (lets.length === 0 || replacements.size === 0) return null;

  // 3. Render the main expression with replacements
  // Apply same filtering as describeJustification (carrier, type, var-ref suppression)
  const visibleArgStrs: string[] = [];
  for (let i = 0; i < args.length; i++) {
    const arg = args[i];
    // Skip implicit-like args (same heuristic as describeJustification)
    if (arg.tag === 'Meta' || arg.tag === 'Hole' || arg.tag === 'Sort') continue;
    if (arg.tag === 'Var' && arg.index < context.length && isCarrierEntry(context[arg.index])) continue;
    if (arg.tag === 'Const' && notations.get(arg.name)?.kind === 'const' &&
        ['\\mathbb{N}', '\\text{Type}', '\\mathbb{R}'].includes((notations.get(arg.name) as any)?.latex)) continue;

    if (replacements.has(i)) {
      visibleArgStrs.push(replacements.get(i)!);
    } else if (isEffectiveVarRef(arg, context)) {
      continue; // Skip var refs
    } else {
      visibleArgStrs.push(describeJustification(arg, context, notations));
    }
  }

  // 4. Apply string replacements for nested projection references
  // Sort longest first to avoid partial matches
  stringReplacements.sort((a, b) => b[0].length - a[0].length);
  const fnLatex = `\\text{${escapeLaTeX(fnName)}}`;
  const displayArgs = visibleArgStrs.slice(0, 8);
  let mainExpr = displayArgs.length > 0
    ? `${fnLatex}(${displayArgs.join(',\\, ')})`
    : fnLatex;

  for (const [from, to] of stringReplacements) {
    mainExpr = mainExpr.split(from).join(to);
  }

  return { lets, mainExpr };
}

/**
 * Recursively walk a term tree collecting DPair/Pair projection bases.
 * Each base is grouped by structural key, with the set of projection chains found.
 * Does NOT recurse into lambda/let bodies (shifted de Bruijn indices would cause
 * false mismatches), but string replacement catches those occurrences anyway since
 * the rendered LaTeX for the base is identical regardless of depth.
 */
function collectProjectionBasesFromTerm(
  term: TTKTerm,
  result: Map<string, { base: TTKTerm, projections: Map<string, TTKTerm> }>,
): void {
  // Try stripping projections from this term
  const stripped = stripProjections(term);
  if (stripped.projections.length > 0) {
    const key = termStructuralKey(stripped.base);
    if (!result.has(key)) {
      result.set(key, { base: stripped.base, projections: new Map() });
    }
    const projKey = stripped.projections.join('.');
    if (!result.get(key)!.projections.has(projKey)) {
      result.get(key)!.projections.set(projKey, term);
    }
    // Don't recurse further — the base is the important part, and it may
    // contain nested projections that stripProjections already handles
    return;
  }

  // Not a projection — recurse into subterms (but not into binder bodies)
  switch (term.tag) {
    case 'App':
      collectProjectionBasesFromTerm(term.fn, result);
      collectProjectionBasesFromTerm(term.arg, result);
      break;
    case 'Binder':
      collectProjectionBasesFromTerm(term.domain, result);
      // Skip body: lambda/let bodies have shifted indices
      break;
    case 'Match':
      collectProjectionBasesFromTerm(term.scrutinee, result);
      // Skip clause bodies: shifted indices
      break;
  }
}

/**
 * Check if a term is a "value computation" — an expression computing a value
 * (not a proof). In proof rendering, these are typically obvious from the theorem
 * statement and should be suppressed for readability.
 * E.g., |f(x)+g(x)-(L+M)| or (a+c) in proof of a+c ≤ b+d.
 */
function isValueTerm(term: TTKTerm, notations: NotationTable): boolean {
  const spine = extractAppSpine(term);
  if (spine.fn.tag !== 'Const') return false;
  const name = spine.fn.name;
  // Known value-producing operations
  if (['radd', 'rsub', 'rmul', 'rneg', 'rabs', 'rinv', 'rhalf',
       'rzero', 'rone', 'rtwo', 'Carrier'].includes(name)) return true;
  // Infix notation entries produce values
  const entry = notations.get(name);
  if (entry && entry.kind === 'infix') return true;
  // COF value projections
  if (name.startsWith('CompleteOrderedField.') &&
      ['add', 'mul', 'neg', 'zero', 'one', 'inv', 'sub'].some(
        op => name.endsWith('.' + op))) return true;
  return false;
}

/** Check if a term would render as an infix expression (needs parens if nested). */
function isInfixTerm(term: TTKTerm, notations: NotationTable): boolean {
  if (term.tag !== 'App') return false;
  const spine = extractAppSpine(term);
  if (spine.fn.tag !== 'Const') return false;
  const entry = notations.get(spine.fn.name);
  return entry?.kind === 'infix';
}

/** Get the infix operator LaTeX string for a term, or null if not infix. */
function getInfixOp(term: TTKTerm, notations: NotationTable): string | null {
  if (term.tag !== 'App') return null;
  const spine = extractAppSpine(term);
  if (spine.fn.tag !== 'Const') return null;
  const entry = notations.get(spine.fn.name);
  if (entry?.kind !== 'infix') return null;
  return entry.latex;
}

/** Check if a term is a + infix that renders as subtraction (add+neg pattern). */
function rendersAsSub(term: TTKTerm, notations: NotationTable): boolean {
  if (getInfixOp(term, notations) !== '+') return false;
  const spine = extractAppSpine(term);
  if (spine.fn.tag !== 'Const') return false;
  const entry = notations.get(spine.fn.name);
  if (!entry || entry.kind !== 'infix') return false;
  const visible = spine.args.filter((_, i) => !entry.skipArgs.includes(i));
  return visible.length >= 2 && isNegation(visible[1], notations) !== null;
}

/**
 * Check if a term is a negation application. Returns the inner (negated) term, or null.
 * Recognizes rneg, CompleteOrderedField.neg, and *.neg prefix entries.
 */
function isNegation(term: TTKTerm, notations: NotationTable): TTKTerm | null {
  const spine = extractAppSpine(term);
  if (spine.fn.tag !== 'Const') return null;
  const entry = notations.get(spine.fn.name);
  if (!entry || entry.kind !== 'prefix' || entry.latex !== '-') return null;
  if (spine.args.length < entry.arity) return null;
  const visible = spine.args.filter((_, i) => !entry.skipArgs.includes(i));
  if (visible.length === 1) return visible[0];
  return null;
}

function renderNotation(
  entry: NotationEntry,
  name: string,
  args: TTKTerm[],
  context: string[],
  notations: NotationTable,
): string {
  switch (entry.kind) {
    case 'const':
      // Shouldn't have args for a 0-arity const, but if it does, render them
      if (args.length > 0) {
        const argsStr = args.map(a => termToLatex(a, context, notations)).join('\\;');
        return `${entry.latex}\\;${argsStr}`;
      }
      return entry.latex;

    case 'prefix': {
      if (args.length >= entry.arity) {
        const visible = args.filter((_, i) => !entry.skipArgs.includes(i));
        const extra = args.slice(entry.arity);
        let result: string;
        if (visible.length === 0) {
          // All args skipped (e.g., rzero(R), rone(R)) — just show the symbol
          result = entry.latex;
        } else if (visible.length === 1 && /^[^a-zA-Z\\]+$/.test(entry.latex) &&
                   !isInfixTerm(visible[0], notations)) {
          // Operator prefix (e.g., -) with non-infix arg: render without parens
          // -a, -f(x), -|x| instead of -(a), -(f(x)), -(|x|)
          // But keep parens for infix: -(a + b) not -a + b
          const inner = termToLatex(visible[0], context, notations);
          result = `${entry.latex}${inner}`;
        } else {
          const inner = visible.map(a => termToLatex(a, context, notations)).join(',\\,');
          result = `${entry.latex}(${inner})`;
        }
        if (extra.length > 0) {
          result += '\\;' + extra.map(a => termToLatex(a, context, notations)).join('\\;');
        }
        return result;
      }
      // Partial application
      return `\\text{${escapeLaTeX(name)}}`;
    }

    case 'infix': {
      const visible = args.filter((_, i) => !entry.skipArgs.includes(i));
      if (visible.length >= 2) {
        const lhs = termToLatex(visible[0], context, notations);
        // Detect a + neg(b) → a - b
        if (entry.latex === '+') {
          const negInner = isNegation(visible[1], notations);
          if (negInner) {
            const needsWrap = isInfixTerm(negInner, notations);
            const rhs = termToLatex(negInner, context, notations);
            const extra = visible.slice(2);
            let result = needsWrap ? `${lhs} - (${rhs})` : `${lhs} - ${rhs}`;
            if (extra.length > 0) {
              result += '\\;' + extra.map(a => termToLatex(a, context, notations)).join('\\;');
            }
            return result;
          }
        }
        const rhs = termToLatex(visible[1], context, notations);
        // Operator precedence: wrap operands to avoid ambiguity
        const lhsOp = getInfixOp(visible[0], notations);
        const rhsOp = getInfixOp(visible[1], notations);
        const isMultiplicative = entry.latex === '\\cdot' || entry.latex === '\\times';
        const isAdditive = (op: string | null) =>
          op === '+' || op === '-' || rendersAsSub(visible[1], notations);
        const rendersAsSubLhs = rendersAsSub(visible[0], notations);
        // Rules:
        // - Subtraction/division: wrap any infix RHS
        // - Addition: wrap subtraction RHS (structural or add+neg)
        // - Multiplication: wrap additive LHS and RHS
        const wrapLhs =
          isMultiplicative && (lhsOp === '+' || lhsOp === '-' || rendersAsSubLhs);
        const wrapRhs =
          ((entry.latex === '-' || entry.latex === '/') && isInfixTerm(visible[1], notations)) ||
          (entry.latex === '+' && (rhsOp === '-' || rendersAsSub(visible[1], notations))) ||
          (isMultiplicative && (rhsOp === '+' || rhsOp === '-' || rendersAsSub(visible[1], notations)));
        const extra = visible.slice(2);
        const lhsFinal = wrapLhs ? `(${lhs})` : lhs;
        let result = wrapRhs ? `${lhsFinal} ${entry.latex} (${rhs})` : `${lhsFinal} ${entry.latex} ${rhs}`;
        if (extra.length > 0) {
          result += '\\;' + extra.map(a => termToLatex(a, context, notations)).join('\\;');
        }
        return result;
      }
      if (visible.length === 1) {
        // Partial application: (x +)
        return `(${termToLatex(visible[0], context, notations)} ${entry.latex} \\cdot)`;
      }
      return `(${entry.latex})`;
    }

    case 'custom': {
      const renderArgs = entry.arity !== undefined ? args.slice(0, entry.arity) : args;
      const result = entry.render(renderArgs, context, notations);
      if (entry.arity !== undefined && args.length > entry.arity) {
        const overflow = args.slice(entry.arity).filter(a =>
          !(a.tag === 'Var' && a.index < context.length && isCarrierEntry(context[a.index])) &&
          a.tag !== 'Meta' && a.tag !== 'Hole' && a.tag !== 'Sort'
        );
        if (overflow.length > 0) {
          const overflowStr = overflow.map(a => termToLatex(a, context, notations)).join(',\\, ');
          return `${result}(${overflowStr})`;
        }
      }
      return result;
    }
  }
}

// ============================================================================
// Pattern Rendering
// ============================================================================

function patternToLatex(pattern: TTKPattern, notations: NotationTable): string {
  switch (pattern.tag) {
    case 'PVar':
      return renderVarName(pattern.name);
    case 'PWild':
      return '\\_';
    case 'PCtor': {
      const entry = notations.get(pattern.name);
      const ctorName = entry && entry.kind === 'const' ? entry.latex : `\\text{${escapeLaTeX(pattern.name)}}`;
      // Suppress trivial args (wildcards and _-named vars — implicit type/value args)
      const visibleArgs = pattern.args.filter(p =>
        !(p.tag === 'PWild') && !(p.tag === 'PVar' && p.name === '_')
      );
      if (visibleArgs.length === 0) return ctorName;
      const args = visibleArgs.map(p => patternToLatex(p, notations)).join('\\;');
      return `${ctorName}\\;${args}`;
    }
  }
}

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
// Type Rendering (for theorem statements, using ∀ for propositions)
// ============================================================================

/**
 * Render a Pi type as a theorem statement: ∀ n m : N, ...
 * Groups consecutive binders with the same type.
 */
// ---- Binder grouping helpers (shared by typeToLatex and convertTheorem) ----

interface BinderGroup {
  names: string[];
  typeLatex: string;
  isCarrierSet: boolean;
}

/** Collect carrier latex values for detecting ∈-style binders. */
const CARRIER_LATEX_VALUES = new Set(Object.values(CARRIER_TYPES));

/**
 * Group consecutive Pi binders by rendered type, suppressing carrier types.
 * Returns the groups and the final rendering context.
 */
function buildBinderGroups(
  binders: Array<{ name: string; type: TTKTerm }>,
  context: string[],
  notations: NotationTable,
): { groups: BinderGroup[]; finalCtx: string[] } {
  const groups: BinderGroup[] = [];
  let ctx = [...context];

  for (const b of binders) {
    const cl = isCarrierType(b.type);
    if (cl) {
      ctx = [LATEX_PREFIX + cl, ...ctx];
      continue;
    }
    const typeLatex = termToLatex(b.type, ctx, notations);
    const isCarrierSet = CARRIER_LATEX_VALUES.has(typeLatex);
    ctx = [b.name, ...ctx];
    const last = groups[groups.length - 1];
    if (last && last.typeLatex === typeLatex) {
      last.names.push(b.name);
    } else {
      groups.push({ names: [b.name], typeLatex, isCarrierSet });
    }
  }

  return { groups, finalCtx: ctx };
}

/**
 * Format a binder group as LaTeX: "x, y : T" or "x, y ∈ ℝ" or just "T" for anon.
 */
function formatBinderGroup(g: BinderGroup): string {
  if (g.names.every(n => n === '_')) return g.typeLatex;
  const names = g.names.map(renderVarName).join(',\\, ');
  const sep = g.isCarrierSet ? ' \\in ' : ' : ';
  return `${names}${sep}${g.typeLatex}`;
}

// ---- typeToLatex ----

export function typeToLatex(term: TTKTerm, context: string[], notations: NotationTable): string {
  const { binders, body } = extractPiSpine(term);

  if (binders.length === 0) {
    return termToLatex(term, context, notations);
  }

  const isPropLike = looksLikeProp(body, binders.length);
  const { groups, finalCtx } = buildBinderGroups(binders, context, notations);
  const bodyLatex = termToLatex(body, finalCtx, notations);

  // If all binders were suppressed (all carrier types), just return the body
  if (groups.length === 0) {
    return bodyLatex;
  }

  if (isPropLike) {
    const binderParts = groups.map(formatBinderGroup);
    return `\\forall\\, ${binderParts.join(',\\; ')},\\; ${bodyLatex}`;
  } else {
    // Arrow style: N → N → N, but (a : N) → (f : N → N) → ... for named binders
    const parts: string[] = [];
    for (const g of groups) {
      if (g.names.every(n => n === '_')) {
        for (const _name of g.names) {
          parts.push(g.typeLatex);
        }
      } else {
        // Named binder group: show as (name : type)
        parts.push(`(${formatBinderGroup(g)})`);
      }
    }
    parts.push(bodyLatex);
    return parts.join(' \\to ');
  }
}

/**
 * Heuristic: does the body of a Pi look like a proposition?
 * Check for common propositional forms: Equal, Leq, Void, DPair, Limit, etc.
 */
function looksLikeProp(body: TTKTerm, depth: number): boolean {
  const spine = extractAppSpine(body);
  if (spine.fn.tag === 'Const') {
    const name = spine.fn.name;
    // Direct propositional types
    if (['Equal', 'Leq', 'LessThan', 'Void', 'DecEq', 'Limit'].includes(name)) return true;
    // DPair as existential (not sigma type): DPair(A, P) is propositional if A is not a Sort
    // (DPair Type COF is a sigma type = Real, not a proposition)
    if (name === 'DPair' && spine.args.length >= 2) {
      return spine.args[0].tag !== 'Sort';
    }
    // Our wrappers for relations
    if (['rle', 'rlt'].includes(name)) return true;
    // Record field projections that are relations (e.g. CompleteOrderedField.le)
    if (name.endsWith('.le') || name.endsWith('.lt')) return true;
    // User-defined propositional type names (e.g. EpsDeltaWitness)
    if (_knownPropNames.has(name)) return true;
    // Pair used as conjunction — if either component is prop-like
    if (name === 'Pair' && spine.args.length >= 2) {
      return looksLikeProp(spine.args[0], depth) || looksLikeProp(spine.args[1], depth);
    }
  }
  // If the body is a Pi that looks like a prop, propagate
  if (body.tag === 'Binder' && body.binderKind.tag === 'BPi') {
    return looksLikeProp(body.body, depth + 1);
  }
  return false;
}

// ============================================================================
// Proof Term Rendering
// ============================================================================

interface TransStep {
  lhs: TTKTerm;
  rhs: TTKTerm;
  justification: TTKTerm;
}

/**
 * Detect a chain of `trans` applications.
 * trans : {A} -> {x} -> {y} -> {z} -> Equal x y -> Equal y z -> Equal x z
 * Spine args: [A, x, y, z, proof_xy, proof_yz]
 * Flattens both sides: trans(trans(a,b), trans(c,d)) → [a, b, c, d]
 */
function detectTransChain(term: TTKTerm): TransStep[] | null {
  const spine = extractAppSpine(term);
  if (spine.fn.tag !== 'Const' || spine.fn.name !== 'trans') return null;
  if (spine.args.length < 6) return null;

  const [_A, x, y, z, proofXY, proofYZ] = spine.args;

  const result: TransStep[] = [];

  // Flatten left side (proofXY may itself be a trans chain)
  const leftSteps = detectTransChain(proofXY);
  if (leftSteps) {
    result.push(...leftSteps);
  } else {
    result.push({ lhs: x, rhs: y, justification: proofXY });
  }

  // Flatten right side (proofYZ may itself be a trans chain)
  const rightSteps = detectTransChain(proofYZ);
  if (rightSteps) {
    result.push(...rightSteps);
  } else {
    result.push({ lhs: y, rhs: z, justification: proofYZ });
  }

  return result;
}

/**
 * Detect `sym` application: sym : {A} -> {x} -> {y} -> Equal x y -> Equal y x
 * Spine args: [A, x, y, proof]
 */
function detectSym(term: TTKTerm): { inner: TTKTerm } | null {
  const spine = extractAppSpine(term);
  if (spine.fn.tag !== 'Const' || spine.fn.name !== 'sym') return null;
  if (spine.args.length < 4) return null;
  return { inner: spine.args[3] };
}

/**
 * Try to flatten a deeply nested single-proof-arg chain.
 * f(g(h(base))) where each function has exactly 1 non-suppressible arg
 * becomes a list of rendered steps in forward order (innermost first).
 * Returns null if the term is not a suitable chain (< 3 levels).
 */
function tryFlattenProofChain(
  term: TTKTerm,
  context: string[],
  notations: NotationTable,
): string | null {
  type ChainStep = { rendered: string; isConst: boolean };
  const steps: ChainStep[] = [];
  let current = term;
  let endedWithLeaf = false;

  const SPECIAL_NAMES = new Set([
    'refl', 'sym', 'cong', 'congSucc', 'congPlusRight', 'congPlusLeft',
    'replace', 'MkDPair', 'MkPair', 'MkLimit', 'eitherElim',
  ]);

  while (true) {
    const sp = extractAppSpine(current);

    // Handle Const function applications (Named lemma path)
    if (sp.fn.tag === 'Const') {
      const name = sp.fn.name;
      // Stop at special-cased names that have their own rendering
      if (SPECIAL_NAMES.has(name)) break;
      // Stop at accessor projections (Pair.fst/snd, DPair.fst/snd)
      const ACCESSOR_PROJECTIONS_CHAIN = new Set(['Pair.fst', 'Pair.snd', 'DPair.fst', 'DPair.snd']);
      if (ACCESSOR_PROJECTIONS_CHAIN.has(name)) break;

      // Determine visible args based on context
      let visibleArgs: TTKTerm[];
      const dotIdx = name.indexOf('.');
      const entry = notations.get(name);

      if (dotIdx > 0 && sp.args.length >= 2 && !ACCESSOR_PROJECTIONS_CHAIN.has(name)) {
        // Record projection: skip first 2 args (A, inst), filter rest
        visibleArgs = sp.args.slice(2).filter(a =>
          a.tag !== 'Meta' && a.tag !== 'Hole' && a.tag !== 'Sort'
        );
      } else if (entry && entry.kind === 'custom' && entry.arity !== undefined) {
        // Custom notation with arity: visible = args beyond skipped params
        visibleArgs = sp.args.filter(a =>
          a.tag !== 'Meta' && a.tag !== 'Hole' && a.tag !== 'Sort' &&
          !(a.tag === 'Var' && a.index < context.length && isCarrierEntry(context[a.index]))
        );
      } else if (entry) {
        break; // Other notation entries, let normal rendering handle them
      } else {
        // Named lemma: filter out implicit/carrier args
        visibleArgs = sp.args.filter(a =>
          a.tag !== 'Meta' && a.tag !== 'Hole' && a.tag !== 'Sort' &&
          !(a.tag === 'Var' && a.index < context.length && isCarrierEntry(context[a.index])) &&
          !(a.tag === 'Const' && notations.get(a.name)?.kind === 'const' &&
            ['\\mathbb{N}', '\\text{Type}', '\\mathbb{R}'].includes((notations.get(a.name) as any)?.latex))
        );
      }

      const isSup = (a: TTKTerm) => isEffectiveVarRef(a, context) || isValueTerm(a, notations);
      const meaningful = visibleArgs.filter(a => !isSup(a));

      // Compute display name
      const displayName = dotIdx > 0
        ? `\\text{${escapeLaTeX(name.substring(dotIdx + 1))}}`
        : `\\text{${escapeLaTeX(name)}}`;

      if (meaningful.length === 0) {
        // Leaf: no proof args
        steps.push({ rendered: displayName, isConst: true });
        endedWithLeaf = true;
        break;
      }
      if (meaningful.length === 1) {
        // Single proof arg: extend chain
        steps.push({ rendered: displayName, isConst: true });
        current = meaningful[0];
        continue;
      }
      break; // Multiple proof args, can't flatten
    }

    // Handle Var-function applications (hypothesis applied as function)
    if (sp.fn.tag === 'Var' && sp.fn.index < context.length && sp.args.length > 0) {
      const fnName = context[sp.fn.index];
      if (!isCarrierEntry(fnName)) {
        const fnLatex = isHypothesisName(fnName)
          ? '\\text{assumption}'
          : renderVarName(fnName);
        const visibleArgs = sp.args.filter(a =>
          a.tag !== 'Meta' && a.tag !== 'Hole' && a.tag !== 'Sort' &&
          !(a.tag === 'Var' && a.index < context.length && isCarrierEntry(context[a.index]))
        );
        const isSup = (a: TTKTerm) => isEffectiveVarRef(a, context) || isValueTerm(a, notations);
        const meaningful = visibleArgs.filter(a => !isSup(a));

        if (meaningful.length === 0) {
          steps.push({ rendered: fnLatex, isConst: false });
          endedWithLeaf = true;
          break;
        }
        if (meaningful.length === 1) {
          steps.push({ rendered: fnLatex, isConst: false });
          current = meaningful[0];
          continue;
        }
      }
      break;
    }

    break; // Can't flatten further
  }

  // Need at least 2 outer steps for chain flattening to be worthwhile
  // (2 steps + base = 3 segments, e.g., "base ; step1 ; step2")
  // Exception: 1 Const step with a complex base is still worth flattening
  // e.g., convertEps(coreEstimate(a, b)) → coreEstimate(a, b) ; convertEps
  if (steps.length < 2) {
    if (steps.length === 1 && !endedWithLeaf && steps[0].isConst) {
      const baseRendered = describeJustification(current, context, notations);
      if (baseRendered.length > 20) {
        return `${baseRendered}\\;;\\, ${steps[0].rendered}`;
      }
    }
    return null;
  }

  // Steps are collected outermost-first: [outer, middle, inner]
  // Reverse for forward order: [inner, middle, outer]
  const reversed = [...steps].reverse();

  // Check if we ended with a leaf (0 meaningful args → pushed to steps and broke)
  // vs breaking out with unprocessed `current` (special name, multi-arg, etc.)
  if (endedWithLeaf) {
    // All terms processed into steps — just join them
    return reversed.map(s => s.rendered).join('\\;;\\, ');
  } else {
    // `current` is an unprocessed base term — render it and prepend
    const baseRendered = describeJustification(current, context, notations);
    return [baseRendered, ...reversed.map(s => s.rendered)].join('\\;;\\, ');
  }
}

/**
 * Short description of a proof justification for equational chain annotations.
 * Tries to be concise: "refl", "sym(plusZeroRight(m))", "cong_S(IH)", etc.
 */
function describeJustification(term: TTKTerm, context: string[], notations: NotationTable): string {
  // Try chain flattening first: f(g(h(x))) → x ; h ; g ; f
  const chainResult = tryFlattenProofChain(term, context, notations);
  if (chainResult) return chainResult;

  // refl (with or without implicit args)
  const spine = extractAppSpine(term);
  if (spine.fn.tag === 'Const') {
    const name = spine.fn.name;

    if (name === 'refl') return '\\text{refl}';

    // sym(inner)
    if (name === 'sym' && spine.args.length >= 4) {
      const inner = describeJustification(spine.args[3], context, notations);
      return `\\text{sym}(${inner})`;
    }

    // congSucc: {n} {m} proof
    if (name === 'congSucc' && spine.args.length >= 3) {
      const inner = describeJustification(spine.args[2], context, notations);
      return `\\text{cong}_S(${inner})`;
    }

    // congPlusRight: {n} {m} (p : Nat) proof
    if (name === 'congPlusRight' && spine.args.length >= 4) {
      const p = termToLatex(spine.args[2], context, notations);
      const inner = describeJustification(spine.args[3], context, notations);
      return `\\text{cong}_{+R}(${p},\\, ${inner})`;
    }

    // congPlusLeft: {n} {m} (p : Nat) proof
    if (name === 'congPlusLeft' && spine.args.length >= 4) {
      const p = termToLatex(spine.args[2], context, notations);
      const inner = describeJustification(spine.args[3], context, notations);
      return `\\text{cong}_{+L}(${p},\\, ${inner})`;
    }

    // trans: {A} x y z proof_xy proof_yz — flatten nested trans chains
    // trans(a, trans(b, trans(c, d))) → a;\, b;\, c;\, d
    if (name === 'trans' && spine.args.length >= 6) {
      const steps: string[] = [];
      let cur: TTKTerm = term;
      while (true) {
        const sp = extractAppSpine(cur);
        if (sp.fn.tag === 'Const' && sp.fn.name === 'trans' && sp.args.length >= 6) {
          steps.push(describeJustification(sp.args[4], context, notations));
          cur = sp.args[5];
        } else {
          steps.push(describeJustification(cur, context, notations));
          break;
        }
      }
      if (steps.length <= 2) {
        return `\\text{trans}(${steps.join(',\\, ')})`;
      }
      // 3+ steps: render as semicolon-separated chain (more readable than nested trans)
      return steps.join('\\;;\\, ');
    }

    // cong: {A} {B} x y f proof — strip cong wrapper, just show the inner proof
    // In equational proofs, the reader sees what changed from LHS→RHS context;
    // citing just the base lemma (without the congruence motive) is standard math style.
    if (name === 'cong' && spine.args.length >= 6) {
      return describeJustification(spine.args[5], context, notations);
    }

    // replace: {A} x y P proof px — flatten nested chains, suppress motive
    // replace(P, eq1, replace(P', eq2, base)) → base (by eq2, eq1)
    if (name === 'replace' && spine.args.length >= 6) {
      const rewrites: string[] = [];
      let cur: TTKTerm = term;
      while (true) {
        const sp = extractAppSpine(cur);
        if (sp.fn.tag === 'Const' && sp.fn.name === 'replace' && sp.args.length >= 6) {
          rewrites.push(describeJustification(sp.args[4], context, notations));
          cur = sp.args[5]; // the inner proof (P x)
        } else {
          break;
        }
      }
      const baseDesc = describeJustification(cur, context, notations);
      // Rewrites collected outermost-first; reverse for application order
      const rewriteStrs = rewrites.reverse();
      const parts = rewriteStrs.length === 1
        ? `\\text{by } ${rewriteStrs[0]}`
        : `\\text{by } ${rewriteStrs.join(',\\, ')}`;
      return `${baseDesc}\\;(${parts})`;
    }

    // Ordering transitivity: skip value args, show just the two proofs
    // CompleteOrderedField.leTrans: (A, inst, a, b, c, h1, h2)
    if (name === 'CompleteOrderedField.leTrans' && spine.args.length >= 7) {
      const h1 = describeJustification(spine.args[5], context, notations);
      const h2 = describeJustification(spine.args[6], context, notations);
      return `\\text{leTrans}(${h1},\\, ${h2})`;
    }
    // User-defined ordering transitivity: (R, a, b, c, h1, h2)
    if (['leLtTrans', 'ltLeTrans', 'leLtTransLe', 'ltLeTransLe'].includes(name) && spine.args.length >= 6) {
      const h1 = describeJustification(spine.args[4], context, notations);
      const h2 = describeJustification(spine.args[5], context, notations);
      return `\\text{${escapeLaTeX(name)}}(${h1},\\, ${h2})`;
    }

    // MkDPair — existential witness: render with proof-aware rendering
    // Flatten nested MkPair: ⟨x, (a,b)⟩ → ⟨x, a, b⟩
    if (name === 'MkDPair' && spine.args.length >= 6) {
      const fst = termToLatex(spine.args[4], context, notations);
      // Check if snd is MkPair — flatten to ⟨fst, a, b⟩
      const sndTerm = spine.args[5];
      const sndSpine = extractAppSpine(sndTerm);
      if (sndSpine.fn.tag === 'Const' && sndSpine.fn.name === 'MkPair' && sndSpine.args.length >= 4) {
        const a = describeJustification(sndSpine.args[2], context, notations);
        const b = describeJustification(sndSpine.args[3], context, notations);
        return `\\langle ${fst},\\, ${a},\\, ${b} \\rangle`;
      }
      const snd = describeJustification(sndTerm, context, notations);
      return `\\langle ${fst},\\, ${snd} \\rangle`;
    }

    // MkPair — conjunction/pair: render both components with proof-aware rendering
    if (name === 'MkPair' && spine.args.length >= 4) {
      const a = describeJustification(spine.args[2], context, notations);
      const b = describeJustification(spine.args[3], context, notations);
      return `(${a},\\, ${b})`;
    }

    // MkLimit — record constructor wrapping a proof term
    if (name === 'MkLimit' && spine.args.length >= 5) {
      const inner = describeJustification(spine.args[4], context, notations);
      return `\\langle ${inner} \\rangle`;
    }

    // Record projections (Foo.bar): skip first 2 args (A and inst), then apply
    // proof-aware rendering (allVarRefs suppression, recursive describeJustification)
    // Accessor projections (Pair.fst → π₁, etc.) skip this handler so their
    // notation table entries render properly with mathematical symbols.
    const ACCESSOR_PROJECTIONS: Set<string> = new Set(['Pair.fst', 'Pair.snd', 'DPair.fst', 'DPair.snd']);
    const dotIdx = name.indexOf('.');
    if (dotIdx > 0 && spine.args.length >= 2 && !ACCESSOR_PROJECTIONS.has(name)) {
      const projName = name.substring(dotIdx + 1);
      const remainingArgs = spine.args.slice(2);
      const visibleRemaining = remainingArgs.filter(a =>
        a.tag !== 'Meta' && a.tag !== 'Hole' && a.tag !== 'Sort'
      );
      const projLatex = `\\text{${escapeLaTeX(projName)}}`;
      if (visibleRemaining.length === 0) return projLatex;
      const isSuppressibleProj = (a: TTKTerm) => isEffectiveVarRef(a, context) || isValueTerm(a, notations);
      if (visibleRemaining.every(isSuppressibleProj)) return projLatex;
      const meaningfulRemaining = visibleRemaining.filter(a => !isSuppressibleProj(a));
      const displayRemaining = meaningfulRemaining.length > 0 ? meaningfulRemaining : visibleRemaining;
      const argStrs = displayRemaining.slice(0, 6).map(a => describeJustification(a, context, notations));
      const suffix = displayRemaining.length > 6 ? ',\\ldots' : '';
      return `${projLatex}(${argStrs.join(',\\, ')}${suffix})`;
    }

    // Projection of hypothesis variable: π₁(hab) → assumption
    if (ACCESSOR_PROJECTIONS.has(name)) {
      const projIdx = name.startsWith('DPair') ? 4 : 2;
      if (spine.args.length > projIdx) {
        const target = spine.args[projIdx];
        if (target.tag === 'Var' && target.index < context.length &&
            !isCarrierEntry(context[target.index]) && isHypothesisName(context[target.index])) {
          return '\\text{assumption}';
        }
      }
    }

    // Check if notation table handles this term — let it render cleanly
    // In proof context, suppress obvious overflow args (e.g., bnd₁(x, hx) → bnd₁)
    const entry = notations.get(name);
    if (entry) {
      const arity = entry.kind === 'custom' ? entry.arity :
                    (entry.kind === 'prefix' || entry.kind === 'infix') ? entry.arity : undefined;
      if (arity !== undefined && spine.args.length > arity) {
        const baseResult = renderNotation(entry, name, spine.args.slice(0, arity), context, notations);
        const overflow = spine.args.slice(arity).filter(a =>
          !(a.tag === 'Var' && a.index < context.length && isCarrierEntry(context[a.index])) &&
          a.tag !== 'Meta' && a.tag !== 'Hole' && a.tag !== 'Sort'
        );
        const isSup = (a: TTKTerm) => isEffectiveVarRef(a, context) || isValueTerm(a, notations);
        if (overflow.length === 0 || overflow.every(isSup)) return baseResult;
        const meaningful = overflow.filter(a => !isSup(a));
        const display = meaningful.length > 0 ? meaningful : overflow;
        const argStrs = display.map(a => describeJustification(a, context, notations));
        return `${baseResult}(${argStrs.join(',\\, ')})`;
      }
      return renderNotation(entry, name, spine.args, context, notations);
    }

    // Named lemma applied to visible args
    // Skip implicit args (heuristic: args that are Meta, Sort, Hole, known type constants, or carrier vars)
    const visibleArgs = spine.args.filter(a =>
      a.tag !== 'Meta' && a.tag !== 'Hole' && a.tag !== 'Sort' &&
      !(a.tag === 'Var' && a.index < context.length && isCarrierEntry(context[a.index])) &&
      !(a.tag === 'Const' && notations.get(a.name)?.kind === 'const' &&
        ['\\mathbb{N}', '\\text{Type}', '\\mathbb{R}'].includes((notations.get(a.name) as any)?.latex))
    );

    const nameLatex = `\\text{${escapeLaTeX(name)}}`;
    if (visibleArgs.length === 0) return nameLatex;
    // Suppressible args: context-forwarding var refs AND value computations
    // (e.g., |f(x)+g(x)-(L+M)|) that are obvious from the theorem statement.
    const isSuppressible = (a: TTKTerm) => isEffectiveVarRef(a, context) || isValueTerm(a, notations);
    if (visibleArgs.every(isSuppressible)) return nameLatex;
    // Filter out suppressible args and show only meaningful (proof) ones.
    // "coreEstimate(f, g, x₀, L, M, ½·ε, ...)" → "coreEstimate(½·ε, ...)"
    const meaningfulArgs = visibleArgs.filter(a => !isSuppressible(a));
    const displayArgs = meaningfulArgs.length > 0 ? meaningfulArgs : visibleArgs;
    // Show up to 6 args, using describeJustification recursively so nested
    // proof combinators (replace, trans, leTrans, etc.) get improved rendering
    const argStrs = displayArgs.slice(0, 6).map(a => describeJustification(a, context, notations));
    const suffix = displayArgs.length > 6 ? ',\\ldots' : '';
    return `${nameLatex}(${argStrs.join(',\\, ')}${suffix})`;
  }

  // Var-function application: neab(proof) — apply proof-aware arg rendering
  if (spine.fn.tag === 'Var' && spine.fn.index < context.length && spine.args.length > 0) {
    const fnName = context[spine.fn.index];
    if (!isCarrierEntry(fnName)) {
      // Hypothesis variable used as a function: neab(leAntisym(...)) → assumption(leAntisym(...))
      const fnLatex = isHypothesisName(fnName)
        ? '\\text{assumption}'
        : renderVarName(fnName);
      const visibleArgs = spine.args.filter(a =>
        a.tag !== 'Meta' && a.tag !== 'Hole' && a.tag !== 'Sort' &&
        !(a.tag === 'Var' && a.index < context.length && isCarrierEntry(context[a.index]))
      );
      if (visibleArgs.length === 0) return fnLatex;
      const isSuppressibleVar = (a: TTKTerm) => isEffectiveVarRef(a, context) || isValueTerm(a, notations);
      if (visibleArgs.every(isSuppressibleVar)) return fnLatex;
      const meaningfulArgs = visibleArgs.filter(a => !isSuppressibleVar(a));
      const displayArgs = meaningfulArgs.length > 0 ? meaningfulArgs : visibleArgs;
      const argStrs = displayArgs.slice(0, 6).map(a => describeJustification(a, context, notations));
      const suffix = displayArgs.length > 6 ? ',\\ldots' : '';
      return `${fnLatex}(${argStrs.join(',\\, ')}${suffix})`;
    }
  }

  // Variable reference
  if (term.tag === 'Var' && term.index < context.length) {
    const varName = context[term.index];
    if (!isCarrierEntry(varName) && isHypothesisName(varName)) {
      return '\\text{assumption}';
    }
    return renderVarName(varName);
  }

  // Lambda — strip binders, extend context, and render the body
  // This handles e.g. \x hx => convertEps(...) inside MkPair proof tuples
  if (term.tag === 'Binder' && term.binderKind.tag === 'BLam') {
    let body: TTKTerm = term;
    let ctx = [...context];
    while (body.tag === 'Binder' && body.binderKind.tag === 'BLam') {
      const cl = isCarrierType(body.domain);
      ctx = [cl ? LATEX_PREFIX + cl : body.name, ...ctx];
      body = body.body;
    }
    return describeJustification(body, ctx, notations);
  }

  // Fallback: render the term (may be verbose)
  return termToLatex(term, context, notations);
}

/**
 * Render a trans chain as a KaTeX aligned equational proof.
 * Skips identity steps where LHS and RHS render identically
 * (e.g. reassociations that are invisible without explicit grouping).
 */
function renderTransChain(steps: TransStep[], context: string[], notations: NotationTable): string {
  // Filter out identity steps (where LHS and RHS render the same)
  const filteredSteps = steps.filter(step => {
    const lhsStr = termToLatex(step.lhs, context, notations);
    const rhsStr = termToLatex(step.rhs, context, notations);
    return lhsStr !== rhsStr;
  });

  // If all steps are identity (shouldn't happen), just show the LHS
  if (filteredSteps.length === 0) {
    const lhs = termToLatex(steps[0].lhs, context, notations);
    return `${lhs}`;
  }

  // Single-step chain: render inline instead of aligned block
  if (filteredSteps.length === 1) {
    const step = filteredSteps[0];
    const lhs = termToLatex(step.lhs, context, notations);
    const rhs = termToLatex(step.rhs, context, notations);
    const just = describeJustification(step.justification, context, notations);
    return `${lhs} = ${rhs} \\quad\\small\\text{by } ${just}`;
  }

  const lines: string[] = [];
  for (let i = 0; i < filteredSteps.length; i++) {
    const step = filteredSteps[i];
    const just = describeJustification(step.justification, context, notations);
    if (i === 0) {
      const lhs = termToLatex(step.lhs, context, notations);
      const rhs = termToLatex(step.rhs, context, notations);
      lines.push(`${lhs} &= ${rhs} & \\quad\\small\\text{by } ${just}`);
    } else {
      const rhs = termToLatex(step.rhs, context, notations);
      lines.push(`&= ${rhs} & \\quad\\small\\text{by } ${just}`);
    }
  }
  return `\\begin{aligned}\n${lines.join(' \\\\\n')}\n\\end{aligned}`;
}

// ============================================================================
// Inequality Chain Detection (leTrans, leLtTrans, ltLeTrans)
// ============================================================================

interface InequalityStep {
  lhs: TTKTerm;
  rhs: TTKTerm;
  relation: '\\le' | '<';
  justification: TTKTerm;
}

/**
 * Detect a chain of ordering transitivity:
 *   leTrans(A, inst, a, b, c, h1, h2)  — a ≤ b ≤ c
 *   leLtTrans(R, a, b, c, h1, h2)      — a ≤ b < c
 *   ltLeTrans(R, a, b, c, h1, h2)      — a < b ≤ c
 * Recursively flattens h2 if it's also a transitivity step.
 */
function detectInequalityChain(term: TTKTerm): InequalityStep[] | null {
  const spine = extractAppSpine(term);
  if (spine.fn.tag !== 'Const') return null;

  const name = spine.fn.name;
  const args = spine.args;

  let a: TTKTerm, b: TTKTerm, c: TTKTerm, h1: TTKTerm, h2: TTKTerm;
  let rel1: '\\le' | '<', rel2: '\\le' | '<';

  if (name === 'CompleteOrderedField.leTrans' && args.length >= 7) {
    // (A, inst, a, b, c, h1, h2) — skip A, inst
    a = args[2]; b = args[3]; c = args[4]; h1 = args[5]; h2 = args[6];
    rel1 = '\\le'; rel2 = '\\le';
  } else if ((name === 'leLtTrans') && args.length >= 6) {
    // (R, a, b, c, h1, h2) — skip R
    a = args[1]; b = args[2]; c = args[3]; h1 = args[4]; h2 = args[5];
    rel1 = '\\le'; rel2 = '<';
  } else if ((name === 'ltLeTrans') && args.length >= 6) {
    a = args[1]; b = args[2]; c = args[3]; h1 = args[4]; h2 = args[5];
    rel1 = '<'; rel2 = '\\le';
  } else if ((name === 'leLtTransLe' || name === 'ltLeTransLe') && args.length >= 6) {
    // User-defined wrappers that are just leTrans
    a = args[1]; b = args[2]; c = args[3]; h1 = args[4]; h2 = args[5];
    rel1 = '\\le'; rel2 = '\\le';
  } else {
    return null;
  }

  // Recursively check if h2 is also a transitivity step
  const rest = detectInequalityChain(h2);
  if (rest) {
    return [{ lhs: a, rhs: b, relation: rel1, justification: h1 }, ...rest];
  }

  return [
    { lhs: a, rhs: b, relation: rel1, justification: h1 },
    { lhs: b, rhs: c, relation: rel2, justification: h2 },
  ];
}

/**
 * Render an inequality chain as a KaTeX aligned proof.
 *   a ≤ b   by h1
 *     < c   by h2
 */
function renderInequalityChain(steps: InequalityStep[], context: string[], notations: NotationTable): string {
  const lines: string[] = [];
  for (let i = 0; i < steps.length; i++) {
    const step = steps[i];
    const just = describeJustification(step.justification, context, notations);
    if (i === 0) {
      const lhs = termToLatex(step.lhs, context, notations);
      const rhs = termToLatex(step.rhs, context, notations);
      lines.push(`${lhs} &${step.relation} ${rhs} & \\quad\\small\\text{by } ${just}`);
    } else {
      const rhs = termToLatex(step.rhs, context, notations);
      lines.push(`&${step.relation} ${rhs} & \\quad\\small\\text{by } ${just}`);
    }
  }
  return `\\begin{aligned}\n${lines.join(' \\\\\n')}\n\\end{aligned}`;
}

/**
 * Strip outer lambdas from a term, building a rendering context.
 * Detects carrier type binders and pushes carrier LaTeX instead of the name.
 */
function stripLambdasWithCarrier(
  term: TTKTerm,
  baseContext: string[],
): { body: TTKTerm; context: string[] } {
  const names: string[] = [];
  let current = term;
  while (current.tag === 'Binder' && current.binderKind.tag === 'BLam') {
    const carrierLatex = isCarrierType(current.domain);
    names.push(carrierLatex ? LATEX_PREFIX + carrierLatex : current.name);
    current = current.body;
  }
  return { body: current, context: [...names.reverse(), ...baseContext] };
}

// ---- Proof rendering helpers ----

/**
 * Check if a match is trivial argument destructuring (single clause, all PVar/PWild).
 * These are just "intros" — naming the function arguments — not real case analysis.
 */
function isTrivialIntroMatch(matchTerm: TTKTerm & { tag: 'Match' }): boolean {
  if (matchTerm.clauses.length !== 1) return false;
  return matchTerm.clauses[0].patterns.every(p => p.tag === 'PVar' || p.tag === 'PWild');
}

/**
 * Build rendering context from trivial match patterns, suppressing carrier positions.
 * Returns entries in reverse order (ready to prepend to context).
 */
function buildIntroContext(
  patterns: TTKPattern[],
  carrierPositions?: Map<number, string>,
): string[] {
  const entries: string[] = [];
  for (let i = 0; i < patterns.length; i++) {
    const pat = patterns[i];
    const cl = carrierPositions?.get(i);
    const vars = collectPatternVars([pat]);
    if (cl) {
      for (const _v of vars) entries.push(LATEX_PREFIX + cl);
    } else {
      entries.push(...vars);
    }
  }
  return entries.reverse();
}

/**
 * Strip let bindings from a proof body, rendering each as a "Let name := val." block.
 * Carrier-typed lets are suppressed (pushed into context as carrier substitutions).
 */
function stripLetsToBlocks(
  term: TTKTerm,
  context: string[],
  notations: NotationTable,
  indent: string,
): { blocks: LatexBlock[]; body: TTKTerm; context: string[] } {
  const blocks: LatexBlock[] = [];
  let current = term;
  let ctx = context;
  while (current.tag === 'Binder' && current.binderKind.tag === 'BLet') {
    const cl = isCarrierType(current.domain);
    if (cl) {
      ctx = [LATEX_PREFIX + cl, ...ctx];
    } else {
      // Flatten inner lets from defVal (e.g., suffices body containing have chains)
      const ctxBeforeFlatten = ctx;
      let defVal = current.binderKind.defVal;
      while (defVal.tag === 'Binder' && defVal.binderKind.tag === 'BLet') {
        const innerCl = isCarrierType(defVal.domain);
        if (innerCl) {
          ctx = [LATEX_PREFIX + innerCl, ...ctx];
        } else {
          const innerVal = describeJustification(defVal.binderKind.defVal, ctx, notations);
          blocks.push({ kind: 'rule', latex: `${indent}\\text{Let } ${renderVarName(defVal.name)} := ${innerVal}\\text{.}` });
          ctx = [defVal.name, ...ctx];
        }
        defVal = defVal.body;
      }
      // defVal is now the innermost body (actual value of the outer let)
      const val = describeJustification(defVal, ctx, notations);
      blocks.push({ kind: 'rule', latex: `${indent}\\text{Let } ${renderVarName(current.name)} := ${val}\\text{.}` });
      // Restore context: body only sees the outer let name, not inner let names
      ctx = [current.name, ...ctxBeforeFlatten];
    }
    current = current.body;
  }
  return { blocks, body: current, context: ctx };
}

/**
 * Render the RHS of a match clause (a proof body) as blocks.
 * Handles let bindings, trans chains, nested matches, and simple terms.
 */
function proofBodyToBlocks(
  term: TTKTerm,
  context: string[],
  notations: NotationTable,
  indent: string,
  carrierPositions?: Map<number, string>,
): LatexBlock[] {
  // Strip any remaining lambdas (e.g. "intros m p" inside a case)
  let { body: current, context: ctx } = stripLambdasWithCarrier(term, context);

  // Strip let bindings into proof step blocks
  const { blocks: letBlocks, body: afterLets, context: afterLetsCtx } =
    stripLetsToBlocks(current, ctx, notations, indent);
  current = afterLets;
  ctx = afterLetsCtx;

  // Nested Match → render as nested cases (no "Proof." prefix)
  if (current.tag === 'Match') {
    return [...letBlocks, ...renderMatchProof(current, ctx, notations, carrierPositions, false)];
  }

  // Try trans chain
  const chain = detectTransChain(current);
  if (chain) {
    return [...letBlocks, { kind: 'rule', latex: `${indent}${renderTransChain(chain, ctx, notations)}` }];
  }

  // Inequality chain
  const ineqChain = detectInequalityChain(current);
  if (ineqChain) {
    return [...letBlocks, { kind: 'rule', latex: `${indent}${renderInequalityChain(ineqChain, ctx, notations)}` }];
  }

  // MkDPair+MkPair: existential witness with conjunction — render as structured proof
  // ⟨witness, proof1, proof2⟩ → "Choose witness. (i) proof1 (ii) proof2"
  const dSpine = extractAppSpine(current);
  if (dSpine.fn.tag === 'Const' && dSpine.fn.name === 'MkDPair' && dSpine.args.length >= 6) {
    const witness = termToLatex(dSpine.args[4], ctx, notations);
    const sndTerm = dSpine.args[5];
    const sndSpine = extractAppSpine(sndTerm);
    if (sndSpine.fn.tag === 'Const' && sndSpine.fn.name === 'MkPair' && sndSpine.args.length >= 4) {
      const p1 = describeJustification(sndSpine.args[2], ctx, notations);
      const p2 = describeJustification(sndSpine.args[3], ctx, notations);
      return [
        ...letBlocks,
        { kind: 'rule', latex: `${indent}\\text{Choose } ${witness}\\text{.}` },
        { kind: 'rule', latex: `${indent}\\text{(i)}\\quad ${p1}` },
        { kind: 'rule', latex: `${indent}\\text{(ii)}\\quad ${p2}` },
      ];
    }
  }

  // Simple proof term — render concisely as justification
  const desc = describeJustification(current, ctx, notations);
  return [...letBlocks, { kind: 'rule', latex: `${indent}${desc}` }];
}

/**
 * Render a Match node as case analysis proof.
 * Only shows constructor patterns (PCtor) in case headers — suppresses PVar/PWild.
 * carrierPositions maps Pi-binder indices to carrier LaTeX for suppression.
 */
function renderMatchProof(
  matchTerm: TTKTerm & { tag: 'Match' },
  context: string[],
  notations: NotationTable,
  carrierPositions?: Map<number, string>,
  includeProofHeader: boolean = true,
): LatexBlock[] {
  const blocks: LatexBlock[] = [];

  // Determine what we're case-splitting on
  const isHoleScrutinee = matchTerm.scrutinee.tag === 'Hole' && matchTerm.scrutinee.id === '_scrutinee';
  const scrutineeLatex = matchTerm.scrutinee.tag === 'Var' && matchTerm.scrutinee.index < context.length
    ? renderVarName(context[matchTerm.scrutinee.index])
    : isHoleScrutinee ? '' : termToLatex(matchTerm.scrutinee, context, notations);

  // Header: "Proof. By cases on X:" or just "By cases on X:"
  const prefix = includeProofHeader ? '\\textit{Proof.}\\;' : '';
  if (isHoleScrutinee) {
    blocks.push({ kind: 'comment', latex: `${prefix}\\text{By pattern matching:}` });
  } else {
    blocks.push({ kind: 'comment', latex: `${prefix}\\text{By cases on } ${scrutineeLatex}\\text{:}` });
  }

  for (const clause of matchTerm.clauses) {
    // Build context and case header, suppressing carrier + PVar/PWild patterns
    const ctxEntries: string[] = [];
    const visiblePatParts: string[] = [];

    for (let pi = 0; pi < clause.patterns.length; pi++) {
      const pat = clause.patterns[pi];
      const carrierLatex = carrierPositions?.get(pi);
      const vars = collectPatternVars([pat]);

      if (carrierLatex) {
        for (const _v of vars) {
          ctxEntries.push(LATEX_PREFIX + carrierLatex);
        }
      } else {
        // Only show constructor patterns in case header (not PVar/PWild)
        if (pat.tag === 'PCtor') {
          visiblePatParts.push(patternToLatex(pat, notations));
        }
        ctxEntries.push(...vars);
      }
    }

    const clauseCtx = [...ctxEntries.reverse(), ...context];

    // Case header: only if there are constructor patterns to show
    if (visiblePatParts.length > 0) {
      const patLatex = visiblePatParts.join('\\;');
      blocks.push({ kind: 'rule', latex: `\\quad\\textbf{Case}\\;${patLatex}\\text{:}` });
    }

    // Render the RHS proof
    const rhsBlocks = proofBodyToBlocks(clause.rhs, clauseCtx, notations, '\\quad\\quad ', carrierPositions);
    blocks.push(...rhsBlocks);
  }

  return blocks;
}

/**
 * Main entry: convert a proof term into LaTeX blocks.
 * Strips lambdas, skips trivial intro matches, extracts let bindings,
 * then dispatches on Match / trans / sym / simple.
 */
function proofToLatex(
  term: TTKTerm,
  context: string[],
  notations: NotationTable,
  carrierPositions?: Map<number, string>,
  eitherCaseLabels?: Map<string, { left: string; right: string }>,
): LatexBlock[] {
  // 1. Strip outer lambdas, detecting carrier types
  let { body: current, context: ctx } = stripLambdasWithCarrier(term, context);

  // 2. Skip trivial intro match (single clause, all PVar/PWild)
  //    These are just function argument destructuring, not real case analysis.
  if (current.tag === 'Match' && isTrivialIntroMatch(current)) {
    const clause = current.clauses[0];
    ctx = [...buildIntroContext(clause.patterns, carrierPositions), ...ctx];
    current = clause.rhs;
    // Strip more lambdas in case RHS starts with them
    const s = stripLambdasWithCarrier(current, ctx);
    current = s.body;
    ctx = s.context;
  }

  // 3. Strip let bindings into proof step blocks
  const { blocks: letBlocks, body: afterLets, context: afterLetsCtx } =
    stripLetsToBlocks(current, ctx, notations, '');
  current = afterLets;
  ctx = afterLetsCtx;

  // 3.5. MkLimit unwrapping: expose inner proof for structured rendering.
  // MkLimit(R, f, x0, L, \eps \heps => body) → strip to body in extended context.
  {
    const mkLimitSpine = extractAppSpine(current);
    if (mkLimitSpine.fn.tag === 'Const' && mkLimitSpine.fn.name === 'MkLimit' && mkLimitSpine.args.length >= 5) {
      const innerProof = mkLimitSpine.args[4];
      const stripped = stripLambdasWithCarrier(innerProof, ctx);
      current = stripped.body;
      ctx = stripped.context;
      // Re-strip lets from unwrapped body
      const innerLets = stripLetsToBlocks(current, ctx, notations, '');
      letBlocks.push(...innerLets.blocks);
      current = innerLets.body;
      ctx = innerLets.context;
    }
  }

  // 4. Render the final proof body

  // Non-trivial Match → case analysis
  if (current.tag === 'Match') {
    if (letBlocks.length > 0) {
      return [
        { kind: 'comment', latex: '\\textit{Proof.}' },
        ...letBlocks,
        ...renderMatchProof(current, ctx, notations, carrierPositions, false),
      ];
    }
    return renderMatchProof(current, ctx, notations, carrierPositions);
  }

  // Trans chain
  const chain = detectTransChain(current);
  if (chain) {
    return [
      { kind: 'comment', latex: '\\textit{Proof.}' },
      ...letBlocks,
      { kind: 'rule', latex: renderTransChain(chain, ctx, notations) },
    ];
  }

  // Inequality chain: leTrans / leLtTrans / ltLeTrans
  const ineqChain = detectInequalityChain(current);
  if (ineqChain) {
    return [
      { kind: 'comment', latex: '\\textit{Proof.}' },
      ...letBlocks,
      { kind: 'rule', latex: renderInequalityChain(ineqChain, ctx, notations) },
    ];
  }

  // Sym
  const symMatch = detectSym(current);
  if (symMatch) {
    const inner = describeJustification(symMatch.inner, ctx, notations);
    if (letBlocks.length > 0) {
      return [
        { kind: 'comment', latex: '\\textit{Proof.}' },
        ...letBlocks,
        { kind: 'rule', latex: `\\text{sym}(${inner})` },
      ];
    }
    return [{ kind: 'comment', latex: `\\textit{Proof.}\\quad\\text{sym}(${inner})` }];
  }

  // eitherElim → structured case analysis
  const eSpine = extractAppSpine(current);
  if (eSpine.fn.tag === 'Const' && eSpine.fn.name === 'eitherElim' && eSpine.args.length >= 6) {
    const typeA = eSpine.args[0];  // Left type (what inl proves)
    const typeB = eSpine.args[1];  // Right type (what inr proves)
    const fInl = eSpine.args[3];
    const fInr = eSpine.args[4];
    const scrutinee = eSpine.args[5];

    // Try to get case labels: first from type args, then from Either binder types
    let leftLabel: string | null = null;
    let rightLabel: string | null = null;
    if (typeA.tag !== 'Hole' && typeA.tag !== 'Meta') {
      leftLabel = termToLatex(typeA, ctx, notations);
    }
    if (typeB.tag !== 'Hole' && typeB.tag !== 'Meta') {
      rightLabel = termToLatex(typeB, ctx, notations);
    }
    // Fallback: look up scrutinee variable in Either case labels from theorem type
    if ((!leftLabel || !rightLabel) && eitherCaseLabels &&
        scrutinee.tag === 'Var' && scrutinee.index < ctx.length) {
      const varName = ctx[scrutinee.index];
      // Try without LATEX_PREFIX since the name in the map is the original binder name
      const labels = eitherCaseLabels.get(varName);
      if (labels) {
        leftLabel = leftLabel || labels.left;
        rightLabel = rightLabel || labels.right;
      }
    }

    // Cross-case CSE: factor out repeated DPair/Pair projection bases
    // shared across both case bodies into let-bindings before "By cases:".
    const cseLetBlocks: LatexBlock[] = [];
    const cseReplacements: [string, string][] = [];

    if (fInl.tag === 'Binder' && fInl.binderKind.tag === 'BLam' &&
        fInr.tag === 'Binder' && fInr.binderKind.tag === 'BLam') {
      const projBases = new Map<string, { base: TTKTerm, projections: Map<string, TTKTerm> }>();
      collectProjectionBasesFromTerm(fInl.body, projBases);
      collectProjectionBasesFromTerm(fInr.body, projBases);

      const extractable = [...projBases.values()].filter(g => g.projections.size >= 2);

      if (extractable.length > 0) {
        // Use inl case context for rendering (same result for both since base
        // doesn't reference the case variable at index 0)
        const caseCtx = [fInl.name || 'h', ...ctx];

        for (let gi = 0; gi < extractable.length; gi++) {
          const group = extractable[gi];
          const sub = extractable.length > 1 ? `_{${gi + 1}}` : '';
          const baseLatex = termToLatex(group.base, caseCtx, notations);

          // Determine projection family and complete the set
          const hasDPairOfPair = group.projections.has('dfst') ||
            group.projections.has('dsnd.pfst') || group.projections.has('dsnd.psnd');
          const hasPlainPair = group.projections.has('pfst') || group.projections.has('psnd');

          const projNames = new Map<string, string>();
          if (hasDPairOfPair) {
            projNames.set('dfst', `\\delta${sub}`);
            projNames.set('dsnd.pfst', `h${sub}`);
            projNames.set('dsnd.psnd', `\\text{bnd}${sub}`);
          } else if (hasPlainPair) {
            projNames.set('pfst', `\\pi_1${sub}`);
            projNames.set('psnd', `\\pi_2${sub}`);
          }

          if (projNames.size === 0) continue;

          // Build string replacement patterns
          for (const [projKey, name] of projNames) {
            let pattern: string | undefined;
            if (projKey === 'dfst') pattern = `\\pi_1(${baseLatex})`;
            else if (projKey === 'dsnd.pfst') pattern = `\\pi_1(\\pi_2(${baseLatex}))`;
            else if (projKey === 'dsnd.psnd') pattern = `\\pi_2(\\pi_2(${baseLatex}))`;
            else if (projKey === 'pfst') pattern = `\\pi_1(${baseLatex})`;
            else if (projKey === 'psnd') pattern = `\\pi_2(${baseLatex})`;
            if (pattern) cseReplacements.push([pattern, name]);
          }

          // Sort names in canonical order for the let-binding
          const order = ['dfst', 'dsnd.pfst', 'dsnd.psnd', 'pfst', 'psnd'];
          const sortedNames = [...projNames.entries()]
            .sort(([a], [b]) => order.indexOf(a) - order.indexOf(b))
            .map(([_, name]) => name);

          cseLetBlocks.push({
            kind: 'rule',
            latex: `\\text{Let } (${sortedNames.join(',\\, ')}) = ${baseLatex}`,
          });
        }

        // Sort replacements longest-first to avoid partial matches
        cseReplacements.sort((a, b) => b[0].length - a[0].length);
      }
    }

    // Fallback: reconstruct case types from scrutinee structure
    // e.g., leTotal(R, inst, a, b) → left: a ≤ b, right: b ≤ a
    if (!leftLabel || !rightLabel) {
      const scrutSpine = extractAppSpine(scrutinee);
      if (scrutSpine.fn.tag === 'Const' && scrutSpine.fn.name.endsWith('.leTotal') && scrutSpine.args.length >= 4) {
        let aLatex = termToLatex(scrutSpine.args[2], ctx, notations);
        let bLatex = termToLatex(scrutSpine.args[3], ctx, notations);
        // Apply CSE replacements so δ₁/δ₂ appear instead of full projection expressions
        for (const [from, to] of cseReplacements) {
          aLatex = aLatex.split(from).join(to);
          bLatex = bLatex.split(from).join(to);
        }
        leftLabel = leftLabel || `${aLatex} \\leq ${bLatex}`;
        rightLabel = rightLabel || `${bLatex} \\leq ${aLatex}`;
      }
    }

    const resultBlocks: LatexBlock[] = [];
    if (letBlocks.length > 0 || cseLetBlocks.length > 0) {
      resultBlocks.push({ kind: 'comment', latex: '\\textit{Proof.}' });
      resultBlocks.push(...letBlocks);
      resultBlocks.push(...cseLetBlocks);
    }

    // Header: "By cases:" with scrutinee info if available
    const prefix = (letBlocks.length > 0 || cseLetBlocks.length > 0) ? '' : '\\textit{Proof.}\\;';
    const scrutineeDesc = (leftLabel && rightLabel) ? ` (${termToLatex(scrutinee, ctx, notations)})` : '';
    let scrutineeDescCSE = scrutineeDesc;
    for (const [from, to] of cseReplacements) {
      scrutineeDescCSE = scrutineeDescCSE.split(from).join(to);
    }
    resultBlocks.push({ kind: 'comment', latex: `${prefix}\\text{By cases}${scrutineeDescCSE}\\text{:}` });

    // Helper to apply CSE string replacements to rendered blocks
    const applyCSE = (blocks: LatexBlock[]): LatexBlock[] => {
      if (cseReplacements.length === 0) return blocks;
      return blocks.map(block => {
        let latex = block.latex;
        for (const [from, to] of cseReplacements) {
          latex = latex.split(from).join(to);
        }
        return { ...block, latex };
      });
    };

    // Case 1: use the type label if available
    if (fInl.tag === 'Binder' && fInl.binderKind.tag === 'BLam') {
      const varName = fInl.name || 'h';
      const caseStr = leftLabel || `\\text{inl}\\;(${renderVarName(varName)})`;
      resultBlocks.push({ kind: 'rule', latex: `\\quad\\textbf{Case}\\;${caseStr}\\text{:}` });
      const inlCtx = [varName, ...ctx];
      resultBlocks.push(...applyCSE(proofBodyToBlocks(fInl.body, inlCtx, notations, '\\quad\\quad ', carrierPositions)));
    }

    // Case 2: use the type label if available
    if (fInr.tag === 'Binder' && fInr.binderKind.tag === 'BLam') {
      const varName = fInr.name || 'h';
      const caseStr = rightLabel || `\\text{inr}\\;(${renderVarName(varName)})`;
      resultBlocks.push({ kind: 'rule', latex: `\\quad\\textbf{Case}\\;${caseStr}\\text{:}` });
      const inrCtx = [varName, ...ctx];
      resultBlocks.push(...applyCSE(proofBodyToBlocks(fInr.body, inrCtx, notations, '\\quad\\quad ', carrierPositions)));
    }

    return resultBlocks;
  }

  // Conjunction proof: MkPair(A, B, proof1, proof2) → render as two parts
  if (eSpine.fn.tag === 'Const' && eSpine.fn.name === 'MkPair' && eSpine.args.length >= 4) {
    const proof1 = eSpine.args[2];
    const proof2 = eSpine.args[3];
    const desc1 = describeJustification(proof1, ctx, notations);
    const desc2 = describeJustification(proof2, ctx, notations);
    if (letBlocks.length > 0) {
      return [
        { kind: 'comment', latex: '\\textit{Proof.}' },
        ...letBlocks,
        { kind: 'rule', latex: `\\text{(i)}\\quad ${desc1}` },
        { kind: 'rule', latex: `\\text{(ii)}\\quad ${desc2}` },
      ];
    }
    return [
      { kind: 'comment', latex: '\\textit{Proof.}' },
      { kind: 'rule', latex: `\\text{(i)}\\quad ${desc1}` },
      { kind: 'rule', latex: `\\text{(ii)}\\quad ${desc2}` },
    ];
  }

  // DPair/Pair destructuring: detect repeated projection patterns and render as let-bindings.
  // E.g. pickDelta(π₁(X), π₁(Y), π₁(π₂(X)), ...) → Let (δ₁, h₁, bnd₁) = X; ...
  if (eSpine.fn.tag === 'Const' && eSpine.args.length >= 4) {
    const destrResult = detectDestructuringLets(eSpine.args, ctx, notations, eSpine.fn.name);
    if (destrResult) {
      return [
        { kind: 'comment', latex: '\\textit{Proof.}' },
        ...letBlocks,
        ...destrResult.lets.map(l => ({ kind: 'rule' as const, latex: l })),
        { kind: 'rule', latex: destrResult.mainExpr },
      ];
    }
  }

  // Simple proof (refl, single application, etc.)
  const desc = describeJustification(current, ctx, notations);
  if (letBlocks.length > 0) {
    return [
      { kind: 'comment', latex: '\\textit{Proof.}' },
      ...letBlocks,
      { kind: 'rule', latex: desc },
    ];
  }
  // Long proofs get their own line for readability
  if (desc.length > 70) {
    return [
      { kind: 'comment', latex: '\\textit{Proof.}' },
      { kind: 'rule', latex: desc },
    ];
  }
  return [{ kind: 'comment', latex: `\\textit{Proof.}\\quad${desc}` }];
}

// ============================================================================
// Declaration Conversion
// ============================================================================

type DeclCategory = 'inductive' | 'record' | 'definition' | 'theorem' | 'postulate';

function classifyDecl(decl: CompiledDeclaration): DeclCategory {
  if (decl.kind === 'inductive' && decl.isRecord) return 'record';
  if (decl.kind === 'inductive') return 'inductive';
  if (decl.tacticInfoTree !== undefined) return 'theorem';
  if (decl.surfaceValue?.tag === 'TacticBlock') return 'theorem';
  if (!decl.kernelValue && decl.kernelType) return 'postulate';
  // Check if the return type looks propositional → classify as theorem
  if (decl.kernelType && decl.kernelValue) {
    const returnType = getReturnType(decl.kernelType);
    if (looksLikeProp(returnType, 0)) return 'theorem';
  }
  return 'definition';
}

/** Extract the innermost body of nested Pi types (the return type). */
function getReturnType(type: TTKTerm): TTKTerm {
  let current = type;
  while (current.tag === 'Binder' && current.binderKind.tag === 'BPi') {
    current = current.body;
  }
  return current;
}

function convertInductive(decl: CompiledDeclaration, notations: NotationTable): LatexBlock[] {
  const blocks: LatexBlock[] = [];
  const name = decl.name ?? '?';
  const nameLatex = notations.get(name)?.kind === 'const'
    ? (notations.get(name) as { latex: string }).latex
    : `\\text{${escapeLaTeX(name)}}`;

  // Header: data Name : Type where
  if (decl.kernelType) {
    const typeLatex = termToLatex(decl.kernelType, [], notations);
    blocks.push({ kind: 'header', latex: `\\textbf{data}\\;${nameLatex} : ${typeLatex}\\;\\textbf{where}` });
  } else {
    blocks.push({ kind: 'header', latex: `\\textbf{data}\\;${nameLatex}\\;\\textbf{where}` });
  }

  // Constructors
  if (decl.kernelConstructors) {
    for (const ctor of decl.kernelConstructors) {
      const ctorNameLatex = notations.get(ctor.name)?.kind === 'const'
        ? (notations.get(ctor.name) as { latex: string }).latex
        : `\\text{${escapeLaTeX(ctor.name)}}`;
      const ctorType = termToLatex(ctor.type, [], notations);
      blocks.push({ kind: 'rule', latex: `${ctorNameLatex} : ${ctorType}` });
    }
  }

  return blocks;
}

function convertRecord(decl: CompiledDeclaration, notations: NotationTable): LatexBlock[] {
  const blocks: LatexBlock[] = [];
  const name = decl.name ?? '?';
  const nameLatex = `\\text{${escapeLaTeX(name)}}`;

  // For records, show params from the constructor type's Pi spine
  if (decl.kernelConstructors && decl.kernelConstructors.length > 0) {
    const ctorType = decl.kernelConstructors[0].type;
    const { binders } = extractPiSpine(ctorType);

    // The params are the ones from the inductive type itself
    // The fields are the remaining binders after params
    const nParams = decl.surfaceParams?.length ?? 0;
    const params = binders.slice(0, nParams);
    const fields = binders.slice(nParams);

    // Header: record Name (params) where
    let header = `\\textbf{record}\\;${nameLatex}`;
    if (params.length > 0) {
      let ctx: string[] = [];
      const paramParts: string[] = [];
      for (const p of params) {
        paramParts.push(`(${renderVarName(p.name)} : ${termToLatex(p.type, ctx, notations)})`);
        ctx = [p.name, ...ctx];
      }
      header += `\\;${paramParts.join('\\;')}`;
    }
    header += `\\;\\textbf{where}`;
    blocks.push({ kind: 'header', latex: header });

    // Fields
    let fieldCtx: string[] = [];
    // Build context with params
    for (const p of params) {
      fieldCtx = [p.name, ...fieldCtx];
    }
    for (const f of fields) {
      const fieldType = termToLatex(f.type, fieldCtx, notations);
      blocks.push({ kind: 'rule', latex: `\\text{${escapeLaTeX(f.name)}} : ${fieldType}` });
      fieldCtx = [f.name, ...fieldCtx];
    }
  } else {
    blocks.push({ kind: 'header', latex: `\\textbf{record}\\;${nameLatex}\\;\\textbf{where}` });
  }

  return blocks;
}

function convertDefinition(decl: CompiledDeclaration, notations: NotationTable): LatexBlock[] {
  const blocks: LatexBlock[] = [];
  const name = decl.name ?? '?';
  const nameLatex = `\\text{${escapeLaTeX(name)}}`;

  // Determine carrier positions from the type signature
  const carrierMap = decl.kernelType ? getCarrierPositions(decl.kernelType) : new Map<number, string>();

  // Header: name : type
  if (decl.kernelType) {
    // For definitions that are simple type aliases (LessThan), use typeToLatex for the signature
    const typeStr = typeToLatex(decl.kernelType, [], notations);
    blocks.push({ kind: 'header', latex: `${nameLatex} : ${typeStr}` });
  }

  // Body: equations from pattern matching
  if (decl.kernelValue) {
    const clauses = extractClauses(decl.kernelValue);
    if (clauses.length > 0) {
      for (const clause of clauses) {
        // Build context and LHS patterns, suppressing carrier positions
        const ctxEntries: string[] = [];
        const lhsPatParts: string[] = [];

        for (let pi = 0; pi < clause.patterns.length; pi++) {
          const pat = clause.patterns[pi];
          const carrierLatex = carrierMap.get(pi);
          const vars = collectPatternVars([pat]);

          if (carrierLatex) {
            // Carrier position — use carrier LaTeX in context, suppress from LHS
            for (const _v of vars) {
              ctxEntries.push(LATEX_PREFIX + carrierLatex);
            }
          } else {
            lhsPatParts.push(patternToLatex(pat, notations));
            ctxEntries.push(...vars);
          }
        }

        const clauseCtx = [...ctxEntries.reverse()];
        const lhsPats = lhsPatParts.join('\\;');
        const rhs = termToLatex(clause.rhs, clauseCtx, notations);
        const lhsStr = lhsPats.length > 0 ? `${nameLatex}\\;${lhsPats}` : nameLatex;
        blocks.push({ kind: 'rule', latex: `${lhsStr} = ${rhs}` });
      }
    } else {
      // Non-pattern-match definition: name = value
      const valStr = termToLatex(decl.kernelValue, [], notations);
      blocks.push({ kind: 'rule', latex: `${nameLatex} := ${valStr}` });
    }
  }

  return blocks;
}

function convertTheorem(decl: CompiledDeclaration, notations: NotationTable): LatexBlock[] {
  const blocks: LatexBlock[] = [];
  const name = decl.name ?? '?';
  const nameLatex = `\\text{${escapeLaTeX(name)}}`;

  // Compute carrier positions for proof rendering
  const carrierPositions = decl.kernelType ? getCarrierPositions(decl.kernelType) : new Map<number, string>();

  if (decl.kernelType) {
    let { binders, body } = extractPiSpine(decl.kernelType);
    const isPropLike = binders.length > 0 && looksLikeProp(body, binders.length);

    // Detect negation conclusion: ... → Equal X Y → ⊥  →  fold into X ≠ Y
    if (isPropLike && body.tag === 'Const' && body.name === 'Void' && binders.length > 0) {
      const lastBinder = binders[binders.length - 1];
      if (!isCarrierType(lastBinder.type)) {
        const eqSpine = extractAppSpine(lastBinder.type);
        if (eqSpine.fn.tag === 'Const' && eqSpine.fn.name === 'Equal' && eqSpine.args.length >= 3) {
          binders = binders.slice(0, -1);
          body = {
            tag: 'Binder', name: '_', binderKind: { tag: 'BPi' },
            domain: lastBinder.type, body: { tag: 'Const', name: 'Void' },
          } as TTKTerm;
        }
      }
    }

    if (isPropLike) {
      // "Theorem (name). Let ... . Suppose ... . Then:" + boxed conclusion
      const { groups, finalCtx } = buildBinderGroups(binders, [], notations);
      const bodyLatex = termToLatex(body, finalCtx, notations);

      // Classify groups: named binders → "Let", unnamed (all _) → "Suppose"
      const letGroups: BinderGroup[] = [];
      const supposeGroups: BinderGroup[] = [];
      for (const g of groups) {
        if (g.names.every(n => n === '_')) {
          supposeGroups.push(g);
        } else {
          letGroups.push(g);
        }
      }

      // Post-merge carrier set groups that share the same typeLatex in the Let section
      // e.g., "x₀, L, M ∈ ℝ" and "ε ∈ ℝ" → "x₀, L, M, ε ∈ ℝ"
      const mergedLetGroups: BinderGroup[] = [];
      for (const g of letGroups) {
        const existing = g.isCarrierSet
          ? mergedLetGroups.find(m => m.isCarrierSet && m.typeLatex === g.typeLatex)
          : undefined;
        if (existing) {
          existing.names.push(...g.names);
        } else {
          mergedLetGroups.push({ ...g, names: [...g.names] });
        }
      }

      const letParts = mergedLetGroups.map(formatBinderGroup);
      const supposeParts = supposeGroups.map(formatBinderGroup);

      // Check if hypotheses are long (contain quantifiers or the total is > 120 chars)
      const supposeStr = supposeParts.join('\\text{ and }');
      const hasLongHypotheses = supposeParts.length >= 3 &&
        (supposeStr.length > 120 || supposeParts.some(p => p.includes('\\forall') || p.includes('\\implies')));

      // Group hypotheses into lines: short ones merge, long ones get their own line
      const emitSupposeBlocks = () => {
        if (!hasLongHypotheses) {
          blocks.push({ kind: 'header', latex: `\\quad\\text{Suppose } ${supposeStr}\\text{. Then:}` });
          return;
        }
        // Group consecutive short hypotheses together, break at long ones
        const isLong = (p: string) => p.length > 60 || p.includes('\\forall') || p.includes('\\implies');
        const lines: string[] = [];
        let current: string[] = [];
        for (const p of supposeParts) {
          if (isLong(p)) {
            if (current.length > 0) { lines.push(current.join('\\text{ and }')); current = []; }
            lines.push(p);
          } else {
            current.push(p);
          }
        }
        if (current.length > 0) lines.push(current.join('\\text{ and }'));
        for (let i = 0; i < lines.length; i++) {
          const prefix = i === 0 ? '\\quad\\text{Suppose }' : '\\quad\\quad\\text{and }';
          const suffix = i === lines.length - 1 ? '\\text{. Then:}' : '\\text{,}';
          blocks.push({ kind: 'header', latex: `${prefix}${lines[i]}${suffix}` });
        }
      };

      if (letParts.length > 0 && supposeParts.length > 0) {
        blocks.push({ kind: 'header', latex: `\\textbf{Theorem}\\;(${nameLatex})\\text{. Let } ${letParts.join('\\text{ and }')}\\text{.}` });
        emitSupposeBlocks();
      } else if (letParts.length > 0) {
        blocks.push({ kind: 'header', latex: `\\textbf{Theorem}\\;(${nameLatex})\\text{. Let } ${letParts.join('\\text{ and }')}\\text{. Then:}` });
      } else if (supposeParts.length > 0) {
        if (hasLongHypotheses) {
          blocks.push({ kind: 'header', latex: `\\textbf{Theorem}\\;(${nameLatex})\\text{.}` });
          emitSupposeBlocks();
        } else {
          blocks.push({ kind: 'header', latex: `\\textbf{Theorem}\\;(${nameLatex})\\text{. Suppose } ${supposeStr}\\text{. Then:}` });
        }
      } else {
        blocks.push({ kind: 'header', latex: `\\textbf{Theorem}\\;(${nameLatex})\\text{:}` });
      }
      blocks.push({ kind: 'header', latex: `\\boxed{\\displaystyle ${bodyLatex}}` });
    } else {
      // Non-propositional: simple "name : type" format
      const typeStr = typeToLatex(decl.kernelType, [], notations);
      blocks.push({ kind: 'header', latex: `\\textbf{Theorem}\\;${nameLatex} : ${typeStr}` });
    }
  }

  // Build case labels for Either-typed binders (for eitherElim rendering)
  // Pi binder names may be "_" (unnamed), so we remap to actual pattern variable names
  // from the kernel value's intro match if available.
  let eitherCaseLabels: Map<string, { left: string; right: string }> | undefined;
  if (decl.kernelType) {
    const { binders: typeBinders } = extractPiSpine(decl.kernelType);

    // Get pattern variable names from the kernel value's trivial intro match
    let patternVarNames: string[] | undefined;
    if (decl.kernelValue?.tag === 'Match' && isTrivialIntroMatch(decl.kernelValue)) {
      patternVarNames = decl.kernelValue.clauses[0].patterns.flatMap(p => collectPatternVars([p]));
    }

    let scanCtx: string[] = [];
    let binderIdx = 0;
    for (const b of typeBinders) {
      const cl = isCarrierType(b.type);
      if (cl) {
        scanCtx = [LATEX_PREFIX + cl, ...scanCtx];
        binderIdx++;
        continue;
      }
      // Check if this binder has Either type
      const eitherSpine = extractAppSpine(b.type);
      if (eitherSpine.fn.tag === 'Const' && eitherSpine.fn.name === 'Either' && eitherSpine.args.length >= 2) {
        if (!eitherCaseLabels) eitherCaseLabels = new Map();
        const leftStr = termToLatex(eitherSpine.args[0], scanCtx, notations);
        const rightStr = termToLatex(eitherSpine.args[1], scanCtx, notations);
        // Use pattern variable name if available (Pi binder may be "_")
        const keyName = patternVarNames?.[binderIdx] ?? b.name;
        eitherCaseLabels.set(keyName, { left: leftStr, right: rightStr });
      }
      scanCtx = [b.name, ...scanCtx];
      binderIdx++;
    }
  }

  // Render proof body from kernel value
  if (decl.kernelValue) {
    const proofBlocks = proofToLatex(decl.kernelValue, [], notations, carrierPositions, eitherCaseLabels);
    blocks.push(...proofBlocks);
  } else {
    blocks.push({ kind: 'comment', latex: '\\textit{Proof.}\\quad\\square' });
  }

  return blocks;
}

function convertPostulate(decl: CompiledDeclaration, notations: NotationTable): LatexBlock[] {
  const blocks: LatexBlock[] = [];
  const name = decl.name ?? '?';
  const nameLatex = `\\text{${escapeLaTeX(name)}}`;

  if (decl.kernelType) {
    const typeStr = typeToLatex(decl.kernelType, [], notations);
    blocks.push({ kind: 'header', latex: `\\textbf{axiom}\\;${nameLatex} : ${typeStr}` });
  }

  return blocks;
}

/**
 * Extract pattern match clauses from a definition's kernel value.
 * Definitions may be wrapped in lambdas before the Match node.
 */
function extractClauses(term: TTKTerm): TTKClause[] {
  let current = term;
  // Peel off lambdas
  while (current.tag === 'Binder' && current.binderKind.tag === 'BLam') {
    current = current.body;
  }
  if (current.tag === 'Match') {
    return current.clauses;
  }
  return [];
}

// ============================================================================
// Main Converter
// ============================================================================

/**
 * Convert compiled blocks into a LaTeX document.
 */
export function convertToLatex(result: CompileResult, notations?: NotationTable): LatexDocument {
  const n = notations ?? makeDefaultNotations();
  const sections: LatexSection[] = [];

  // Build set of user-defined propositional type names by scanning definition bodies.
  // e.g. EpsDeltaWitness = \... => Pair (0 < delta) (...) — body is Pair of props.
  // Function equations compile to Match terms, so we look at the first clause RHS too.
  _knownPropNames = new Set();
  for (const block of result.blocks) {
    for (const decl of block.declarations) {
      if (decl.name && decl.kernelValue && decl.kind !== 'inductive') {
        let body: TTKTerm = decl.kernelValue;
        while (body.tag === 'Binder' && body.binderKind.tag === 'BLam') body = body.body;
        if (body.tag === 'Match' && body.clauses.length > 0) body = body.clauses[0].rhs;
        while (body.tag === 'Binder' && body.binderKind.tag === 'BLam') body = body.body;
        if (looksLikeProp(body, 0)) {
          _knownPropNames.add(decl.name);
        }
      }
    }
  }

  for (const block of result.blocks) {
    if (block.isComment) continue;

    for (const decl of block.declarations) {
      if (!decl.name) continue;
      if (decl.isWithAuxiliary) continue;

      const category = classifyDecl(decl);
      let blocks: LatexBlock[];

      try {
        switch (category) {
          case 'inductive':
            blocks = convertInductive(decl, n);
            break;
          case 'record':
            blocks = convertRecord(decl, n);
            break;
          case 'definition':
            blocks = convertDefinition(decl, n);
            break;
          case 'theorem':
            blocks = convertTheorem(decl, n);
            break;
          case 'postulate':
            blocks = convertPostulate(decl, n);
            break;
        }
      } catch (e) {
        blocks = [{ kind: 'header', latex: `\\text{${escapeLaTeX(decl.name)}}` }];
        blocks.push({ kind: 'comment', latex: `\\textcolor{red}{\\text{Conversion error: ${escapeLaTeX(String(e))}}}` });
      }

      const errors = decl.checkErrors.map(e => e.message);

      sections.push({
        name: decl.name,
        category,
        checkSuccess: decl.checkSuccess,
        errors,
        blocks,
      });
    }
  }

  return { sections };
}

// ============================================================================
// Utilities
// ============================================================================

function escapeLaTeX(s: string): string {
  return s.replace(/\\/g, '\\backslash ')
    .replace(/_/g, '\\_')
    .replace(/\{/g, '\\{')
    .replace(/\}/g, '\\}')
    .replace(/#/g, '\\#')
    .replace(/%/g, '\\%')
    .replace(/&/g, '\\&');
}
