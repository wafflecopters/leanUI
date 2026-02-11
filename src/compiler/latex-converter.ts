/**
 * latex-converter.ts — Convert CompiledDeclaration[] into structured LaTeX for rendering.
 *
 * Pure functions, no React. Produces LatexDocument which the LaTeXPanel renders.
 */

import { CompiledDeclaration, CompiledBlock, CompileResult } from './compile';
import { TTKTerm, TTKPattern, TTKClause } from './kernel';
import { extractAppSpine, extractPiSpine, AppSpine } from './term';
import { occursIn } from './kernel';

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
    return `${escapeLaTeX(subscriptMatch[1])}_{${subscriptMatch[2]}}`;
  }
  return escapeLaTeX(cleaned);
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
  | { kind: 'custom'; render: (args: TTKTerm[], ctx: string[], n: NotationTable) => string };

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

  // Either
  table.set('Either', { kind: 'custom', render: (args, ctx, n) => {
    if (args.length === 2) {
      return `${termToLatex(args[0], ctx, n)} \\oplus ${termToLatex(args[1], ctx, n)}`;
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

  // replace: {A} x y P proof px — show as substitution
  table.set('replace', { kind: 'custom', render: (args, ctx, n) => {
    if (args.length >= 6) {
      const P = termToLatex(args[3], ctx, n);
      const proof = termToLatex(args[4], ctx, n);
      const px = termToLatex(args[5], ctx, n);
      return `\\text{subst}(${P},\\, ${proof},\\, ${px})`;
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
  table.set('DPair', { kind: 'custom', render: (args, ctx, n) => {
    if (args.length >= 4) {
      const A = args[2];
      const B = args[3];
      // If B is a lambda, render as Σ (x : A), body
      if (B.tag === 'Binder' && B.binderKind.tag === 'BLam') {
        const varName = B.name || 'x';
        const aStr = termToLatex(A, ctx, n);
        const bodyCtx = [varName, ...ctx];
        const bodyStr = termToLatex(B.body, bodyCtx, n);
        return `\\Sigma\\,(${renderVarName(varName)} : ${aStr}),\\, ${bodyStr}`;
      }
      // Not a lambda — render as Σ A B
      return `\\Sigma\\,(${termToLatex(A, ctx, n)})\\,(${termToLatex(B, ctx, n)})`;
    }
    // 2-arg form (legacy)
    if (args.length === 2) {
      return `\\Sigma\\,(${termToLatex(args[0], ctx, n)})\\,(${termToLatex(args[1], ctx, n)})`;
    }
    return '\\Sigma';
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
  table.set('DPair.fst', { kind: 'custom', render: (args, ctx, n) => {
    if (args.length >= 5) {
      return `\\pi_1(${termToLatex(args[4], ctx, n)})`;
    }
    return '\\pi_1';
  }});
  // DPair.snd — skip 4 params (u, v, A, B), show projection of 5th arg
  table.set('DPair.snd', { kind: 'custom', render: (args, ctx, n) => {
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
  table.set('Pair.fst', { kind: 'custom', render: (args, ctx, n) => {
    if (args.length >= 3) {
      return `\\pi_1(${termToLatex(args[2], ctx, n)})`;
    }
    return '\\pi_1';
  }});
  // Pair.snd({A}, {B}, p) → π₂(p)
  table.set('Pair.snd', { kind: 'custom', render: (args, ctx, n) => {
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

  // Absolute value: rabs R x → |x|
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
        return `\\lim_{${renderVarName(varName)} \\to ${x0}} ${body} = ${lVal}`;
      }
      // Named function: render as f(x) = L
      const fStr = termToLatex(f, ctx, n);
      return `\\lim_{x \\to ${x0}} ${fStr}(x) = ${lVal}`;
    }
    return '\\text{Limit}';
  }});
  // Limit.eps_delta — record projection: R, f, x0, L (4 params), then instance, eps, epsProof
  table.set('Limit.eps_delta', { kind: 'custom', render: (args, ctx, n) => {
    if (args.length >= 7) {
      const limitProof = termToLatex(args[4], ctx, n);
      const epsArg = termToLatex(args[5], ctx, n);
      const epsProof = termToLatex(args[6], ctx, n);
      return `${limitProof}.\\varepsilon\\delta(${epsArg},\\, ${epsProof})`;
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

  // EpsDeltaWitness — abbreviate: skip R, show concise version
  table.set('EpsDeltaWitness', { kind: 'custom', render: (args, ctx, n) => {
    // EpsDeltaWitness R f x0 L eps [delta]
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
  table.set('CompleteOrderedField.abs', { kind: 'custom', render: (args, ctx, n) => {
    if (args.length >= 3) {
      return `\\left|${termToLatex(args[2], ctx, n)}\\right|`;
    }
    return '|\\cdot|';
  }});

  // Proof projections: skip 2 params, render as \text{name}(visible_args...)
  const proofProjections = [
    'addAssoc', 'addComm', 'addZeroRight', 'negRight',
    'mulAssoc', 'mulOneLeft', 'mulOneRight', 'mulComm',
    'distribLeft', 'distribRight',
    'leRefl', 'leAntisym', 'leTrans', 'leTotal',
    'addLeLeft', 'mulNonneg', 'absTriangle',
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
            return `${domain} \\to ${body}`;
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
        const rhs = termToLatex(visible[1], context, notations);
        const extra = visible.slice(2);
        let result = `${lhs} ${entry.latex} ${rhs}`;
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

    case 'custom':
      return entry.render(args, context, notations);
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
      if (pattern.args.length === 0) return ctorName;
      const args = pattern.args.map(p => patternToLatex(p, notations)).join('\\;');
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
    // Arrow style: N → N → N
    const parts: string[] = [];
    for (const g of groups) {
      for (const _name of g.names) {
        parts.push(g.typeLatex);
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
    if (['Equal', 'Leq', 'LessThan', 'Void', 'DecEq', 'Limit', 'DPair'].includes(name)) return true;
    // Our wrappers for relations
    if (['rle', 'rlt'].includes(name)) return true;
    // Record field projections that are relations (e.g. CompleteOrderedField.le)
    if (name.endsWith('.le') || name.endsWith('.lt')) return true;
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
 */
function detectTransChain(term: TTKTerm): TransStep[] | null {
  const spine = extractAppSpine(term);
  if (spine.fn.tag !== 'Const' || spine.fn.name !== 'trans') return null;
  if (spine.args.length < 6) return null;

  const [_A, x, y, z, proofXY, proofYZ] = spine.args;

  // Check if proofYZ is itself a trans (recursive chain)
  const rest = detectTransChain(proofYZ);
  if (rest) {
    return [{ lhs: x, rhs: y, justification: proofXY }, ...rest];
  }

  return [
    { lhs: x, rhs: y, justification: proofXY },
    { lhs: y, rhs: z, justification: proofYZ },
  ];
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
 * Short description of a proof justification for equational chain annotations.
 * Tries to be concise: "refl", "sym(plusZeroRight(m))", "cong_S(IH)", etc.
 */
function describeJustification(term: TTKTerm, context: string[], notations: NotationTable): string {
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

    // trans: {A} x y z proof_xy proof_yz — show as chain or concise
    if (name === 'trans' && spine.args.length >= 6) {
      const p1 = describeJustification(spine.args[4], context, notations);
      const p2 = describeJustification(spine.args[5], context, notations);
      return `\\text{trans}(${p1},\\, ${p2})`;
    }

    // cong: {A} {B} x y f proof — show function and proof
    if (name === 'cong' && spine.args.length >= 6) {
      const f = termToLatex(spine.args[4], context, notations);
      const inner = describeJustification(spine.args[5], context, notations);
      return `\\text{cong}(${f},\\, ${inner})`;
    }

    // replace: {A} x y P proof px — show predicate and proof
    if (name === 'replace' && spine.args.length >= 6) {
      const P = termToLatex(spine.args[3], context, notations);
      const proof = describeJustification(spine.args[4], context, notations);
      const px = describeJustification(spine.args[5], context, notations);
      return `\\text{subst}(${P},\\, ${proof},\\, ${px})`;
    }

    // Check if notation table handles this term — let it render cleanly
    const entry = notations.get(name);
    if (entry) {
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
    // Show up to 3 args concisely
    const argStrs = visibleArgs.slice(0, 3).map(a => termToLatex(a, context, notations));
    const suffix = visibleArgs.length > 3 ? ',\\ldots' : '';
    return `${nameLatex}(${argStrs.join(',\\,')}${suffix})`;
  }

  // Variable reference
  if (term.tag === 'Var' && term.index < context.length) {
    return renderVarName(context[term.index]);
  }

  // Lambda — describe briefly
  if (term.tag === 'Binder' && term.binderKind.tag === 'BLam') {
    return `\\lambda\\text{-term}`;
  }

  // Fallback: render the term (may be verbose)
  return termToLatex(term, context, notations);
}

/**
 * Render a trans chain as a KaTeX aligned equational proof.
 */
function renderTransChain(steps: TransStep[], context: string[], notations: NotationTable): string {
  const lines: string[] = [];
  for (let i = 0; i < steps.length; i++) {
    const step = steps[i];
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

/**
 * Render the RHS of a match clause (a proof body) as blocks.
 * Detects trans chains, sym, simple terms, or falls back to termToLatex.
 */
function proofBodyToBlocks(
  term: TTKTerm,
  context: string[],
  notations: NotationTable,
  indent: string,
  carrierPositions?: Map<number, string>,
): LatexBlock[] {
  // Strip any remaining lambdas (e.g. "intros m p" inside a case)
  const { body: current, context: ctx } = stripLambdasWithCarrier(term, context);

  // Nested Match → render as nested cases
  if (current.tag === 'Match') {
    return renderMatchProof(current, ctx, notations, carrierPositions);
  }

  // Try trans chain
  const chain = detectTransChain(current);
  if (chain) {
    return [{ kind: 'rule', latex: `${indent}${renderTransChain(chain, ctx, notations)}` }];
  }

  // Simple proof term — render concisely as justification
  const desc = describeJustification(current, ctx, notations);
  return [{ kind: 'rule', latex: `${indent}${desc}` }];
}

/**
 * Render a Match node as induction/cases proof.
 * carrierPositions maps Pi-binder indices to carrier LaTeX for suppression.
 */
function renderMatchProof(
  matchTerm: TTKTerm & { tag: 'Match' },
  context: string[],
  notations: NotationTable,
  carrierPositions?: Map<number, string>,
): LatexBlock[] {
  const blocks: LatexBlock[] = [];

  // Determine what we're inducting on
  const scrutineeLatex = matchTerm.scrutinee.tag === 'Var' && matchTerm.scrutinee.index < context.length
    ? escapeLaTeX(context[matchTerm.scrutinee.index])
    : termToLatex(matchTerm.scrutinee, context, notations);

  blocks.push({ kind: 'comment', latex: `\\textit{Proof.}\\;\\text{By induction on } ${scrutineeLatex}\\text{:}` });

  for (const clause of matchTerm.clauses) {
    // Build context and case header, suppressing carrier-position patterns
    const ctxEntries: string[] = [];
    const visiblePatParts: string[] = [];

    for (let pi = 0; pi < clause.patterns.length; pi++) {
      const pat = clause.patterns[pi];
      const carrierLatex = carrierPositions?.get(pi);
      const vars = collectPatternVars([pat]);

      if (carrierLatex) {
        // Carrier position — substitute in context, suppress from display
        for (const _v of vars) {
          ctxEntries.push(LATEX_PREFIX + carrierLatex);
        }
      } else {
        visiblePatParts.push(patternToLatex(pat, notations));
        ctxEntries.push(...vars);
      }
    }

    const clauseCtx = [...ctxEntries.reverse(), ...context];

    // Case header: render visible patterns only
    if (visiblePatParts.length > 0) {
      const patLatex = visiblePatParts.join('\\;');
      blocks.push({ kind: 'rule', latex: `\\textbf{Case}\\;${patLatex}\\text{:}` });
    }

    // Render the RHS proof
    const rhsBlocks = proofBodyToBlocks(clause.rhs, clauseCtx, notations, '\\quad ', carrierPositions);
    blocks.push(...rhsBlocks);
  }

  return blocks;
}

/**
 * Main entry: convert a proof term into LaTeX blocks.
 * Strips outer lambdas, then dispatches on Match / trans / simple.
 */
function proofToLatex(
  term: TTKTerm,
  context: string[],
  notations: NotationTable,
  carrierPositions?: Map<number, string>,
): LatexBlock[] {
  // Strip outer lambdas, detecting carrier types
  const { body: current, context: ctx } = stripLambdasWithCarrier(term, context);

  // Match → induction
  if (current.tag === 'Match') {
    return renderMatchProof(current, ctx, notations, carrierPositions);
  }

  // Trans chain at top level
  const chain = detectTransChain(current);
  if (chain) {
    return [
      { kind: 'comment', latex: '\\textit{Proof.}' },
      { kind: 'rule', latex: renderTransChain(chain, ctx, notations) },
    ];
  }

  // Sym wrapping something
  const symMatch = detectSym(current);
  if (symMatch) {
    const inner = describeJustification(symMatch.inner, ctx, notations);
    return [{ kind: 'comment', latex: `\\textit{Proof.}\\quad\\text{sym}(${inner})` }];
  }

  // Simple proof (refl, single application, etc.)
  const desc = describeJustification(current, ctx, notations);
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
    const { binders, body } = extractPiSpine(decl.kernelType);
    const isPropLike = binders.length > 0 && looksLikeProp(body, binders.length);

    if (isPropLike) {
      // "Theorem (name). Let ... and ... . Then:" + boxed conclusion
      const { groups, finalCtx } = buildBinderGroups(binders, [], notations);
      const bodyLatex = termToLatex(body, finalCtx, notations);
      const binderParts = groups.map(formatBinderGroup);

      if (binderParts.length > 0) {
        const bindersStr = binderParts.join('\\text{ and }');
        blocks.push({ kind: 'header', latex: `\\textbf{Theorem}\\;(${nameLatex})\\text{. Let } ${bindersStr}\\text{. Then:}` });
      } else {
        blocks.push({ kind: 'header', latex: `\\textbf{Theorem}\\;(${nameLatex})\\text{:}` });
      }
      blocks.push({ kind: 'rule', latex: `\\boxed{\\displaystyle ${bodyLatex}}` });
    } else {
      // Non-propositional: simple "name : type" format
      const typeStr = typeToLatex(decl.kernelType, [], notations);
      blocks.push({ kind: 'header', latex: `\\textbf{Theorem}\\;${nameLatex} : ${typeStr}` });
    }
  }

  // Render proof body from kernel value
  if (decl.kernelValue) {
    const proofBlocks = proofToLatex(decl.kernelValue, [], notations, carrierPositions);
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
