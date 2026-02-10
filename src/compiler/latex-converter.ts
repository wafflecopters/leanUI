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

  // DPair
  table.set('DPair', { kind: 'custom', render: (args, ctx, n) => {
    if (args.length === 2) {
      return `\\Sigma\\;(${termToLatex(args[0], ctx, n)})\\;(${termToLatex(args[1], ctx, n)})`;
    }
    return '\\Sigma';
  }});
  table.set('MkDPair', { kind: 'custom', render: (args, ctx, n) => {
    // {A} {fn} fst snd — skip 2 implicits
    const visible = args.slice(2);
    if (visible.length >= 2) {
      return `\\langle ${termToLatex(visible[0], ctx, n)},\\, ${termToLatex(visible[1], ctx, n)} \\rangle`;
    }
    return '\\text{MkDPair}';
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

  // ---- Real Analysis notations ----
  // All operations take (R : Real) as first arg — skip it in rendering.

  // Field operations on reals: radd R x y → x + y
  table.set('radd', { kind: 'infix', latex: '+', arity: 3, skipArgs: [0] });
  table.set('rmul', { kind: 'infix', latex: '\\cdot', arity: 3, skipArgs: [0] });
  table.set('rsub', { kind: 'infix', latex: '-', arity: 3, skipArgs: [0] });
  table.set('rzero', { kind: 'prefix', latex: '0', arity: 1, skipArgs: [0] });
  table.set('rone', { kind: 'prefix', latex: '1', arity: 1, skipArgs: [0] });
  table.set('rneg', { kind: 'prefix', latex: '-', arity: 2, skipArgs: [0] });

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
      const f = termToLatex(args[1], ctx, n);
      const x0 = termToLatex(args[2], ctx, n);
      const lVal = termToLatex(args[3], ctx, n);
      return `\\lim_{x \\to ${x0}} ${f}(x) = ${lVal}`;
    }
    return '\\text{Limit}';
  }});

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
        return escapeLaTeX(context[term.index]);
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
      const domain = termToLatex(term.domain, context, notations);
      const newCtx = [term.name, ...context];
      const body = termToLatex(term.body, newCtx, notations);
      const isAnon = term.name === '_' || term.name === '';

      switch (term.binderKind.tag) {
        case 'BPi':
          if (isAnon || !occursIn(0, term.body)) {
            return `${domain} \\to ${body}`;
          }
          return `\\Pi\\, (${escapeLaTeX(term.name)} : ${domain}),\\, ${body}`;

        case 'BLam':
          if (isAnon) {
            return `\\lambda\\, \\_ .\\, ${body}`;
          }
          return `\\lambda\\, ${escapeLaTeX(term.name)} .\\, ${body}`;

        case 'BLet': {
          const defVal = termToLatex(term.binderKind.defVal, context, notations);
          return `\\text{let } ${escapeLaTeX(term.name)} := ${defVal} \\text{ in } ${body}`;
        }
      }
      break; // unreachable but satisfies TS
    }

    case 'App': {
      // Render as f(a, b, c) math-style instead of juxtaposition
      const spine = extractAppSpine(term);
      const fnStr = termToLatex(spine.fn, context, notations);
      const argsStr = spine.args.map(a => termToLatex(a, context, notations)).join(',\\, ');
      return `${fnStr}(${argsStr})`;
    }

    case 'Hole':
      return `?_{${term.id}}`;

    case 'Meta':
      return `?_{${term.id}}`;

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
        const inner = visible.map(a => termToLatex(a, context, notations)).join(',\\,');
        const extra = args.slice(entry.arity);
        let result = `${entry.latex}(${inner})`;
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
      return escapeLaTeX(pattern.name);
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
export function typeToLatex(term: TTKTerm, context: string[], notations: NotationTable): string {
  const { binders, body } = extractPiSpine(term);

  if (binders.length === 0) {
    return termToLatex(term, context, notations);
  }

  // Determine if this looks like a proposition (returns a type that could be a proof)
  // Heuristic: if the body contains Equal, Leq, Void, or is a Type-valued thing, use ∀
  const isPropLike = looksLikeProp(body, binders.length);

  // Group consecutive binders with same rendered type
  const groups: { names: string[]; typeLatex: string }[] = [];
  let runningCtx = [...context];

  for (let i = 0; i < binders.length; i++) {
    const b = binders[i];
    const typeLatex = termToLatex(b.type, runningCtx, notations);
    runningCtx = [b.name, ...runningCtx];

    const lastGroup = groups[groups.length - 1];
    if (lastGroup && lastGroup.typeLatex === typeLatex) {
      lastGroup.names.push(b.name);
    } else {
      groups.push({ names: [b.name], typeLatex });
    }
  }

  const bodyLatex = termToLatex(body, runningCtx, notations);

  if (isPropLike) {
    // ∀ n m : N, p : N, body
    const binderParts = groups.map(g => {
      const names = g.names.map(escapeLaTeX).join('\\, ');
      return `${names} : ${g.typeLatex}`;
    });
    return `\\forall\\, ${binderParts.join(',\\; ')},\\; ${bodyLatex}`;
  } else {
    // Arrow style: N → N → N
    const parts: string[] = [];
    for (const g of groups) {
      for (const name of g.names) {
        // If the variable is used in the body, show as dependent
        // For simplicity, use arrow notation for function types
        parts.push(g.typeLatex);
      }
    }
    parts.push(bodyLatex);
    return parts.join(' \\to ');
  }
}

/**
 * Heuristic: does the body of a Pi look like a proposition?
 * Check for common propositional forms: Equal, Leq, Void, DPair, etc.
 */
function looksLikeProp(body: TTKTerm, depth: number): boolean {
  const spine = extractAppSpine(body);
  if (spine.fn.tag === 'Const') {
    const name = spine.fn.name;
    if (['Equal', 'Leq', 'LessThan', 'Void', 'DecEq'].includes(name)) return true;
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

    // Named lemma applied to visible args
    // Skip implicit args (heuristic: args that are Meta, or look like types)
    const visibleArgs = spine.args.filter(a =>
      a.tag !== 'Meta' && a.tag !== 'Sort' && !(a.tag === 'Const' && notations.get(a.name)?.kind === 'const' && ['\\mathbb{N}', '\\text{Type}'].includes((notations.get(a.name) as any)?.latex))
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
    return escapeLaTeX(context[term.index]);
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
 * Render the RHS of a match clause (a proof body) as blocks.
 * Detects trans chains, sym, simple terms, or falls back to termToLatex.
 */
function proofBodyToBlocks(
  term: TTKTerm,
  context: string[],
  notations: NotationTable,
  indent: string,
): LatexBlock[] {
  // Strip any remaining lambdas (e.g. "intros m p" inside a case)
  let current = term;
  const extraNames: string[] = [];
  while (current.tag === 'Binder' && current.binderKind.tag === 'BLam') {
    extraNames.push(current.name);
    current = current.body;
  }
  const ctx = [...extraNames.reverse(), ...context];

  // Nested Match → render as nested cases
  if (current.tag === 'Match') {
    return renderMatchProof(current, ctx, notations);
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
 */
function renderMatchProof(
  matchTerm: TTKTerm & { tag: 'Match' },
  context: string[],
  notations: NotationTable,
): LatexBlock[] {
  const blocks: LatexBlock[] = [];

  // Determine what we're inducting on
  const scrutineeLatex = matchTerm.scrutinee.tag === 'Var' && matchTerm.scrutinee.index < context.length
    ? escapeLaTeX(context[matchTerm.scrutinee.index])
    : termToLatex(matchTerm.scrutinee, context, notations);

  blocks.push({ kind: 'comment', latex: `\\textit{Proof.}\\;\\text{By induction on } ${scrutineeLatex}\\text{:}` });

  for (const clause of matchTerm.clauses) {
    const patVars = collectPatternVars(clause.patterns);
    const clauseCtx = [...patVars.reverse(), ...context];

    // Case header: render the pattern
    const patLatex = clause.patterns.map(p => patternToLatex(p, notations)).join('\\;');
    blocks.push({ kind: 'rule', latex: `\\textbf{Case}\\;${patLatex}\\text{:}` });

    // Render the RHS proof
    const rhsBlocks = proofBodyToBlocks(clause.rhs, clauseCtx, notations, '\\quad ');
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
): LatexBlock[] {
  // Strip outer lambdas (from intro tactic)
  let current = term;
  const lambdaNames: string[] = [];
  while (current.tag === 'Binder' && current.binderKind.tag === 'BLam') {
    lambdaNames.push(current.name);
    current = current.body;
  }
  const ctx = [...lambdaNames.reverse(), ...context];

  // Match → induction
  if (current.tag === 'Match') {
    return renderMatchProof(current, ctx, notations);
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
  return 'definition';
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
        paramParts.push(`(${escapeLaTeX(p.name)} : ${termToLatex(p.type, ctx, notations)})`);
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
        const patVars = collectPatternVars(clause.patterns);
        const clauseCtx = [...patVars.reverse()];
        const lhsPats = clause.patterns.map(p => patternToLatex(p, notations)).join('\\;');
        const rhs = termToLatex(clause.rhs, clauseCtx, notations);
        blocks.push({ kind: 'rule', latex: `${nameLatex}\\;${lhsPats} = ${rhs}` });
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

  // Header: Theorem name : ∀ ...
  if (decl.kernelType) {
    const typeStr = typeToLatex(decl.kernelType, [], notations);
    blocks.push({ kind: 'header', latex: `\\textbf{Theorem}\\;${nameLatex} : ${typeStr}` });
  }

  // Render proof body from kernel value
  if (decl.kernelValue) {
    const proofBlocks = proofToLatex(decl.kernelValue, [], notations);
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
