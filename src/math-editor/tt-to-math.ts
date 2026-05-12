/**
 * Reverse conversion: TTerm (surface parse tree) → MathNode tree.
 *
 * Used to pre-fill the structured math editor from an existing parsed
 * type signature. Walks the TTerm Pi-spine, reverse-matches @syntax
 * patterns, and builds MathNode trees.
 */

import { TTerm, TPattern, shiftSurfaceTerm, occursInTT } from '../compiler/surface';
import { SyntaxRegistry, SyntaxEntry, PatternElement } from './syntax-registry';
import { renderStaticLatex } from './render';

/** Pretty-print a canonical RatLit. If `den` is a positive power of 10,
 *  format as a decimal (e.g., 928/5 reduces to ... actually no, prefer
 *  decimal when den ∈ {1, 2, 4, 5, 8, 10, 20, 25, 50, 100, ...}). For
 *  brevity we just check power-of-10 here. The integer case (den=1) only
 *  arises for signed integers — non-negative collapses to NatLit upstream. */
function prettyPrintRatLit(num: bigint, den: bigint): string {
  // den=1 → render as plain integer (no decimal point). Reached for
  // negative integer literals (positive ones become NatLit via mkRatLit).
  if (den === 1n) return num.toString();
  // Check if den is a higher power of 10 → decimal representation.
  let d = den;
  let dec = 0;
  while (d > 1n && d % 10n === 0n) { d = d / 10n; dec++; }
  if (d === 1n) {
    // It's `num / 10^dec`, render as decimal.
    const sign = num < 0n ? '-' : '';
    const abs = num < 0n ? -num : num;
    const s = abs.toString().padStart(dec + 1, '0');
    const intPart = s.slice(0, s.length - dec);
    const fracPart = s.slice(s.length - dec);
    return `${sign}${intPart}.${fracPart}`;
  }
  return `${num}/${den}`;
}
import {
  MathNode, MathRow,
  mkRow, mkSymbol, mkHole, mkSup, mkSub, mkBigOp, mkFrac, mkAccent, mkDelimiter, mkText, mkGroup,
} from './types';

/** Callback that wraps MathNode[] for a subterm with annotation (e.g., \htmlId). */
export type SubtermAnnotator = (nodes: MathNode[], term: TTerm, ctx: string[]) => MathNode[];

// ============================================================================
// Reverse Registry
// ============================================================================

export interface ReverseRegistry {
  sourceToVisual: Map<string, string>;   // "Nat" → "\\mathbb{N}"
  nameToEntry: Map<string, SyntaxEntry>; // "plus" → entry with pattern [$0, +, $1]
  /** Names that should be delta-reduced (unfolded) before rendering */
  unfoldNames: Set<string>;
}

/** Extract function name from a template string (first space-delimited token). */
function templateFunctionName(template: string): string {
  const firstSpace = template.indexOf(' ');
  return firstSpace >= 0 ? template.slice(0, firstSpace) : template;
}

export function buildReverseRegistry(registry: SyntaxRegistry): ReverseRegistry {
  const sourceToVisual = new Map<string, string>();
  const nameToEntry = new Map<string, SyntaxEntry>();
  const unfoldNames = new Set<string>();

  let r: SyntaxRegistry | undefined = registry;
  while (r) {
    for (const [symbol, { source }] of r.symbolMap) {
      if (!sourceToVisual.has(source)) {
        sourceToVisual.set(source, symbol);
      }
    }
    for (const entry of r.entries) {
      // Key by the function name in the template (e.g., "Equal" from "Equal {$$A} $$0 $$1")
      const fnName = templateFunctionName(entry.template);
      // Skip infix patterns where template starts with $ (not a function name)
      if (!fnName.startsWith('$') && !nameToEntry.has(fnName)) {
        nameToEntry.set(fnName, entry);
      }
    }
    if (r.unfoldNames) {
      for (const name of r.unfoldNames) {
        unfoldNames.add(name);
      }
    }
    r = r.parent;
  }

  return { sourceToVisual, nameToEntry, unfoldNames };
}

// ============================================================================
// Template Parsing — extract arg-to-capture mapping
// ============================================================================

export type TemplateSlot =
  | { kind: 'direct'; capture: string }
  | { kind: 'implicit'; capture: string }
  | { kind: 'lambda'; binderCapture: string; bodyCapture: string };

/**
 * Parse template slots from a template string.
 * E.g., "sum $$1 $$2 (\\$0 => $$3)" → [direct($1), direct($2), lambda($0, $3)]
 */
export function parseTemplateSlots(template: string): TemplateSlot[] {
  // Strip function name (first token)
  const firstSpace = template.indexOf(' ');
  if (firstSpace < 0) return [];
  let rest = template.slice(firstSpace).trim();

  const slots: TemplateSlot[] = [];
  while (rest.length > 0) {
    rest = rest.trimStart();
    if (rest.length === 0) break;

    // Implicit: {$$N} or {$N}
    const implicitMatch = rest.match(/^\{\$\$?(\w+)\}/);
    if (implicitMatch) {
      slots.push({ kind: 'implicit', capture: implicitMatch[1] });
      rest = rest.slice(implicitMatch[0].length);
      continue;
    }

    // Lambda: (\\...$N => $$M) — manual parsing to handle variable backslashes
    if (rest.startsWith('(')) {
      const lambdaResult = tryParseLambdaSlot(rest);
      if (lambdaResult) {
        slots.push(lambdaResult.slot);
        rest = rest.slice(lambdaResult.consumed);
        continue;
      }
    }

    // Direct: $$N or $N
    const directMatch = rest.match(/^\$\$?(\w+)/);
    if (directMatch) {
      slots.push({ kind: 'direct', capture: directMatch[1] });
      rest = rest.slice(directMatch[0].length);
      continue;
    }

    // Skip unknown character
    rest = rest.slice(1);
  }

  return slots;
}

/** Try to parse a lambda slot like (\$N => $$M) from the start of `s`. */
function tryParseLambdaSlot(s: string): { slot: TemplateSlot; consumed: number } | null {
  // Skip '('
  let j = 1;
  // Skip any leading backslashes
  while (j < s.length && s[j] === '\\') j++;
  // Expect '$'
  if (j >= s.length || s[j] !== '$') return null;
  j++; // skip $
  // Read binder capture name
  let binderName = '';
  while (j < s.length && /\w/.test(s[j])) { binderName += s[j]; j++; }
  if (!binderName) return null;
  // Skip whitespace
  while (j < s.length && s[j] === ' ') j++;
  // Expect '=>'
  if (s.slice(j, j + 2) !== '=>') return null;
  j += 2;
  // Skip whitespace
  while (j < s.length && s[j] === ' ') j++;
  // Read body capture: $$M or $M
  if (j >= s.length || s[j] !== '$') return null;
  j++; // skip first $
  if (j < s.length && s[j] === '$') j++; // skip optional second $
  let bodyName = '';
  while (j < s.length && /\w/.test(s[j])) { bodyName += s[j]; j++; }
  if (!bodyName) return null;
  // Expect ')'
  if (j >= s.length || s[j] !== ')') return null;
  j++; // skip )

  return {
    slot: { kind: 'lambda', binderCapture: binderName, bodyCapture: bodyName },
    consumed: j,
  };
}

// ============================================================================
// Pi-spine decomposition
// ============================================================================

export interface BinderInfo {
  names: string[];
  domain: TTerm;
  isImplicit: boolean;
}

/** Structural equality for TTerms (for grouping same-domain binders). */
function ttermStructuralEqual(a: TTerm, b: TTerm): boolean {
  if (a.tag !== b.tag) return false;
  switch (a.tag) {
    case 'Const': return (b as typeof a).name === a.name;
    case 'Var': return (b as typeof a).index === a.index;
    case 'Sort': return ttermStructuralEqual(a.level, (b as typeof a).level);
    case 'ULit': return (b as typeof a).n === a.n;
    case 'ULevel': case 'UOmega': return true;
    case 'App': {
      const bApp = b as typeof a;
      return ttermStructuralEqual(a.fn, bApp.fn) && ttermStructuralEqual(a.arg, bApp.arg);
    }
    default: return false;
  }
}

/** Check if a TTerm contains any Var references (used to prevent grouping across de Bruijn shifts). */
function domainHasVars(term: TTerm): boolean {
  switch (term.tag) {
    case 'Var': return true;
    case 'App': return domainHasVars((term as any).fn) || domainHasVars((term as any).arg);
    case 'Binder': return (term.domain ? domainHasVars(term.domain) : false) || domainHasVars(term.body);
    case 'Sort': return domainHasVars(term.level);
    case 'Annot': return domainHasVars(term.term) || domainHasVars(term.type);
    default: return false;
  }
}

export function decomposePiSpine(type: TTerm): { binders: BinderInfo[]; body: TTerm } {
  const binders: BinderInfo[] = [];
  let current = type;

  while (true) {
    if (current.tag === 'MultiBinder' && current.binderKind.tag === 'BPiTT') {
      binders.push({
        names: [...current.names],
        domain: current.domain,
        isImplicit: current.named === true,
      });
      current = current.body;
      continue;
    }

    if (current.tag === 'Binder' && current.binderKind.tag === 'BPiTT') {
      const isImplicit = current.named === true;
      const last = binders[binders.length - 1];

      // Group consecutive same-domain non-implicit binders.
      // Don't group anonymous ('_') binders — they're separate hypotheses.
      // Also only group when domain has no Var references (avoids de Bruijn shift confusion).
      if (last && !isImplicit && !last.isImplicit &&
          current.name !== '_' && !last.names.includes('_') &&
          current.domain && !domainHasVars(current.domain) &&
          ttermStructuralEqual(last.domain, current.domain)) {
        last.names.push(current.name);
      } else {
        binders.push({
          names: [current.name],
          domain: current.domain!,
          isImplicit,
        });
      }
      current = current.body;
      continue;
    }

    break;
  }

  return { binders, body: current };
}

// ============================================================================
// Carrier-parameterized constant symbols (render-only, not bidirectional)
// ============================================================================

/** Constants whose first arg is a carrier/Real parameter that should be suppressed. */
/** Nullary constants: first arg is carrier (suppressed), no other args. */
const CARRIER_CONST_SYMBOLS = new Map<string, string>([
  ['rzero', '0'],
  ['rone', '1'],
  ['rtwo', '2'],
  ['Carrier', '\\mathbb{R}'],
]);

/** Prefix operators: first arg may be carrier (suppressed), last arg is the operand. */
const CARRIER_PREFIX_OPS = new Map<string, string>([
  ['rneg', '-'],
]);

// ============================================================================
// Core conversion: TTerm → MathNode[]
// ============================================================================

function flattenApp(term: TTerm): { fn: TTerm; args: TTerm[] } {
  const args: TTerm[] = [];
  let current = term;
  while (current.tag === 'App') {
    args.unshift(current.arg);
    current = current.fn;
  }
  return { fn: current, args };
}

export function ttermToMathNodes(term: TTerm, rev: ReverseRegistry, ctx: string[], annotate?: SubtermAnnotator): MathNode[] {
  const raw = ttermToMathNodesRaw(term, rev, ctx, annotate);
  return annotate ? annotate(raw, term, ctx) : raw;
}

/** Core rendering logic — returns unannotated nodes for this level (children may be annotated). */
function ttermToMathNodesRaw(term: TTerm, rev: ReverseRegistry, ctx: string[], annotate?: SubtermAnnotator): MathNode[] {
  switch (term.tag) {
    case 'Const': {
      const visual = rev.sourceToVisual.get(term.name);
      if (visual) return [mkSymbol(visual)];
      return [mkSymbol(term.name)];
    }

    case 'Var': {
      const name = ctx[term.index];
      if (name) return [mkSymbol(name)];
      return [mkSymbol(`?v${term.index}`)];
    }

    case 'App': {
      // Beta-reduce lambda applications before rendering:
      // (\x => body)(arg) → render body with arg in context (visual substitution)
      if (term.fn.tag === 'Binder' && term.fn.binderKind.tag === 'BLamTT') {
        const argNodes = ttermToMathNodes(term.arg, rev, ctx, annotate);
        const argStr = renderStaticLatex(mkRow(argNodes));
        // Put the rendered arg as the "variable name" so Var(0) in body renders as the arg
        const bodyCtx = [argStr, ...ctx];
        return ttermToMathNodes(term.fn.body, rev, bodyCtx, annotate);
      }
      const { fn, args } = flattenApp(term);

      if (fn.tag === 'Const') {
        // Carrier-parameterized constants: suppress the carrier arg and render as a symbol.
        // E.g., rzero(R) → 0,  rone(R) → 1,  Carrier(R) → ℝ
        const carrierSymbol = CARRIER_CONST_SYMBOLS.get(fn.name);
        if (carrierSymbol !== undefined && args.length >= 1) {
          if (args.length === 1) return [mkSymbol(carrierSymbol)];
          const overflowNodes: MathNode[] = [];
          for (let i = 1; i < args.length; i++) {
            if (i > 1) overflowNodes.push(mkSymbol(','));
            overflowNodes.push(...ttermToMathNodes(args[i], rev, ctx, annotate));
          }
          return [mkSymbol(carrierSymbol), mkDelimiter('(', ')', mkRow(overflowNodes))];
        }

        // Carrier-parameterized prefix operators: suppress carrier, render as prefix + last arg.
        // E.g., rneg(R, c) → -(c),  rneg(c) → -(c)  (R may be implicit)
        const prefixOp = CARRIER_PREFIX_OPS.get(fn.name);
        if (prefixOp !== undefined && args.length >= 1) {
          const operand = args[args.length - 1];
          const operandNodes = ttermToMathNodes(operand, rev, ctx, annotate);
          // Wrap in parens if the operand is complex (multi-node = infix/app)
          if (operandNodes.length > 1) {
            return [mkSymbol(prefixOp), mkDelimiter('(', ')', mkRow(operandNodes))];
          }
          return [mkSymbol(prefixOp), ...operandNodes];
        }

        const entry = rev.nameToEntry.get(fn.name);
        if (entry) {
          const captures = buildCaptureMap(entry, args, rev, ctx, annotate);
          if (captures) {
            return buildFromPattern(entry.pattern, captures);
          }
        }

        // Fallback: f(a, b)
        const visual = rev.sourceToVisual.get(fn.name);
        const fnNode = visual ? mkSymbol(visual) : mkSymbol(fn.name);

        if (args.length === 0) return [fnNode];

        const argNodes: MathNode[] = [];
        for (let i = 0; i < args.length; i++) {
          if (i > 0) argNodes.push(mkSymbol(','));
          argNodes.push(...ttermToMathNodes(args[i], rev, ctx, annotate));
        }
        return [fnNode, mkDelimiter('(', ')', mkRow(argNodes))];
      }

      // Non-const function (e.g., variable applied to args)
      const fnNodes = ttermToMathNodes(fn, rev, ctx, annotate);
      if (args.length === 0) return fnNodes;

      const argNodes: MathNode[] = [];
      for (let i = 0; i < args.length; i++) {
        if (i > 0) argNodes.push(mkSymbol(','));
        argNodes.push(...ttermToMathNodes(args[i], rev, ctx, annotate));
      }
      return [...fnNodes, mkDelimiter('(', ')', mkRow(argNodes))];
    }

    case 'Binder': {
      if (term.binderKind.tag === 'BLamTT') {
        const lamName = chooseFreshName(term.name || 'x', ctx);
        const bodyCtx = [lamName, ...ctx];
        const bodyNodes = ttermToMathNodes(term.body, rev, bodyCtx, annotate);
        return [mkSymbol(lamName), mkSymbol('\\to'), ...bodyNodes];
      }
      if (term.binderKind.tag === 'BPiTT') {
        // Negation: A → Void renders as ¬A (or ¬(A) for complex A)
        if (term.body && term.body.tag === 'Const' && term.body.name === 'Void') {
          const domainNodes = term.domain ? ttermToMathNodes(term.domain, rev, ctx, annotate) : [mkHole()];
          const needsParens = term.domain && (
            term.domain.tag === 'Binder' ||
            (term.domain.tag === 'App' && term.domain.fn.tag === 'App') // multi-arg apps
          );
          if (needsParens) {
            return [mkSymbol('\\neg'), mkDelimiter('(', ')', mkRow(domainNodes))];
          }
          return [mkSymbol('\\neg'), ...domainNodes];
        }
        const domainNodes = term.domain ? ttermToMathNodes(term.domain, rev, ctx, annotate) : [mkHole()];
        const piName = (term.name && term.name !== '_') ? chooseFreshName(term.name, ctx) : term.name;
        const bodyCtx = [piName, ...ctx];
        const bodyNodes = ttermToMathNodes(term.body, rev, bodyCtx, annotate);
        // Named dependent binder: render as (name : domain) → body
        if (piName !== '_' && piName !== '' && occursInTT(0, term.body)) {
          return [
            mkDelimiter('(', ')', mkRow([mkSymbol(piName), mkSymbol(':'), ...domainNodes])),
            mkSymbol('\\to'), ...bodyNodes,
          ];
        }
        // Wrap domain in parens when it's a function type to avoid ambiguity
        // e.g., (A → C) → (B → C) → C, not A → C → B → C → C
        if (term.domain && term.domain.tag === 'Binder' && term.domain.binderKind.tag === 'BPiTT') {
          return [mkDelimiter('(', ')', mkRow(domainNodes)), mkSymbol('\\to'), ...bodyNodes];
        }
        return [...domainNodes, mkSymbol('\\to'), ...bodyNodes];
      }
      return [mkHole()];
    }

    case 'MultiBinder': {
      if (term.binderKind.tag === 'BPiTT') {
        const domainNodes = ttermToMathNodes(term.domain, rev, ctx, annotate);
        const bodyCtx = [...[...term.names].reverse(), ...ctx];
        const bodyNodes = ttermToMathNodes(term.body, rev, bodyCtx, annotate);
        return [...domainNodes, mkSymbol('\\to'), ...bodyNodes];
      }
      return [mkHole()];
    }

    case 'Sort':
      return [mkSymbol('Type')];

    case 'NatLit':
      // Numeric literal — render the BigInt value directly. Without this
      // case, NatLit fell through to the default branch and rendered as
      // □, e.g. \`@ofNat(R, NatLit 1)\` showed as \`@ofNat(R, □)\`.
      return [mkSymbol(term.value.toString())];

    case 'RatLit':
      // Rational literal — render as decimal when den is a power of 10
      // (the typical case for parsed decimals like 1.5 → 3/2 or 185.6 →
      // 928/5). Otherwise fall back to fraction form. Sign goes on the
      // numerator since canonical form has den > 0.
      return [mkSymbol(prettyPrintRatLit(term.num, term.den))];

    case 'Hole':
      return [mkHole()];

    case 'Annot':
      // Delegate to the annotated call (not raw) so the inner term gets its own annotation
      return ttermToMathNodes(term.term, rev, ctx, annotate);

    case 'Match': {
      const scrutNodes = term.scrutinee.tag === 'Hole'
        ? [] : [...ttermToMathNodes(term.scrutinee, rev, ctx, annotate), mkSymbol('\\,')];
      const clauseNodes: MathNode[] = [];
      for (let i = 0; i < term.clauses.length; i++) {
        if (i > 0) clauseNodes.push(mkSymbol('\\mid'));
        const clause = term.clauses[i];
        const patStr = clause.patterns.map(p => renderPattern(p)).join(',\\,');
        const patVars = collectTPatternVars(clause.patterns);
        const clauseCtx = [...[...patVars].reverse(), ...ctx];
        const rhsNodes = ttermToMathNodes(clause.rhs, rev, clauseCtx, annotate);
        clauseNodes.push(mkSymbol(patStr), mkSymbol('\\Rightarrow'), ...rhsNodes);
      }
      return [
        mkDelimiter('\\{', '\\}', mkRow([
          ...scrutNodes,
          ...clauseNodes,
        ])),
      ];
    }

    // The remaining tags (ULevel, ULit, UOmega, AbsurdMarker, WithClause,
    // TacticBlock) shouldn't appear in user-facing display: ULevel/UOmega/ULit
    // live inside Sort terms and are handled in the level pretty-printer;
    // AbsurdMarker only appears on RHS of pattern clauses; WithClause is
    // desugared during elaboration; TacticBlock is rewritten to its produced
    // term. If one slips through, render as □ so it's visible (and the
    // exhaustiveness check below catches missing tags at compile time).
    case 'ULevel':
    case 'ULit':
    case 'UOmega':
    case 'AbsurdMarker':
    case 'WithClause':
    case 'TacticBlock':
      return [mkHole()];

    default: {
      // Exhaustiveness check: TypeScript narrows `term` to `never` here. Adding
      // a new TTerm tag without a case above will produce a compile error,
      // preventing the silent □ regression that we hit twice with NatLit.
      const _exhaustive: never = term;
      void _exhaustive;
      return [mkHole()];
    }
  }
}

// ============================================================================
// Pattern rendering helpers (for Match display)
// ============================================================================

/** Render a TPattern to a string for display in match expressions. */
function renderPattern(p: TPattern): string {
  switch (p.tag) {
    case 'PVar': return p.name;
    case 'PWild': return '\\_';
    case 'PCtor': {
      if (p.args.length === 0) return p.name;
      return `${p.name}(${p.args.map(a => renderPattern(a)).join(', ')})`;
    }
  }
}

/** Collect bound variable names from patterns (in order). */
function collectTPatternVars(patterns: TPattern[]): string[] {
  const vars: string[] = [];
  for (const p of patterns) collectTPatternVarsInto(p, vars);
  return vars;
}

function collectTPatternVarsInto(p: TPattern, vars: string[]): void {
  switch (p.tag) {
    case 'PVar': vars.push(p.name); break;
    case 'PWild': vars.push('_'); break;
    case 'PCtor': for (const a of p.args) collectTPatternVarsInto(a, vars); break;
  }
}

// ============================================================================
// Helpers
// ============================================================================

/** Pick a fresh variable name not already in ctx. Tries base, then base2, base3, ... */
function chooseFreshName(base: string, ctx: string[]): string {
  if (!ctx.includes(base)) return base;
  for (let i = 2; ; i++) {
    const name = `${base}${i}`;
    if (!ctx.includes(name)) return name;
  }
}

// ============================================================================
// Capture map: map TTerm args to pattern capture names
// ============================================================================

function buildCaptureMap(
  entry: SyntaxEntry,
  args: TTerm[],
  rev: ReverseRegistry,
  ctx: string[],
  annotate?: SubtermAnnotator,
): Map<string, MathNode[]> | null {
  const slots = parseTemplateSlots(entry.template);
  const captures = new Map<string, MathNode[]>();
  // Count direct + lambda slots (args that need to be consumed)
  const consumableSlots = slots.filter(s => s.kind === 'direct' || s.kind === 'lambda').length;
  const implicitSlots = slots.filter(s => s.kind === 'implicit').length;
  // When surface term has more args than consumable slots (implicit args present
  // from kernel→surface which doesn't strip them), skip leading args.
  // This handles both needsR carrier args and implicit universe params like {u} {v}.
  let argIdx = args.length > consumableSlots ? args.length - consumableSlots : 0;

  for (const slot of slots) {
    switch (slot.kind) {
      case 'implicit':
        // No corresponding surface arg — skip
        break;
      case 'direct':
        if (argIdx >= args.length) return null;
        captures.set(slot.capture, ttermToMathNodes(args[argIdx], rev, ctx, annotate));
        argIdx++;
        break;
      case 'lambda':
        if (argIdx >= args.length) return null;
        {
          const arg = args[argIdx];
          if (arg.tag === 'Binder' && arg.binderKind.tag === 'BLamTT') {
            const capName = chooseFreshName(arg.name || 'x', ctx);
            captures.set(slot.binderCapture, [mkSymbol(capName)]);
            const bodyCtx = [capName, ...ctx];
            captures.set(slot.bodyCapture, ttermToMathNodes(arg.body, rev, bodyCtx, annotate));
          } else {
            const binderName = chooseFreshName('x', ctx);
            captures.set(slot.binderCapture, [mkSymbol(binderName)]);
            const shiftedArg = shiftSurfaceTerm(1, arg, 0);
            const syntheticBody: TTerm = {
              tag: 'App',
              fn: shiftedArg,
              arg: { tag: 'Var', index: 0 },
            };
            const bodyCtx = [binderName, ...ctx];
            captures.set(slot.bodyCapture, ttermToMathNodes(syntheticBody, rev, bodyCtx, annotate));
          }
        }
        argIdx++;
        break;
    }
  }

  return captures;
}

// ============================================================================
// Operator precedence for parenthesization
// ============================================================================

const PREC_RELATION = 0;   // =, ≤, <, →, etc.
const PREC_ADDITIVE = 1;   // +, -
const PREC_MULTIPLICATIVE = 2; // ·, ×
const PREC_ATOM = 100;     // no infix operator

type Assoc = 'left' | 'right' | 'none';

const SYMBOL_PREC = new Map<string, number>([
  ['=', PREC_RELATION], ['\\le', PREC_RELATION], ['\\leq', PREC_RELATION],
  ['\\ge', PREC_RELATION], ['\\geq', PREC_RELATION],
  ['<', PREC_RELATION], ['>', PREC_RELATION],
  ['\\neq', PREC_RELATION], ['\\in', PREC_RELATION],
  ['\\to', PREC_RELATION], ['\\implies', PREC_RELATION],
  ['+', PREC_ADDITIVE], ['-', PREC_ADDITIVE],
  ['\\cdot', PREC_MULTIPLICATIVE], ['\\times', PREC_MULTIPLICATIVE],
]);

/** Associativity of infix operators. Default is 'left' if not listed. */
const SYMBOL_ASSOC = new Map<string, Assoc>([
  ['\\to', 'right'],
  ['\\implies', 'right'],
  // All arithmetic operators are left-associative by default
]);

/** Get the minimum precedence of top-level operators in a node array. */
function nodesMinPrec(nodes: readonly MathNode[]): number {
  let minPrec = PREC_ATOM;
  for (const n of nodes) {
    if (n.tag === 'Symbol') {
      const p = SYMBOL_PREC.get(n.value);
      if (p !== undefined && p < minPrec) minPrec = p;
    }
    // Look inside Group (htmlId annotation wrapper) to find operators
    if (n.tag === 'Group') minPrec = Math.min(minPrec, nodesMinPrec(n.children));
    // BigOp body extends ambiguously — treat as lowest arithmetic precedence
    if (n.tag === 'BigOp') minPrec = Math.min(minPrec, PREC_ADDITIVE - 1);
  }
  return minPrec;
}

/** Get the precedence of an infix pattern from its literal operators. */
function patternPrec(pattern: PatternElement[]): number {
  let minPrec = PREC_ATOM;
  for (const pe of pattern) {
    if (pe.tag === 'literal') {
      const p = SYMBOL_PREC.get(pe.symbol);
      if (p !== undefined && p < minPrec) minPrec = p;
    }
  }
  return minPrec;
}

/**
 * Check if a capture needs parens due to precedence or associativity.
 * @param position 'left' if this capture is to the LEFT of the infix op, 'right' if to the right.
 * @param patAssoc associativity of the pattern's operator.
 */
function captureNeedsWrap(
  nodes: MathNode[],
  patPrec: number,
  isFollowedByLiteral: boolean,
  position?: 'left' | 'right',
  patAssoc?: Assoc,
): boolean {
  const capPrec = nodesMinPrec(nodes);
  // Wrap if capture has strictly lower precedence than pattern operator
  if (capPrec < patPrec) return true;
  // Same precedence: wrap if associativity conflicts with position.
  // E.g., left-assoc +: a+(b+c) wraps RHS; right-assoc →: (a→b)→c wraps LHS.
  if (capPrec === patPrec && position) {
    const assoc = patAssoc ?? 'left';
    if (assoc === 'left' && position === 'right') return true;
    if (assoc === 'right' && position === 'left') return true;
  }
  // BigOp at end of capture followed by more content is always ambiguous
  if (isFollowedByLiteral && nodes.length > 0 && nodes[nodes.length - 1].tag === 'BigOp') return true;
  return false;
}

// ============================================================================
// Pattern → MathNode[] builder
// ============================================================================

export function buildFromPattern(pattern: PatternElement[], captures: Map<string, MathNode[]>): MathNode[] {
  const result: MathNode[] = [];
  const pPrec = patternPrec(pattern);
  // Find the infix operator's associativity (from the first literal in the pattern)
  const patOp = pattern.find(pe => pe.tag === 'literal' && SYMBOL_PREC.has(pe.symbol));
  const patAssoc: Assoc = patOp && patOp.tag === 'literal' ? (SYMBOL_ASSOC.get(patOp.symbol) ?? 'left') : 'left';
  // Find the index of the first literal to determine capture positions
  const firstLitIdx = pattern.findIndex(pe => pe.tag === 'literal' && SYMBOL_PREC.has(pe.symbol));

  for (let pi = 0; pi < pattern.length; pi++) {
    const pe = pattern[pi];
    switch (pe.tag) {
      case 'literal':
        result.push(mkSymbol(pe.symbol));
        break;

      case 'text':
        result.push(mkText(pe.content));
        break;

      case 'capture': {
        const nodes = captures.get(pe.name);
        if (nodes && nodes.length > 0) {
          const nextIsLit = pi + 1 < pattern.length && pattern[pi + 1].tag === 'literal';
          // Determine if this capture is left or right of the infix operator
          const position: 'left' | 'right' | undefined = firstLitIdx >= 0
            ? (pi < firstLitIdx ? 'left' : 'right')
            : undefined;
          if (pPrec < PREC_ATOM && captureNeedsWrap(nodes, pPrec, nextIsLit, position, patAssoc)) {
            result.push(mkDelimiter('(', ')', mkRow(nodes)));
          } else {
            result.push(...nodes);
          }
        } else {
          result.push(mkHole());
        }
        break;
      }

      case 'bigop': {
        const below = pe.below ? buildPatternRow(pe.below, captures) : null;
        const above = pe.above ? buildPatternRow(pe.above, captures) : null;
        const body = pe.body ? buildPatternRow(pe.body, captures) : mkRow([mkHole()]);
        const op = pe.operator as 'sum' | 'int' | 'prod' | 'lim';
        result.push(mkBigOp(op, below, above, body));
        break;
      }

      case 'frac': {
        const numer = buildPatternRow(pe.numer, captures);
        const denom = buildPatternRow(pe.denom, captures);
        result.push(mkFrac(numer, denom));
        break;
      }

      case 'delimiter': {
        const inner = buildPatternRow(pe.inner, captures);
        result.push(mkDelimiter(pe.open, pe.close, inner));
        break;
      }

      case 'accent': {
        const body = buildPatternRow(pe.body, captures);
        const accentType = pe.accent as 'vec' | 'hat' | 'bar' | 'tilde' | 'dot' | 'overline';
        result.push(mkAccent(accentType, body));
        break;
      }

      case 'sub': {
        // If all captures in the subscript are unbound (implicit), skip it
        if (allCapturesUnbound(pe.sub, captures)) {
          result.push(...buildFromPattern(pe.base, captures));
        } else {
          const base = buildBaseRow(pe.base, captures);
          const sub = buildPatternRow(pe.sub, captures);
          result.push(mkSub(base, sub));
        }
        break;
      }

      case 'sup': {
        if (allCapturesUnbound(pe.sup, captures)) {
          result.push(...buildFromPattern(pe.base, captures));
        } else {
          const base = buildBaseRow(pe.base, captures);
          const sup = buildPatternRow(pe.sup, captures);
          result.push(mkSup(base, sup));
        }
        break;
      }
    }
  }

  return result;
}

function buildPatternRow(elements: PatternElement[], captures: Map<string, MathNode[]>): MathRow {
  return mkRow(buildFromPattern(elements, captures));
}

/** Infix symbols that require parens when placed inside a sup/sub base. */
const INFIX_SYMBOLS = new Set([
  '+', '-', '=', '\\cdot', '\\times',
  '\\to', '\\leq', '\\geq', '\\neq', '\\in',
  '\\implies', '\\iff', '\\subset', '\\subseteq',
]);

/** Check if a list of MathNodes contains an infix operator (looks inside Groups). */
function containsInfix(nodes: readonly MathNode[]): boolean {
  return nodes.some(n =>
    n.tag === 'Symbol' ? INFIX_SYMBOLS.has(n.value) :
    n.tag === 'Group' ? containsInfix(n.children) :
    false
  );
}

/**
 * Build a MathRow for use as a sup/sub base, wrapping in parens if the
 * captured content contains infix operators. Without this, `Succ(a - b)`
 * would render as `a - b'` instead of `(a - b)'`.
 */
function buildBaseRow(elements: PatternElement[], captures: Map<string, MathNode[]>): MathRow {
  const nodes = buildFromPattern(elements, captures);
  if (containsInfix(nodes)) {
    return mkRow([mkDelimiter('(', ')', mkRow(nodes))]);
  }
  return mkRow(nodes);
}

/** Collect all capture names from a pattern element list. */
function collectCaptureNames(elements: PatternElement[]): string[] {
  const names: string[] = [];
  function walk(elems: PatternElement[]) {
    for (const e of elems) {
      switch (e.tag) {
        case 'capture': names.push(e.name); break;
        case 'sub': walk(e.base); walk(e.sub); break;
        case 'sup': walk(e.base); walk(e.sup); break;
        case 'bigop':
          if (e.below) walk(e.below);
          if (e.above) walk(e.above);
          if (e.body) walk(e.body);
          break;
        case 'frac': walk(e.numer); walk(e.denom); break;
        case 'delimiter': walk(e.inner); break;
        case 'accent': walk(e.body); break;
      }
    }
  }
  walk(elements);
  return names;
}

/**
 * Check if all captures in a pattern element list are unbound.
 * Returns true ONLY when there are captures and ALL are unbound.
 * Returns false when there are no captures (literal-only patterns should be kept).
 */
function allCapturesUnbound(elements: PatternElement[], captures: Map<string, MathNode[]>): boolean {
  const captureNames = collectCaptureNames(elements);
  if (captureNames.length === 0) return false; // no captures → keep the element
  return captureNames.every(name => !captures.has(name));
}

// ============================================================================
// Top-level: TTerm type → MathRow for structured editor
// ============================================================================

/** Check if a TTerm domain is a function type (Pi/arrow), e.g., Nat -> Nat. */
function domainIsFunctionType(domain: TTerm): boolean {
  if (domain.tag === 'Binder' && domain.binderKind.tag === 'BPiTT') return true;
  if (domain.tag === 'MultiBinder' && domain.binderKind.tag === 'BPiTT') return true;
  return false;
}

export function surfaceTypeToMathRow(type: TTerm, registry: SyntaxRegistry): MathRow {
  const rev = buildReverseRegistry(registry);
  const { binders, body } = decomposePiSpine(type);

  const nodes: MathNode[] = [];

  // Collect all binder names for context building
  const allNames: string[] = [];
  for (const b of binders) {
    for (const name of b.names) {
      allNames.push(name);
    }
  }

  // Full context for body: innermost-first (de Bruijn order)
  const fullCtx = [...allNames].reverse();

  let nonImplicitCount = 0;
  let namesSeenSoFar = 0;

  for (const b of binders) {
    if (b.isImplicit) {
      namesSeenSoFar += b.names.length;
      continue; // skip implicit binders
    }

    // Context for this binder's domain: names from previous binders only
    const domainCtx = allNames.slice(0, namesSeenSoFar);
    const domainCtxReversed = [...domainCtx].reverse();

    if (nonImplicitCount > 0) {
      nodes.push(mkText('and'));
    }

    const isAnonymous = b.names.every(n => n === '_');

    if (isAnonymous) {
      // Anonymous hypothesis: just the type expression
      const typeNodes = ttermToMathNodes(b.domain, rev, domainCtxReversed);
      nodes.push(...typeNodes);
    } else {
      // Named binder: ∀ n, m ∈ type
      nodes.push(mkSymbol('\\forall'));
      for (let j = 0; j < b.names.length; j++) {
        if (j > 0) nodes.push(mkSymbol(','));
        nodes.push(mkSymbol(b.names[j]));
      }
      // Use ":" for function-type domains (e.g., f : ℕ → ℕ), "∈" for simple types (e.g., n ∈ ℕ)
      nodes.push(mkSymbol(domainIsFunctionType(b.domain) ? ':' : '\\in'));
      const domainNodes = ttermToMathNodes(b.domain, rev, domainCtxReversed);
      nodes.push(...domainNodes);
    }

    namesSeenSoFar += b.names.length;
    nonImplicitCount++;
  }

  // Body
  if (nonImplicitCount > 0) {
    nodes.push(mkSymbol(','));
    nodes.push(mkText('then'));
  }

  const bodyNodes = ttermToMathNodes(body, rev, fullCtx);
  nodes.push(...bodyNodes);

  return mkRow(nodes);
}
