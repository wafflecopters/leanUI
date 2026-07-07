/**
 * Lean `CodeWithInfos` → `MathRow` converter.
 *
 * This is the M3 producer that replaces the old TT `surfaceTypeToMathRow`: it
 * turns Lean's tagged pretty-printed expressions into the math editor's MathRow
 * model, so the WYSIWYG renders real Lean expressions. The whole math editor
 * (render / edit / navigate / source round-trip) is reused unchanged — only the
 * thing that *produces* a MathRow is new.
 *
 * Input shape (emitted by lean/Extract.lean's `ttToJson`, mirroring
 * `Lean.Widget.TaggedText SubexprInfo`):
 *
 *   text   → { t: 'text', s: string }
 *   append → { t: 'append', kids: TaggedJson[] }
 *   tag    → { t: 'tag', pos: string, child: TaggedJson }   // pos = SubExpr.Pos
 *
 * Each `tag` is a subexpression; we wrap its rendered nodes in a `Group` whose
 * htmlId encodes the subexpr position, so the proof-tree UI can target subterms
 * for click-to-rewrite — the same mechanism the TT path used.
 */
import {
  mkGroup,
  mkRow,
  mkSymbol,
  mkFrac,
  mkSup,
  mkSub,
  mkBigOp,
  mkText,
  type GroupNode,
  type MathNode,
  type MathRow,
  type SymbolNode,
} from '../math-editor/types';
import { renderStaticLatex } from '../math-editor/render';
import type { TaggedText } from './types';

// ── wire format ────────────────────────────────────────────────────────────

/** @deprecated use TaggedText from ./types — kept as an alias for existing imports. */
export type TaggedJson = TaggedText;

/** Prefix for subexpression-group htmlIds, so they're recognizable downstream. */
export const SUBEXPR_HTML_PREFIX = 'subexpr:';

// ── Lean unicode → LaTeX, only where KaTeX needs it ─────────────────────────
// The renderer already maps Greek letters and passes single chars / `\cmd`
// through. We only need to translate the operator/relation glyphs that KaTeX
// won't accept raw. Anything not listed falls through unchanged (handled by the
// renderer's symbol rules), which keeps this table small and generic.
const UNICODE_TO_LATEX: Record<string, string> = {
  '→': '\\to',
  '↔': '\\iff',
  '⟶': '\\longrightarrow',
  '∀': '\\forall',
  '∃': '\\exists',
  '¬': '\\neg',
  '∧': '\\wedge',
  '∨': '\\vee',
  '≤': '\\leq',
  '≥': '\\geq',
  '≠': '\\neq',
  '∈': '\\in',
  '∉': '\\notin',
  '⊆': '\\subseteq',
  '⊂': '\\subset',
  '∪': '\\cup',
  '∩': '\\cap',
  '×': '\\times',
  '·': '\\cdot',
  '∘': '\\circ',
  '≡': '\\equiv',
  '≈': '\\approx',
  '∼': '\\sim',
  '∅': '\\emptyset',
  '↦': '\\mapsto',
  '⊢': '\\vdash',
  '∑': '\\sum',
  '∏': '\\prod',
  '∫': '\\int',
  'ℕ': '\\mathbb{N}',
  'ℤ': '\\mathbb{Z}',
  'ℚ': '\\mathbb{Q}',
  'ℝ': '\\mathbb{R}',
  'ℂ': '\\mathbb{C}',
  '⊤': '\\top',
  '⊥': '\\bot',
};

/** Single chars that are their own symbol token and split runs around them. */
const PUNCT = new Set([
  '(', ')', '[', ']', '{', '}', ',', '+', '-', '=', '<', '>', '/', '*', ':', '|',
]);

function isSpace(ch: string): boolean {
  return ch === ' ' || ch === '\t' || ch === '\n';
}

function isWordChar(ch: string): boolean {
  // Identifier-ish: letters, digits, underscore, prime, dot (Nat.succ), and any
  // non-ASCII glyph not handled as an operator (subscripts, primes, etc.).
  if (UNICODE_TO_LATEX[ch] !== undefined || PUNCT.has(ch) || isSpace(ch)) return false;
  return true;
}

/**
 * Tokenize a run of Lean pretty-printed plain text into SymbolNodes.
 *
 * Strategy: greedily accumulate identifier/word characters into one symbol
 * (so `Nat.succ`, `x₀`, `foo` stay whole, which lets the renderer apply its
 * operatorname/subscript rules), and emit operators/punctuation as their own
 * one-char symbols (translated to LaTeX where needed). Whitespace is dropped —
 * the renderer reinserts spacing around operators.
 */
export function tokenizeText(s: string): MathNode[] {
  const nodes: MathNode[] = [];
  let i = 0;
  const chars = Array.from(s); // codepoint-safe
  let word = '';
  const flush = () => {
    if (word.length > 0) {
      nodes.push(mkSymbol(word));
      word = '';
    }
  };
  while (i < chars.length) {
    const ch = chars[i];
    if (isSpace(ch)) {
      flush();
      i++;
      continue;
    }
    const latex = UNICODE_TO_LATEX[ch];
    if (latex !== undefined) {
      flush();
      nodes.push(mkSymbol(latex));
      i++;
      continue;
    }
    if (PUNCT.has(ch)) {
      flush();
      // `*` displays as the math centered dot `·` (the TT editor's convention);
      // other punctuation passes through. `/` and `^` stay literal here so the
      // structural pass can still recognize them as Frac/Sup operators.
      nodes.push(mkSymbol(ch === '*' ? '\\cdot' : ch));
      i++;
      continue;
    }
    // word character
    word += ch;
    i++;
  }
  flush();
  return nodes;
}

/** Is this node the bare operator symbol `op`? */
function isOpSymbol(n: MathNode, op: string): boolean {
  return n.tag === 'Symbol' && (n as SymbolNode).value === op;
}

/**
 * Rewrite leading dependent-Pi binders `( x y : T ) → …` into the mathematical
 * reading `∀ x, y ∈ T, …` (Lean prints `(n : Nat) → P n`; mathematicians read
 * `∀ n ∈ ℕ, P n` — the same convention the TT math editor used). The flat node
 * sequence for one binder is: `(`  <var…>  `:`  <type…>  `)`  `\to`  <rest>.
 * Variables are comma-separated and the binder TYPE is kept after `∈`.
 * Consecutive binder groups merge under ONE ∀, joined by "and":
 * `∀ f, g ∈ Carrier(R) → Carrier(R) and x0, L, M ∈ Carrier(R), <body>`.
 * Only fires on a leading `(` that is actually a binder (top-level `:` before
 * the matching `)` then `\to`).
 */
function recognizeForall(nodes: MathNode[]): MathNode[] | null {
  if (nodes.length === 0 || !isOpSymbol(nodes[0], '(')) return null;
  // Find the matching close paren for the opening one.
  let depth = 0;
  let close = -1;
  let colon = -1;
  for (let i = 0; i < nodes.length; i++) {
    if (isOpSymbol(nodes[i], '(')) depth++;
    else if (isOpSymbol(nodes[i], ')')) {
      depth--;
      if (depth === 0) { close = i; break; }
    } else if (depth === 1 && colon === -1 && isOpSymbol(nodes[i], ':')) {
      colon = i;
    }
  }
  // Must be `( var : type )` immediately followed by `\to`.
  if (close === -1 || colon === -1) return null;
  if (close + 1 >= nodes.length || !isOpSymbol(nodes[close + 1], '\\to')) return null;

  const varNodes = nodes.slice(1, colon); // between `(` and `:`
  const typeNodes = nodes.slice(colon + 1, close); // between `:` and `)`
  const rest = nodes.slice(close + 2); // after `) \to`
  if (varNodes.length === 0) return null;

  // f, g ∈ <type>
  const group: MathNode[] = [];
  varNodes.forEach((v, i) => {
    if (i > 0) group.push(mkSymbol(','));
    group.push(v);
  });
  group.push(mkSymbol('\\in'), ...typeNodes);

  const restConverted = recognizeForall(rest) ?? rest;

  // Merge a directly-following binder group into this ∀, joined by "and".
  // Inline case (no subterm wrappers): rest converted to [∀, …] right here.
  if (restConverted.length > 0 && isOpSymbol(restConverted[0], '\\forall')) {
    return [mkSymbol('\\forall'), ...group, mkText('and'), ...restConverted.slice(1)];
  }
  // Wrapped case: rest is one Group whose nested level already produced [∀, …]
  // bottom-up inside its tag — strip that ∀ but keep the Group (htmlId).
  if (restConverted.length === 1 && restConverted[0].tag === 'Group') {
    const g = restConverted[0] as GroupNode;
    if (g.children.length > 0 && isOpSymbol(g.children[0], '\\forall')) {
      return [mkSymbol('\\forall'), ...group, mkText('and'), mkGroup(g.htmlId, g.children.slice(1))];
    }
  }
  return [mkSymbol('\\forall'), ...group, mkSymbol(','), ...restConverted];
}

/**
 * Restructure a flat sibling list into structural math nodes, mirroring how the
 * old TT pipeline emitted real Frac/Sup/Sub/BigOp instead of flat text:
 *
 *   a / b      → FracNode(a, b)          (lowest precedence — split first)
 *   base ^ exp → SupNode(base, exp)
 *   base _ sub → SubNode(base, sub)
 *   ∑/∏/∫ body → BigOpNode(operator, …, body)
 *
 * We split on the FIRST occurrence (left-to-right) of the lowest-precedence
 * structural operator present, recursing into each side. Operators are the bare
 * symbols Lean's delaborator emits between tagged operands (` / `, ` ^ `, …),
 * which tokenizeText turns into single Symbol nodes.
 */
function restructure(nodes: MathNode[]): MathNode[] {
  if (nodes.length <= 1) return nodes;

  // Dependent Pi binders → ∀ (outermost; do before infix splits).
  const forall = recognizeForall(nodes);
  if (forall) return forall;

  // Fraction: a / b  (split on the first top-level `/`).
  const slash = nodes.findIndex((n) => isOpSymbol(n, '/'));
  if (slash > 0 && slash < nodes.length - 1) {
    const numer = restructure(nodes.slice(0, slash));
    const denom = restructure(nodes.slice(slash + 1));
    return [mkFrac(mkRow(numer), mkRow(denom))];
  }

  // Superscript: base ^ exp.
  const caret = nodes.findIndex((n) => isOpSymbol(n, '^'));
  if (caret > 0 && caret < nodes.length - 1) {
    const base = restructure(nodes.slice(0, caret));
    const exp = restructure(nodes.slice(caret + 1));
    return [mkSup(mkRow(base), mkRow(exp))];
  }

  // Subscript: base _ sub (Lean emits `_` as a symbol from tokenizeText).
  const under = nodes.findIndex((n) => isOpSymbol(n, '_'));
  if (under > 0 && under < nodes.length - 1) {
    const base = restructure(nodes.slice(0, under));
    const sub = restructure(nodes.slice(under + 1));
    return [mkSub(mkRow(base), mkRow(sub))];
  }

  // Big operator: ∑/∏/∫ … body — operator (already mapped to \sum etc.) is the
  // first node; the rest is the body. (No below/above unless emitted separately.)
  const bigOps: Record<string, 'sum' | 'prod' | 'int'> = {
    '\\sum': 'sum',
    '\\prod': 'prod',
    '\\int': 'int',
  };
  if (nodes[0].tag === 'Symbol' && bigOps[(nodes[0] as SymbolNode).value]) {
    const op = bigOps[(nodes[0] as SymbolNode).value];
    const body = restructure(nodes.slice(1));
    return [mkBigOp(op, null, null, mkRow(body))];
  }

  // Function application: a run of value atoms with no infix operator between
  // them is `head arg₁ arg₂ …` (juxtaposition = application in Lean). Render it
  // the mathematical way, `head(arg₁, arg₂, …)` — so `f x` shows as `f(x)`.
  if (nodes.length >= 2 && nodes.every(isAppAtom)) {
    const [head, ...args] = nodes;
    const inner: MathNode[] = [];
    args.forEach((a, i) => {
      if (i > 0) inner.push(mkSymbol(','));
      inner.push(a);
    });
    return [head, mkSymbol('('), ...inner, mkSymbol(')')];
  }

  return nodes;
}

/** Symbols that are operators/punctuation (NOT application operands). */
const APP_STOP = new Set([
  '+', '-', '=', '<', '>', '/', '*', ':', '|', ',', '(', ')', '[', ']', '{', '}', '^', '_', "'",
  '\\to', '\\cdot', '\\leq', '\\geq', '\\neq', '\\in', '\\notin', '\\wedge', '\\vee',
  '\\forall', '\\exists', '\\neg', '\\mapsto', '\\iff', '\\times', '\\circ', '\\equiv',
  '\\approx', '\\sim', '\\subseteq', '\\subset', '\\cup', '\\cap', '\\vdash', '\\longrightarrow',
]);

/** A node that can be a function-application operand (a value, not an operator). */
function isAppAtom(n: MathNode): boolean {
  if (n.tag === 'Symbol') return !APP_STOP.has((n as SymbolNode).value);
  return n.tag === 'Group' || n.tag === 'Frac' || n.tag === 'Sup' ||
    n.tag === 'Sub' || n.tag === 'SubSup' || n.tag === 'BigOp' ||
    n.tag === 'Delimiter' || n.tag === 'Accent';
}

/**
 * Recognize our summation notation `∑[ i , lo , hi ] body` and build a real
 * `BigOpNode` rendering as `\sum_{i = lo}^{hi} body`. Operates on the raw tagged
 * kids (before tokenization) where the `∑[`/`,`/`]` text leaves and the four
 * operand subtrees are still cleanly separated. Null if the shape doesn't match.
 */
function recognizeSum(kids: TaggedJson[], wrap: boolean): MathNode[] | null {
  if (kids.length === 0) return null;
  const first = kids[0];
  if (first.t !== 'text' || !first.s.includes('∑[')) return null;

  const operands: TaggedJson[] = [];
  let sawClose = false;
  for (let k = 1; k < kids.length; k++) {
    const kid = kids[k];
    if (kid.t === 'text') {
      if (kid.s.includes(']')) sawClose = true;
      continue;
    }
    operands.push(kid);
  }
  if (operands.length < 4 || !sawClose) return null;

  const [iVar, lo, hi, body] = operands;
  const below = mkRow([...nodesOf(iVar, wrap), mkSymbol('='), ...nodesOf(lo, wrap)]);
  const above = mkRow(nodesOf(hi, wrap));
  const bodyRow = mkRow(restructure(nodesOf(body, wrap)));
  return [mkBigOp('sum', below, above, bodyRow)];
}

// ── implication chains: `H₁ → H₂ → C` between PROPS reads `H₁ and H₂ ⟹ C` ──

/** Flatten a tagged subtree to its plain pretty-printed text. */
function plainText(tt: TaggedJson): string {
  switch (tt.t) {
    case 'text':
      return tt.s;
    case 'append':
      return tt.kids.map(plainText).join('');
    case 'tag':
      return plainText(tt.child);
  }
}

/** Generic proposition-shape test: the segment mentions a relation symbol
 *  (`=`, `≤`, `<`, `∈`, …). Distinguishes hypothesis chains (`lim… = L → …`)
 *  from FUNCTION types (`Carrier R → Carrier R`), which must keep their arrows
 *  — without any domain-specific names (kernel-purity rule). Lambda arrows
 *  (`=>`) are stripped first so `fun x => k` alone doesn't read as a prop. */
const RELATION_CHARS = /[=≠≤≥<>∈∉⊆⊂∣⊢]/u;
function isPropLike(seg: readonly TaggedJson[]): boolean {
  const text = seg.map(plainText).join('').replace(/=>/g, '');
  return RELATION_CHARS.test(text);
}

/** A text kid that is EXACTLY a top-level arrow separator (` → `). Binder
 *  levels print `) → ` / `} → ` and are deliberately not matched, so this
 *  only fires between whole antecedents/consequent. */
function isPureArrowText(k: TaggedJson): boolean {
  return k.t === 'text' && k.s.trim() === '→';
}

/**
 * Recognize a top-level implication chain `H₁ → H₂ → … → C` where EVERY
 * segment is proposition-like, and render it as `H₁ and H₂ and … ⟹ C` — the
 * mathematical reading of curried hypotheses. Lean pp nests the chain to the
 * right (`H₁ → (H₂ → C)` across tags), so we walk into lone tag/append RHSs to
 * collect all segments. Null when there's no pure arrow or any segment looks
 * like a type (function arrows stay arrows).
 */
function recognizeImplicationChain(kids: TaggedJson[], wrap: boolean): MathNode[] | null {
  const segs: TaggedJson[][] = [];
  let current: TaggedJson[] = kids;
  for (;;) {
    const i = current.findIndex(isPureArrowText);
    if (i === -1) {
      segs.push(current);
      break;
    }
    segs.push(current.slice(0, i));
    let rhs = current.slice(i + 1);
    // Descend across the right-nested pp structure (lone tag → its child;
    // lone append → its kids) so the whole chain flattens into segments.
    while (rhs.length === 1 && rhs[0].t === 'tag') rhs = [rhs[0].child];
    if (rhs.length === 1 && rhs[0].t === 'append') rhs = rhs[0].kids;
    current = rhs;
  }
  if (segs.length < 2) return null;
  if (segs.some((s) => s.length === 0) || !segs.every(isPropLike)) return null;

  const out: MathNode[] = [];
  segs.forEach((seg, i) => {
    if (i > 0) out.push(i === segs.length - 1 ? mkSymbol('\\implies') : mkText('and'));
    // Render each segment through nodesOf's append path so notation recognizers
    // (limit, ∑) still fire on segments the chain walk unwrapped from their tag.
    out.push(...nodesOf(seg.length === 1 ? seg[0] : { t: 'append', kids: seg }, wrap));
  });
  return out;
}

/** If a tagged operand is a lambda `fun bv => body`, return its bound-variable
 *  and body node-lists; else null. Lets the limit renderer show
 *  `\lim_{x → x0} (f x + g x)` from `Limit (fun x => f x + g x) x0 L`. */
function asLambda(tt: TaggedJson, wrap: boolean): { bv: MathNode[]; body: MathNode[] } | null {
  let node: TaggedJson = tt;
  if (node.t === 'tag') node = node.child;
  if (node.t !== 'append') return null;
  const kids = node.kids;
  if (!(kids[0]?.t === 'text' && /^\s*fun\b/.test(kids[0].s))) return null;
  const arrow = kids.findIndex((k) => k.t === 'text' && k.s.includes('=>'));
  if (arrow < 0) return null;
  // Drop the leading "fun " from the first text kid; bv = tags before `=>`.
  const bvKids = kids.slice(1, arrow);
  const bodyKids = kids.slice(arrow + 1);
  return {
    bv: restructure(bvKids.flatMap((k) => nodesOf(k, false))),
    body: restructure(bodyKids.flatMap((k) => nodesOf(k, wrap))),
  };
}

/**
 * Recognize the limit notation `lim⟦x0⟧ f = L` (from the Real-analysis preset's
 * `notation` for `Limit`) and render it as `\lim_{x → x0} f(x) = L`. Mirrors
 * `recognizeSum`: keys on the notation MARKER (`lim⟦`), not the `Limit`
 * definition name, so the generic renderer stays domain-agnostic. A lambda `f`
 * contributes its own bound variable + body; any other `f` is applied to a
 * fresh `x`. Null if the shape doesn't match.
 */
function recognizeLimit(kids: TaggedJson[], wrap: boolean): MathNode[] | null {
  const firstText = kids.find((k) => k.t === 'text');
  if (!firstText || firstText.t !== 'text' || !firstText.s.includes('lim⟦')) return null;
  const operands = kids.filter((k) => k.t === 'tag');
  if (operands.length < 3) return null;
  const x0 = operands[0];
  const f = operands[1];
  const L = operands[operands.length - 1];

  const lam = asLambda(f, wrap);
  const bvNodes = lam ? lam.bv : [mkSymbol('x')];
  const bodyNodes = lam
    ? lam.body
    : [...nodesOf(f, wrap), mkSymbol('('), mkSymbol('x'), mkSymbol(')')];

  const subscript = mkRow([...bvNodes, mkSymbol('\\to'), ...nodesOf(x0, wrap)]);
  const limNode = mkSub(mkRow([mkSymbol('\\lim')]), subscript);
  return [limNode, ...bodyNodes, mkSymbol('='), ...nodesOf(L, wrap)];
}

/**
 * Convert a tagged-text node into MathNodes (structurally enriched).
 *
 * `wrap` controls subexpression Group wrappers: TRUE for read-only views (each
 * subterm gets a `Group{htmlId}` for click-to-select), FALSE for the editable
 * MathEditor (Group htmlIds collide with the editor's `n-<id>` click protocol,
 * breaking cursor placement — so editors get a clean tree with no Group nodes).
 */
function nodesOf(tt: TaggedJson, wrap: boolean): MathNode[] {
  switch (tt.t) {
    case 'text':
      return restructure(tokenizeText(tt.s));
    case 'append': {
      const chain = recognizeImplicationChain(tt.kids, wrap);
      if (chain) return chain;
      const lim = recognizeLimit(tt.kids, wrap);
      if (lim) return lim;
      const sum = recognizeSum(tt.kids, wrap);
      if (sum) return sum;
      return restructure(tt.kids.flatMap((k) => nodesOf(k, wrap)));
    }
    case 'tag': {
      const inner = restructure(nodesOf(tt.child, wrap));
      if (inner.length === 0) return [];
      if (!wrap) return inner; // editable: no Group wrappers
      return [mkGroup(`${SUBEXPR_HTML_PREFIX}${tt.pos}`, inner)];
    }
  }
}

/**
 * Convert Lean `CodeWithInfos` JSON into a MathRow for the math editor.
 *
 * Pass `wrapSubterms: false` when seeding the INTERACTIVE editor (clean tree,
 * working cursor); default `true` wraps subterms in Group nodes for the
 * read-only click-to-select views.
 */
export function codeWithInfosToMathRow(tagged: TaggedJson, opts?: { wrapSubterms?: boolean }): MathRow {
  return mkRow(nodesOf(tagged, opts?.wrapSubterms ?? true));
}

/**
 * Render a Lean tagged expression directly to a LaTeX string, via the math
 * editor's own static renderer. Used where the existing UI contract expects a
 * LaTeX string (e.g. `NodeGoalInfo.goalLatex`, `TypedHypothesis.type`) rather
 * than a MathRow. Returns `fallback` if conversion/render fails.
 */
export function taggedToLatex(tagged: TaggedJson | undefined, fallback = ''): string {
  if (!tagged) return fallback;
  try {
    return renderStaticLatex(codeWithInfosToMathRow(tagged));
  } catch {
    return fallback;
  }
}
