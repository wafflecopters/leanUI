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
  // Display cleanup: the preset's data-existential is spelled ∃' in SOURCE
  // (to coexist with core's Prop ∃), but reads as a plain quantifier.
  const chars = Array.from(s.replace(/∃'/g, '∃')); // codepoint-safe
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
    if (ch === '+' && chars[i + 1] === '+') {
      // List append `++` — one operator, typeset tight. Two separate `+`
      // symbols rendered as the baffling "pre +  + post".
      flush();
      nodes.push(mkSymbol('+\\!\\!+'));
      i += 2;
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
 * Drop a leading IMPLICIT binder `{ x : T } → rest`, returning the restructured
 * rest (which may strip further implicits / recognize ∀ in turn). Null when the
 * nodes don't start with an implicit-binder-then-arrow shape. Without this the
 * braces reach KaTeX as grouping and `{R : Real} → …` displays as the baffling
 * `R : Real → …`.
 */
function stripImplicitBinder(nodes: MathNode[]): MathNode[] | null {
  if (nodes.length === 0 || !isOpSymbol(nodes[0], '{')) return null;
  let depth = 0;
  let close = -1;
  let colon = -1;
  for (let i = 0; i < nodes.length; i++) {
    if (isOpSymbol(nodes[i], '{')) depth++;
    else if (isOpSymbol(nodes[i], '}')) {
      depth--;
      if (depth === 0) { close = i; break; }
    } else if (depth === 1 && colon === -1 && isOpSymbol(nodes[i], ':')) {
      colon = i;
    }
  }
  // Must be `{ var : type }` immediately followed by `\to` and a nonempty rest.
  if (close === -1 || colon === -1) return null;
  if (close + 1 >= nodes.length || !isOpSymbol(nodes[close + 1], '\\to')) return null;
  const rest = nodes.slice(close + 2);
  if (rest.length === 0) return null;
  return restructure(rest);
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
/** A top-level arrow chain in a ∀ body reads as prose: `A → B → C` becomes
 *  "A and B, then C" — the style the binder prose already uses. Heuristic:
 *  in a THEOREM body after binders, arrows are implications; a rare
 *  function-typed body would read oddly, which is the price of prose. */
function arrowChainToProse(body: MathNode[]): MathNode[] {
  // The tagged path wraps the body in a click-target Group; transform its
  // children and keep the id. (Verified the hard way: the plain-text path
  // worked while the real header kept its arrows.)
  if (body.length === 1 && body[0].tag === 'Group') {
    const g = body[0] as GroupNode;
    return [mkGroup(g.htmlId, arrowChainToProse([...g.children]))];
  }
  const segs: MathNode[][] = [];
  let cur: MathNode[] = [];
  let depth = 0;
  let inBar = false;
  for (const n of body) {
    if (n.tag === 'Symbol') {
      const v = (n as SymbolNode).value;
      if (v === '(' || v === '[' || v === '{' || v === '⟨') depth++;
      else if (v === ')' || v === ']' || v === '}' || v === '⟩') depth--;
      else if (v === '|') inBar = !inBar;
      else if (v === '\\to' && depth === 0 && !inBar) {
        segs.push(cur);
        cur = [];
        continue;
      }
    }
    cur.push(n);
  }
  segs.push(cur);
  // The tagged tree right-nests `A → (B → C)` in Groups: keep flattening the
  // LAST segment while it is a lone Group hiding more top-level arrows.
  while (segs.length >= 1) {
    const last = segs[segs.length - 1];
    if (last.length !== 1 || last[0].tag !== 'Group') break;
    const kids = (last[0] as GroupNode).children;
    let d = 0; let bar = false; let hasArrow = false;
    for (const k of kids) {
      if (k.tag !== 'Symbol') continue;
      const v = (k as SymbolNode).value;
      if (v === '(' || v === '[' || v === '{' || v === '⟨') d++;
      else if (v === ')' || v === ']' || v === '}' || v === '⟩') d--;
      else if (v === '|') bar = !bar;
      else if (v === '\\to' && d === 0 && !bar) { hasArrow = true; break; }
    }
    if (!hasArrow) break;
    const inner = arrowChainToProse([...kids]);
    // The recursive call returned "B and C, then D" style nodes — splice as
    // its own segments by re-splitting on the markers we just placed? No:
    // simpler and correct — replace the segment with the Group's children
    // and RE-RUN the whole split.
    return arrowChainToProse([
      ...segs.slice(0, -1).flatMap((sg, i) => (i > 0 ? [mkSymbol('\\to'), ...sg] : sg)),
      ...(segs.length > 1 ? [mkSymbol('\\to')] : []),
      ...kids,
    ]);
    void inner;
  }
  if (segs.length < 2 || segs.some((sg) => sg.length === 0)) return body;
  const out: MathNode[] = [];
  const premises = segs.slice(0, -1);
  premises.forEach((sg, i) => {
    if (i > 0) out.push(mkText('and'));
    out.push(...sg);
  });
  out.push(mkSymbol(','), mkText('then'), ...segs[segs.length - 1]);
  return out;
}

/** All Symbol values in a node list, recursing through containers. */
function collectSymbolValues(nodes: readonly MathNode[]): string[] {
  const out: string[] = [];
  for (const n of nodes) {
    if (n.tag === 'Symbol') out.push((n as SymbolNode).value);
    const kids = (n as { children?: readonly MathNode[] }).children;
    if (kids) out.push(...collectSymbolValues(kids));
  }
  return out;
}

/** Does any Symbol (recursively, through Groups/containers) match a name? */
function nodesMentionSymbol(nodes: readonly MathNode[], names: ReadonlySet<string>): boolean {
  for (const n of nodes) {
    if (n.tag === 'Symbol' && names.has((n as SymbolNode).value)) return true;
    const kids = (n as { children?: readonly MathNode[] }).children;
    if (kids && nodesMentionSymbol(kids, names)) return true;
    for (const key of ['num', 'den', 'base', 'sup', 'sub', 'body', 'below', 'above'] as const) {
      const part = (n as unknown as Record<string, { children?: readonly MathNode[] } | undefined>)[key];
      if (part?.children && nodesMentionSymbol(part.children, names)) return true;
    }
  }
  return false;
}

function recognizeForallTelescope(nodes: MathNode[]): MathNode[] | null {
  if (nodes.length === 0 || !isOpSymbol(nodes[0], '\\forall')) return null;
  let i = 1;
  const groups: Array<{ implicit: boolean; vars: MathNode[]; type: MathNode[] }> = [];
  while (i < nodes.length) {
    const open = nodes[i];
    const isImp = isOpSymbol(open, '{');
    const isExp = isOpSymbol(open, '(');
    if (!isImp && !isExp) break;
    const closeCh = isImp ? '}' : ')';
    let depth = 0;
    let close = -1;
    let colon = -1;
    for (let j = i; j < nodes.length; j++) {
      if (isOpSymbol(nodes[j], isImp ? '{' : '(')) depth++;
      else if (isOpSymbol(nodes[j], closeCh)) {
        depth--;
        if (depth === 0) { close = j; break; }
      } else if (depth === 1 && colon === -1 && isOpSymbol(nodes[j], ':')) colon = j;
    }
    if (close === -1 || colon === -1) return null;
    groups.push({
      implicit: isImp,
      vars: nodes.slice(i + 1, colon),
      type: nodes.slice(colon + 1, close),
    });
    i = close + 1;
  }
  if (groups.length === 0 || i >= nodes.length || !isOpSymbol(nodes[i], ',')) return null;
  const body = arrowChainToProse(restructure(nodes.slice(i + 1)));
  // An implicit binder is elided ONLY when its name never surfaces in the
  // displayed remainder. "∀ n ∈ ℕ … List(W) …" with no binder for W shows a
  // FREE variable — a paper introduces W before using it. The check runs on
  // the DISPLAYED tree, which is exactly the right criterion: RA's {R : Real}
  // stays hidden because its goals show ℝ (the unexpander consumed R), while
  // a W that survives into List(W) keeps its binder. Right-to-left, so a kept
  // binder's own type can pull in earlier ones (VectorSpace(K) keeps K).
  const kept: boolean[] = groups.map((g) => !g.implicit);
  for (let gi = groups.length - 1; gi >= 0; gi--) {
    if (kept[gi]) continue;
    // Tagged-path binder vars arrive wrapped in subexpr Groups — collect
    // Symbol names recursively, not just at the top level.
    const names = new Set(collectSymbolValues(groups[gi].vars));
    if (names.size === 0) continue;
    const visible: MathNode[] = [
      ...groups.filter((_, gj) => gj > gi && kept[gj]).flatMap((g) => [...g.vars, ...g.type]),
      ...body,
    ];
    if (nodesMentionSymbol(visible, names)) kept[gi] = true;
  }
  const explicit = groups.filter((_, gi) => kept[gi]);
  if (explicit.length === 0) return body;
  const out: MathNode[] = [mkSymbol('\\forall')];
  explicit.forEach((g, gi) => {
    if (gi > 0) out.push(mkText('and'));
    g.vars.forEach((v, vi) => {
      if (vi > 0) out.push(mkSymbol(','));
      out.push(v);
    });
    out.push(mkSymbol('\\in'), ...restructure(g.type));
  });
  out.push(mkSymbol(','), ...body);
  return out;
}

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

  // Implicit binders `{x : T} → …` are elided — mathematicians don't write
  // implicit arguments (they're `{}`-implicit precisely because the reader
  // infers them). The source keeps them; this is display only.
  const stripped = stripImplicitBinder(nodes);
  if (stripped) return stripped;

  // Dependent Pi binders → ∀ (outermost; do before infix splits).
  const forall = recognizeForall(nodes);
  if (forall) return forall;

  // A NATIVE `∀ {K : F} {W : G} (n : Nat) (vs : T), body` binder telescope.
  // Untreated, the `{}` braces reach KaTeX as invisible grouping and the
  // binders MASH into "K : Field'W : VectorSpace(K)(n : Nat)…". Implicit
  // groups are elided (readers infer them — same policy as
  // stripImplicitBinder); explicit ones join with "and"; when nothing
  // explicit remains the ∀ disappears entirely.
  const telescope = recognizeForallTelescope(nodes);
  if (telescope) return telescope;

  // Fraction / superscript / subscript: these bind TIGHTER than everything
  // around them, so they take only the ADJACENT operands (an atom or a
  // parenthesized group), never the whole run — `0 < eps / 2` must render
  // `0 < \frac{eps}{2}`, not `\frac{0<eps}{2}`; `(eps / 2)` must not split
  // its parens across numerator and denominator. Leftmost occurrence first,
  // then recurse (the built node is itself an operand for later rules, so
  // `f (a / 2)` becomes `f(\frac{a}{2})` via the application rule).
  for (const [op, build] of TIGHT_BINARY_OPS) {
    for (let i = 1; i < nodes.length - 1; i++) {
      if (!isOpSymbol(nodes[i], op)) continue;
      const left = operandEndingAt(nodes, i - 1);
      const right = operandStartingAt(nodes, i + 1);
      if (!left || !right) continue;
      const built = build(
        mkRow(restructure(left.operand)),
        mkRow(restructure(right.operand)),
      );
      return restructure([...nodes.slice(0, left.start), built, ...nodes.slice(right.end + 1)]);
    }
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

  // Postfix projections: an atom spelled `.length` GLUES to the operand
  // before it — `vs.length`, `(pre ++ post).length` — it is never a call
  // argument. (The application rule below used to render `vs(.length)`.)
  for (let i = 1; i < nodes.length; i++) {
    const n = nodes[i];
    if (n.tag !== 'Symbol' || !/^\.[A-Za-z_]/.test((n as SymbolNode).value)) continue;
    const prev = nodes[i - 1];
    if (!isAppAtom(prev)) continue;
    const merged =
      prev.tag === 'Symbol'
        ? mkSymbol((prev as SymbolNode).value + (n as SymbolNode).value)
        // A group/parenthesized operand keeps its own structure (and its
        // click-target ids); the projection rides along in a plain group.
        : mkGroup('', [prev, mkSymbol((n as SymbolNode).value)]);
    return restructure([...nodes.slice(0, i - 1), merged, ...nodes.slice(i + 1)]);
  }

  // Function application on maximal atom RUNS: juxtaposition = application
  // even when the run sits between operators — `|f x - L|` must read
  // `|f(x) − L|`, not the product-looking `|fx − L|`. (The old rule fired
  // only when the ENTIRE list was atoms, so one operator anywhere killed it.)
  {
    let changed = false;
    const out: MathNode[] = [];
    let run: MathNode[] = [];
    const flushRun = () => {
      const headIsFn =
        run.length >= 2 &&
        run[0].tag === 'Symbol' &&
        /^[A-Za-z_\\]/.test((run[0] as SymbolNode).value) &&
        !/^\\/.test((run[0] as SymbolNode).value);
      if (headIsFn) {
        const [head, ...args] = run;
        out.push(head, mkSymbol('('));
        args.forEach((a, i) => {
          if (i > 0) out.push(mkSymbol(','));
          out.push(a);
        });
        out.push(mkSymbol(')'));
        changed = true;
      } else {
        out.push(...run);
      }
      run = [];
    };
    for (const n of nodes) {
      if (isAppAtom(n)) run.push(n);
      else {
        flushRun();
        out.push(n);
      }
    }
    flushRun();
    if (changed) return out;
  }

  return nodes;
}

/** Tight-binding binary operators handled by adjacent-operand extraction. */
const TIGHT_BINARY_OPS: ReadonlyArray<[string, (l: MathRow, r: MathRow) => MathNode]> = [
  ['/', (l, r) => mkFrac(l, r)],
  ['^', (l, r) => mkSup(l, r)],
  ['_', (l, r) => mkSub(l, r)],
];

/** The operand ENDING at `end` (inclusive): a parenthesized group (returned
 *  WITHOUT its parens) or a single value atom. Null when `end` isn't a value
 *  (e.g. an operator) — the caller then leaves the tight op literal. */
function operandEndingAt(nodes: MathNode[], end: number): { start: number; operand: MathNode[] } | null {
  if (end < 0) return null;
  if (isOpSymbol(nodes[end], ')')) {
    let depth = 0;
    for (let i = end; i >= 0; i--) {
      if (isOpSymbol(nodes[i], ')')) depth++;
      else if (isOpSymbol(nodes[i], '(')) {
        depth--;
        if (depth === 0) return { start: i, operand: nodes.slice(i + 1, end) };
      }
    }
    return null;
  }
  return isAppAtom(nodes[end]) ? { start: end, operand: [nodes[end]] } : null;
}

/** The operand STARTING at `start` (inclusive) — mirror of operandEndingAt. */
function operandStartingAt(nodes: MathNode[], start: number): { end: number; operand: MathNode[] } | null {
  if (start >= nodes.length) return null;
  if (isOpSymbol(nodes[start], '(')) {
    let depth = 0;
    for (let i = start; i < nodes.length; i++) {
      if (isOpSymbol(nodes[i], '(')) depth++;
      else if (isOpSymbol(nodes[i], ')')) {
        depth--;
        if (depth === 0) return { end: i, operand: nodes.slice(start + 1, i) };
      }
    }
    return null;
  }
  return isAppAtom(nodes[start]) ? { end: start, operand: [nodes[start]] } : null;
}

/** Symbols that are operators/punctuation (NOT application operands). */
const APP_STOP = new Set([
  '+', '+\\!\\!+', '-', '=', '<', '>', '/', '*', ':', '|', ',', '(', ')', '[', ']', '{', '}', '^', '_', "'",
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
 * segment is proposition-like, and render it as `H₁ and H₂ and …, then C` —
 * the mathematical reading of curried hypotheses. Lean pp nests the chain to the
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
    // Hypotheses join with "and"; the consequent reads ", then" — so the whole
    // chain is the sentence `H₁ and H₂, then C`.
    if (i > 0) {
      if (i === segs.length - 1) out.push(mkSymbol(','), mkText('then'));
      else out.push(mkText('and'));
    }
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
 * Render PLAIN pretty-printed Lean text (no tags) to LaTeX — for slot types in
 * the term builder, where we only have text segments of a larger type. Reuses
 * the same tokenize→restructure pipeline as tagged rendering.
 */
export function mathTextToLatex(text: string, fallback = ''): string {
  try {
    // A TOP-LEVEL application renders call-style: `ltLeTrans |x - x0| deltaF
    // deltaG h1 a` → `ltLeTrans(|x−x₀|, δ_F, δ_G, h₁, a)`. The tokenize→
    // restructure path only recognized `f x y` when every arg was a plain
    // name; one parenthesized argument broke its call-detection and the rest
    // concatenated with NO separators at all (`…(ε/2)h₂`, `)δ_Fδ_Gh₁a`).
    const parts = splitTopLevelApplication(text.trim());
    if (parts && parts.length >= 2 && /^[A-Za-z_][A-Za-z0-9_'.]*$/.test(parts[0])) {
      const args = parts.slice(1).map((a) => mathTextToLatex(stripOuterParens(a), a));
      const head = renderStaticLatex(mkRow(restructure(tokenizeText(parts[0]))));
      return `${head}(${args.join(', ')})`;
    }
    return renderStaticLatex(mkRow(restructure(tokenizeText(text))));
  } catch {
    return fallback || text;
  }
}

/** Split `f a (b c) |d - e| h` into its top-level pieces, or null when the
 *  text is an EXPRESSION rather than an application (any top-level operator:
 *  `0 < ε / 2`, `|a| + |b|`, `fun x => …` all keep the expression path). */
function splitTopLevelApplication(text: string): string[] | null {
  const parts: string[] = [];
  let depth = 0;
  let inBar = false;
  let cur = '';
  for (const ch of text) {
    if (ch === '(' || ch === '[' || ch === '⟨' || ch === '{') depth++;
    else if (ch === ')' || ch === ']' || ch === '⟩' || ch === '}') depth--;
    else if (ch === '|') inBar = !inBar;
    if (depth === 0 && !inBar) {
      if (ch === ' ') {
        if (cur) parts.push(cur);
        cur = '';
        continue;
      }
      // An operator at top level means this is not a bare application.
      if ('+-*/=<>≤≥≠∧∨→↔,:λ'.includes(ch)) return null;
    }
    cur += ch;
  }
  if (depth !== 0 || inBar) return null;
  if (cur) parts.push(cur);
  return parts;
}

function stripOuterParens(a: string): string {
  if (!a.startsWith('(') || !a.endsWith(')')) return a;
  // Only strip when the FIRST paren matches the LAST one.
  let depth = 0;
  for (let i = 0; i < a.length; i++) {
    if (a[i] === '(') depth++;
    else if (a[i] === ')') { depth--; if (depth === 0 && i < a.length - 1) return a; }
  }
  return a.slice(1, -1);
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
