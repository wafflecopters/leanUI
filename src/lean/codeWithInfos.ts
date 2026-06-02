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
  type MathNode,
  type MathRow,
} from '../math-editor/types';
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
      nodes.push(mkSymbol(ch));
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

/** Convert a tagged-text node into a flat list of MathNodes. */
function nodesOf(tt: TaggedJson): MathNode[] {
  switch (tt.t) {
    case 'text':
      return tokenizeText(tt.s);
    case 'append':
      return tt.kids.flatMap(nodesOf);
    case 'tag': {
      const inner = nodesOf(tt.child);
      // Wrap the subexpression in a Group so it's individually selectable.
      // Skip empty wrappers (can happen for zero-width tags).
      if (inner.length === 0) return [];
      return [mkGroup(`${SUBEXPR_HTML_PREFIX}${tt.pos}`, inner)];
    }
  }
}

/**
 * Convert Lean `CodeWithInfos` JSON into a MathRow ready for the math editor.
 *
 * The result is flat (a linear sequence of symbols + group wrappers) — the
 * editor's structural nodes (Frac, Sub/Sup, BigOp…) are introduced by user
 * editing, not by this initial render. This matches how the TT path produced
 * type signatures: a readable linear form that's fully editable.
 */
export function codeWithInfosToMathRow(tagged: TaggedJson): MathRow {
  return mkRow(nodesOf(tagged));
}
