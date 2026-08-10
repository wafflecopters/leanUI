/**
 * Render a plain-text Lean EXPRESSION as LaTeX, without parsing Lean.
 *
 * The old converter passed the text through almost verbatim, which handed
 * KaTeX strings it was never meant to see: `_` became a subscript (so the
 * projection `eps_delta` rendered as "epsₐelta"), multi-char names were
 * italicized like products of single variables, and application spacing
 * vanished entirely (`divTwoPos ε epsPos` → "divTwoPosεepsPos").
 *
 * This is still a HEURISTIC, deliberately: only Lean parses Lean, and this
 * layer only decides how tokens LOOK. It tokenizes, renders each identifier
 * through the same `renderNameLatex` the prose view uses (so `h2` → h₂,
 * `eps_delta` → upright with a literal underscore, `x'` keeps its prime), and
 * re-inserts application spacing as thin spaces.
 */
import { renderNameLatex } from './name-latex';

/** One token: identifiers (incl. projection dots, primes, underscores, Greek),
 *  numbers, multi-char operators, or any single non-space character. */
const TOKEN_RE =
  /[A-Za-zͰ-Ͽ_][A-Za-z0-9Ͱ-Ͽ_'.]*|\d+|->|=>|:=|<->|[^\sA-Za-z0-9]/g;

const OPERATOR_LATEX: Record<string, string> = {
  '->': '\\to ',
  '=>': '\\Rightarrow ',
  '→': '\\to ',
  '↔': '\\leftrightarrow ',
  '≤': '\\le ',
  '≥': '\\ge ',
  '≠': '\\ne ',
  '∀': '\\forall ',
  '∃': '\\exists ',
  '*': '\\cdot ',
};

/** Names with a conventional notation of their own. */
const SPECIAL_NAMES: Record<string, string> = {
  Nat: '\\mathbb{N}',
  Int: '\\mathbb{Z}',
  Type: '\\text{Type}',
  Prop: '\\text{Prop}',
  fun: '\\textsf{fun}',
  refl: '\\textsf{refl}',
};

function isIdent(tok: string): boolean {
  return /^[A-Za-zͰ-Ͽ_]/.test(tok);
}

function isNumber(tok: string): boolean {
  return /^\d+$/.test(tok);
}

/** A projection chain (`limF.eps_delta`) renders each segment as a NAME,
 *  joined by literal dots — never as subscripts. */
function identLatex(tok: string): string {
  const special = SPECIAL_NAMES[tok];
  if (special) return special;
  return tok
    .split('.')
    .filter(Boolean)
    .map((seg) => renderNameLatex(seg, 'textsf'))
    .join('.');
}

/** Does a thin space belong between these two rendered tokens? Application
 *  (atom followed by atom / opening bracket) does; operators bind their own
 *  spacing. `f x h1` → `f\,x\,h_{1}`, but `ε / 2` stays tight.
 *
 *  `|` is the one ambiguous bracket — the same character opens and closes an
 *  absolute value — so the caller says which side this occurrence is on
 *  (tracked by parity): an OPENING bar is an atom-start (`f |x|` gaps before
 *  it), a CLOSING bar is an atom-end (`|x| g` gaps after). */
function needsGap(prev: string, next: string, prevBarCloses: boolean, nextBarOpens: boolean): boolean {
  const prevAtom = isIdent(prev) || isNumber(prev) || prev === ')' || prev === '⟩' || (prev === '|' && prevBarCloses);
  const nextAtom = isIdent(next) || isNumber(next) || next === '(' || next === '⟨' || (next === '|' && nextBarOpens);
  return prevAtom && nextAtom;
}

export function exprToLatex(text: string): string {
  const tokens = text.match(TOKEN_RE) ?? [];
  let out = '';
  let prev: string | null = null;
  let barsSeen = 0; // even → the next `|` opens, odd → it closes
  for (const tok of tokens) {
    const prevBarCloses = prev === '|' && barsSeen % 2 === 0; // prev bar was the closer
    const nextBarOpens = tok === '|' && barsSeen % 2 === 0;
    if (prev !== null && needsGap(prev, tok, prevBarCloses, nextBarOpens)) out += '\\,';
    if (tok === '|') barsSeen++;
    if (OPERATOR_LATEX[tok]) out += OPERATOR_LATEX[tok];
    else if (isIdent(tok)) out += identLatex(tok);
    else if (isNumber(tok)) out += tok;
    else if (tok === '#' || tok === '$' || tok === '%' || tok === '&') out += `\\${tok}`;
    else out += tok;
    prev = tok;
  }
  return out;
}
