/**
 * Render a variable/identifier name as KaTeX-safe LaTeX.
 *
 * Greek Unicode characters (ε, δ, ...) have no metrics in KaTeX's
 * `Main-Regular` text font — putting them inside `\text{...}` produces
 * "No character metrics" warnings and bad rendering. Math mode is fine,
 * so this helper keeps Greek in math mode and only wraps ASCII runs in
 * the chosen text wrapper.
 */

const GREEK_LATEX: Record<string, string> = {
  'α': '\\alpha', 'β': '\\beta', 'γ': '\\gamma', 'δ': '\\delta',
  'ε': '\\varepsilon', 'ζ': '\\zeta', 'η': '\\eta', 'θ': '\\theta',
  'λ': '\\lambda', 'μ': '\\mu', 'π': '\\pi', 'σ': '\\sigma',
  'φ': '\\varphi', 'ψ': '\\psi', 'ω': '\\omega',
};

export type NameWrapper = 'text' | 'textsf' | 'mathit';

function escapeUnderscores(s: string): string {
  return s.replace(/_/g, '\\_');
}

function hasGreek(name: string): boolean {
  for (const ch of name) if (GREEK_LATEX[ch]) return true;
  return false;
}

/** Render Greek chars as math commands and group ASCII runs in the chosen wrapper. */
function renderMixed(name: string, wrapper: NameWrapper): string {
  let result = '';
  let buf = '';
  const flush = () => {
    if (buf) {
      result += `\\${wrapper}{${escapeUnderscores(buf)}}`;
      buf = '';
    }
  };
  for (const ch of name) {
    const greek = GREEK_LATEX[ch];
    if (greek) {
      flush();
      result += greek;
    } else {
      buf += ch;
    }
  }
  flush();
  return result;
}

/**
 * Render a name for inclusion in a LaTeX expression (math context).
 *
 * @param wrapper how to wrap multi-letter ASCII runs:
 *   - 'text'    → upright serif (matches body text)
 *   - 'textsf'  → upright sans-serif
 *   - 'mathit'  → math italic (multi-letter)
 */
export function renderNameLatex(name: string, wrapper: NameWrapper = 'text'): string {
  // Single char: math letter (Greek included — fine in math mode).
  if (name.length === 1) return GREEK_LATEX[name] ?? name;

  // Primed single char: x' or δ'
  if (name.length === 2 && name[1] === "'") {
    const head = GREEK_LATEX[name[0]] ?? name[0];
    return `${head}'`;
  }

  // Greek prefix + alphanumeric tail: δF → \delta_{F}, ε1 → \varepsilon_{1}
  const head = GREEK_LATEX[name[0]];
  if (head && /^[a-zA-Z0-9]+$/.test(name.slice(1))) {
    return `${head}_{${name.slice(1)}}`;
  }

  // ASCII letter + digit tail: x0 → {x}_{0}, n12 → {n}_{12}
  if (/^[a-zA-Z]\d+$/.test(name)) {
    return `{${name[0]}}_{${name.slice(1)}}`;
  }

  // Mixed Greek anywhere else: split into Greek/ASCII runs.
  if (hasGreek(name)) return renderMixed(name, wrapper);

  // Pure ASCII multi-char: wrap.
  return `\\${wrapper}{${escapeUnderscores(name)}}`;
}
