/**
 * Render a variable/identifier name as KaTeX-safe LaTeX.
 *
 * Greek Unicode characters (ε, δ, ...) have no metrics in KaTeX's text fonts
 * (`Main-Regular`, `Main-Bold`) — putting them inside `\text{...}` or
 * `\textbf{...}` produces "No character metrics" warnings and bad rendering.
 * Math mode is fine, so this helper keeps Greek in math mode and only wraps
 * ASCII runs in the chosen text wrapper. For bold, Greek is wrapped in
 * `\boldsymbol{...}` (math-mode bold) instead of `\textbf{...}`.
 */

const GREEK_LATEX: Record<string, string> = {
  'α': '\\alpha', 'β': '\\beta', 'γ': '\\gamma', 'δ': '\\delta',
  'ε': '\\varepsilon', 'ζ': '\\zeta', 'η': '\\eta', 'θ': '\\theta',
  'λ': '\\lambda', 'μ': '\\mu', 'π': '\\pi', 'σ': '\\sigma',
  'φ': '\\varphi', 'ψ': '\\psi', 'ω': '\\omega',
};

export type NameWrapper = 'text' | 'textsf' | 'mathit' | 'textbf';

function escapeUnderscores(s: string): string {
  return s.replace(/_/g, '\\_');
}

function hasGreek(name: string): boolean {
  for (const ch of name) if (GREEK_LATEX[ch]) return true;
  return false;
}

function renderGreek(greekCmd: string, wrapper: NameWrapper): string {
  // \boldsymbol works in math mode and has Greek metrics; \textbf does not.
  return wrapper === 'textbf' ? `\\boldsymbol{${greekCmd}}` : greekCmd;
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
      result += renderGreek(greek, wrapper);
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
 *   - 'textbf'  → bold (Greek goes through \boldsymbol)
 */
export function renderNameLatex(name: string, wrapper: NameWrapper = 'text'): string {
  // Single char.
  if (name.length === 1) {
    const greek = GREEK_LATEX[name];
    if (greek) return renderGreek(greek, wrapper);
    return wrapper === 'textbf' ? `\\textbf{${name}}` : name;
  }

  // Primed single char: x' or δ'
  if (name.length === 2 && name[1] === "'") {
    const greek = GREEK_LATEX[name[0]];
    const head = greek ? renderGreek(greek, wrapper) : (wrapper === 'textbf' ? `\\textbf{${name[0]}}` : name[0]);
    return `${head}'`;
  }

  // Greek prefix + alphanumeric tail: δF → \delta_{F}, ε1 → \varepsilon_{1}
  const greekHead = GREEK_LATEX[name[0]];
  if (greekHead && /^[a-zA-Z0-9]+$/.test(name.slice(1))) {
    const tail = name.slice(1);
    const tailRendered = wrapper === 'textbf' ? `\\textbf{${tail}}` : tail;
    return `${renderGreek(greekHead, wrapper)}_{${tailRendered}}`;
  }

  // ASCII letter + digit tail: x0 → {x}_{0}, n12 → {n}_{12}
  if (/^[a-zA-Z]\d+$/.test(name)) {
    const head = wrapper === 'textbf' ? `\\textbf{${name[0]}}` : name[0];
    return `${head}_{${name.slice(1)}}`;
  }

  // Mixed Greek anywhere else: split into Greek/ASCII runs.
  if (hasGreek(name)) return renderMixed(name, wrapper);

  // Pure ASCII multi-char: wrap.
  return `\\${wrapper}{${escapeUnderscores(name)}}`;
}
