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
  'ι': '\\iota', 'κ': '\\kappa', 'λ': '\\lambda', 'μ': '\\mu',
  'ν': '\\nu', 'ξ': '\\xi', 'π': '\\pi', 'ρ': '\\rho',
  'σ': '\\sigma', 'τ': '\\tau', 'υ': '\\upsilon', 'φ': '\\varphi',
  'χ': '\\chi', 'ψ': '\\psi', 'ω': '\\omega',
  'Γ': '\\Gamma', 'Δ': '\\Delta', 'Θ': '\\Theta', 'Λ': '\\Lambda',
  'Ξ': '\\Xi', 'Π': '\\Pi', 'Σ': '\\Sigma', 'Φ': '\\Phi',
  'Ψ': '\\Psi', 'Ω': '\\Omega',
};

/** Inverse of GREEK_LATEX, plus a few common aliases the user is likely to
 *  type that aren't in our canonical Unicode set (e.g. `\epsilon` → ε is
 *  conventionally `\varepsilon` in KaTeX, but the user shouldn't have to
 *  know that). */
const LATEX_TO_GREEK: Record<string, string> = (() => {
  const m: Record<string, string> = {};
  for (const [ch, cmd] of Object.entries(GREEK_LATEX)) m[cmd] = ch;
  // Common aliases — what the user types vs the canonical command.
  m['\\epsilon'] = 'ε';     // we display Unicode ε as \varepsilon
  m['\\phi'] = 'φ';         // we display Unicode φ as \varphi
  return m;
})();

/** Convert user-typed LaTeX-style commands in a binder name to Unicode
 *  characters our renderer already handles. This lets the user type
 *  `\delta_f` in a rename field and have it become the kernel name `δ_f`,
 *  which `renderNameLatex` then renders as `\delta_{f}` via the
 *  Greek+subscript path.
 *
 *  Conservative: only transforms `\command` tokens where `command` is a
 *  letter run that maps to a known Greek/Unicode char. Anything else is
 *  passed through unchanged — the user can still type plain identifiers
 *  like `x`, `foo`, `n12` and they work exactly as before. */
export function normalizeBinderNameInput(input: string): string {
  return input.replace(/\\([a-zA-Z]+)/g, (whole, cmd) => {
    const ch = LATEX_TO_GREEK['\\' + cmd];
    return ch ?? whole;
  });
}

export type NameWrapper = 'text' | 'textsf' | 'mathit' | 'textbf';

function escapeUnderscores(s: string): string {
  return s.replace(/_/g, '\\_');
}

function hasGreek(name: string): boolean {
  for (const ch of name) if (GREEK_LATEX[ch]) return true;
  return false;
}

/** Names people spell out in ASCII for Greek binders. Deliberately short —
 *  each entry risks a false positive on a real word, so only the ones that
 *  actually appear as binder names. */
const SPELLED_GREEK: Record<string, string> = {
  alpha: '\\alpha', beta: '\\beta', gamma: '\\gamma', delta: '\\delta',
  epsilon: '\\varepsilon', eps: '\\varepsilon', zeta: '\\zeta', eta: '\\eta',
  theta: '\\theta', lambda: '\\lambda', mu: '\\mu', sigma: '\\sigma',
  phi: '\\varphi', psi: '\\psi', omega: '\\omega',
};

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

  // Explicit subscript: `δ_f` → δ subscript f, `x_foo` → x subscript foo.
  // The user types this directly (e.g. via `\delta_f` → `δ_f` after
  // `normalizeBinderNameInput`) and expects it to render as a real
  // subscript, not as an underscore-in-text.
  const subscriptMatch = name.match(/^(.)_([a-zA-Z0-9]+)$/);
  if (subscriptMatch) {
    const headCh = subscriptMatch[1];
    const tail = subscriptMatch[2];
    const greekHead = GREEK_LATEX[headCh];
    const headRendered = greekHead
      ? renderGreek(greekHead, wrapper)
      : (wrapper === 'textbf' ? `\\textbf{${headCh}}` : headCh);
    const tailRendered = wrapper === 'textbf' ? `\\textbf{${tail}}` : tail;
    return `${headRendered}_{${tailRendered}}`;
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

  // Spelled-out Greek head + SHORT tail: `deltaF` → δ_F, `delta` → δ — the
  // same binder the goal view already shows as δ_F. The tail must be one
  // capital letter or digits, so ordinary words never false-positive
  // (`epsPos` keeps its name; `deltaFdeltaG` is not a subscript).
  {
    const m = name.match(/^([a-z]+?)([A-Z]|\d+)?$/);
    const spelled = m ? SPELLED_GREEK[m[1]] : undefined;
    if (m && spelled) {
      const head = renderGreek(spelled, wrapper);
      if (m[2] === undefined) return head;
      const tail = wrapper === 'textbf' ? `\\textbf{${m[2]}}` : m[2];
      return `${head}_{${tail}}`;
    }
  }

  // Mixed Greek anywhere else: split into Greek/ASCII runs.
  if (hasGreek(name)) return renderMixed(name, wrapper);

  // Pure ASCII multi-char: wrap.
  return `\\${wrapper}{${escapeUnderscores(name)}}`;
}
