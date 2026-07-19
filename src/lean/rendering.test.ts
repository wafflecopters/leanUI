/**
 * RENDERING REGRESSION BATTERY — plain Lean pretty-printed text → LaTeX.
 *
 * Every display convention the WYSIWYG relies on, locked in one table:
 * fractions bind tight (adjacent operands only, parens respected), Greek
 * (unicode + spelled-out), application as f(x), quantifiers, operators.
 * When a rendering looks wrong in the UI, reproduce it HERE first.
 */
import { describe, expect, test } from 'vitest';
import { codeWithInfosToMathRow } from './codeWithInfos';
import { renderStaticLatex } from '../math-editor/render';

/** Render plain pp text exactly like the UI does (no subterm wrappers). */
function tex(text: string): string {
  return renderStaticLatex(codeWithInfosToMathRow({ t: 'text', s: text }, { wrapSubterms: false }))
    .replace(/\s+/g, ' ')
    .trim();
}

describe('fractions bind TIGHT (the builder-slot regressions)', () => {
  test('0 < eps / 2 — the relation stays outside the fraction', () => {
    expect(tex('0 < eps / 2')).toBe('0<\\frac{\\operatorname{eps}}{2}');
  });

  test('(eps / 2) — parens are not split across the fraction', () => {
    expect(tex('(eps / 2)')).toBe('(\\frac{\\operatorname{eps}}{2})');
  });

  test('eps / 2 — plain fraction', () => {
    expect(tex('eps / 2')).toBe('\\frac{\\operatorname{eps}}{2}');
  });

  test('a + b / c — fraction takes only its operands', () => {
    expect(tex('a + b / c')).toBe('a + \\frac{b}{c}');
  });

  test('(a + b) / c — parenthesized numerator group (parens dropped)', () => {
    expect(tex('(a + b) / c')).toBe('\\frac{a + b}{c}');
  });

  test('f (a / 2) — fraction inside an application argument', () => {
    expect(tex('f (a / 2)')).toBe('f(\\frac{a}{2})');
  });

  test('a / b / c — leftmost first, result is an operand again', () => {
    expect(tex('a / b / c')).toBe('\\frac{\\frac{a}{b}}{c}');
  });
});

describe('superscripts bind tight too', () => {
  test('x ^ 2 + 1', () => {
    expect(tex('x ^ 2 + 1')).toBe('{x}^{2} + 1');
  });
});

describe('Greek + names', () => {
  test('unicode ε and δ', () => {
    expect(tex('ε + δ')).toBe('\\varepsilon + \\delta');
  });

  test('spelled-out names with subscript suffixes', () => {
    expect(tex('deltaF + epsilon0')).toBe('\\delta_{F} + \\varepsilon_{0}');
  });

  test('x0 as subscript', () => {
    expect(tex('x0')).toBe('{x}_{0}');
  });
});

describe('application style', () => {
  test('f x → f(x); g a b → g(a, b)', () => {
    expect(tex('f x')).toBe('f(x)');
    expect(tex('g a b')).toBe('g(a,b)');
  });

  test('operators stop the application rule', () => {
    expect(tex('a + b')).toBe('a + b');
  });
});

describe('quantifiers and structure', () => {
  test("the data existential ∃' reads as a plain ∃", () => {
    const t = tex("∃' delta ∈ ℝ, P delta");
    expect(t).toContain('\\exists');
    expect(t).not.toContain("'");
  });

  test('binder keeps its type: (n : MyNat) → P n', () => {
    const t = tex('(n : MyNat) → P n');
    expect(t).toContain('\\forall');
    expect(t).toContain('\\in');
    expect(t).not.toContain(':');
  });

  test('implicit binders are elided', () => {
    expect(tex('{R : Real} → P')).toBe('P');
  });

  test('prop implication chain reads and/then (tagged pp structure)', () => {
    // Chain recognition works on Lean's tagged nesting, not raw text.
    const latex = renderStaticLatex(
      codeWithInfosToMathRow(
        {
          t: 'append',
          kids: [
            { t: 'tag', pos: '/h1', child: { t: 'text', s: 'a = b' } },
            { t: 'text', s: ' → ' },
            { t: 'tag', pos: '/c', child: { t: 'text', s: 'c = d' } },
          ],
        },
        { wrapSubterms: false },
      ),
    );
    expect(latex).toContain('\\text{then}');
    expect(latex).not.toContain('\\to');
  });

  test('function types keep their arrows', () => {
    expect(tex('ℝ → ℝ')).toBe('\\mathbb{R} \\to \\mathbb{R}');
  });
});
