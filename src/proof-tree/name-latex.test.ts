import { describe, expect, test } from 'vitest';
import { renderNameLatex, normalizeBinderNameInput } from './name-latex';

describe('renderNameLatex', () => {
  describe('text wrapper (default)', () => {
    test('single Greek char → math command', () => {
      expect(renderNameLatex('ε')).toBe('\\varepsilon');
    });

    test('Greek prefix + ASCII tail → subscripted', () => {
      expect(renderNameLatex('δF')).toBe('\\delta_{F}');
    });

    test('mixed Greek/ASCII run keeps Greek out of \\text', () => {
      const out = renderNameLatex('εδ');
      // Both chars are Greek, must NOT be wrapped in \text{...}
      expect(out).not.toMatch(/\\text\{[^}]*[α-ωΑ-Ω]/u);
      expect(out).toContain('\\varepsilon');
      expect(out).toContain('\\delta');
    });

    test('pure ASCII multichar wraps in \\text', () => {
      expect(renderNameLatex('foo')).toBe('\\text{foo}');
    });
  });

  describe('textbf wrapper', () => {
    test('single Greek char must NOT end up bare inside \\textbf{}', () => {
      // \textbf{ε} triggers KaTeX "No character metrics for 'ε' in style 'Main-Bold' and mode 'text'"
      const out = renderNameLatex('ε', 'textbf');
      expect(out).not.toMatch(/\\textbf\{ε\}/u);
      // Should use math-mode bold for Greek (\boldsymbol works in math mode)
      expect(out).toMatch(/\\boldsymbol\{\\varepsilon\}|\\bm\{\\varepsilon\}|\\pmb\{\\varepsilon\}/);
    });

    test('Greek prefix + ASCII tail → no Greek inside \\textbf{}', () => {
      const out = renderNameLatex('δF', 'textbf');
      expect(out).not.toMatch(/\\textbf\{[^}]*[α-ωΑ-Ω]/u);
      expect(out).not.toMatch(/\\text\{[^}]*[α-ωΑ-Ω]/u);
    });

    test('mixed Greek/ASCII (εδ) → no Greek in \\textbf', () => {
      const out = renderNameLatex('εδ', 'textbf');
      expect(out).not.toMatch(/\\textbf\{[^}]*[α-ωΑ-Ω]/u);
      expect(out).not.toMatch(/\\text\{[^}]*[α-ωΑ-Ω]/u);
    });

    test('pure ASCII → wrapped in \\textbf', () => {
      expect(renderNameLatex('foo', 'textbf')).toBe('\\textbf{foo}');
    });
  });

  // Image #56: typing `\delta_f` in a rename input should end up rendering
  // as δ subscript f, not the literal string "\delta_f".
  describe('subscript pattern: head_<tail>', () => {
    test('Greek head + underscore + alphanumeric tail → subscripted', () => {
      expect(renderNameLatex('δ_f')).toBe('\\delta_{f}');
      expect(renderNameLatex('ε_0')).toBe('\\varepsilon_{0}');
      expect(renderNameLatex('λ_xy')).toBe('\\lambda_{xy}');
    });

    test('ASCII head + underscore + alphanumeric tail → subscripted', () => {
      expect(renderNameLatex('x_y')).toBe('x_{y}');
      expect(renderNameLatex('f_max')).toBe('f_{max}');
    });

    test('underscore-tail subscript renders WITHOUT escaping the underscore', () => {
      // The earlier code path wrapped underscores in \text{x\_y}, producing
      // literal "x_y" output. The subscript path must take precedence.
      expect(renderNameLatex('x_y')).not.toContain('\\text');
      expect(renderNameLatex('x_y')).not.toContain('\\_');
    });
  });
});

describe('normalizeBinderNameInput', () => {
  test('LaTeX-style Greek command → Unicode char', () => {
    expect(normalizeBinderNameInput('\\delta')).toBe('δ');
    expect(normalizeBinderNameInput('\\alpha')).toBe('α');
    expect(normalizeBinderNameInput('\\Sigma')).toBe('Σ');
  });

  test('common aliases (\\epsilon, \\phi) → Unicode', () => {
    // KaTeX uses \varepsilon for ε by convention; accept what the user types.
    expect(normalizeBinderNameInput('\\epsilon')).toBe('ε');
    expect(normalizeBinderNameInput('\\phi')).toBe('φ');
  });

  test('LaTeX command followed by subscript → Unicode + subscript syntax', () => {
    // `\delta_f` → `δ_f` (the renderer turns the underscore into a subscript).
    expect(normalizeBinderNameInput('\\delta_f')).toBe('δ_f');
  });

  test('plain ASCII identifier is unchanged', () => {
    expect(normalizeBinderNameInput('x')).toBe('x');
    expect(normalizeBinderNameInput('foo')).toBe('foo');
    expect(normalizeBinderNameInput('n12')).toBe('n12');
  });

  test('unknown LaTeX command passes through unchanged', () => {
    // Don't garble user input we don't understand.
    expect(normalizeBinderNameInput('\\foo')).toBe('\\foo');
    expect(normalizeBinderNameInput('\\bizarre_thing')).toBe('\\bizarre_thing');
  });

  test('end-to-end: `\\delta_f` typed → renders as \\delta_{f}', () => {
    const normalized = normalizeBinderNameInput('\\delta_f');
    expect(renderNameLatex(normalized)).toBe('\\delta_{f}');
  });
});
