import { describe, expect, test } from 'vitest';
import { renderNameLatex } from './name-latex';

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
});
