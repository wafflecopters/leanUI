import { useMemo } from 'react';
import katex from 'katex';
import 'katex/dist/katex.min.css';
import type { TaggedText } from '../lean/types';
import { codeWithInfosToMathRow } from '../lean/codeWithInfos';
import { renderStaticLatex } from '../math-editor/render';

/**
 * Read-only WYSIWYG rendering of a Lean expression.
 *
 * Takes Lean's tagged pretty-print (`CodeWithInfos`), converts it to the math
 * editor's MathRow model, renders to LaTeX, and typesets with KaTeX — the same
 * render path the interactive editor uses, just static. This is the M3 proof
 * that Lean expressions display as real math in the WYSIWYG; the interactive
 * MathEditor reuses the identical MathRow.
 */
export function LeanMathView({ tagged, fallback }: { tagged?: TaggedText; fallback?: string }) {
  const html = useMemo(() => {
    if (!tagged) return null;
    try {
      const row = codeWithInfosToMathRow(tagged);
      // `\displaystyle` gives display-math STYLE (limits below `\lim`/`\sum`,
      // full-size fractions) while staying inline — so `lim_{x→x0}` stacks the
      // subscript under `lim` instead of trailing it.
      const latex = `\\displaystyle ${renderStaticLatex(row)}`;
      return katex.renderToString(latex, {
        throwOnError: false,
        displayMode: false,
        trust: true, // allow \htmlId from Group nodes
        strict: false,
      });
    } catch {
      return null;
    }
  }, [tagged]);

  if (html === null) {
    return <span style={{ fontFamily: 'ui-monospace, monospace', color: '#79c0ff' }}>{fallback ?? ''}</span>;
  }
  return <span dangerouslySetInnerHTML={{ __html: html }} />;
}
