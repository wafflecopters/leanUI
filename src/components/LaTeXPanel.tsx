/**
 * LaTeXPanel — Scrollable split-panel rendering of a LatexDocument.
 *
 * Each declaration is rendered as a card with a green/red left border,
 * category badge, name, and KaTeX-rendered blocks.
 */

import React, { useEffect, useRef, useCallback } from 'react';
import katex from 'katex';
import 'katex/dist/katex.min.css';
import { LatexDocument, LatexSection, LatexBlock } from '../compiler/latex-converter';

// ============================================================================
// Inline KaTeX renderer (display or inline mode)
// ============================================================================

function KaTeX({ tex, display = true, style }: { tex: string; display?: boolean; style?: React.CSSProperties }) {
  const ref = useRef<HTMLSpanElement>(null);

  useEffect(() => {
    if (ref.current) {
      try {
        katex.render(tex, ref.current, {
          displayMode: display,
          throwOnError: false,
        });
      } catch {
        ref.current.innerHTML = `<span style="color:#f85149">LaTeX: ${tex}</span>`;
      }
    }
  }, [tex, display]);

  return <span ref={ref} style={{ color: '#ffffff', ...style }} />;
}

// ============================================================================
// Category badge colors
// ============================================================================

const CATEGORY_COLORS: Record<string, string> = {
  inductive: '#7ee787',
  record: '#79c0ff',
  definition: '#d2a8ff',
  theorem: '#ffa657',
  postulate: '#ff7b72',
};

const CATEGORY_LABELS: Record<string, string> = {
  inductive: 'Inductive',
  record: 'Record',
  definition: 'Def',
  theorem: 'Theorem',
  postulate: 'Axiom',
};

// ============================================================================
// Section renderer
// ============================================================================

function SectionCard({ section }: { section: LatexSection }) {
  const borderColor = section.checkSuccess ? '#238636' : '#da3633';
  const catColor = CATEGORY_COLORS[section.category] ?? '#8b949e';

  return (
    <div style={{
      borderLeft: `3px solid ${borderColor}`,
      padding: '8px 12px',
      marginBottom: '12px',
      background: '#161b22',
      borderRadius: '0 6px 6px 0',
    }}>
      {/* Header line: badge + name */}
      <div style={{ display: 'flex', alignItems: 'center', gap: '8px', marginBottom: '6px' }}>
        <span style={{
          fontSize: '10px',
          fontWeight: 600,
          color: '#0d1117',
          background: catColor,
          borderRadius: '3px',
          padding: '1px 6px',
          textTransform: 'uppercase',
          letterSpacing: '0.5px',
        }}>
          {CATEGORY_LABELS[section.category]}
        </span>
        <span style={{ color: '#c9d1d9', fontFamily: 'monospace', fontSize: '13px' }}>
          {section.name}
        </span>
        {!section.checkSuccess && (
          <span style={{
            fontSize: '10px',
            color: '#f85149',
            fontWeight: 600,
          }}>
            ERROR
          </span>
        )}
      </div>

      {/* LaTeX blocks */}
      <div style={{ paddingLeft: '4px' }}>
        {section.blocks.map((block, i) => (
          <BlockRenderer key={i} block={block} />
        ))}
      </div>

      {/* Errors */}
      {section.errors.length > 0 && (
        <div style={{ marginTop: '6px' }}>
          {section.errors.map((err, i) => (
            <div key={i} style={{
              color: '#f85149',
              fontSize: '11px',
              fontFamily: 'monospace',
              padding: '2px 0',
              whiteSpace: 'pre-wrap',
            }}>
              {err}
            </div>
          ))}
        </div>
      )}
    </div>
  );
}

function BlockRenderer({ block }: { block: LatexBlock }) {
  switch (block.kind) {
    case 'header':
      return (
        <div style={{ margin: '4px 0' }}>
          <KaTeX tex={block.latex} display={true} />
        </div>
      );
    case 'rule':
      return (
        <div style={{ margin: '2px 0', paddingLeft: '16px' }}>
          <KaTeX tex={block.latex} display={true} />
        </div>
      );
    case 'comment':
      return (
        <div style={{ margin: '4px 0', paddingLeft: '16px' }}>
          <KaTeX tex={block.latex} display={true} />
        </div>
      );
  }
}

// ============================================================================
// Main panel
// ============================================================================

interface LaTeXPanelProps {
  document: LatexDocument | null;
}

export function LaTeXPanel({ document }: LaTeXPanelProps) {
  if (!document) {
    return (
      <div style={{
        display: 'flex',
        alignItems: 'center',
        justifyContent: 'center',
        height: '100%',
        color: '#8b949e',
        fontSize: '14px',
      }}>
        Compile code to see LaTeX rendering
      </div>
    );
  }

  if (document.sections.length === 0) {
    return (
      <div style={{
        display: 'flex',
        alignItems: 'center',
        justifyContent: 'center',
        height: '100%',
        color: '#8b949e',
        fontSize: '14px',
      }}>
        No declarations to render
      </div>
    );
  }

  return (
    <div className="latex-panel" style={{ padding: '12px' }}>
      <style>{`.latex-panel .katex { color: #ffffff; }`}</style>
      {document.sections.map((section, i) => (
        <SectionCard key={`${section.name}-${i}`} section={section} />
      ))}
    </div>
  );
}
