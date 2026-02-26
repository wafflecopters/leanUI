import React, { useEffect, useMemo, useRef, useState } from 'react';
import katex from 'katex';
import { CompiledDeclaration } from '../compiler/compile';
import { TeXExpressionEditor } from './TeXExpressionEditor';
import { MathEditor } from './MathEditor';
import { createDefaultRegistry, SyntaxRegistry, SyntaxEntry, patternToDisplayLatex } from '../math-editor/syntax-registry';

export interface WYSIWYGPanelProps {
  /** Compiled declarations for display (zonked kernel terms — no unsolved metas) */
  declarations: CompiledDeclaration[];
  /** Called with new source text when the user edits a box */
  onCodeChange: (code: string) => void;
}

/** Color for the declaration kind badge */
function declKindColor(decl: CompiledDeclaration): string {
  if (decl.kind === 'inductive') {
    if (decl.isRecord) return '#a371f7';
    return '#3fb950';
  }
  return '#58a6ff';
}

export function WYSIWYGPanel({ declarations }: WYSIWYGPanelProps) {
  const registry = useMemo(() => createDefaultRegistry(), []);

  // Per-box editable name
  const [localNames, setLocalNames] = useState<string[]>(() =>
    declarations.map(d => d.name || '')
  );
  // Per-box LaTeX input
  const [localLatex, setLocalLatex] = useState<string[]>(() =>
    declarations.map(() => '')
  );

  const handleNameChange = (index: number, value: string) => {
    setLocalNames(prev => {
      const next = [...prev];
      next[index] = value;
      return next;
    });
  };

  const handleLatexChange = (index: number, value: string) => {
    setLocalLatex(prev => {
      const next = [...prev];
      next[index] = value;
      return next;
    });
  };

  return (
    <div style={{
      padding: '16px',
      color: '#c9d1d9',
      fontFamily: '-apple-system, BlinkMacSystemFont, "Segoe UI", Helvetica, Arial, sans-serif',
    }}>
      <h3 style={{
        margin: '0 0 16px 0',
        color: '#e6edf3',
        fontSize: '14px',
        fontWeight: 600,
        letterSpacing: '0.02em',
      }}>
        WYSIWYG Editor
      </h3>

      {declarations.map((decl, i) => (
        <div key={i} style={{
          marginBottom: '12px',
          border: '1px solid #30363d',
          borderRadius: '6px',
          overflow: 'hidden',
          backgroundColor: '#161b22',
        }}>
          {/* Header: kind badge + editable name */}
          <div style={{
            display: 'flex',
            alignItems: 'center',
            padding: '6px 10px',
            backgroundColor: '#21262d',
            borderBottom: '1px solid #30363d',
            gap: '8px',
          }}>
            <span style={{
              fontSize: '11px',
              fontWeight: 600,
              color: declKindColor(decl),
              textTransform: 'uppercase',
              letterSpacing: '0.04em',
              flexShrink: 0,
            }}>
              definition
            </span>
            <input
              type="text"
              value={localNames[i] ?? decl.name ?? ''}
              onChange={(e) => handleNameChange(i, e.target.value)}
              spellCheck={false}
              style={{
                flex: 1,
                background: 'none',
                border: 'none',
                outline: 'none',
                color: '#e6edf3',
                fontFamily: '"JetBrains Mono", "Fira Code", Menlo, Consolas, monospace',
                fontSize: '13px',
                fontWeight: 500,
                padding: '2px 4px',
                borderRadius: '3px',
              }}
              onFocus={(e) => {
                e.currentTarget.style.backgroundColor = '#0d1117';
              }}
              onBlur={(e) => {
                e.currentTarget.style.backgroundColor = 'transparent';
              }}
            />
          </div>

          {/* LaTeX input */}
          <div style={{
            padding: '6px 10px',
            borderBottom: '1px solid #30363d',
            display: 'flex',
            alignItems: 'center',
            gap: '8px',
          }}>
            <span style={{
              fontSize: '11px',
              color: '#8b949e',
              flexShrink: 0,
            }}>
              LaTeX
            </span>
            <input
              type="text"
              value={localLatex[i] ?? ''}
              onChange={(e) => handleLatexChange(i, e.target.value)}
              placeholder="\forall x, f(x) + g(x)"
              spellCheck={false}
              style={{
                flex: 1,
                background: '#0d1117',
                border: '1px solid #30363d',
                borderRadius: '4px',
                outline: 'none',
                color: '#c9d1d9',
                fontFamily: '"JetBrains Mono", "Fira Code", Menlo, Consolas, monospace',
                fontSize: '13px',
                padding: '4px 8px',
              }}
              onFocus={(e) => {
                e.currentTarget.style.borderColor = '#58a6ff';
              }}
              onBlur={(e) => {
                e.currentTarget.style.borderColor = '#30363d';
              }}
            />
          </div>

          {/* TeX preview */}
          <TeXExpressionEditor latex={localLatex[i] ?? ''} />

          {/* Structured math editor */}
          <div style={{ padding: '6px 10px', borderTop: '1px solid #30363d' }}>
            <SyntaxReferencePanel registry={registry} />
            <div style={{
              fontSize: '11px',
              color: '#8b949e',
              marginBottom: '4px',
            }}>
              Structured Editor
            </div>
            <MathEditor placeholder="type math here" registry={registry} />
          </div>
        </div>
      ))}
    </div>
  );
}

// ============================================================================
// Syntax Reference Panel — compact display of available syntax patterns
// ============================================================================

function SyntaxReferenceEntry({ entry }: { entry: SyntaxEntry }) {
  const ref = useRef<HTMLSpanElement>(null);
  const latex = useMemo(() => patternToDisplayLatex(entry.pattern), [entry.pattern]);

  useEffect(() => {
    if (!ref.current) return;
    try {
      katex.render(latex, ref.current, {
        displayMode: false,
        throwOnError: false,
        trust: (context) => ['\\htmlId', '\\class', '\\textcolor'].includes(context.command),
        strict: false,
      });
    } catch {
      ref.current.textContent = latex;
    }
  }, [latex]);

  // Clean template for display: \$x => body → λx => body, $$a → a, $a → a
  const displayTemplate = entry.template
    .replace(/\\\$/g, 'λ')       // \$ (lambda binder) → λ
    .replace(/\$\$/g, '$')       // $$ (auto-paren sigil) → $ (temporary)
    .replace(/\$/g, '');          // strip all remaining $ sigils

  return (
    <>
      <span ref={ref} style={{ fontSize: '11px', justifySelf: 'end' }} />
      <span style={{ color: '#30363d', fontSize: '10px' }}>{'\u2192'}</span>
      <span style={{
        fontFamily: '"JetBrains Mono", "Fira Code", Menlo, Consolas, monospace',
        color: '#8b949e',
        fontSize: '10px',
      }}>
        {displayTemplate}
      </span>
    </>
  );
}

function SymbolMapEntry({ symbol, source }: { symbol: string; source: string }) {
  const ref = useRef<HTMLSpanElement>(null);

  useEffect(() => {
    if (!ref.current) return;
    try {
      katex.render(symbol, ref.current, {
        displayMode: false,
        throwOnError: false,
        strict: false,
      });
    } catch {
      ref.current.textContent = symbol;
    }
  }, [symbol]);

  return (
    <>
      <span ref={ref} style={{ fontSize: '11px', justifySelf: 'end' }} />
      <span style={{ color: '#30363d', fontSize: '10px' }}>{'\u2192'}</span>
      <span style={{
        fontFamily: '"JetBrains Mono", "Fira Code", Menlo, Consolas, monospace',
        color: '#8b949e',
        fontSize: '10px',
      }}>
        {source}
      </span>
    </>
  );
}

function SyntaxReferencePanel({ registry }: { registry: SyntaxRegistry }) {
  const [expanded, setExpanded] = useState(false);

  const symbolEntries = useMemo(() =>
    [...registry.symbolMap.entries()],
    [registry.symbolMap]
  );

  return (
    <div style={{
      marginBottom: '4px',
      borderRadius: '4px',
      border: '1px solid #21262d',
      backgroundColor: '#0d1117',
      overflow: 'hidden',
    }}>
      <div
        onClick={() => setExpanded(prev => !prev)}
        style={{
          display: 'flex',
          alignItems: 'center',
          gap: '6px',
          padding: '3px 8px',
          cursor: 'pointer',
          userSelect: 'none',
          fontSize: '10px',
          color: '#484f58',
          letterSpacing: '0.03em',
        }}
      >
        <span style={{ fontSize: '8px' }}>{expanded ? '\u25BC' : '\u25B6'}</span>
        <span>Syntax ({registry.entries.length + symbolEntries.length})</span>
      </div>

      {expanded && (
        <div style={{
          padding: '4px 8px 6px',
          display: 'grid',
          gridTemplateColumns: 'auto auto 1fr',
          rowGap: '2px',
          columnGap: '8px',
          alignItems: 'center',
          borderTop: '1px solid #21262d',
        }}>
          {symbolEntries.map(([sym, { source }]) => (
            <SymbolMapEntry key={sym} symbol={sym} source={source} />
          ))}
          {registry.entries.map(entry => (
            <SyntaxReferenceEntry key={entry.name} entry={entry} />
          ))}
        </div>
      )}
    </div>
  );
}
