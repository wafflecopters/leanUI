import React, { useState } from 'react';
import { CompiledDeclaration } from '../compiler/compile';
import { TeXExpressionEditor } from './TeXExpressionEditor';
import { MathEditor } from './MathEditor';

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
            <div style={{
              fontSize: '11px',
              color: '#8b949e',
              marginBottom: '4px',
            }}>
              Structured Editor
            </div>
            <MathEditor placeholder="type math here" />
          </div>
        </div>
      ))}
    </div>
  );
}
