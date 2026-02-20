import React, { useState, useEffect, useRef, useCallback } from 'react';
import { CompiledDeclaration, parseTTSource } from '../compiler/compile';
import { prettyPrintCompiledDeclaration } from '../compiler/declaration-printer';

export interface WYSIWYGPanelProps {
  /** Compiled declarations for display (zonked kernel terms — no unsolved metas) */
  declarations: CompiledDeclaration[];
  /** Called with new source text when the user edits a box */
  onCodeChange: (code: string) => void;
}

/** Label for the declaration kind badge */
function declKindLabel(decl: CompiledDeclaration): string {
  if (decl.kind === 'inductive') {
    if (decl.isRecord) return 'record';
    return 'inductive';
  }
  return 'definition';
}

/** Color for the declaration kind badge */
function declKindColor(decl: CompiledDeclaration): string {
  if (decl.kind === 'inductive') {
    if (decl.isRecord) return '#a371f7';
    return '#3fb950';
  }
  return '#58a6ff';
}

/**
 * Validate that a box's text parses successfully.
 * Returns null on success, error message on failure.
 */
function validateBoxText(text: string): string | null {
  try {
    const result = parseTTSource(text);
    let hasDecleration = false;
    for (const block of result.blocks) {
      if (block.kind === 'declarations' && block.declarations.length > 0) {
        hasDecleration = true;
      }
      if (block.kind === 'error') {
        return block.errors[0]?.message || 'Parse error';
      }
    }
    if (!hasDecleration) {
      return 'No declaration found';
    }
    return null;
  } catch (e) {
    return e instanceof Error ? e.message : String(e);
  }
}

export function WYSIWYGPanel({ declarations, onCodeChange }: WYSIWYGPanelProps) {
  // Local textarea content per box
  const [localTexts, setLocalTexts] = useState<string[]>([]);
  // Which box is being edited (null = sync from props)
  const [editingIndex, setEditingIndex] = useState<number | null>(null);
  // Parse errors per box
  const [errors, setErrors] = useState<(string | null)[]>([]);
  // "+" menu state
  const [addMenuOpen, setAddMenuOpen] = useState(false);

  // Ref to track the latest local texts for closures
  const localTextsRef = useRef(localTexts);
  localTextsRef.current = localTexts;

  // Sync local texts from compiled declarations when not editing
  useEffect(() => {
    if (editingIndex === null) {
      const texts = declarations.map(d => prettyPrintCompiledDeclaration(d));
      setLocalTexts(texts);
      setErrors(declarations.map(() => null));
    }
  }, [declarations, editingIndex]);

  const handleFocus = useCallback((index: number) => {
    setEditingIndex(index);
  }, []);

  const handleChange = useCallback((index: number, value: string) => {
    setLocalTexts(prev => {
      const next = [...prev];
      next[index] = value;
      return next;
    });
    // Clear error on edit
    setErrors(prev => {
      const next = [...prev];
      next[index] = null;
      return next;
    });
  }, []);

  const handleBlur = useCallback((index: number) => {
    const text = localTextsRef.current[index];
    if (text === undefined) {
      setEditingIndex(null);
      return;
    }

    // Validate the edited box
    const error = validateBoxText(text);
    if (error) {
      setErrors(prev => {
        const next = [...prev];
        next[index] = error;
        return next;
      });
      setEditingIndex(null);
      return;
    }

    // Reconstruct full source from all box texts and push up
    setEditingIndex(null);
    const fullSource = localTextsRef.current.join('\n\n') + '\n';
    onCodeChange(fullSource);
  }, [onCodeChange]);

  const handleDelete = useCallback((index: number) => {
    const newTexts = localTextsRef.current.filter((_, i) => i !== index);
    const fullSource = newTexts.join('\n\n') + '\n';
    onCodeChange(fullSource);
  }, [onCodeChange]);

  const handleAdd = useCallback((kind: 'inductive' | 'record' | 'def') => {
    setAddMenuOpen(false);
    let template: string;
    switch (kind) {
      case 'inductive':
        template = 'inductive NewType : Type where\n  MkNewType : NewType';
        break;
      case 'record':
        template = 'record NewRecord where\n  field : Type';
        break;
      case 'def':
        template = 'newDef : Type\nnewDef = _';
        break;
    }
    const newTexts = [...localTextsRef.current, template];
    const fullSource = newTexts.join('\n\n') + '\n';
    onCodeChange(fullSource);
  }, [onCodeChange]);

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

      {/* Declaration boxes */}
      {declarations.map((decl, i) => (
        <div key={i} style={{
          marginBottom: '12px',
          border: '1px solid #30363d',
          borderRadius: '6px',
          overflow: 'hidden',
          backgroundColor: '#161b22',
        }}>
          {/* Header */}
          <div style={{
            display: 'flex',
            alignItems: 'center',
            justifyContent: 'space-between',
            padding: '6px 10px',
            backgroundColor: '#21262d',
            borderBottom: '1px solid #30363d',
          }}>
            <div style={{ display: 'flex', alignItems: 'center', gap: '8px' }}>
              <span style={{
                fontSize: '11px',
                fontWeight: 600,
                color: declKindColor(decl),
                textTransform: 'uppercase',
                letterSpacing: '0.04em',
              }}>
                {declKindLabel(decl)}
              </span>
              <span style={{ fontSize: '13px', color: '#e6edf3', fontWeight: 500 }}>
                {decl.name || '(anonymous)'}
              </span>
            </div>
            <button
              onClick={() => handleDelete(i)}
              style={{
                background: 'none',
                border: 'none',
                color: '#8b949e',
                cursor: 'pointer',
                fontSize: '16px',
                padding: '0 4px',
                lineHeight: 1,
              }}
              title="Delete declaration"
            >
              &times;
            </button>
          </div>

          {/* Textarea */}
          <textarea
            value={localTexts[i] ?? ''}
            onChange={(e) => handleChange(i, e.target.value)}
            onFocus={() => handleFocus(i)}
            onBlur={() => handleBlur(i)}
            spellCheck={false}
            style={{
              width: '100%',
              minHeight: '60px',
              padding: '8px 10px',
              backgroundColor: '#0d1117',
              color: '#c9d1d9',
              border: 'none',
              outline: 'none',
              resize: 'vertical',
              fontFamily: '"JetBrains Mono", "Fira Code", "Cascadia Code", Menlo, Consolas, monospace',
              fontSize: '13px',
              lineHeight: '1.5',
              boxSizing: 'border-box',
            }}
            rows={Math.max(2, (localTexts[i] ?? '').split('\n').length)}
          />

          {/* Error indicator */}
          {errors[i] && (
            <div style={{
              padding: '4px 10px',
              fontSize: '12px',
              color: '#f85149',
              backgroundColor: 'rgba(248, 81, 73, 0.1)',
              borderTop: '1px solid #30363d',
            }}>
              {errors[i]}
            </div>
          )}
        </div>
      ))}

      {/* Add button */}
      <div style={{ position: 'relative', textAlign: 'center', marginTop: '8px' }}>
        <button
          onClick={() => setAddMenuOpen(!addMenuOpen)}
          style={{
            background: '#21262d',
            border: '1px solid #30363d',
            borderRadius: '6px',
            color: '#c9d1d9',
            cursor: 'pointer',
            fontSize: '20px',
            padding: '4px 24px',
            lineHeight: 1,
          }}
          title="Add declaration"
        >
          +
        </button>

        {addMenuOpen && (
          <div style={{
            position: 'absolute',
            top: '100%',
            left: '50%',
            transform: 'translateX(-50%)',
            marginTop: '4px',
            backgroundColor: '#161b22',
            border: '1px solid #30363d',
            borderRadius: '6px',
            overflow: 'hidden',
            zIndex: 10,
            minWidth: '140px',
          }}>
            {([
              { kind: 'inductive' as const, label: 'Type', color: '#3fb950' },
              { kind: 'record' as const, label: 'Record', color: '#a371f7' },
              { kind: 'def' as const, label: 'Definition', color: '#58a6ff' },
            ]).map(item => (
              <button
                key={item.kind}
                onClick={() => handleAdd(item.kind)}
                style={{
                  display: 'block',
                  width: '100%',
                  padding: '8px 16px',
                  background: 'none',
                  border: 'none',
                  borderBottom: '1px solid #21262d',
                  color: item.color,
                  cursor: 'pointer',
                  fontSize: '13px',
                  textAlign: 'left',
                }}
                onMouseEnter={(e) => { e.currentTarget.style.backgroundColor = '#21262d'; }}
                onMouseLeave={(e) => { e.currentTarget.style.backgroundColor = 'transparent'; }}
              >
                {item.label}
              </button>
            ))}
          </div>
        )}
      </div>
    </div>
  );
}
