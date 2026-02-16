import React, { useState, useEffect, useRef, useCallback } from 'react';
import { ParsedDeclaration } from '../parser/parser';
import { prettyPrintDeclaration } from '../compiler/declaration-printer';
import { parseTTSource } from '../compiler/compile';
import { resolvePatternsInDeclarations } from '../parser/pattern-resolution';

export interface WYSIWYGPanelProps {
  declarations: ParsedDeclaration[];
  onDeclarationsChange: (decls: ParsedDeclaration[]) => void;
}

/** Label for the declaration kind badge */
function declKindLabel(decl: ParsedDeclaration): string {
  if (decl.kind === 'inductive') return 'inductive';
  if (decl.kind === 'record') return 'record';
  if (decl.kind === 'def') {
    if (decl.isPostulate) return 'postulate';
    return 'definition';
  }
  return 'expression';
}

/** Color for the declaration kind badge */
function declKindColor(decl: ParsedDeclaration): string {
  if (decl.kind === 'inductive') return '#3fb950';
  if (decl.kind === 'record') return '#a371f7';
  if (decl.kind === 'def') return '#58a6ff';
  return '#8b949e';
}

/**
 * Build a constructor name set from the declarations for pattern resolution.
 */
function buildSymbolContext(decls: ParsedDeclaration[]): Set<string> {
  const names = new Set<string>();
  for (const d of decls) {
    if (d.constructors) {
      for (const c of d.constructors) {
        names.add(c.name);
      }
    }
  }
  return names;
}

/**
 * Parse a single declaration's text, resolving patterns using
 * the constructor names from all other declarations.
 */
function parseBoxText(
  text: string,
  allDecls: ParsedDeclaration[],
  boxIndex: number
): { decls: ParsedDeclaration[]; error: string | null } {
  try {
    const result = parseTTSource(text);
    const parsed: ParsedDeclaration[] = [];
    for (const block of result.blocks) {
      if (block.kind === 'declarations') {
        parsed.push(...block.declarations);
      }
    }
    if (parsed.length === 0) {
      return { decls: [], error: 'No declaration found' };
    }

    // Build symbol context from all other declarations
    const otherDecls = allDecls.filter((_, i) => i !== boxIndex);
    const ctx = buildSymbolContext([...otherDecls, ...parsed]);
    const resolved = resolvePatternsInDeclarations(parsed, ctx);

    return { decls: resolved, error: null };
  } catch (e) {
    return { decls: [], error: e instanceof Error ? e.message : String(e) };
  }
}

export function WYSIWYGPanel({ declarations, onDeclarationsChange }: WYSIWYGPanelProps) {
  // Local textarea content per box
  const [localTexts, setLocalTexts] = useState<string[]>([]);
  // Which box is being edited (null = sync from props)
  const [editingIndex, setEditingIndex] = useState<number | null>(null);
  // Parse errors per box
  const [errors, setErrors] = useState<(string | null)[]>([]);
  // "+" menu state
  const [addMenuOpen, setAddMenuOpen] = useState(false);

  // Ref to track the latest declarations for closures
  const declsRef = useRef(declarations);
  declsRef.current = declarations;

  // Sync local texts from declarations when not editing
  useEffect(() => {
    if (editingIndex === null) {
      const texts = declarations.map(d => prettyPrintDeclaration(d));
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
    const text = localTexts[index];
    if (text === undefined) {
      setEditingIndex(null);
      return;
    }

    const { decls: parsed, error } = parseBoxText(text, declsRef.current, index);

    if (error || parsed.length === 0) {
      setErrors(prev => {
        const next = [...prev];
        next[index] = error || 'Empty declaration';
        return next;
      });
      setEditingIndex(null);
      return;
    }

    // Replace declaration(s) at this index with parsed result
    const newDecls = [...declsRef.current];
    newDecls.splice(index, 1, ...parsed);
    setEditingIndex(null);
    onDeclarationsChange(newDecls);
  }, [localTexts, onDeclarationsChange]);

  const handleDelete = useCallback((index: number) => {
    const newDecls = declsRef.current.filter((_, i) => i !== index);
    onDeclarationsChange(newDecls);
  }, [onDeclarationsChange]);

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

    // Parse the template to get a real declaration
    const { decls: parsed } = parseBoxText(template, declsRef.current, -1);
    if (parsed.length > 0) {
      onDeclarationsChange([...declsRef.current, ...parsed]);
    }
  }, [onDeclarationsChange]);

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
