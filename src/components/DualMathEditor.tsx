/**
 * DualMathEditor — type signature editor with combined term display.
 *
 * The proof/definition editor has been removed — proofs are now handled
 * by the structured ProofTreeEditor.
 */

import React, { useCallback, useMemo, useRef, useState } from 'react';
import { MathEditor, MathEditorHandle } from './MathEditor';
import { SyntaxRegistry, convertToSource } from '../math-editor/syntax-registry';
import { inferTypeSignatureParts } from '../math-editor/type-inference';
import { MathEditorState, MathRow } from '../math-editor/types';

export interface DualMathEditorProps {
  placeholder?: string;
  registry?: SyntaxRegistry;
  initialTypeRoot?: MathRow;
}

/** Shared container styles — no individual border, embedded inside the outer wrapper. */
const editorContainerStyle: React.CSSProperties = {
  border: 'none',
  borderRadius: 0,
  backgroundColor: 'transparent',
};

export function DualMathEditor({ placeholder, registry, initialTypeRoot }: DualMathEditorProps) {
  const typeRef = useRef<MathEditorHandle>(null);

  // Compute initial state for type editor
  const typeInitialState = useMemo<MathEditorState | undefined>(() => {
    if (!initialTypeRoot || initialTypeRoot.children.length === 0) return undefined;
    return {
      root: initialTypeRoot,
      cursor: { path: [], offset: initialTypeRoot.children.length },
      commandBuffer: null,
      textBuffer: null,
    };
  }, [initialTypeRoot]);

  // Track root for combined term display
  const [typeRoot, setTypeRoot] = useState<MathRow | null>(initialTypeRoot ?? null);

  const handleTypeChange = useCallback((state: MathEditorState) => {
    setTypeRoot(state.root);
  }, []);

  const handleTypeClaim = useCallback(() => {
    // No-op now that there's only one editor
  }, []);

  // Combined term display
  const combinedTerm = useMemo(() => {
    if (!typeRoot) return null;

    const parts: string[] = [];

    // Type signature parts
    const typeParts = inferTypeSignatureParts(typeRoot, registry);
    if (typeParts) {
      parts.push(...typeParts);
    }

    return parts.length > 0 ? parts : null;
  }, [typeRoot, registry]);

  return (
    <div>
      {/* Outer container with shared border */}
      <div style={{
        borderRadius: '6px',
        border: '1px solid #30363d',
        backgroundColor: '#0d1117',
        overflow: 'hidden',
      }}>
        {/* Type signature editor */}
        <MathEditor
          ref={typeRef}
          initialState={typeInitialState}
          placeholder={placeholder}
          registry={registry}
          active={true}
          onFocusClaim={handleTypeClaim}
          onChange={handleTypeChange}
          showTypeInference={false}
          containerStyle={editorContainerStyle}
        />
      </div>

      {/* Combined term display */}
      {combinedTerm && (
        <div style={{
          marginTop: '4px',
          fontSize: '12px',
          fontFamily: '"JetBrains Mono", "Fira Code", Menlo, Consolas, monospace',
          color: '#484f58',
          textAlign: 'center',
          lineHeight: '1.8',
        }}>
          {combinedTerm.map((part, i) => (
            <React.Fragment key={i}>
              {i > 0 && <span style={{ color: '#30363d' }}>{' -> '}</span>}
              <span style={{ whiteSpace: 'nowrap' }}>{part}</span>
            </React.Fragment>
          ))}
        </div>
      )}
    </div>
  );
}
