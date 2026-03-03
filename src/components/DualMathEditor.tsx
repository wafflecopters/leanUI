/**
 * DualMathEditor — two MathEditor instances stacked vertically.
 *
 * Top: type signature editor (declaration)
 * Bottom: proof/definition editor with "Proof:" prefix
 *
 * The cursor transfers between them via arrow keys. Only the active
 * editor shows a cursor.
 */

import React, { useCallback, useMemo, useRef, useState } from 'react';
import { MathEditor, MathEditorHandle } from './MathEditor';
import { SyntaxRegistry, convertToSource } from '../math-editor/syntax-registry';
import { inferTypeSignatureParts } from '../math-editor/type-inference';
import { MathEditorState, MathRow, createEditorState } from '../math-editor/types';

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
  const [activeEditor, setActiveEditor] = useState<'type' | 'proof'>('type');
  const typeRef = useRef<MathEditorHandle>(null);
  const proofRef = useRef<MathEditorHandle>(null);

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

  // Track roots for combined term display
  const [typeRoot, setTypeRoot] = useState<MathRow | null>(initialTypeRoot ?? null);
  const [proofRoot, setProofRoot] = useState<MathRow | null>(null);

  const handleTypeChange = useCallback((state: MathEditorState) => {
    setTypeRoot(state.root);
  }, []);

  const handleProofChange = useCallback((state: MathEditorState) => {
    setProofRoot(state.root);
  }, []);

  // Transfer: type editor down → proof editor
  const handleTransferDown = useCallback(() => {
    setActiveEditor('proof');
    // Small delay to let React re-render with active=true before focusing
    setTimeout(() => proofRef.current?.focus(), 0);
  }, []);

  // Transfer: proof editor up → type editor
  const handleTransferUp = useCallback(() => {
    setActiveEditor('type');
    setTimeout(() => typeRef.current?.focus(), 0);
  }, []);

  // Click handlers
  const handleTypeClaim = useCallback(() => {
    setActiveEditor('type');
  }, []);

  const handleProofClaim = useCallback(() => {
    setActiveEditor('proof');
  }, []);

  // Combined term display
  const combinedTerm = useMemo(() => {
    if (!typeRoot && !proofRoot) return null;

    const parts: string[] = [];

    // Type signature parts
    if (typeRoot) {
      const typeParts = inferTypeSignatureParts(typeRoot, registry);
      if (typeParts) {
        parts.push(...typeParts);
      }
    }

    // Proof/definition expression
    if (proofRoot && proofRoot.children.length > 0) {
      const proofResult = convertToSource(registry ?? { symbolMap: new Map(), entries: [] }, proofRoot.children);
      if (proofResult.source !== '?') {
        // If we have type parts, the last part is the body — replace it with the full expression
        // Actually, just append the proof as a separate display
        parts.push(proofResult.source);
      }
    }

    return parts.length > 0 ? parts : null;
  }, [typeRoot, proofRoot, registry]);

  return (
    <div>
      {/* Outer container with shared border */}
      <div style={{
        borderRadius: '6px',
        border: '1px solid #30363d',
        backgroundColor: '#0d1117',
        overflow: 'hidden',
      }}>
        {/* Type signature editor (top) */}
        <MathEditor
          ref={typeRef}
          initialState={typeInitialState}
          placeholder={placeholder}
          registry={registry}
          active={activeEditor === 'type'}
          onTransferDown={handleTransferDown}
          onFocusClaim={handleTypeClaim}
          onChange={handleTypeChange}
          showTypeInference={false}
          containerStyle={editorContainerStyle}
        />

        {/* Thin divider */}
        <div style={{
          borderTop: '1px dashed #30363d',
          margin: '0 12px',
        }} />

        {/* Proof/definition editor (bottom) */}
        <MathEditor
          ref={proofRef}
          placeholder="enter proof"
          registry={registry}
          active={activeEditor === 'proof'}
          onTransferUp={handleTransferUp}
          onFocusClaim={handleProofClaim}
          onChange={handleProofChange}
          proofPrefix={"\\text{Proof: }"}
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
