/**
 * MathEditor — a structured WYSIWYG math editor rendered via KaTeX.
 *
 * The editor maintains a tree of MathNodes. Keyboard input mutates the tree
 * immutably. The tree is rendered to LaTeX with \htmlId annotations, and
 * KaTeX renders it to the DOM. Click events map back to tree positions via
 * the \htmlId-generated DOM ids.
 */

import React, { useCallback, useEffect, useMemo, useRef, useState } from 'react';
import katex from 'katex';
import 'katex/dist/katex.min.css';
import { MathEditorState, createEditorState, MathRow, MathNode } from '../math-editor/types';
import { handleInput, InputAction, getCommandCandidates, getSelectedCandidate } from '../math-editor/input';
import { moveRight, moveLeft, moveUp, moveDown, resolveRow, findChildIndex, getSlots, getSlotRow, clampOffsetBeforeHoles } from '../math-editor/navigation';
import { renderToLatex } from '../math-editor/render';
import { inferTypeSignature } from '../math-editor/type-inference';
import { SyntaxRegistry } from '../math-editor/syntax-registry';

export interface MathEditorProps {
  /** Initial state (optional — creates empty state by default) */
  initialState?: MathEditorState;
  /** Called whenever the state changes */
  onChange?: (state: MathEditorState) => void;
  /** Placeholder text shown when empty */
  placeholder?: string;
  /** Syntax registry for expression conversion (uses default if not provided) */
  registry?: SyntaxRegistry;
}

export function MathEditor({ initialState, onChange, placeholder, registry }: MathEditorProps) {
  const [state, setState] = useState<MathEditorState>(initialState ?? createEditorState);
  const containerRef = useRef<HTMLDivElement>(null);
  const katexRef = useRef<HTMLDivElement>(null);

  // Notify parent of changes
  useEffect(() => {
    onChange?.(state);
  }, [state, onChange]);

  // Render LaTeX via KaTeX
  const latex = useMemo(() => renderToLatex(state), [state]);

  useEffect(() => {
    if (!katexRef.current) return;

    const isEmpty = state.root.children.length === 0;

    if (isEmpty && placeholder) {
      // Show placeholder with cursor
      try {
        const placeholderLatex = `\\htmlId{cursor}{\\textcolor{#4488ff}{\\rule[-0.15em]{1.5px}{1.05em}}}\\textcolor{#484f58}{\\text{${placeholder}}}`;
        katex.render(placeholderLatex, katexRef.current, {
          displayMode: true,
          throwOnError: false,
          trust: (context) => ['\\htmlId', '\\class'].includes(context.command),
          strict: false,
        });
      } catch {
        katexRef.current.textContent = placeholder;
      }
      return;
    }

    try {
      katex.render(latex, katexRef.current, {
        displayMode: true,
        throwOnError: false,
        trust: (context) => ['\\htmlId', '\\class'].includes(context.command),
        strict: false,
      });
    } catch {
      katexRef.current.innerHTML = `<span style="color:#f85149">Render error</span>`;
    }
  }, [latex, placeholder, state.root.children.length]);

  // Keyboard handler
  const handleKeyDown = useCallback((e: React.KeyboardEvent) => {
    // Navigation keys
    if (e.key === 'ArrowRight') {
      e.preventDefault();
      setState(prev => moveRight(prev));
      return;
    }
    if (e.key === 'ArrowLeft') {
      e.preventDefault();
      setState(prev => moveLeft(prev));
      return;
    }
    if (e.key === 'ArrowUp') {
      e.preventDefault();
      setState(prev => moveUp(prev));
      return;
    }
    if (e.key === 'ArrowDown') {
      e.preventDefault();
      setState(prev => moveDown(prev));
      return;
    }

    // Tab — in command mode: accept command; otherwise jump to next slot
    if (e.key === 'Tab') {
      e.preventDefault();
      setState(prev => {
        if (prev.commandBuffer !== null) {
          return handleInput(prev, { type: 'char', char: 'Tab' });
        }
        return moveRight(prev);
      });
      return;
    }

    // Backspace
    if (e.key === 'Backspace') {
      e.preventDefault();
      setState(prev => handleInput(prev, { type: 'backspace' }));
      return;
    }

    // Enter in command mode triggers command execution
    if (e.key === 'Enter') {
      e.preventDefault();
      setState(prev => {
        if (prev.commandBuffer !== null) {
          return handleInput(prev, { type: 'char', char: 'Enter' });
        }
        return prev;
      });
      return;
    }

    // Escape — cancel command mode
    if (e.key === 'Escape') {
      e.preventDefault();
      setState(prev => ({ ...prev, commandBuffer: null }));
      return;
    }

    // Regular character input — single printable char
    if (e.key.length === 1 && !e.ctrlKey && !e.metaKey) {
      e.preventDefault();
      setState(prev => handleInput(prev, { type: 'char', char: e.key }));
      return;
    }
  }, []);

  // Click handler — map DOM click to cursor position
  const handleClick = useCallback((e: React.MouseEvent) => {
    // Focus the container
    containerRef.current?.focus();

    // Find the clicked node via htmlId
    const target = e.target as HTMLElement;
    const nodeEl = target.closest('[id^="n-"]') as HTMLElement | null;
    if (!nodeEl) {
      // Clicked outside any node — put cursor at end of root
      setState(prev => ({
        ...prev,
        cursor: { path: [], offset: prev.root.children.length },
      }));
      return;
    }

    const nodeIdStr = nodeEl.id.slice(2); // strip 'n-'
    const nodeId = parseInt(nodeIdStr, 10);
    if (isNaN(nodeId)) return;

    // Find path to this node in the tree
    const pathResult = findNodePath(state.root, nodeId);
    if (!pathResult) return;

    // Determine if click is on left or right half of the element
    const rect = nodeEl.getBoundingClientRect();
    const clickX = e.clientX;
    const isRightHalf = clickX > rect.left + rect.width / 2;

    const { parentPath, indexInParent, node } = pathResult;
    const slots = getSlots(node);

    if (slots.length > 0) {
      // Compound node — enter its first slot (or last slot if right half)
      if (isRightHalf) {
        const lastSlot = slots[slots.length - 1];
        const slotRow = getSlotRow(node, lastSlot.name)!;
        setState(prev => ({
          ...prev,
          cursor: {
            path: [...parentPath, { nodeId: node.id, slot: lastSlot.name }],
            offset: clampOffsetBeforeHoles(slotRow.children.length, slotRow),
          },
        }));
      } else {
        const firstSlot = slots[0];
        setState(prev => ({
          ...prev,
          cursor: {
            path: [...parentPath, { nodeId: node.id, slot: firstSlot.name }],
            offset: 0,
          },
        }));
      }
    } else {
      // Leaf node — position cursor before or after it
      setState(prev => ({
        ...prev,
        cursor: {
          path: parentPath,
          offset: isRightHalf ? indexInParent + 1 : indexInParent,
        },
      }));
    }
  }, [state.root]);

  // Command candidates
  const candidates = state.commandBuffer !== null ? getCommandCandidates(state.commandBuffer) : [];
  const selected = state.commandBuffer !== null ? getSelectedCandidate(state.commandBuffer) : null;

  // Type inference
  const typeSignature = useMemo(() => inferTypeSignature(state.root, registry), [state.root, registry]);

  return (
    <>
      <div
        ref={containerRef}
        tabIndex={0}
        onKeyDown={handleKeyDown}
        onClick={handleClick}
        style={{
          padding: '12px 16px',
          minHeight: '48px',
          cursor: 'text',
          outline: 'none',
          borderRadius: '6px',
          border: '1px solid #30363d',
          backgroundColor: '#0d1117',
          position: 'relative',
          display: 'flex',
          alignItems: 'center',
          justifyContent: 'center',
        }}
        onFocus={(e) => {
          e.currentTarget.style.borderColor = '#58a6ff';
        }}
        onBlur={(e) => {
          e.currentTarget.style.borderColor = '#30363d';
        }}
      >
        <div
          ref={katexRef}
          style={{
            color: '#ffffff',
            minHeight: '24px',
          }}
        />

        {/* Command buffer + candidates bar */}
        {state.commandBuffer !== null && (
          <div style={{
            position: 'absolute',
            bottom: '2px',
            left: '8px',
            right: '8px',
            fontSize: '11px',
            fontFamily: '"JetBrains Mono", "Fira Code", Menlo, Consolas, monospace',
            display: 'flex',
            gap: '6px',
            alignItems: 'center',
            overflow: 'hidden',
          }}>
            <span style={{ color: '#58a6ff', flexShrink: 0 }}>
              \{state.commandBuffer}
            </span>
            {candidates.length > 0 && (
              <span style={{ color: '#484f58', flexShrink: 0 }}>|</span>
            )}
            {candidates.slice(0, 8).map(c => (
              <span
                key={c}
                style={{
                  color: c === selected ? '#e6edf3' : '#484f58',
                  backgroundColor: c === selected ? '#30363d' : 'transparent',
                  padding: '0 3px',
                  borderRadius: '2px',
                  flexShrink: 0,
                }}
              >
                \{c}
              </span>
            ))}
            {candidates.length > 8 && (
              <span style={{ color: '#484f58' }}>+{candidates.length - 8}</span>
            )}
          </div>
        )}

        {/* Text buffer indicator */}
        {state.textBuffer !== null && (
          <div style={{
            position: 'absolute',
            bottom: '2px',
            left: '8px',
            fontSize: '11px',
            fontFamily: '"JetBrains Mono", "Fira Code", Menlo, Consolas, monospace',
            color: '#58a6ff',
          }}>
            text: {state.textBuffer || '…'}
          </div>
        )}
      </div>

      {/* Type inference display — outside the editor box so it's not clipped */}
      {typeSignature && (
        <div style={{
          marginTop: '4px',
          fontSize: '12px',
          fontFamily: '"JetBrains Mono", "Fira Code", Menlo, Consolas, monospace',
          color: '#484f58',
          textAlign: 'center',
          whiteSpace: 'nowrap',
          overflow: 'hidden',
          textOverflow: 'ellipsis',
        }}>
          {typeSignature}
        </div>
      )}
    </>
  );
}

// ============================================================================
// Tree traversal helper — find a node by ID and return its path
// ============================================================================

interface NodePathResult {
  parentPath: MathEditorState['cursor']['path'];
  indexInParent: number;
  node: MathNode;
}

function findNodePath(
  root: MathRow,
  targetId: number,
  currentPath: MathEditorState['cursor']['path'] = []
): NodePathResult | null {
  for (let i = 0; i < root.children.length; i++) {
    const child = root.children[i];
    if (child.id === targetId) {
      return { parentPath: currentPath, indexInParent: i, node: child };
    }

    // Search in slots
    const slots = getSlots(child);
    for (const slot of slots) {
      const slotRow = getSlotRow(child, slot.name);
      if (slotRow) {
        const result = findNodePath(
          slotRow,
          targetId,
          [...currentPath, { nodeId: child.id, slot: slot.name }]
        );
        if (result) return result;
      }
    }
  }
  return null;
}
