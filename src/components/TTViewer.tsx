/**
 * TT (Typed Term) Viewer Component
 *
 * This component displays the underlying TT proof term being constructed.
 * It shows:
 * 1. The complete proof term with proper De Bruijn indices
 * 2. Holes (metavariables) that need to be filled
 * 3. Type information
 * 4. Pretty-printed version for readability
 *
 * This is the "ground truth" of what we're actually constructing,
 * separate from the UI representation.
 */

import { useState } from 'react';
import { TTerm, prettyPrint, TContext } from '../types/tt-core';
import { inferType, extractHoles, TypeCheckError } from '../types/tt-typecheck';

export interface TTViewerProps {
  /** The current proof term */
  proofTerm: TTerm | null;

  /** Context for the proof (variable names and types) */
  context?: TContext;

  /** Whether to show the raw AST structure */
  showRawAST?: boolean;
}

export function TTViewer({ proofTerm, context = [], showRawAST: initialShowRaw = false }: TTViewerProps) {
  const [showRawAST, setShowRawAST] = useState(initialShowRaw);
  const [showTypeInfo, setShowTypeInfo] = useState(true);
  const [expandedHoles, setExpandedHoles] = useState<Set<string>>(new Set());

  if (!proofTerm) {
    return (
      <div style={{
        padding: '20px',
        backgroundColor: '#f5f5f5',
        border: '2px solid #ddd',
        borderRadius: '8px',
        fontFamily: 'monospace',
        color: '#888'
      }}>
        <div style={{ fontWeight: 'bold', marginBottom: '8px', color: '#666' }}>
          TT Proof Term
        </div>
        <div style={{ fontStyle: 'italic' }}>
          No proof term constructed yet. Start by creating a claim and beginning a proof.
        </div>
      </div>
    );
  }

  // Extract holes from the term
  const holes = extractHoles(proofTerm);

  // Try to infer the type of the proof term
  let termType: TTerm | null = null;
  let typeError: string | null = null;
  try {
    termType = inferType(proofTerm, context);
  } catch (error) {
    if (error instanceof TypeCheckError) {
      typeError = error.message;
    } else {
      typeError = String(error);
    }
  }

  // Toggle hole expansion
  const toggleHole = (holeId: string) => {
    const newExpanded = new Set(expandedHoles);
    if (newExpanded.has(holeId)) {
      newExpanded.delete(holeId);
    } else {
      newExpanded.add(holeId);
    }
    setExpandedHoles(newExpanded);
  };

  return (
    <div style={{
      padding: '20px',
      backgroundColor: '#fafafa',
      border: '2px solid #007acc',
      borderRadius: '8px',
      fontFamily: 'monospace',
      fontSize: '14px',
      maxHeight: '400px',
      overflow: 'auto'
    }}>
      {/* Header */}
      <div style={{
        display: 'flex',
        justifyContent: 'space-between',
        alignItems: 'center',
        marginBottom: '16px',
        borderBottom: '2px solid #007acc',
        paddingBottom: '8px'
      }}>
        <div style={{ fontWeight: 'bold', fontSize: '16px', color: '#007acc' }}>
          TT Proof Term
        </div>
        <div style={{ display: 'flex', gap: '12px' }}>
          <button
            onClick={() => setShowTypeInfo(!showTypeInfo)}
            style={{
              padding: '4px 12px',
              backgroundColor: showTypeInfo ? '#007acc' : '#e0e0e0',
              color: showTypeInfo ? 'white' : '#333',
              border: 'none',
              borderRadius: '4px',
              cursor: 'pointer',
              fontSize: '12px'
            }}
          >
            {showTypeInfo ? 'Hide' : 'Show'} Type Info
          </button>
          <button
            onClick={() => setShowRawAST(!showRawAST)}
            style={{
              padding: '4px 12px',
              backgroundColor: showRawAST ? '#007acc' : '#e0e0e0',
              color: showRawAST ? 'white' : '#333',
              border: 'none',
              borderRadius: '4px',
              cursor: 'pointer',
              fontSize: '12px'
            }}
          >
            {showRawAST ? 'Hide' : 'Show'} Raw AST
          </button>
        </div>
      </div>

      {/* Type Information */}
      {showTypeInfo && (
        <div style={{
          marginBottom: '16px',
          padding: '12px',
          backgroundColor: typeError ? '#ffebee' : '#e3f2fd',
          borderLeft: `4px solid ${typeError ? '#f44336' : '#2196f3'}`,
          borderRadius: '4px'
        }}>
          <div style={{ fontWeight: 'bold', marginBottom: '4px', color: typeError ? '#c62828' : '#1565c0' }}>
            Type:
          </div>
          {typeError ? (
            <div style={{ color: '#c62828', fontSize: '12px' }}>
              <strong>Type Error:</strong> {typeError}
            </div>
          ) : termType ? (
            <div style={{ color: '#1565c0' }}>
              {prettyPrint(termType, context.map(b => b.name))}
            </div>
          ) : (
            <div style={{ color: '#666', fontStyle: 'italic' }}>Unknown</div>
          )}
        </div>
      )}

      {/* Holes Summary */}
      {holes.length > 0 && (
        <div style={{
          marginBottom: '16px',
          padding: '12px',
          backgroundColor: '#fff9c4',
          borderLeft: '4px solid #f57c00',
          borderRadius: '4px'
        }}>
          <div style={{ fontWeight: 'bold', marginBottom: '8px', color: '#e65100' }}>
            Holes ({holes.length}):
          </div>
          <div style={{ display: 'flex', flexDirection: 'column', gap: '8px' }}>
            {holes.map(hole => (
              <div key={hole.id} style={{
                padding: '8px',
                backgroundColor: 'white',
                border: '1px solid #ffb74d',
                borderRadius: '4px'
              }}>
                <div style={{ display: 'flex', justifyContent: 'space-between', alignItems: 'center' }}>
                  <div>
                    <span style={{ color: '#d84315', fontWeight: 'bold' }}>?{hole.id}</span>
                    <span style={{ color: '#666', marginLeft: '8px' }}>:</span>
                    <span style={{ color: '#1976d2', marginLeft: '8px' }}>
                      {prettyPrint(hole.type, hole.context.map(b => b.name))}
                    </span>
                  </div>
                  <button
                    onClick={() => toggleHole(hole.id)}
                    style={{
                      padding: '2px 8px',
                      backgroundColor: '#ff9800',
                      color: 'white',
                      border: 'none',
                      borderRadius: '4px',
                      cursor: 'pointer',
                      fontSize: '10px'
                    }}
                  >
                    {expandedHoles.has(hole.id) ? 'Hide' : 'Show'} Context
                  </button>
                </div>
                {expandedHoles.has(hole.id) && hole.context.length > 0 && (
                  <div style={{
                    marginTop: '8px',
                    padding: '8px',
                    backgroundColor: '#f5f5f5',
                    borderRadius: '4px',
                    fontSize: '12px'
                  }}>
                    <div style={{ fontWeight: 'bold', marginBottom: '4px', color: '#666' }}>
                      Context:
                    </div>
                    {hole.context.map((binding, idx) => (
                      <div key={idx} style={{ marginLeft: '8px', color: '#555' }}>
                        {binding.name} : {prettyPrint(binding.type, hole.context.slice(0, idx).map(b => b.name))}
                      </div>
                    ))}
                  </div>
                )}
              </div>
            ))}
          </div>
        </div>
      )}

      {/* Pretty-Printed Term */}
      <div style={{
        marginBottom: '16px',
        padding: '12px',
        backgroundColor: '#e8f5e9',
        borderLeft: '4px solid #4caf50',
        borderRadius: '4px'
      }}>
        <div style={{ fontWeight: 'bold', marginBottom: '8px', color: '#2e7d32' }}>
          Pretty-Printed Term:
        </div>
        <div style={{
          fontFamily: 'monospace',
          fontSize: '13px',
          color: '#1b5e20',
          whiteSpace: 'pre-wrap',
          wordBreak: 'break-word'
        }}>
          {prettyPrint(proofTerm, context.map(b => b.name))}
        </div>
      </div>

      {/* Raw AST */}
      {showRawAST && (
        <div style={{
          marginBottom: '16px',
          padding: '12px',
          backgroundColor: '#f3e5f5',
          borderLeft: '4px solid #9c27b0',
          borderRadius: '4px'
        }}>
          <div style={{ fontWeight: 'bold', marginBottom: '8px', color: '#6a1b9a' }}>
            Raw AST:
          </div>
          <pre style={{
            margin: 0,
            fontSize: '11px',
            color: '#4a148c',
            overflow: 'auto',
            maxHeight: '300px'
          }}>
            {JSON.stringify(proofTerm, null, 2)}
          </pre>
        </div>
      )}

      {/* Summary */}
      <div style={{
        marginTop: '12px',
        padding: '8px',
        backgroundColor: holes.length > 0 ? '#fff3e0' : '#e8f5e9',
        borderRadius: '4px',
        fontSize: '12px',
        color: '#666',
        fontStyle: 'italic'
      }}>
        {holes.length > 0 ? (
          <>
            ⚠️ Proof incomplete: {holes.length} hole{holes.length > 1 ? 's' : ''} remaining
          </>
        ) : (
          <>
            ✓ Proof complete: no holes remaining
          </>
        )}
      </div>
    </div>
  );
}
