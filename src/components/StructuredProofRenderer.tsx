import React from 'react';
import {
  ProofElement,
  EquationElement,
  CommentElement,
  CaseSplitElement,
  SublemmaElement,
  StructuredProof,
  ExpressionNode
} from '../types/enhanced-focus';
import { MathJaxExpressionRenderer } from './MathJaxExpressionRenderer';

interface StructuredProofRendererProps {
  proof: StructuredProof;
  onElementClick?: (element: ProofElement) => void;
  showJustifications?: boolean;
}

interface EquationRendererProps {
  element: EquationElement;
  onElementClick?: (element: ProofElement) => void;
  showJustification?: boolean;
  isAligned?: boolean;
  alignmentRef?: React.RefObject<HTMLDivElement>;
}

interface AlignmentInfo {
  maxLeftWidth: number;
  totalElements: number;
}

// Helper function to extract left and right sides from an equality expression
function extractSidesFromEquality(node: ExpressionNode): { left: ExpressionNode; right: ExpressionNode } | null {
  if (node.type === 'equality' || (node.type === 'binop' && node.operator === '=')) {
    if (node.children.length >= 2) {
      return {
        left: node.children[0],
        right: node.children[1]
      };
    }
  }
  return null;
}

// Helper function to calculate alignment info for equations
function calculateAlignment(elements: ProofElement[]): AlignmentInfo {
  // For now, use a simple approach - we'll measure in the actual component
  return {
    maxLeftWidth: 120, // Default estimate
    totalElements: elements.filter(el => el.type === 'equation').length
  };
}

function EquationRenderer({ element, onElementClick, showJustification = true, isAligned = true }: EquationRendererProps) {
  const sides = extractSidesFromEquality(element.content as ExpressionNode);

  if (!sides) {
    // Fallback: render the full expression
    return (
      <div
        style={{
          display: 'flex',
          alignItems: 'center',
          padding: '8px 0',
          cursor: onElementClick ? 'pointer' : 'default'
        }}
        onClick={() => onElementClick?.(element)}
      >
        <div style={{ minWidth: '40px', textAlign: 'center', fontFamily: 'monospace' }}>
          <MathJaxExpressionRenderer
            expression={element.content as ExpressionNode}
            focusPath={[]}
            onFocusChange={() => {}}
            isActive={false}
          />
        </div>
        {showJustification && element.justification && (
          <div style={{
            marginLeft: '20px',
            fontSize: '14px',
            color: '#666',
            fontStyle: 'italic'
          }}>
            ({element.justification})
          </div>
        )}
      </div>
    );
  }

  return (
    <div
      style={{
        display: 'flex',
        alignItems: 'center',
        padding: '6px 0',
        cursor: onElementClick ? 'pointer' : 'default',
        transition: 'background-color 0.2s ease'
      }}
      onClick={() => onElementClick?.(element)}
      onMouseEnter={(e) => {
        e.currentTarget.style.backgroundColor = '#f8f9fa';
      }}
      onMouseLeave={(e) => {
        e.currentTarget.style.backgroundColor = 'transparent';
      }}
    >
      {/* Left side of equation */}
      <div style={{
        display: 'flex',
        justifyContent: 'flex-end',
        alignItems: 'center',
        minWidth: isAligned ? '120px' : 'auto',
        marginRight: '8px'
      }}>
        <MathJaxExpressionRenderer
          expression={sides.left}
          focusPath={[]}
          onFocusChange={() => {}}
          isActive={false}
        />
      </div>

      {/* Equals sign */}
      <div style={{
        fontSize: '18px',
        fontWeight: 'bold',
        color: '#007acc',
        margin: '0 12px',
        minWidth: '20px',
        textAlign: 'center'
      }}>
        =
      </div>

      {/* Right side of equation */}
      <div style={{ flex: 1, display: 'flex', alignItems: 'center' }}>
        <MathJaxExpressionRenderer
          expression={sides.right}
          focusPath={[]}
          onFocusChange={() => {}}
          isActive={false}
        />

        {showJustification && element.justification && (
          <div style={{
            marginLeft: '20px',
            fontSize: '13px',
            color: '#666',
            fontStyle: 'italic',
            backgroundColor: '#f8f9fa',
            padding: '2px 8px',
            borderRadius: '12px',
            border: '1px solid #e9ecef'
          }}>
            {element.justification}
          </div>
        )}
      </div>
    </div>
  );
}

function CommentRenderer({ element, onElementClick }: { element: CommentElement; onElementClick?: (element: ProofElement) => void }) {
  const getCommentStyle = (commentType: CommentElement['commentType']) => {
    switch (commentType) {
      case 'explanation':
        return { backgroundColor: '#e8f4f8', borderLeft: '4px solid #17a2b8', color: '#0c5460' };
      case 'assumption':
        return { backgroundColor: '#f8f9fa', borderLeft: '4px solid #6c757d', color: '#495057' };
      case 'goal':
        return { backgroundColor: '#d4edda', borderLeft: '4px solid #28a745', color: '#155724' };
      case 'strategy':
        return { backgroundColor: '#fff3cd', borderLeft: '4px solid #ffc107', color: '#856404' };
      default:
        return { backgroundColor: '#f8f9fa', borderLeft: '4px solid #6c757d', color: '#495057' };
    }
  };

  const style = getCommentStyle(element.commentType);

  return (
    <div
      style={{
        ...style,
        padding: '12px 16px',
        margin: '8px 0',
        borderRadius: '0 6px 6px 0',
        fontSize: '14px',
        fontStyle: element.commentType === 'explanation' ? 'italic' : 'normal',
        cursor: onElementClick ? 'pointer' : 'default'
      }}
      onClick={() => onElementClick?.(element)}
    >
      <div style={{ fontWeight: '500', textTransform: 'capitalize', marginBottom: '4px' }}>
        {element.commentType}:
      </div>
      {element.content as string}
    </div>
  );
}

function CaseSplitRenderer({ element, onElementClick }: { element: CaseSplitElement; onElementClick?: (element: ProofElement) => void }) {
  return (
    <div style={{ margin: '16px 0' }}>
      <div style={{
        fontWeight: 'bold',
        fontSize: '16px',
        color: '#495057',
        marginBottom: '12px',
        cursor: onElementClick ? 'pointer' : 'default'
      }}
      onClick={() => onElementClick?.(element)}
      >
        Case Split: {element.content as string}
      </div>

      <div style={{ marginLeft: '20px' }}>
        {element.cases.map((caseElement, index) => (
          <div key={caseElement.id} style={{
            marginBottom: '16px',
            padding: '12px',
            border: '1px solid #e9ecef',
            borderRadius: '6px',
            backgroundColor: '#fafbfc'
          }}>
            <div style={{
              fontWeight: '600',
              color: '#007acc',
              marginBottom: '8px',
              fontSize: '14px'
            }}>
              Case {index + 1}: {element.conditions?.[index] || `Condition ${index + 1}`}
            </div>
            <StructuredProofRenderer
              proof={{
                elements: [caseElement],
                metadata: {
                  assumptions: [],
                  goal: {} as ExpressionNode
                }
              }}
              onElementClick={onElementClick}
            />
          </div>
        ))}
      </div>
    </div>
  );
}

function SublemmaRenderer({ element, onElementClick }: { element: SublemmaElement; onElementClick?: (element: ProofElement) => void }) {
  return (
    <div style={{
      margin: '20px 0',
      border: '2px solid #007acc',
      borderRadius: '8px',
      backgroundColor: '#f8fcff'
    }}>
      <div style={{
        backgroundColor: '#007acc',
        color: 'white',
        padding: '8px 16px',
        fontWeight: 'bold',
        borderRadius: '6px 6px 0 0',
        cursor: onElementClick ? 'pointer' : 'default'
      }}
      onClick={() => onElementClick?.(element)}
      >
        Lemma: {element.content as string}
      </div>

      <div style={{ padding: '16px' }}>
        <div style={{
          fontWeight: '600',
          marginBottom: '12px',
          color: '#495057'
        }}>
          Statement:
        </div>
        <div style={{ marginBottom: '16px', marginLeft: '12px' }}>
          <MathJaxExpressionRenderer
            expression={element.statement}
            focusPath={[]}
            onFocusChange={() => {}}
            isActive={false}
          />
        </div>

        <div style={{
          fontWeight: '600',
          marginBottom: '8px',
          color: '#495057'
        }}>
          Proof:
        </div>
        <div style={{ marginLeft: '12px' }}>
          <StructuredProofRenderer
            proof={{
              elements: element.proof,
              metadata: {
                assumptions: [],
                goal: {} as ExpressionNode
              }
            }}
            onElementClick={onElementClick}
          />
        </div>
      </div>
    </div>
  );
}

export function StructuredProofRenderer({
  proof,
  onElementClick,
  showJustifications = true
}: StructuredProofRendererProps) {
  const alignmentInfo = calculateAlignment(proof.elements);

  if (proof.elements.length === 0) {
    return (
      <div style={{
        padding: '24px',
        textAlign: 'center',
        color: '#666',
        fontStyle: 'italic',
        backgroundColor: '#f8f9fa',
        borderRadius: '8px',
        border: '2px dashed #dee2e6'
      }}>
        No proof steps yet. Start building your structured proof by applying rules.
      </div>
    );
  }

  return (
    <div style={{
      fontFamily: 'system-ui, -apple-system, sans-serif',
      lineHeight: 1.6,
      padding: '16px',
      backgroundColor: 'white',
      border: '1px solid #e9ecef',
      borderRadius: '8px',
      boxShadow: '0 2px 4px rgba(0,0,0,0.05)'
    }}>
      {/* Proof header */}
      {proof.metadata.theorem && (
        <div style={{
          marginBottom: '20px',
          padding: '12px 16px',
          backgroundColor: '#007acc',
          color: 'white',
          borderRadius: '6px',
          fontWeight: 'bold',
          fontSize: '16px'
        }}>
          Theorem: {proof.metadata.theorem}
        </div>
      )}

      {/* Assumptions */}
      {proof.metadata.assumptions.length > 0 && (
        <div style={{
          marginBottom: '16px',
          padding: '12px',
          backgroundColor: '#f8f9fa',
          borderRadius: '6px',
          border: '1px solid #e9ecef'
        }}>
          <div style={{ fontWeight: '600', marginBottom: '8px', color: '#495057' }}>
            Assumptions:
          </div>
          <ul style={{ margin: '0', paddingLeft: '20px' }}>
            {proof.metadata.assumptions.map(assumption => (
              <li key={assumption.id} style={{ marginBottom: '4px', fontSize: '14px' }}>
                <strong>{assumption.name}:</strong> {assumption.description}
              </li>
            ))}
          </ul>
        </div>
      )}

      {/* Proof elements */}
      <div style={{
        backgroundColor: '#fafbfc',
        padding: '16px',
        borderRadius: '6px',
        border: '1px solid #e9ecef'
      }}>
        <div style={{
          fontWeight: '600',
          marginBottom: '12px',
          color: '#495057',
          fontSize: '15px'
        }}>
          Proof:
        </div>

        {proof.elements.map((element, index) => {
          const key = `${element.id}-${index}`;

          switch (element.type) {
            case 'equation':
              return (
                <EquationRenderer
                  key={key}
                  element={element as EquationElement}
                  onElementClick={onElementClick}
                  showJustification={showJustifications}
                  isAligned={alignmentInfo.totalElements > 1}
                />
              );

            case 'comment':
              return (
                <CommentRenderer
                  key={key}
                  element={element as CommentElement}
                  onElementClick={onElementClick}
                />
              );

            case 'case_split':
              return (
                <CaseSplitRenderer
                  key={key}
                  element={element as CaseSplitElement}
                  onElementClick={onElementClick}
                />
              );

            case 'sublemma':
              return (
                <SublemmaRenderer
                  key={key}
                  element={element as SublemmaElement}
                  onElementClick={onElementClick}
                />
              );

            default:
              return (
                <div key={key} style={{
                  padding: '8px 12px',
                  backgroundColor: '#fff3cd',
                  border: '1px solid #ffeaa7',
                  borderRadius: '4px',
                  margin: '8px 0',
                  fontSize: '14px'
                }}>
                  Unknown proof element type: {element.type}
                </div>
              );
          }
        })}
      </div>
    </div>
  );
}