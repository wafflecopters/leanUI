import { useState, useEffect } from 'react';
import { ExpressionNode } from '../types/enhanced-focus';
import { leanClient, LeanCheckResponse } from '../services/lean-client';

interface ASTModalProps {
  expression: ExpressionNode;
  isOpen: boolean;
  onClose: () => void;
}

export function ASTModal({ expression, isOpen, onClose }: ASTModalProps) {
  const [leanResponse, setLeanResponse] = useState<LeanCheckResponse | null>(null);
  const [isChecking, setIsChecking] = useState(false);
  const [serverAvailable, setServerAvailable] = useState<boolean | null>(null);

  // Check server health when modal opens
  useEffect(() => {
    if (isOpen) {
      checkServerHealth();
      checkExpressionWithLean();
    }
  }, [isOpen, expression]);

  const checkServerHealth = async () => {
    const isHealthy = await leanClient.checkHealth();
    setServerAvailable(isHealthy);
  };

  const checkExpressionWithLean = async () => {
    setIsChecking(true);
    try {
      // Ensure we have a session
      if (!leanClient.getCurrentSessionId()) {
        const sessionResult = await leanClient.createSession();
        if (!sessionResult.success) {
          setLeanResponse({
            success: false,
            error: sessionResult.error || 'Failed to create Lean session'
          });
          return;
        }
      }

      // Convert expression to Lean syntax
      const leanSyntax = leanClient.expressionToLeanSyntax(expression);

      // Basic assumptions for our mathematical context
      const assumptions = ['(f : ℝ → ℝ)', '(c : ℝ)', '(x : ℝ)'];

      const response = await leanClient.checkExpression(leanSyntax, assumptions);
      setLeanResponse(response);
    } catch (error) {
      console.error('Error checking expression:', error);
      setLeanResponse({
        success: false,
        error: String(error)
      });
    } finally {
      setIsChecking(false);
    }
  };

  const renderAST = (node: ExpressionNode, depth: number = 0): JSX.Element => {
    const indent = depth * 16;
    const hasChildren = node.children && node.children.length > 0;

    return (
      <div key={`ast-${depth}-${Date.now()}`} style={{ marginLeft: indent, fontSize: '13px' }}>
        <div style={{
          padding: '4px 8px',
          backgroundColor: depth % 2 === 0 ? '#f8f9fa' : '#e9ecef',
          border: '1px solid #dee2e6',
          borderRadius: '4px',
          margin: '2px 0',
          fontFamily: 'monospace'
        }}>
          <strong style={{ color: '#007acc' }}>{node.type}</strong>
          {node.operator && <span style={{ color: '#dc3545' }}> op: "{node.operator}"</span>}
          {node.value !== undefined && <span style={{ color: '#28a745' }}> val: "{node.value}"</span>}
          <div style={{ color: '#6c757d', fontSize: '11px', marginTop: '2px' }}>
            raw: "{node.raw}"
          </div>
        </div>
        {hasChildren && (
          <div>
            {node.children.map((child, childIndex) =>
              <div key={childIndex}>
                {renderAST(child, depth + 1)}
              </div>
            )}
          </div>
        )}
      </div>
    );
  };

  if (!isOpen) {
    return null;
  }

  return (
    <div style={{
      position: 'fixed',
      top: 0,
      left: 0,
      right: 0,
      bottom: 0,
      backgroundColor: 'rgba(0, 0, 0, 0.5)',
      zIndex: 10000,
      display: 'flex',
      alignItems: 'center',
      justifyContent: 'center',
      padding: '20px'
    }}>
      <div style={{
        backgroundColor: 'white',
        borderRadius: '12px',
        padding: '24px',
        maxWidth: '800px',
        maxHeight: '80vh',
        width: '100%',
        overflow: 'auto',
        boxShadow: '0 10px 25px rgba(0, 0, 0, 0.2)',
        position: 'relative'
      }}>
        {/* Header */}
        <div style={{
          display: 'flex',
          justifyContent: 'space-between',
          alignItems: 'center',
          marginBottom: '20px',
          borderBottom: '2px solid #007acc',
          paddingBottom: '16px'
        }}>
          <h2 style={{
            margin: 0,
            fontSize: '20px',
            fontWeight: 'bold',
            color: '#007acc'
          }}>
            AST & Lean Analysis
          </h2>
          <button
            onClick={onClose}
            style={{
              background: 'none',
              border: 'none',
              fontSize: '24px',
              cursor: 'pointer',
              color: '#6c757d',
              fontWeight: 'bold',
              padding: '4px 8px',
              borderRadius: '4px'
            }}
          >
            ×
          </button>
        </div>

        {/* Server Status */}
        <div style={{ marginBottom: '20px' }}>
          <div style={{
            fontSize: '14px',
            color: '#6c757d',
            marginBottom: '8px',
            fontWeight: '500'
          }}>
            🔗 Lean Server Status:
          </div>
          <div style={{ display: 'flex', alignItems: 'center', gap: '12px' }}>
            <span style={{
              padding: '4px 12px',
              borderRadius: '6px',
              fontSize: '12px',
              fontWeight: 'bold',
              backgroundColor: serverAvailable ? '#d4edda' : '#f8d7da',
              color: serverAvailable ? '#155724' : '#721c24'
            }}>
              {serverAvailable === null ? 'Checking...' :
               serverAvailable ? '✅ Connected' : '❌ Disconnected'}
            </span>
            {serverAvailable === false && (
              <button
                onClick={checkServerHealth}
                style={{
                  padding: '4px 12px',
                  fontSize: '12px',
                  backgroundColor: '#007acc',
                  color: 'white',
                  border: 'none',
                  borderRadius: '4px',
                  cursor: 'pointer'
                }}
              >
                🔄 Retry
              </button>
            )}
          </div>
        </div>

        {/* AST Structure */}
        <div style={{ marginBottom: '24px' }}>
          <h3 style={{
            margin: '0 0 12px 0',
            fontSize: '16px',
            color: '#495057',
            fontWeight: 'bold'
          }}>
            🌳 AST Structure:
          </h3>
          <div style={{
            maxHeight: '300px',
            overflow: 'auto',
            border: '2px solid #dee2e6',
            borderRadius: '8px',
            padding: '12px',
            backgroundColor: '#f8f9fa'
          }}>
            {renderAST(expression)}
          </div>
        </div>

        {/* Lean Integration */}
        {serverAvailable && (
          <div>
            <h3 style={{
              margin: '0 0 12px 0',
              fontSize: '16px',
              color: '#495057',
              fontWeight: 'bold'
            }}>
              🔬 Lean Analysis:
            </h3>

            {/* Lean Syntax */}
            <div style={{ marginBottom: '16px' }}>
              <div style={{
                fontSize: '14px',
                color: '#6c757d',
                marginBottom: '6px',
                fontWeight: '500'
              }}>
                📝 Lean Syntax:
              </div>
              <div style={{
                padding: '12px',
                backgroundColor: '#f8f9fa',
                border: '2px solid #e9ecef',
                borderRadius: '6px',
                fontFamily: 'monospace',
                fontSize: '14px',
                wordBreak: 'break-all',
                color: '#032f62'
              }}>
                {leanClient.expressionToLeanSyntax(expression)}
              </div>
            </div>

            {/* Loading State */}
            {isChecking && (
              <div style={{
                padding: '16px',
                backgroundColor: '#fff3cd',
                border: '2px solid #ffeaa7',
                borderRadius: '8px',
                fontSize: '14px',
                color: '#856404',
                textAlign: 'center'
              }}>
                🔄 Checking with Lean server...
              </div>
            )}

            {/* Results */}
            {leanResponse && !isChecking && (
              <div style={{
                padding: '16px',
                backgroundColor: leanResponse.success ? '#d4edda' : '#f8d7da',
                border: `2px solid ${leanResponse.success ? '#c3e6cb' : '#f5c6cb'}`,
                borderRadius: '8px',
                fontSize: '14px',
                color: leanResponse.success ? '#155724' : '#721c24'
              }}>
                {leanResponse.success ? (
                  <div>
                    <strong>✅ Valid Lean Expression</strong>
                    {leanResponse.typeInfo && leanResponse.typeInfo.length > 0 && (
                      <div style={{ marginTop: '8px' }}>
                        <div style={{ fontWeight: 'bold', marginBottom: '4px' }}>Type Information:</div>
                        {leanResponse.typeInfo.map((info, index) => (
                          <div key={index} style={{
                            fontFamily: 'monospace',
                            fontSize: '12px',
                            backgroundColor: 'rgba(255,255,255,0.7)',
                            padding: '4px 8px',
                            borderRadius: '4px',
                            margin: '2px 0'
                          }}>
                            <strong>{info.expression}</strong> : {info.type}
                          </div>
                        ))}
                      </div>
                    )}
                  </div>
                ) : (
                  <div>
                    <strong>❌ Error in Lean Expression</strong>
                    {leanResponse.errors && leanResponse.errors.length > 0 && (
                      <div style={{ marginTop: '8px' }}>
                        <div style={{ fontWeight: 'bold', marginBottom: '4px' }}>Errors:</div>
                        {leanResponse.errors.map((error, index) => (
                          <div key={index} style={{
                            fontSize: '12px',
                            fontFamily: 'monospace',
                            backgroundColor: 'rgba(255,255,255,0.7)',
                            padding: '4px 8px',
                            borderRadius: '4px',
                            margin: '2px 0'
                          }}>
                            {error}
                          </div>
                        ))}
                      </div>
                    )}
                    {leanResponse.error && (
                      <div style={{
                        marginTop: '8px',
                        fontSize: '12px',
                        fontFamily: 'monospace',
                        backgroundColor: 'rgba(255,255,255,0.7)',
                        padding: '4px 8px',
                        borderRadius: '4px'
                      }}>
                        {leanResponse.error}
                      </div>
                    )}
                  </div>
                )}

                {/* Debug Output */}
                {leanResponse.output && (
                  <details style={{ marginTop: '12px', fontSize: '12px' }}>
                    <summary style={{ cursor: 'pointer', fontWeight: 'bold', padding: '4px 0' }}>
                      🔍 Show Raw Lean Output
                    </summary>
                    <div style={{
                      marginTop: '8px',
                      padding: '8px',
                      backgroundColor: 'rgba(0,0,0,0.1)',
                      borderRadius: '4px',
                      fontFamily: 'monospace',
                      whiteSpace: 'pre-wrap',
                      fontSize: '11px'
                    }}>
                      <div><strong>stdout:</strong> {leanResponse.output.stdout}</div>
                      <div><strong>stderr:</strong> {leanResponse.output.stderr}</div>
                    </div>
                  </details>
                )}
              </div>
            )}

            {/* Re-check Button */}
            <div style={{ marginTop: '16px', textAlign: 'center' }}>
              <button
                onClick={checkExpressionWithLean}
                disabled={isChecking}
                style={{
                  padding: '8px 16px',
                  fontSize: '14px',
                  backgroundColor: '#007acc',
                  color: 'white',
                  border: 'none',
                  borderRadius: '6px',
                  cursor: isChecking ? 'not-allowed' : 'pointer',
                  opacity: isChecking ? 0.6 : 1,
                  fontWeight: 'bold'
                }}
              >
                {isChecking ? '🔄 Checking...' : '🔄 Re-check with Lean'}
              </button>
            </div>
          </div>
        )}

        {/* Close Button */}
        <div style={{ marginTop: '24px', textAlign: 'center', borderTop: '1px solid #e9ecef', paddingTop: '16px' }}>
          <button
            onClick={onClose}
            style={{
              padding: '8px 24px',
              fontSize: '14px',
              backgroundColor: '#6c757d',
              color: 'white',
              border: 'none',
              borderRadius: '6px',
              cursor: 'pointer',
              fontWeight: 'bold'
            }}
          >
            Close
          </button>
        </div>
      </div>
    </div>
  );
}