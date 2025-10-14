import { useState, useEffect } from 'react';
import { ExpressionNode } from '../types/enhanced-focus';
import { leanClient, LeanCheckResponse } from '../services/lean-client';

interface ASTDebugPanelProps {
  expression: ExpressionNode;
  isVisible: boolean;
  onToggle: () => void;
}

export function ASTDebugPanel({ expression, isVisible, onToggle }: ASTDebugPanelProps) {
  const [leanResponse, setLeanResponse] = useState<LeanCheckResponse | null>(null);
  const [isChecking, setIsChecking] = useState(false);
  const [serverAvailable, setServerAvailable] = useState<boolean | null>(null);

  // Check server health on mount
  useEffect(() => {
    // checkServerHealth();
  }, []);

  const checkServerHealth = async () => {
    const isHealthy = await leanClient.checkHealth();
    setServerAvailable(isHealthy);
  };

  // Check expression with Lean when it changes
  useEffect(() => {
    if (isVisible && serverAvailable) {
      checkExpressionWithLean();
    }
  }, [expression, isVisible, serverAvailable]);

  const checkExpressionWithLean = async () => {
    setIsChecking(true);
    try {
      // Ensure we have a session
      if (!leanClient.getCurrentSessionId()) {
        await leanClient.createSession();
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
    const indent = depth * 20;
    const hasChildren = node.children && node.children.length > 0;

    return (
      <div key={`ast-${depth}-${Date.now()}`} style={{ marginLeft: indent, fontSize: '12px' }}>
        <div style={{
          padding: '2px 4px',
          backgroundColor: depth % 2 === 0 ? '#f8f9fa' : '#e9ecef',
          border: '1px solid #dee2e6',
          borderRadius: '3px',
          margin: '1px 0',
          fontFamily: 'monospace'
        }}>
          <strong>{node.type}</strong>
          {node.operator && <span style={{ color: '#007acc' }}> op: "{node.operator}"</span>}
          {node.value !== undefined && <span style={{ color: '#28a745' }}> val: "{node.value}"</span>}
          <span style={{ color: '#6c757d', fontSize: '10px', marginLeft: '8px' }}>
            raw: "{node.raw}"
          </span>
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

  if (!isVisible) {
    return (
      <button
        onClick={onToggle}
        style={{
          position: 'fixed',
          bottom: '20px',
          right: '20px',
          padding: '8px 12px',
          backgroundColor: '#007acc',
          color: 'white',
          border: 'none',
          borderRadius: '4px',
          cursor: 'pointer',
          fontSize: '12px',
          fontWeight: 'bold',
          zIndex: 1000,
          boxShadow: '0 2px 4px rgba(0,0,0,0.2)'
        }}
      >
        Show AST Debug
      </button>
    );
  }

  return (
    <div style={{
      position: 'fixed',
      bottom: '20px',
      right: '20px',
      width: '400px',
      maxHeight: '500px',
      backgroundColor: 'white',
      border: '2px solid #007acc',
      borderRadius: '8px',
      padding: '16px',
      zIndex: 1000,
      boxShadow: '0 4px 8px rgba(0,0,0,0.2)',
      overflow: 'auto',
      fontSize: '14px'
    }}>
      <div style={{
        display: 'flex',
        justifyContent: 'space-between',
        alignItems: 'center',
        marginBottom: '12px',
        borderBottom: '1px solid #e9ecef',
        paddingBottom: '8px'
      }}>
        <h3 style={{
          margin: 0,
          fontSize: '16px',
          fontWeight: 'bold',
          color: '#007acc'
        }}>
          AST Debug Panel
        </h3>
        <button
          onClick={onToggle}
          style={{
            background: 'none',
            border: 'none',
            fontSize: '18px',
            cursor: 'pointer',
            color: '#6c757d'
          }}
        >
          ×
        </button>
      </div>

      {/* Server Status */}
      <div style={{ marginBottom: '12px' }}>
        <div style={{
          fontSize: '12px',
          color: '#6c757d',
          marginBottom: '4px',
          fontWeight: '500'
        }}>
          Lean Server Status:
        </div>
        <span style={{
          padding: '2px 6px',
          borderRadius: '3px',
          fontSize: '11px',
          fontWeight: 'bold',
          backgroundColor: serverAvailable ? '#d4edda' : '#f8d7da',
          color: serverAvailable ? '#155724' : '#721c24'
        }}>
          {serverAvailable === null ? 'Checking...' :
            serverAvailable ? 'Connected' : 'Disconnected'}
        </span>
        {serverAvailable === false && (
          <button
            onClick={checkServerHealth}
            style={{
              marginLeft: '8px',
              padding: '2px 6px',
              fontSize: '10px',
              backgroundColor: '#007acc',
              color: 'white',
              border: 'none',
              borderRadius: '3px',
              cursor: 'pointer'
            }}
          >
            Retry
          </button>
        )}
      </div>

      {/* Custom AST */}
      <div style={{ marginBottom: '16px' }}>
        <h4 style={{
          margin: '0 0 8px 0',
          fontSize: '14px',
          color: '#495057',
          fontWeight: 'bold'
        }}>
          Current AST Structure:
        </h4>
        <div style={{
          maxHeight: '200px',
          overflow: 'auto',
          border: '1px solid #dee2e6',
          borderRadius: '4px',
          padding: '8px'
        }}>
          {renderAST(expression)}
        </div>
      </div>

      {/* Lean Integration */}
      {serverAvailable && (
        <div>
          <h4 style={{
            margin: '0 0 8px 0',
            fontSize: '14px',
            color: '#495057',
            fontWeight: 'bold'
          }}>
            Lean Analysis:
          </h4>

          <div style={{ marginBottom: '8px' }}>
            <div style={{
              fontSize: '12px',
              color: '#6c757d',
              marginBottom: '4px'
            }}>
              Lean Syntax:
            </div>
            <div style={{
              padding: '6px',
              backgroundColor: '#f8f9fa',
              border: '1px solid #e9ecef',
              borderRadius: '3px',
              fontFamily: 'monospace',
              fontSize: '11px',
              wordBreak: 'break-all'
            }}>
              {leanClient.expressionToLeanSyntax(expression)}
            </div>
          </div>

          {isChecking && (
            <div style={{
              padding: '8px',
              backgroundColor: '#fff3cd',
              border: '1px solid #ffeaa7',
              borderRadius: '4px',
              fontSize: '12px',
              color: '#856404'
            }}>
              Checking with Lean server...
            </div>
          )}

          {leanResponse && !isChecking && (
            <div style={{
              padding: '8px',
              backgroundColor: leanResponse.success ? '#d4edda' : '#f8d7da',
              border: `1px solid ${leanResponse.success ? '#c3e6cb' : '#f5c6cb'}`,
              borderRadius: '4px',
              fontSize: '12px',
              color: leanResponse.success ? '#155724' : '#721c24'
            }}>
              {leanResponse.success ? (
                <div>
                  <strong>✓ Valid Lean expression</strong>
                  {leanResponse.typeInfo && leanResponse.typeInfo.length > 0 && (
                    <div style={{ marginTop: '4px' }}>
                      {leanResponse.typeInfo.map((info, index) => (
                        <div key={index} style={{ fontFamily: 'monospace', fontSize: '10px' }}>
                          {info.expression} : {info.type}
                        </div>
                      ))}
                    </div>
                  )}
                </div>
              ) : (
                <div>
                  <strong>✗ Error in Lean expression</strong>
                  {leanResponse.errors && leanResponse.errors.length > 0 && (
                    <div style={{ marginTop: '4px' }}>
                      {leanResponse.errors.map((error, index) => (
                        <div key={index} style={{ fontSize: '10px' }}>{error}</div>
                      ))}
                    </div>
                  )}
                  {leanResponse.error && (
                    <div style={{ marginTop: '4px', fontSize: '10px' }}>
                      {leanResponse.error}
                    </div>
                  )}
                </div>
              )}

              {/* Debug Output */}
              {leanResponse.output && (
                <details style={{ marginTop: '8px', fontSize: '10px' }}>
                  <summary style={{ cursor: 'pointer', fontWeight: 'bold' }}>
                    Show Raw Output
                  </summary>
                  <div style={{
                    marginTop: '4px',
                    padding: '4px',
                    backgroundColor: 'rgba(0,0,0,0.1)',
                    borderRadius: '2px',
                    fontFamily: 'monospace',
                    whiteSpace: 'pre-wrap'
                  }}>
                    <div><strong>stdout:</strong> {leanResponse.output.stdout}</div>
                    <div><strong>stderr:</strong> {leanResponse.output.stderr}</div>
                  </div>
                </details>
              )}
            </div>
          )}

          <button
            onClick={checkExpressionWithLean}
            disabled={isChecking}
            style={{
              marginTop: '8px',
              padding: '4px 8px',
              fontSize: '12px',
              backgroundColor: '#007acc',
              color: 'white',
              border: 'none',
              borderRadius: '3px',
              cursor: isChecking ? 'not-allowed' : 'pointer',
              opacity: isChecking ? 0.6 : 1
            }}
          >
            {isChecking ? 'Checking...' : 'Re-check with Lean'}
          </button>
        </div>
      )}
    </div>
  );
}