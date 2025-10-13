import { useState } from 'react';
import {
  ExpressionNode,
  Assumption,
  LetElement,
  createLetElement,
  parseExpressionToAST
} from '../types/enhanced-focus';
import { MathJaxExpressionRenderer } from './MathJaxExpressionRenderer';
import { InstantiationDialog } from './InstantiationDialog';

interface LetManagerProps {
  letBindings: LetElement[];
  hypotheses: Assumption[];
  onAddLet: (letElement: LetElement) => void;
  onDeleteLet: (id: string) => void;
  onAddHypothesis: (hypothesis: Assumption) => void;
  onDeleteHypothesis: (id: string) => void;
  onInstantiate?: (letId: string, substitutions: Map<string, ExpressionNode>) => void;
  onStartProof?: (letId: string) => void;
}

export function LetManager({
  letBindings,
  hypotheses,
  onAddLet,
  onDeleteLet,
  onAddHypothesis,
  onDeleteHypothesis,
  onInstantiate,
  onStartProof
}: LetManagerProps) {
  const [showAddLet, setShowAddLet] = useState(false);
  const [showAddHypothesis, setShowAddHypothesis] = useState(false);
  const [letName, setLetName] = useState('');
  const [letExpression, setLetExpression] = useState('');
  const [letType, setLetType] = useState<string>('');
  const [letIsClaim, setLetIsClaim] = useState(false);
  const [letProofMethod, setLetProofMethod] = useState<'equality' | 'induction'>('equality');
  const [hypothesisName, setHypothesisName] = useState('');
  const [hypothesisExpression, setHypothesisExpression] = useState('');
  const [hypothesisDescription, setHypothesisDescription] = useState('');
  const [instantiatingLet, setInstantiatingLet] = useState<LetElement | null>(null);

  const handleAddLet = () => {
    if (!letName || !letExpression) return;

    try {
      const expr = parseExpressionToAST(letExpression);

      // Extract unbound variables and create hypotheses for them
      const unboundVars = extractUnboundVariables(expr);

      // Create hypotheses for each unbound variable
      unboundVars.forEach(varName => {
        const hypothesis: Assumption = {
          id: crypto.randomUUID(),
          name: varName,
          expression: `${varName} : ?`, // Type unknown, marked with ?
          description: `Auto-generated: ${varName} is unbound`,
          introducedBy: 'auto'
        };
        onAddHypothesis(hypothesis);
      });

      const letElement = createLetElement(
        letName,
        expr,
        letType || undefined,
        undefined, // derivedFrom
        letIsClaim,
        letIsClaim ? letProofMethod : undefined
      );
      onAddLet(letElement);

      // Reset form
      setLetName('');
      setLetExpression('');
      setLetType('');
      setLetIsClaim(false);
      setLetProofMethod('equality');
      setShowAddLet(false);
    } catch (error) {
      alert(`Error parsing expression: ${error}`);
    }
  };

  // Helper to extract all unbound variables from an expression
  const extractUnboundVariables = (expr: ExpressionNode, boundVars: Set<string> = new Set()): Set<string> => {
    const unboundVars = new Set<string>();

    const traverse = (node: ExpressionNode) => {
      if (node.type === 'variable' && typeof node.value === 'string') {
        const varName = node.value;
        // Check if it's not already bound (by let-bindings or hypotheses)
        const isAlreadyBound =
          boundVars.has(varName) ||
          letBindings.some(l => l.name === varName) ||
          hypotheses.some(h => h.name === varName);

        if (!isAlreadyBound) {
          unboundVars.add(varName);
        }
      }

      // Recurse into children
      if (node.children) {
        node.children.forEach(traverse);
      }
    };

    traverse(expr);
    return unboundVars;
  };

  // Helper to expand LaTeX-style shortcuts to Unicode symbols
  const expandTypeShortcuts = (text: string): string => {
    return text
      // Natural numbers
      .replace(/\\N(?![a-zA-Z])/g, 'ℕ')
      .replace(/\\Nat(?![a-zA-Z])/g, 'ℕ')
      .replace(/\\mathbb\{N\}/g, 'ℕ')
      // Real numbers
      .replace(/\\R(?![a-zA-Z])/g, 'ℝ')
      .replace(/\\Real(?![a-zA-Z])/g, 'ℝ')
      .replace(/\\mathbb\{R\}/g, 'ℝ')
      // Integers
      .replace(/\\Z(?![a-zA-Z])/g, 'ℤ')
      .replace(/\\Int(?![a-zA-Z])/g, 'ℤ')
      .replace(/\\mathbb\{Z\}/g, 'ℤ')
      // Rationals
      .replace(/\\Q(?![a-zA-Z])/g, 'ℚ')
      .replace(/\\mathbb\{Q\}/g, 'ℚ')
      // Complex
      .replace(/\\C(?![a-zA-Z])/g, 'ℂ')
      .replace(/\\mathbb\{C\}/g, 'ℂ')
      // Common operators
      .replace(/\\leq/g, '≤')
      .replace(/\\geq/g, '≥')
      .replace(/\\neq/g, '≠')
      .replace(/\\times/g, '×')
      .replace(/\\cdot/g, '·')
      .replace(/\\in/g, '∈')
      .replace(/\\notin/g, '∉')
      .replace(/\\subset/g, '⊂')
      .replace(/\\subseteq/g, '⊆')
      .replace(/\\forall/g, '∀')
      .replace(/\\exists/g, '∃');
  };

  const handleAddHypothesis = () => {
    if (!hypothesisName || !hypothesisExpression) return;

    try {
      // Try to parse the expression to find unbound variables
      // This handles cases like "x > 0" where we need to create a hypothesis for x
      const expr = parseExpressionToAST(hypothesisExpression);
      const unboundVars = extractUnboundVariables(expr);

      // Filter out the hypothesis name itself from unbound vars
      unboundVars.delete(hypothesisName);

      // Create hypotheses for each unbound variable (except the one being defined)
      unboundVars.forEach(varName => {
        const autoHypothesis: Assumption = {
          id: crypto.randomUUID(),
          name: varName,
          expression: `${varName} : ?`, // Type unknown, marked with ?
          description: `Auto-generated: ${varName} is unbound`,
          introducedBy: 'auto'
        };
        onAddHypothesis(autoHypothesis);
      });
    } catch (error) {
      // If parsing fails, just continue with adding the original hypothesis
      console.warn('Could not parse hypothesis expression for unbound variable extraction:', error);
    }

    const hypothesis: Assumption = {
      id: crypto.randomUUID(),
      name: hypothesisName,
      expression: hypothesisExpression,
      description: hypothesisDescription || hypothesisExpression,
      introducedBy: 'user'
    };

    onAddHypothesis(hypothesis);

    // Reset form
    setHypothesisName('');
    setHypothesisExpression('');
    setHypothesisDescription('');
    setShowAddHypothesis(false);
  };

  return (
    <div style={{
      backgroundColor: '#f8f9fa',
      border: '1px solid #e9ecef',
      borderRadius: '8px',
      padding: '16px',
      marginBottom: '20px'
    }}>
      <h3 style={{ marginTop: 0, color: '#495057' }}>Context Manager</h3>

      {/* Hypotheses Section */}
      <div style={{ marginBottom: '20px' }}>
        <div style={{
          display: 'flex',
          justifyContent: 'space-between',
          alignItems: 'center',
          marginBottom: '12px'
        }}>
          <h4 style={{ margin: 0, color: '#666' }}>Hypotheses</h4>
          <button
            onClick={() => setShowAddHypothesis(!showAddHypothesis)}
            style={{
              padding: '4px 12px',
              backgroundColor: '#007bff',
              color: 'white',
              border: 'none',
              borderRadius: '4px',
              cursor: 'pointer',
              fontSize: '14px'
            }}
          >
            + Add Hypothesis
          </button>
        </div>

        {showAddHypothesis && (
          <div style={{
            padding: '12px',
            backgroundColor: '#fff',
            border: '1px solid #dee2e6',
            borderRadius: '4px',
            marginBottom: '12px'
          }}>
            <input
              type="text"
              placeholder="Name (e.g., h1)"
              value={hypothesisName}
              onChange={(e) => setHypothesisName(e.target.value)}
              style={{
                width: '100%',
                padding: '6px',
                marginBottom: '8px',
                border: '1px solid #ced4da',
                borderRadius: '4px'
              }}
            />
            <input
              type="text"
              placeholder="Type (e.g., x : \R, or proposition like x > 0)"
              value={hypothesisExpression}
              onChange={(e) => setHypothesisExpression(e.target.value)}
              onBlur={(e) => setHypothesisExpression(expandTypeShortcuts(e.target.value))}
              style={{
                width: '100%',
                padding: '6px',
                marginBottom: '8px',
                border: '1px solid #ced4da',
                borderRadius: '4px'
              }}
            />
            <input
              type="text"
              placeholder="Description (optional)"
              value={hypothesisDescription}
              onChange={(e) => setHypothesisDescription(e.target.value)}
              style={{
                width: '100%',
                padding: '6px',
                marginBottom: '8px',
                border: '1px solid #ced4da',
                borderRadius: '4px'
              }}
            />
            <div style={{ display: 'flex', gap: '8px', justifyContent: 'flex-end' }}>
              <button
                onClick={() => setShowAddHypothesis(false)}
                style={{
                  padding: '6px 12px',
                  backgroundColor: '#6c757d',
                  color: 'white',
                  border: 'none',
                  borderRadius: '4px',
                  cursor: 'pointer'
                }}
              >
                Cancel
              </button>
              <button
                onClick={handleAddHypothesis}
                style={{
                  padding: '6px 12px',
                  backgroundColor: '#28a745',
                  color: 'white',
                  border: 'none',
                  borderRadius: '4px',
                  cursor: 'pointer'
                }}
              >
                Add
              </button>
            </div>
          </div>
        )}

        <div style={{ display: 'flex', flexDirection: 'column', gap: '8px' }}>
{hypotheses.map(hypothesis => {
            const isAutoGenerated = hypothesis.introducedBy === 'auto';
            const hasUnknownType = hypothesis.expression.includes(' : ?');

            return (
              <div
                key={hypothesis.id}
                style={{
                  display: 'flex',
                  justifyContent: 'space-between',
                  alignItems: 'center',
                  padding: '8px',
                  backgroundColor: isAutoGenerated ? '#fff9e6' : '#fff',
                  border: `1px solid ${isAutoGenerated && hasUnknownType ? '#ffcc00' : '#dee2e6'}`,
                  borderRadius: '4px',
                  borderLeft: isAutoGenerated && hasUnknownType ? '4px solid #ff9800' : undefined
                }}
              >
                <div style={{ display: 'flex', alignItems: 'center', gap: '12px', flex: 1 }}>
                  {isAutoGenerated && hasUnknownType && (
                    <span style={{ fontSize: '18px' }} title="Auto-generated - needs type">⚠️</span>
                  )}
                  <input
                    type="text"
                    value={hypothesis.expression}
                    onChange={(e) => {
                      const updatedHypothesis = { ...hypothesis, expression: e.target.value };
                      onDeleteHypothesis(hypothesis.id);
                      onAddHypothesis(updatedHypothesis);
                    }}
                    onBlur={(e) => {
                      const expanded = expandTypeShortcuts(e.target.value);
                      if (expanded !== e.target.value) {
                        const updatedHypothesis = { ...hypothesis, expression: expanded };
                        onDeleteHypothesis(hypothesis.id);
                        onAddHypothesis(updatedHypothesis);
                      }
                    }}
                    style={{
                      flex: 1,
                      fontFamily: 'monospace',
                      padding: '4px 8px',
                      border: '1px solid #dee2e6',
                      borderRadius: '4px',
                      backgroundColor: isAutoGenerated && hasUnknownType ? '#fff3cd' : '#fff'
                    }}
                  />
                  {hypothesis.description && hypothesis.description !== hypothesis.expression && (
                    <span style={{ color: '#6c757d', fontSize: '12px', fontStyle: 'italic' }}>
                      ({hypothesis.description})
                    </span>
                  )}
                </div>
                <button
                  onClick={() => onDeleteHypothesis(hypothesis.id)}
                  style={{
                    padding: '2px 8px',
                    backgroundColor: '#dc3545',
                    color: 'white',
                    border: 'none',
                    borderRadius: '4px',
                    cursor: 'pointer',
                    fontSize: '12px'
                  }}
                >
                  Delete
                </button>
              </div>
            );
          })}
        </div>
      </div>

      {/* Let-bindings Section */}
      <div>
        <div style={{
          display: 'flex',
          justifyContent: 'space-between',
          alignItems: 'center',
          marginBottom: '12px'
        }}>
          <h4 style={{ margin: 0, color: '#666' }}>Let Bindings</h4>
          <button
            onClick={() => setShowAddLet(!showAddLet)}
            style={{
              padding: '4px 12px',
              backgroundColor: '#007bff',
              color: 'white',
              border: 'none',
              borderRadius: '4px',
              cursor: 'pointer',
              fontSize: '14px'
            }}
          >
            + Add Let
          </button>
        </div>

        {showAddLet && (
          <div style={{
            padding: '12px',
            backgroundColor: '#fff',
            border: '1px solid #dee2e6',
            borderRadius: '4px',
            marginBottom: '12px'
          }}>
            <input
              type="text"
              placeholder="Variable name (e.g., eq1, x)"
              value={letName}
              onChange={(e) => setLetName(e.target.value)}
              style={{
                width: '100%',
                padding: '6px',
                marginBottom: '8px',
                border: '1px solid #ced4da',
                borderRadius: '4px'
              }}
            />
            <input
              type="text"
              placeholder="Expression (e.g., a + b = c, x \in \R)"
              value={letExpression}
              onChange={(e) => setLetExpression(e.target.value)}
              onBlur={(e) => setLetExpression(expandTypeShortcuts(e.target.value))}
              style={{
                width: '100%',
                padding: '6px',
                marginBottom: '8px',
                border: '1px solid #ced4da',
                borderRadius: '4px'
              }}
            />
            <input
              type="text"
              placeholder="Type annotation (optional, e.g., \R, \N, Prop)"
              value={letType}
              onChange={(e) => setLetType(e.target.value)}
              onBlur={(e) => setLetType(expandTypeShortcuts(e.target.value))}
              style={{
                width: '100%',
                padding: '6px',
                marginBottom: '8px',
                border: '1px solid #ced4da',
                borderRadius: '4px'
              }}
            />

            <div style={{ marginBottom: '8px' }}>
              <label style={{ display: 'flex', alignItems: 'center', gap: '8px' }}>
                <input
                  type="checkbox"
                  checked={letIsClaim}
                  onChange={(e) => setLetIsClaim(e.target.checked)}
                />
                <span style={{ fontSize: '14px' }}>This is a claim to be proved</span>
              </label>
            </div>

            {letIsClaim && (
              <select
                value={letProofMethod}
                onChange={(e) => setLetProofMethod(e.target.value as 'equality' | 'induction')}
                style={{
                  width: '100%',
                  padding: '6px',
                  marginBottom: '8px',
                  border: '1px solid #ced4da',
                  borderRadius: '4px',
                  fontSize: '14px'
                }}
              >
                <option value="equality">Equality Chaining (Direct Proof)</option>
                <option value="induction">Proof by Induction on ℕ</option>
              </select>
            )}
            <div style={{ display: 'flex', gap: '8px', justifyContent: 'flex-end' }}>
              <button
                onClick={() => setShowAddLet(false)}
                style={{
                  padding: '6px 12px',
                  backgroundColor: '#6c757d',
                  color: 'white',
                  border: 'none',
                  borderRadius: '4px',
                  cursor: 'pointer'
                }}
              >
                Cancel
              </button>
              <button
                onClick={handleAddLet}
                style={{
                  padding: '6px 12px',
                  backgroundColor: '#28a745',
                  color: 'white',
                  border: 'none',
                  borderRadius: '4px',
                  cursor: 'pointer'
                }}
              >
                Add
              </button>
            </div>
          </div>
        )}

        <div style={{ display: 'flex', flexDirection: 'column', gap: '8px' }}>
          {letBindings.map(letBinding => (
            <div
              key={letBinding.id}
              style={{
                display: 'flex',
                justifyContent: 'space-between',
                alignItems: 'center',
                padding: '8px',
                backgroundColor: '#fff',
                border: '1px solid #dee2e6',
                borderRadius: '4px'
              }}
            >
              <div style={{ flex: 1 }}>
                <div style={{ display: 'flex', alignItems: 'center', gap: '8px' }}>
                  <span style={{ fontWeight: 'bold', color: '#495057' }}>
                    {letBinding.isClaim ? 'claim' : 'let'} {letBinding.name}
                  </span>
                  {letBinding.typeAnnotation && (
                    <span style={{ color: '#007bff', fontSize: '14px' }}>
                      : {letBinding.typeAnnotation}
                    </span>
                  )}
                  <span style={{ color: '#495057' }}>
                    =
                  </span>
                  {letBinding.isClaim && letBinding.proofStatus && (
                    <span style={{
                      padding: '2px 8px',
                      borderRadius: '4px',
                      fontSize: '12px',
                      fontWeight: 'bold',
                      backgroundColor:
                        letBinding.proofStatus === 'completed' ? '#d4edda' :
                        letBinding.proofStatus === 'in-progress' ? '#fff3cd' : '#f8d7da',
                      color:
                        letBinding.proofStatus === 'completed' ? '#155724' :
                        letBinding.proofStatus === 'in-progress' ? '#856404' : '#721c24'
                    }}>
                      {letBinding.proofStatus === 'completed' ? '✓ Proved' :
                       letBinding.proofStatus === 'in-progress' ? '⚡ Proving...' :
                       '⏳ To Prove'}
                    </span>
                  )}
                </div>
                <div style={{ marginTop: '4px', paddingLeft: '20px' }}>
                  <MathJaxExpressionRenderer
                    expression={letBinding.value}
                    readonly={true}
                  />
                </div>
                {letBinding.isClaim && letBinding.proofMethod && (
                  <div style={{
                    marginTop: '4px',
                    paddingLeft: '20px',
                    fontSize: '12px',
                    color: '#6c757d',
                    fontStyle: 'italic'
                  }}>
                    Method: {letBinding.proofMethod === 'induction' ? 'Induction on ℕ' : 'Equality Chaining'}
                  </div>
                )}
                {letBinding.localHypotheses && letBinding.localHypotheses.length > 0 && (
                  <div style={{
                    marginTop: '8px',
                    paddingLeft: '20px',
                    padding: '8px',
                    backgroundColor: '#e7f3ff',
                    borderLeft: '3px solid #007bff',
                    borderRadius: '4px'
                  }}>
                    <div style={{ fontSize: '12px', fontWeight: 'bold', color: '#0056b3', marginBottom: '4px' }}>
                      Local Hypotheses:
                    </div>
                    {letBinding.localHypotheses.map(hyp => (
                      <div key={hyp.id} style={{ fontSize: '12px', color: '#495057', marginBottom: '2px' }}>
                        <span style={{ fontWeight: 'bold' }}>{hyp.name}:</span> {hyp.expression}
                        {hyp.description && hyp.description !== hyp.expression && (
                          <span style={{ color: '#6c757d', fontStyle: 'italic', marginLeft: '4px' }}>
                            ({hyp.description})
                          </span>
                        )}
                      </div>
                    ))}
                  </div>
                )}
              </div>
              <div style={{ display: 'flex', gap: '4px' }}>
                {letBinding.isClaim && letBinding.proofStatus === 'pending' && onStartProof && (
                  <button
                    onClick={() => onStartProof(letBinding.id)}
                    style={{
                      padding: '2px 8px',
                      backgroundColor: '#9c27b0',
                      color: 'white',
                      border: 'none',
                      borderRadius: '4px',
                      cursor: 'pointer',
                      fontSize: '12px',
                      fontWeight: 'bold'
                    }}
                  >
                    Start Proof
                  </button>
                )}
                {onInstantiate && !letBinding.isClaim && (
                  <button
                    onClick={() => setInstantiatingLet(letBinding)}
                    style={{
                      padding: '2px 8px',
                      backgroundColor: '#17a2b8',
                      color: 'white',
                      border: 'none',
                      borderRadius: '4px',
                      cursor: 'pointer',
                      fontSize: '12px'
                    }}
                  >
                    Instantiate
                  </button>
                )}
                <button
                  onClick={() => onDeleteLet(letBinding.id)}
                  style={{
                    padding: '2px 8px',
                    backgroundColor: '#dc3545',
                    color: 'white',
                    border: 'none',
                    borderRadius: '4px',
                    cursor: 'pointer',
                    fontSize: '12px'
                  }}
                >
                  Delete
                </button>
              </div>
            </div>
          ))}
        </div>
      </div>

      {instantiatingLet && onInstantiate && (
        <InstantiationDialog
          letBinding={instantiatingLet}
          onInstantiate={onInstantiate}
          onClose={() => setInstantiatingLet(null)}
        />
      )}
    </div>
  );
}