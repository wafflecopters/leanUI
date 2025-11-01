import { useState } from 'react';
import {
  ExpressionNode,
  Assumption,
  LetElement,
  createLetElement,
  parseExpressionToAST,
  generateLetName,
  parseGoalEquality,
  TermEditorMode,
  astToString
} from '../types/enhanced-focus';
import { MathJaxExpressionRenderer } from './MathJaxExpressionRenderer';

interface LetManagerProps {
  letBindings: LetElement[];
  hypotheses: Assumption[];
  goal: ExpressionNode | null;
  onAddLet: (letElement: LetElement) => void;
  onDeleteLet: (id: string) => void;
  onAddHypothesis: (hypothesis: Assumption) => void;
  onDeleteHypothesis: (id: string) => void;
  onUpdateHypothesis: (id: string, updatedHypothesis: Assumption) => void;
  onSetGoal: (goal: string) => void;
  onActivateLetEditor?: (letId: string) => void;
  activeLetId?: string | null;
  // Proof workspace state for the active let
  currentExpression?: ExpressionNode | null;
  focusPath?: number[];
  onFocusChange?: (path: number[]) => void;
}

export function LetManager({
  letBindings,
  hypotheses,
  goal,
  onAddLet,
  onDeleteLet,
  onAddHypothesis,
  onDeleteHypothesis,
  onUpdateHypothesis,
  onSetGoal,
  onActivateLetEditor,
  activeLetId,
  currentExpression,
  focusPath = [],
  onFocusChange
}: LetManagerProps) {
  const [showAddLet, setShowAddLet] = useState(false);
  const [showAddHypothesis, setShowAddHypothesis] = useState(false);
  const [showEditGoal, setShowEditGoal] = useState(false);
  const [goalInput, setGoalInput] = useState(goal ? astToString(goal) : '');
  const [editingHypothesisId, setEditingHypothesisId] = useState<string | null>(null);
  const [editingHypothesisValue, setEditingHypothesisValue] = useState('');
  const [letName, setLetName] = useState('');
  const [letExpression, setLetExpression] = useState('');
  const [letType, setLetType] = useState<string>('');
  const [hypothesisName, setHypothesisName] = useState('');
  const [hypothesisExpression, setHypothesisExpression] = useState('');
  const [hypothesisDescription, setHypothesisDescription] = useState('');

  const handleAddLetWithMode = (mode: TermEditorMode) => {
    try {
      // Generate name if empty
      const existingNames = letBindings.map(lb => lb.name);
      const finalName = letName.trim() || generateLetName(existingNames);

      let expr: ExpressionNode;
      let typeAnnotation: string | undefined;
      let equalityChain: any[] | undefined;

      switch (mode.tag) {
        case 'equality-left':
          // Start from left side of goal equality
          expr = {
            id: crypto.randomUUID(),
            type: 'application',
            raw: `refl ${mode.startExpr.raw}`,
            children: [
              { id: crypto.randomUUID(), type: 'variable', value: 'refl', raw: 'refl', children: [] },
              mode.startExpr
            ]
          };
          equalityChain = [{
            type: 'equation',
            expression: mode.startExpr
          }];
          // Type is inferred from goal
          typeAnnotation = undefined;
          break;

        case 'equality-right':
          // Start from right side of goal equality
          expr = {
            id: crypto.randomUUID(),
            type: 'application',
            raw: `refl ${mode.startExpr.raw}`,
            children: [
              { id: crypto.randomUUID(), type: 'variable', value: 'refl', raw: 'refl', children: [] },
              mode.startExpr
            ]
          };
          equalityChain = [{
            type: 'equation',
            expression: mode.startExpr
          }];
          // Type is inferred from goal
          typeAnnotation = undefined;
          break;

        case 'cases':
          // Stub for case-splitting (future implementation)
          expr = {
            id: crypto.randomUUID(),
            type: 'variable',
            value: '?',
            raw: '?',
            children: []
          };
          typeAnnotation = letType || undefined;
          break;

        case 'value':
          // Hand-written term
          if (!letExpression) {
            alert('Please enter an expression for value mode');
            return;
          }
          expr = parseExpressionToAST(letExpression);
          typeAnnotation = letType || undefined;
          break;
      }

      // Extract unbound variables and create hypotheses for them (only for value mode)
      if (mode.tag === 'value') {
        const unboundVars = extractUnboundVariables(expr);
        unboundVars.forEach(varName => {
          const hypothesis: Assumption = {
            id: crypto.randomUUID(),
            name: varName,
            expression: `${varName} : ?`,
            description: `Auto-generated: ${varName} is unbound`,
            introducedBy: 'auto'
          };
          onAddHypothesis(hypothesis);
        });
      }

      const letElement = createLetElement(
        finalName,
        expr,
        typeAnnotation,
        undefined, // derivedFrom
        false, // isClaim - no longer used
        undefined, // proofMethod - no longer used
        mode
      );

      // Add equality chain if present
      if (equalityChain) {
        letElement.equalityChain = equalityChain;
        letElement.editorExpanded = true; // Open editor by default
      }

      onAddLet(letElement);

      // Reset form
      setLetName('');
      setLetExpression('');
      setLetType('');
      setShowAddLet(false);
    } catch (error) {
      alert(`Error creating let-binding: ${error}`);
    }
  };

  // Helper to extract all unbound variables from an expression
  const extractUnboundVariables = (expr: ExpressionNode, boundVars: Set<string> = new Set()): Set<string> => {
    const unboundVars = new Set<string>();

    // Reserved keywords in type theory that should not be treated as variables
    const reservedKeywords = new Set(['Type', 'Prop', 'Sort']);

    const traverse = (node: ExpressionNode) => {
      if (node.type === 'variable' && typeof node.value === 'string') {
        const varName = node.value;

        // Skip reserved keywords
        if (reservedKeywords.has(varName)) {
          return;
        }

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

  const handleAddHypothesis = (expandedExpression?: string) => {
    if (!hypothesisName || !hypothesisExpression) return;

    // Use the provided expanded expression, or the current one
    const finalExpression = expandedExpression || hypothesisExpression;

    try {
      // Try to parse the expression to find unbound variables
      // This handles cases like "x > 0" where we need to create a hypothesis for x
      const expr = parseExpressionToAST(finalExpression);
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
      expression: `${hypothesisName} : ${finalExpression}`,
      description: hypothesisDescription || `${hypothesisName} : ${finalExpression}`,
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
              onKeyDown={(e) => e.key === 'Enter' && handleAddHypothesis()}
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
              onKeyDown={(e) => {
                if (e.key === 'Enter') {
                  // Expand shortcuts and pass directly to handler
                  const expanded = expandTypeShortcuts(hypothesisExpression);
                  setHypothesisExpression(expanded);
                  handleAddHypothesis(expanded);
                }
              }}
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
              onKeyDown={(e) => e.key === 'Enter' && handleAddHypothesis()}
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
                onClick={() => handleAddHypothesis()}
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
                  {editingHypothesisId === hypothesis.id ? (
                    // Edit mode
                    <div style={{ flex: 1, display: 'flex', alignItems: 'center', gap: '8px' }}>
                      <input
                        type="text"
                        value={editingHypothesisValue}
                        onChange={(e) => setEditingHypothesisValue(e.target.value)}
                        onBlur={(e) => {
                          const expanded = expandTypeShortcuts(e.target.value);
                          setEditingHypothesisValue(expanded);
                        }}
                        onKeyDown={(e) => {
                          if (e.key === 'Enter') {
                            // Expand shortcuts before saving
                            const expanded = expandTypeShortcuts(editingHypothesisValue);
                            const updatedHypothesis = {
                              ...hypothesis,
                              expression: expanded,
                              // Clear auto-generated description if type is no longer unknown
                              description: expanded.includes(' : ?') ? hypothesis.description : ''
                            };
                            onUpdateHypothesis(hypothesis.id, updatedHypothesis);
                            setEditingHypothesisId(null);
                          } else if (e.key === 'Escape') {
                            setEditingHypothesisId(null);
                          }
                        }}
                        autoFocus
                        style={{
                          flex: 1,
                          fontFamily: 'monospace',
                          padding: '4px 8px',
                          border: '1px solid #007bff',
                          borderRadius: '4px',
                          backgroundColor: '#fff'
                        }}
                      />
                      <button
                        onClick={() => {
                          // Expand shortcuts before saving
                          const expanded = expandTypeShortcuts(editingHypothesisValue);
                          const updatedHypothesis = {
                            ...hypothesis,
                            expression: expanded,
                            // Clear auto-generated description if type is no longer unknown
                            description: expanded.includes(' : ?') ? hypothesis.description : ''
                          };
                          onUpdateHypothesis(hypothesis.id, updatedHypothesis);
                          setEditingHypothesisId(null);
                        }}
                        style={{
                          padding: '2px 8px',
                          backgroundColor: '#28a745',
                          color: 'white',
                          border: 'none',
                          borderRadius: '4px',
                          cursor: 'pointer',
                          fontSize: '12px'
                        }}
                      >
                        ✓
                      </button>
                    </div>
                  ) : (
                    // Display mode
                    <div
                      style={{ flex: 1, display: 'flex', alignItems: 'center', gap: '8px', cursor: 'pointer' }}
                      onClick={() => {
                        setEditingHypothesisId(hypothesis.id);
                        setEditingHypothesisValue(hypothesis.expression);
                      }}
                      title="Click to edit"
                    >
                      {(() => {
                        // Parse hypothesis expression: "name : Type" or just "Type"
                        const match = hypothesis.expression.match(/^\s*(\w+)\s*:\s*(.+)$/);

                        if (match) {
                          const [, name, typeStr] = match;
                          return (
                            <>
                              <span style={{ fontFamily: 'monospace', fontWeight: 'bold' }}>{name}</span>
                              <span>:</span>
                              {(() => {
                                try {
                                  const typeExpr = parseExpressionToAST(typeStr.trim());
                                  return <MathJaxExpressionRenderer expression={typeExpr} readonly={true} inline={true} />;
                                } catch (error) {
                                  // If parsing fails, show as plain text
                                  return <span style={{ fontFamily: 'monospace' }}>{typeStr}</span>;
                                }
                              })()}
                            </>
                          );
                        } else {
                          // No colon found, just show the whole thing as text
                          return <span style={{ fontFamily: 'monospace' }}>{hypothesis.expression}</span>;
                        }
                      })()}
                    </div>
                  )}
                  {hypothesis.description && hypothesis.description !== hypothesis.expression && !editingHypothesisId && (
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

      {/* Goal Section */}
      <div style={{ marginBottom: '20px' }}>
        <div style={{
          display: 'flex',
          justifyContent: 'space-between',
          alignItems: 'center',
          marginBottom: '12px'
        }}>
          <h4 style={{ margin: 0, color: '#666' }}>Goal</h4>
          <button
            onClick={() => {
              setGoalInput(goal ? astToString(goal) : '');
              setShowEditGoal(!showEditGoal);
            }}
            style={{
              padding: '4px 12px',
              backgroundColor: '#ffc107',
              color: '#000',
              border: 'none',
              borderRadius: '4px',
              cursor: 'pointer',
              fontSize: '14px',
              fontWeight: 'bold'
            }}
          >
            {goal ? 'Edit Goal' : 'Set Goal'}
          </button>
        </div>

        {showEditGoal && (
          <div style={{
            padding: '12px',
            backgroundColor: '#fff',
            border: '1px solid #dee2e6',
            borderRadius: '4px',
            marginBottom: '12px'
          }}>
            <input
              type="text"
              placeholder="Goal type (e.g., x + y = y + x, \forall n, P(n))"
              value={goalInput}
              onChange={(e) => setGoalInput(e.target.value)}
              onBlur={(e) => setGoalInput(expandTypeShortcuts(e.target.value))}
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
                onClick={() => setShowEditGoal(false)}
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
                onClick={() => {
                  if (goalInput.trim()) {
                    onSetGoal(goalInput.trim());
                    setShowEditGoal(false);
                  }
                }}
                style={{
                  padding: '6px 12px',
                  backgroundColor: '#28a745',
                  color: 'white',
                  border: 'none',
                  borderRadius: '4px',
                  cursor: 'pointer'
                }}
              >
                Set
              </button>
            </div>
          </div>
        )}

        {goal && !showEditGoal && (
          <div style={{
            padding: '12px',
            backgroundColor: '#fff9e6',
            border: '2px solid #ffc107',
            borderRadius: '6px',
            display: 'flex',
            justifyContent: 'space-between',
            alignItems: 'center'
          }}>
            <div style={{ flex: 1, fontSize: '16px', color: '#856404' }}>
              <MathJaxExpressionRenderer expression={goal} readonly={true} />
            </div>
          </div>
        )}

        {!goal && !showEditGoal && (
          <div style={{
            padding: '12px',
            backgroundColor: '#f8f9fa',
            border: '1px dashed #ced4da',
            borderRadius: '6px',
            textAlign: 'center',
            color: '#6c757d',
            fontStyle: 'italic'
          }}>
            No goal set yet. Click "Set Goal" to define what you want to prove.
          </div>
        )}
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
            {/* Optional name input */}
            <input
              type="text"
              placeholder="Name (optional, auto-generates _val0, _val1, ...)"
              value={letName}
              onChange={(e) => setLetName(e.target.value)}
              style={{
                width: '100%',
                padding: '6px',
                marginBottom: '12px',
                border: '1px solid #ced4da',
                borderRadius: '4px',
                fontSize: '14px'
              }}
            />

            {/* Mode selection buttons */}
            <div style={{ marginBottom: '12px' }}>
              <div style={{
                fontSize: '13px',
                fontWeight: 'bold',
                color: '#495057',
                marginBottom: '6px'
              }}>
                Choose term editor mode:
              </div>
              <div style={{ display: 'flex', gap: '8px', flexWrap: 'wrap' }}>
                {(() => {
                  const goalEquality = parseGoalEquality(goal);

                  return (
                    <>
                      {/* Show equality buttons only if goal is A = B */}
                      {goalEquality && (
                        <>
                          <button
                            onClick={() => handleAddLetWithMode({
                              tag: 'equality-left',
                              startExpr: goalEquality.left
                            })}
                            style={{
                              padding: '8px 12px',
                              backgroundColor: '#17a2b8',
                              color: 'white',
                              border: 'none',
                              borderRadius: '4px',
                              cursor: 'pointer',
                              fontSize: '13px',
                              fontWeight: 'bold'
                            }}
                            title="Start equality chain from left side of goal"
                          >
                            goal left = ?
                          </button>
                          <button
                            onClick={() => handleAddLetWithMode({
                              tag: 'equality-right',
                              startExpr: goalEquality.right
                            })}
                            style={{
                              padding: '8px 12px',
                              backgroundColor: '#17a2b8',
                              color: 'white',
                              border: 'none',
                              borderRadius: '4px',
                              cursor: 'pointer',
                              fontSize: '13px',
                              fontWeight: 'bold'
                            }}
                            title="Start equality chain from right side of goal"
                          >
                            goal right = ?
                          </button>
                        </>
                      )}

                      {/* Cases button - always available */}
                      <button
                        onClick={() => handleAddLetWithMode({
                          tag: 'cases',
                          eliminator: 'nat'
                        })}
                        style={{
                          padding: '8px 12px',
                          backgroundColor: '#6610f2',
                          color: 'white',
                          border: 'none',
                          borderRadius: '4px',
                          cursor: 'pointer',
                          fontSize: '13px',
                          fontWeight: 'bold'
                        }}
                        title="Case split (nat/bool eliminator)"
                      >
                        cases
                      </button>

                      {/* Value button - always available, opens input */}
                      <button
                        onClick={() => {
                          // For value mode, we need to show expression input
                          // For now, just show alert asking user to use the input below
                          if (!letExpression) {
                            alert('Please enter an expression first, then click "value"');
                            return;
                          }
                          handleAddLetWithMode({ tag: 'value' });
                        }}
                        style={{
                          padding: '8px 12px',
                          backgroundColor: '#28a745',
                          color: 'white',
                          border: 'none',
                          borderRadius: '4px',
                          cursor: 'pointer',
                          fontSize: '13px',
                          fontWeight: 'bold'
                        }}
                        title="Hand-written term"
                      >
                        value
                      </button>
                    </>
                  );
                })()}
              </div>
            </div>

            {/* Expression input - only shown for value mode */}
            <div style={{ marginBottom: '12px' }}>
              <div style={{
                fontSize: '13px',
                color: '#6c757d',
                marginBottom: '4px'
              }}>
                For "value" mode, enter expression:
              </div>
              <input
                type="text"
                placeholder="Expression (e.g., a + b, 5, (foo bar))"
                value={letExpression}
                onChange={(e) => setLetExpression(e.target.value)}
                onBlur={(e) => setLetExpression(expandTypeShortcuts(e.target.value))}
                style={{
                  width: '100%',
                  padding: '6px',
                  border: '1px solid #ced4da',
                  borderRadius: '4px',
                  fontSize: '14px'
                }}
              />
            </div>

            {/* Optional type annotation */}
            <div style={{ marginBottom: '12px' }}>
              <div style={{
                fontSize: '13px',
                color: '#6c757d',
                marginBottom: '4px'
              }}>
                Type annotation (optional, usually inferred):
              </div>
              <input
                type="text"
                placeholder="e.g., \R, \N, Prop"
                value={letType}
                onChange={(e) => setLetType(e.target.value)}
                onBlur={(e) => setLetType(expandTypeShortcuts(e.target.value))}
                style={{
                  width: '100%',
                  padding: '6px',
                  border: '1px solid #ced4da',
                  borderRadius: '4px',
                  fontSize: '14px'
                }}
              />
            </div>

            <div style={{ display: 'flex', gap: '8px', justifyContent: 'flex-end' }}>
              <button
                onClick={() => {
                  setShowAddLet(false);
                  setLetName('');
                  setLetExpression('');
                  setLetType('');
                }}
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

                {/* Inline Term Editor based on editorMode */}
                {letBinding.editorMode && letBinding.editorExpanded && (
                  <div style={{
                    marginTop: '12px',
                    paddingLeft: '20px',
                    padding: '12px',
                    backgroundColor: activeLetId === letBinding.id ? '#e6f7ff' : '#f8f9fa',
                    border: `2px solid ${activeLetId === letBinding.id ? '#1890ff' : '#17a2b8'}`,
                    borderRadius: '6px'
                  }}>
                    {(letBinding.editorMode.tag === 'equality-left' || letBinding.editorMode.tag === 'equality-right') && (
                      <div>
                        <div style={{
                          fontSize: '13px',
                          fontWeight: 'bold',
                          color: '#17a2b8',
                          marginBottom: '12px'
                        }}>
                          Proof (starting from {letBinding.editorMode.tag === 'equality-left' ? 'left' : 'right'})
                        </div>

                        {/* Inline proof workspace for this let-binding */}
                        {activeLetId === letBinding.id ? (
                          <table style={{ width: '100%', marginBottom: '8px' }}>
                            <tbody>
                              {/* Render completed proof steps */}
                              {letBinding.proofElements && letBinding.proofElements.map((element: any, idx: number) => {
                                if (element.type === 'equation') {
                                  const isLastStep = idx === letBinding.proofElements!.length - 1;
                                  const showLeftSide = idx === 0; // Only show left side on first equation

                                  return (
                                    <tr key={element.id || idx}>
                                      <td style={{ textAlign: 'right', paddingRight: '12px', verticalAlign: 'top' }}>
                                        {showLeftSide && (
                                          <MathJaxExpressionRenderer
                                            expression={element.leftSide}
                                            readonly={true}
                                          />
                                        )}
                                      </td>
                                      <td style={{ paddingRight: '8px', verticalAlign: 'top' }}>=</td>
                                      <td style={{ verticalAlign: 'top' }}>
                                        {/* If this is the last step and we're editing, show interactive version */}
                                        {isLastStep && currentExpression && element.rightSide?.id === currentExpression.id ? (
                                          <MathJaxExpressionRenderer
                                            expression={currentExpression}
                                            focusPath={focusPath}
                                            onFocusChange={onFocusChange}
                                            isActive={true}
                                            readonly={false}
                                          />
                                        ) : (
                                          <MathJaxExpressionRenderer
                                            expression={element.rightSide}
                                            readonly={true}
                                          />
                                        )}
                                      </td>
                                      <td style={{ paddingLeft: '12px', fontSize: '13px', color: '#7f8c8d', fontStyle: 'italic' }}>
                                        {element.justification && `(${element.justification})`}
                                      </td>
                                    </tr>
                                  );
                                }
                                return null;
                              })}

                              {/* Current expression being edited (if no steps yet or new step) */}
                              {currentExpression && (!letBinding.proofElements || letBinding.proofElements.length === 0) && (
                                <tr>
                                  <td colSpan={4}>
                                    <MathJaxExpressionRenderer
                                      expression={currentExpression}
                                      focusPath={focusPath}
                                      onFocusChange={onFocusChange}
                                      isActive={true}
                                      readonly={false}
                                    />
                                  </td>
                                </tr>
                              )}
                            </tbody>
                          </table>
                        ) : (
                          <div style={{
                            padding: '16px',
                            backgroundColor: '#fff',
                            border: '1px dashed #dee2e6',
                            borderRadius: '4px',
                            textAlign: 'center',
                            color: '#6c757d',
                            fontSize: '12px',
                            fontStyle: 'italic',
                            cursor: 'pointer'
                          }}
                          onClick={() => onActivateLetEditor && onActivateLetEditor(letBinding.id)}
                          >
                            Click here to start editing this proof...
                          </div>
                        )}
                      </div>
                    )}
                    {letBinding.editorMode.tag === 'cases' && (
                      <div>
                        <div style={{
                          fontSize: '13px',
                          fontWeight: 'bold',
                          color: '#6610f2',
                          marginBottom: '8px'
                        }}>
                          Case Analysis
                        </div>
                        <div style={{
                          fontSize: '12px',
                          color: '#6c757d',
                          fontStyle: 'italic'
                        }}>
                          Case splitting UI coming soon...
                        </div>
                      </div>
                    )}
                    {letBinding.editorMode.tag === 'value' && (
                      <div>
                        <div style={{
                          fontSize: '13px',
                          fontWeight: 'bold',
                          color: '#28a745',
                          marginBottom: '8px'
                        }}>
                          Value Editor
                        </div>
                        <div style={{
                          fontSize: '12px',
                          color: '#6c757d',
                          fontStyle: 'italic'
                        }}>
                          Hand-written term (view only for now)
                        </div>
                      </div>
                    )}
                  </div>
                )}

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
    </div>
  );
}