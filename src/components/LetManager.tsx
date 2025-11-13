import { useState, useRef, useEffect } from 'react';
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
import { FocusableSection } from './FocusableSection';
import { HypothesesSection } from './HypothesesSection';

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
  // Interactive editing of let values
  activeLetId?: string | null;
  onActivateLetEditor?: (letId: string) => void;
  focusPath?: number[];
  onFocusChange?: (path: number[]) => void;
  showFocusAsBetaRedux?: boolean;
  showFocusType?: boolean;
  // Keyboard navigation support - external control of UI state
  showEditGoalExternal?: boolean;
  onShowEditGoalChange?: (show: boolean) => void;
  showAddHypothesisExternal?: boolean;
  onShowAddHypothesisChange?: (show: boolean) => void;
  showAddLetExternal?: boolean;
  onShowAddLetChange?: (show: boolean) => void;
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
  activeLetId,
  onActivateLetEditor,
  focusPath = [],
  onFocusChange,
  showFocusAsBetaRedux = false,
  showFocusType = true,
  showEditGoalExternal,
  onShowEditGoalChange,
  showAddHypothesisExternal,
  onShowAddHypothesisChange,
  showAddLetExternal,
  onShowAddLetChange,
}: LetManagerProps) {
  const [showAddLetInternal, setShowAddLetInternal] = useState(false);
  const [showAddHypothesisInternal, setShowAddHypothesisInternal] = useState(false);
  const [showEditGoalInternal, setShowEditGoalInternal] = useState(false);

  // Use external state if provided, otherwise use internal state
  const showAddLet = showAddLetExternal ?? showAddLetInternal;
  const setShowAddLet = onShowAddLetChange ?? setShowAddLetInternal;
  const showAddHypothesis = showAddHypothesisExternal ?? showAddHypothesisInternal;
  const setShowAddHypothesis = onShowAddHypothesisChange ?? setShowAddHypothesisInternal;
  const showEditGoal = showEditGoalExternal ?? showEditGoalInternal;
  const setShowEditGoal = onShowEditGoalChange ?? setShowEditGoalInternal;
  const [goalInput, setGoalInput] = useState(goal ? astToString(goal) : '');
  const goalInputRef = useRef<HTMLInputElement>(null);
  const [letName, setLetName] = useState('');
  const [letExpression, setLetExpression] = useState('');
  const [letType, setLetType] = useState<string>('');
  const [hypothesisName, setHypothesisName] = useState('');
  const [hypothesisExpression, setHypothesisExpression] = useState('');
  const [hypothesisDescription, setHypothesisDescription] = useState('');

  // Auto-focus goal input when opening goal editor and initialize value
  useEffect(() => {
    if (showEditGoal) {
      // Initialize goal input with current goal value
      setGoalInput(goal ? astToString(goal) : '');
      // Focus the input field
      setTimeout(() => {
        goalInputRef.current?.focus();
      }, 0);
    }
  }, [showEditGoal, goal]);

  const handleAddLetWithMode = (mode: TermEditorMode) => {
    try {
      // Future: When we have multiple goals in scope, we'll need to:
      // 1. Check mode.goalIndex to know which goal is being referenced
      // 2. Display a selector if goalIndex is undefined and multiple goals exist
      // 3. Fetch the appropriate goal from a goals array instead of single 'goal' state
      // For now, we assume goalIndex 0 (or undefined) refers to the single goal.

      // Generate name if empty
      const existingNames = letBindings.map(lb => lb.name);
      const finalName = letName.trim() || generateLetName(existingNames);

      let expr: ExpressionNode;
      let typeAnnotation: string | undefined;
      let equalityChain: any[] | undefined;

      switch (mode.tag) {
        case 'equality-left':
          // NEW BEHAVIOR: Just use the left side directly as the value
          // Type is a hole for inference: let _val0 : ? = A in ?
          expr = mode.startExpr;
          // Type is left as a hole (undefined) for inference
          typeAnnotation = undefined;
          equalityChain = undefined;  // No equality chain for now
          break;

        case 'equality-right':
          // NEW BEHAVIOR: Just use the right side directly as the value
          // Type is a hole for inference: let _val0 : ? = B in ?
          expr = mode.startExpr;
          // Type is left as a hole (undefined) for inference
          typeAnnotation = undefined;
          equalityChain = undefined;  // No equality chain for now
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
      <FocusableSection
        sectionId="hypotheses"
        label="Hypotheses"
        order={0}
        style={{ marginBottom: '20px' }}
      >
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

        <HypothesesSection
          hypotheses={hypotheses}
          onUpdateHypothesis={onUpdateHypothesis}
          onDeleteHypothesis={onDeleteHypothesis}
        />
      </FocusableSection>

      {/* Goal Section */}
      <FocusableSection
        sectionId="goals"
        label="Goals"
        order={1}
        style={{ marginBottom: '20px' }}
      >
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
              ref={goalInputRef}
              type="text"
              placeholder="Goal type (e.g., x + y = y + x, \forall n, P(n))"
              value={goalInput}
              onChange={(e) => setGoalInput(e.target.value)}
              onBlur={(e) => setGoalInput(expandTypeShortcuts(e.target.value))}
              onKeyDown={(e) => {
                if (e.key === 'Enter') {
                  if (goalInput.trim()) {
                    onSetGoal(goalInput.trim());
                    setShowEditGoal(false);
                  }
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
      </FocusableSection>

      {/* Let-bindings Section */}
      <FocusableSection
        sectionId="let bindings"
        label="Let Bindings"
        order={2}
      >
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
                              startExpr: goalEquality.left,
                              goalIndex: 0  // Future-proofing: track which goal this refers to
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
                            title="Create let-binding with goal's left side as value"
                          >
                            goal left
                          </button>
                          <button
                            onClick={() => handleAddLetWithMode({
                              tag: 'equality-right',
                              startExpr: goalEquality.right,
                              goalIndex: 0  // Future-proofing: track which goal this refers to
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
                            title="Create let-binding with goal's right side as value"
                          >
                            goal right
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
                  <span style={{ color: '#007bff', fontSize: '14px' }}>
                    : {letBinding.typeAnnotation || '?'}
                  </span>
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
                {/* Show interactive editor if this let is active for editing */}
                {activeLetId === letBinding.id && onFocusChange ? (
                  <div style={{ marginTop: '4px', paddingLeft: '20px' }}>
                    <MathJaxExpressionRenderer
                      expression={letBinding.value}
                      focusPath={focusPath}
                      onFocusChange={onFocusChange}
                      isActive={true}
                      readonly={false}
                      showFocusAsBetaRedux={showFocusAsBetaRedux}
                      showFocusType={showFocusType}
                    />
                  </div>
                ) : (
                  <div
                    style={{ marginTop: '4px', paddingLeft: '20px', cursor: 'pointer' }}
                    onClick={() => onActivateLetEditor && onActivateLetEditor(letBinding.id)}
                    title="Click to edit this let-binding's value"
                  >
                    <MathJaxExpressionRenderer
                      expression={letBinding.value}
                      readonly={true}
                    />
                  </div>
                )}

                {/* Inline Term Editor based on editorMode - SIMPLIFIED */}
                {letBinding.editorMode && letBinding.editorExpanded && (
                  <div style={{
                    marginTop: '12px',
                    paddingLeft: '20px',
                    padding: '12px',
                    backgroundColor: '#f8f9fa',
                    border: '2px solid #17a2b8',
                    borderRadius: '6px'
                  }}>
                    {/* SIMPLIFIED: No special rendering for equality modes - just show as regular let */}
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
      </FocusableSection>
    </div>
  );
}