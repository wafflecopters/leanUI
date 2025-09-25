import { useState, useCallback } from 'react';
import {
  ExpressionNode,
  FocusPath,
  EnhancedFocusRule,
  Assumption,
  ProofContext,
  parseExpressionToAST,
  getNodeAtPath,
  setNodeAtPath,
  astToString,
  ENHANCED_FOCUS_RULES,
  StructuredProof,
  createTransformationEquationElement,
  createCommentElement,
  CommentElement
} from '../types/enhanced-focus';
import { FocusBreadcrumbs } from './FocusedExpressionRenderer';
import { MathJaxExpressionRenderer } from './MathJaxExpressionRenderer';
import { ExpressionEditor } from './ExpressionRenderer';
import { ASTDebugPanel } from './ASTDebugPanel';

interface EnhancedProofStep {
  id: string;
  expression: ExpressionNode;
  focusPath: FocusPath;
  rule?: EnhancedFocusRule;
  ruleParams?: any;
  newAssumptions?: Assumption[];
  timestamp: number;
  description: string;
}

interface EnhancedRuleApplicationProps {
  rule: EnhancedFocusRule;
  focusedNode: ExpressionNode | null;
  rootExpression: ExpressionNode;
  context: ProofContext;
  onApply: (rule: EnhancedFocusRule, params?: any) => void;
}

function EnhancedRuleApplication({ rule, focusedNode, onApply }: EnhancedRuleApplicationProps) {
  const [params, setParams] = useState<any>({});
  const [showParams, setShowParams] = useState(false);

  if (!focusedNode) {
    return null;
  }

  const isApplicable = true; // Already filtered in parent component

  const handleApply = () => {
    if (rule.requiresParams && !showParams) {
      setShowParams(true);
      return;
    }

    onApply(rule, rule.requiresParams ? params : undefined);
    setShowParams(false);
    setParams({});
  };

  const handleParamChange = (paramName: string, value: string) => {
    setParams((prev: any) => ({ ...prev, [paramName]: value }));
  };

  if (!isApplicable) {
    return null;
  }

  const categoryColors = {
    equality: '#007acc',
    arithmetic: '#28a745',
    algebraic: '#ffc107',
    substitution: '#dc3545',
    introduction: '#6f42c1'
  };

  return (
    <div style={{
      margin: '6px 0',
      padding: '12px',
      border: '2px solid',
      borderColor: categoryColors[rule.category],
      borderRadius: '6px',
      backgroundColor: '#f9f9f9'
    }}>
      <div style={{ display: 'flex', justifyContent: 'space-between', alignItems: 'flex-start', marginBottom: '8px' }}>
        <div style={{ flex: 1 }}>
          <div style={{ display: 'flex', alignItems: 'center', gap: '8px', marginBottom: '4px' }}>
            <strong style={{ color: categoryColors[rule.category] }}>{(rule as any).displayName}</strong>
            <span style={{
              fontSize: '10px',
              padding: '2px 6px',
              backgroundColor: categoryColors[rule.category],
              color: 'white',
              borderRadius: '10px',
              textTransform: 'uppercase',
              fontWeight: 'bold'
            }}>
              {rule.category}
            </span>
          </div>
          <div style={{ fontSize: '13px', color: '#666', marginBottom: '4px' }}>
            {(rule as any).displayDescription}
          </div>
          <div style={{ fontSize: '12px', color: '#888', fontFamily: 'monospace' }}>
            On: <span style={{ backgroundColor: '#e6f3ff', padding: '1px 4px', borderRadius: '2px' }}>
              {focusedNode.raw}
            </span>
          </div>
        </div>
        <button
          onClick={handleApply}
          style={{
            padding: '6px 14px',
            backgroundColor: categoryColors[rule.category],
            color: 'white',
            border: 'none',
            borderRadius: '4px',
            cursor: 'pointer',
            fontSize: '13px',
            fontWeight: 'bold'
          }}
        >
          {showParams ? 'Apply' : 'Apply'}
        </button>
      </div>

      {showParams && rule.requiresParams && rule.paramTemplate && (
        <div style={{ marginTop: '8px', padding: '8px', backgroundColor: '#f0f0f0', borderRadius: '4px' }}>
          {Object.entries(rule.paramTemplate).map(([paramName, description]) => (
            <div key={paramName} style={{ marginBottom: '6px' }}>
              <label style={{ fontSize: '12px', color: '#666', display: 'block', marginBottom: '2px' }}>
                {description}:
              </label>
              <input
                type="text"
                placeholder={`Enter ${paramName}...`}
                value={params[paramName] || ''}
                onChange={(e) => handleParamChange(paramName, e.target.value)}
                style={{
                  width: '100%',
                  padding: '4px 8px',
                  fontFamily: 'monospace',
                  border: '1px solid #ccc',
                  borderRadius: '4px',
                  fontSize: '12px'
                }}
              />
            </div>
          ))}
        </div>
      )}
    </div>
  );
}


interface EnhancedProofHistoryProps {
  steps: EnhancedProofStep[];
  currentStepId?: string;
  onStepClick: (step: EnhancedProofStep) => void;
}

function EnhancedProofHistory({ steps, currentStepId, onStepClick }: EnhancedProofHistoryProps) {
  if (steps.length === 0) {
    return (
      <div style={{ padding: '16px', color: '#666', fontStyle: 'italic' }}>
        No proof steps yet. Start by setting focus and applying rules.
      </div>
    );
  }

  return (
    <div style={{ maxHeight: '400px', overflowY: 'auto' }}>
      <h3 style={{ margin: '0 0 12px 0', fontSize: '16px' }}>Proof Steps:</h3>
      {steps.map((step, index) => (
        <div
          key={step.id}
          style={{
            marginBottom: '12px',
            padding: '10px',
            border: step.id === currentStepId ? '2px solid #007acc' : '1px solid #e0e0e0',
            borderRadius: '6px',
            backgroundColor: step.id === currentStepId ? '#f8fcff' : 'white',
            cursor: 'pointer'
          }}
          onClick={() => onStepClick(step)}
        >
          <div style={{
            fontSize: '12px',
            color: '#666',
            marginBottom: '6px',
            display: 'flex',
            justifyContent: 'space-between'
          }}>
            <span><strong>Step {index + 1}:</strong> {step.description}</span>
            <span>{new Date(step.timestamp).toLocaleTimeString()}</span>
          </div>

          <div style={{
            fontFamily: 'monospace',
            fontSize: '14px',
            backgroundColor: '#f5f5f5',
            padding: '8px',
            borderRadius: '4px',
            marginBottom: '6px'
          }}>
            {astToString(step.expression)}
          </div>

          {step.focusPath.length > 0 && getNodeAtPath(step.expression, step.focusPath) && (
            <div style={{ fontSize: '11px', color: '#888', marginBottom: '4px' }}>
              Focus: {getNodeAtPath(step.expression, step.focusPath)?.raw}
            </div>
          )}

          {step.newAssumptions && step.newAssumptions.length > 0 && (
            <div style={{ fontSize: '11px', color: '#856404' }}>
              New assumptions: {step.newAssumptions.map(a => a.expression).join(', ')}
            </div>
          )}
        </div>
      ))}
    </div>
  );
}

// Helper function to create the proper expression for d/dx (c * f(x))
function createDerivativeExpression(): ExpressionNode {
  return {
    id: crypto.randomUUID(),
    type: 'application',
    children: [
      {
        id: crypto.randomUUID(),
        type: 'variable',
        value: 'deriv',
        children: [],
        raw: 'deriv'
      },
      {
        id: crypto.randomUUID(),
        type: 'binop',
        operator: '*',
        children: [
          {
            id: crypto.randomUUID(),
            type: 'variable',
            value: 'c',
            children: [],
            raw: 'c'
          },
          {
            id: crypto.randomUUID(),
            type: 'application',
            children: [
              {
                id: crypto.randomUUID(),
                type: 'variable',
                value: 'f',
                children: [],
                raw: 'f'
              },
              {
                id: crypto.randomUUID(),
                type: 'variable',
                value: 'x',
                children: [],
                raw: 'x'
              }
            ],
            raw: 'f x'
          }
        ],
        raw: 'c * f x'
      },
      {
        id: crypto.randomUUID(),
        type: 'variable',
        value: 'x',
        children: [],
        raw: 'x'
      }
    ],
    raw: 'deriv (c * f x) x'
  };
}

export function EnhancedProofWorkspace() {
  const [currentExpression, setCurrentExpression] = useState<ExpressionNode>(
    createDerivativeExpression()
  );
  const [focusPath, setFocusPath] = useState<FocusPath>([]);
  const [context, setContext] = useState<ProofContext>({
    assumptions: [],
    variables: new Map([
      ['f', 'ℝ → ℝ'],
      ['c', 'ℝ'],
      ['x', 'ℝ']
    ])
  });
  const [steps, setSteps] = useState<EnhancedProofStep[]>([]);
  const [editingExpression, setEditingExpression] = useState(false);
  const [newExpressionText, setNewExpressionText] = useState('');
  const [showASTDebug, setShowASTDebug] = useState(false);
  const [structuredProof, setStructuredProof] = useState<StructuredProof>({
    elements: [],
    metadata: {
      assumptions: context.assumptions,
      goal: currentExpression
    }
  });

  const focusedNode = getNodeAtPath(currentExpression, focusPath);

  // Suppress unused import warnings (these are used in commented sections)
  console.debug('Unused imports for cleanup later:', { EnhancedProofHistory, generateEnhancedLeanProof, steps });


  const addStep = useCallback((rule: any, params?: any) => {
    if (!focusedNode) {
      alert('No focused node to apply rule to');
      return;
    }

    try {
      const result = rule.applyRule(focusedNode, currentExpression, params);
      const newExpression = setNodeAtPath(currentExpression, focusPath, result.newNode);

      // Update the raw string of the new expression
      newExpression.raw = astToString(newExpression);

      const newStep: EnhancedProofStep = {
        id: crypto.randomUUID(),
        expression: newExpression,
        focusPath: [...focusPath],
        rule,
        ruleParams: params,
        newAssumptions: result.newAssumptions,
        timestamp: Date.now(),
        description: `Applied ${rule.displayName} to "${focusedNode.raw}"`
      };

      setCurrentExpression(newExpression);
      setSteps(prev => [...prev, newStep]);

      // Update structured proof
      const equationElement = createTransformationEquationElement(
        currentExpression,  // previous expression (left side)
        newExpression,      // new expression (right side)
        rule.displayName,
        rule.id
      );
      setStructuredProof(prev => ({
        ...prev,
        elements: [...prev.elements, equationElement],
        metadata: {
          ...prev.metadata,
          goal: newExpression
        }
      }));

      // Add new assumptions to context
      if (result.newAssumptions && result.newAssumptions.length > 0) {
        setContext(prev => ({
          ...prev,
          assumptions: [...prev.assumptions, ...result.newAssumptions!]
        }));

        // Update structured proof metadata
        setStructuredProof(prev => ({
          ...prev,
          metadata: {
            ...prev.metadata,
            assumptions: [...prev.metadata.assumptions, ...result.newAssumptions!]
          }
        }));
      }

    } catch (error) {
      console.error('Error applying rule:', error);
      alert(`Error applying rule: ${error instanceof Error ? error.message : 'Unknown error'}`);
    }
  }, [currentExpression, focusPath, focusedNode]);

  const addComment = useCallback((content: string, commentType: 'explanation' | 'assumption' | 'goal' | 'strategy' = 'explanation') => {
    const commentElement = createCommentElement(content, commentType);
    setStructuredProof(prev => ({
      ...prev,
      elements: [...prev.elements, commentElement]
    }));
  }, []);


  const handleNewExpression = () => {
    if (!newExpressionText.trim()) return;

    try {
      const newExpression = parseExpressionToAST(newExpressionText.trim());
      setCurrentExpression(newExpression);
      setFocusPath([]);
      setSteps([]);
      setContext(prev => ({ ...prev, assumptions: [] }));
      setEditingExpression(false);
      setNewExpressionText('');
    } catch (error) {
      alert(`Error parsing expression: ${error instanceof Error ? error.message : 'Unknown error'}`);
    }
  };

  const startEditing = () => {
    setEditingExpression(true);
    setNewExpressionText(astToString(currentExpression));
  };

  // Get applicable rules, including both forward and reverse directions for bidirectional rules
  const applicableRules = focusedNode ? ENHANCED_FOCUS_RULES.flatMap(rule => {
    const rules = [];

    // Check forward direction
    if (rule.isApplicableToFocus(focusedNode, currentExpression, context)) {
      rules.push({
        ...rule,
        isReverse: false,
        displayName: rule.name,
        displayDescription: rule.description,
        applyRule: (node: any, expression: any, params: any) => rule.applyToFocus(node, expression, params)
      });
    }

    // Check reverse direction for bidirectional rules
    if (rule.bidirectional && rule.isApplicableReverse && rule.applyReverse) {
      if (rule.isApplicableReverse(focusedNode, currentExpression, context)) {
        rules.push({
          ...rule,
          isReverse: true,
          displayName: rule.reverseName || `${rule.name} (Reverse)`,
          displayDescription: rule.reverseDescription || `Reverse of: ${rule.description}`,
          applyRule: (node: any, expression: any, params: any) => rule.applyReverse!(node, expression, params)
        });
      }
    }

    return rules;
  }) : [];

  // Group rules by category
  const rulesByCategory = applicableRules.reduce((acc, rule) => {
    if (!acc[rule.category]) acc[rule.category] = [];
    acc[rule.category].push(rule);
    return acc;
  }, {} as Record<string, EnhancedFocusRule[]>);

  return (
    <div style={{
      padding: '20px',
      fontFamily: 'system-ui, sans-serif',
      maxWidth: '1200px',
      margin: '0 auto'
    }}>
      {/* Header */}
      <div style={{
        display: 'flex',
        justifyContent: 'space-between',
        alignItems: 'center',
        marginBottom: '24px',
        borderBottom: '2px solid #007acc',
        paddingBottom: '16px'
      }}>
        <h2 style={{ margin: 0, color: '#007acc' }}>Mathematical Proof Workspace</h2>
        <div style={{ display: 'flex', gap: '12px' }}>
          <button
            onClick={() => {
              const comment = prompt('Add a comment to the proof:');
              if (comment && comment.trim()) {
                const type = confirm('Is this an explanation comment? (Cancel for assumption/strategy)')
                  ? 'explanation' : 'strategy';
                addComment(comment.trim(), type);
              }
            }}
            style={{
              padding: '8px 16px',
              backgroundColor: '#28a745',
              color: 'white',
              border: 'none',
              borderRadius: '4px',
              cursor: 'pointer',
              fontSize: '14px',
              fontWeight: 'bold'
            }}
          >
            ➕ Add Comment
          </button>
          <button
            onClick={startEditing}
            style={{
              padding: '8px 16px',
              backgroundColor: '#6c757d',
              color: 'white',
              border: 'none',
              borderRadius: '4px',
              cursor: 'pointer'
            }}
          >
            New Expression
          </button>
        </div>
      </div>

      {editingExpression ? (
        <div style={{
          marginBottom: '24px',
          padding: '20px',
          backgroundColor: '#f8f9fa',
          borderRadius: '8px',
          border: '2px solid #e9ecef'
        }}>
          <h3 style={{ marginTop: 0 }}>Enter New Expression:</h3>
          <ExpressionEditor
            value={newExpressionText}
            onChange={setNewExpressionText}
            onSubmit={handleNewExpression}
            placeholder="Enter expression (e.g., x + 4 = 5, p^2 - 9 = 0)"
          />
          <button
            onClick={() => setEditingExpression(false)}
            style={{
              marginLeft: '8px',
              padding: '8px 16px',
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
      ) : (
        <div style={{ display: 'grid', gridTemplateColumns: '2fr 1fr', gap: '24px' }}>
          {/* Main Proof Area */}
          <div style={{
            backgroundColor: 'white',
            border: '2px solid #e9ecef',
            borderRadius: '12px',
            padding: '24px',
            boxShadow: '0 4px 6px rgba(0, 0, 0, 0.05)',
            minHeight: '600px'
          }}>
            <AssumptionsPanel assumptions={context.assumptions} />

            {/* Mathematical Derivation */}
            <div style={{
              backgroundColor: '#fafbfc',
              border: '2px solid #e1e8ed',
              borderRadius: '8px',
              padding: '20px',
              minHeight: '400px'
            }}>
              <h4 style={{
                margin: '0 0 20px 0',
                color: '#495057',
                fontSize: '16px',
                borderBottom: '1px solid #dee2e6',
                paddingBottom: '8px'
              }}>
                🔢 Proof:
              </h4>

              {/* All previous proof steps */}
              {structuredProof.elements.map((element, index) => {
                if (element.type === 'equation') {
                  const eq = element as any;
                  const sides = eq.leftSide && eq.rightSide ? { left: eq.leftSide, right: eq.rightSide } : null;

                  return (
                    <div key={element.id} style={{
                      display: 'flex',
                      alignItems: 'center',
                      padding: 0,
                      margin: 0,
                      borderBottom: index === structuredProof.elements.length - 1 ? 'none' : '1px solid #f0f0f0',
                    }}>
                      <div style={{
                        textAlign: 'right',
                      }}>
                        {/* Only show left side on the first equation */}
                        {index === 0 && (
                          <div style={{
                            fontSize: '16px',
                            color: '#2c3e50',
                            fontFamily: 'KaTeX_Main, "Times New Roman", serif'
                          }}>
                            {sides ? (
                              <MathJaxExpressionRenderer
                                expression={sides.left}
                              />
                            ) : (
                              <MathJaxExpressionRenderer
                                expression={element.content as any}
                              />
                            )}
                          </div>
                        )}
                      </div>

                      <div style={{
                        fontSize: '18px',
                        fontWeight: 'bold',
                        color: '#007acc',
                        minWidth: '12px',
                        textAlign: 'center',
                        margin: 0,
                        padding: 0,
                      }}>
                        =
                      </div>

                      <div style={{
                        flex: 1,
                        padding: 0,
                        margin: 0,
                        textAlign: 'left',  // Ensure left alignment
                      }}>
                        <div style={{
                          fontSize: '16px',
                          color: '#2c3e50',
                          fontFamily: 'KaTeX_Main, "Times New Roman", serif',
                          textAlign: 'left',  // Ensure left alignment for MathJax content
                        }}>
                          {sides ? (
                            <MathJaxExpressionRenderer
                              expression={sides.right}
                            />
                          ) : null}
                        </div>
                      </div>

                      {(element as any).justification && (
                        <div style={{
                          fontSize: '13px',
                          color: '#7f8c8d',
                          fontStyle: 'italic',
                          marginTop: '6px'
                        }}>
                          ({(element as any).justification})
                        </div>
                      )}
                    </div>
                  );
                } else if (element.type === 'comment') {
                  return <ProofComment element={element as CommentElement} />;
                }
                return null;
              })}

              {/* Current active equation with focus */}
              <MathJaxExpressionRenderer
                expression={currentExpression}
                focusPath={focusPath}
                onFocusChange={setFocusPath}
                isActive={true}
                readonly={false}
              />
              <FocusBreadcrumbs
                expression={currentExpression}
                focusPath={focusPath}
                onFocusChange={setFocusPath}
              />
            </div>
          </div>

          <RulesPanel
            rulesByCategory={rulesByCategory}
            focusedNode={focusedNode}
            currentExpression={currentExpression}
            context={context}
            addStep={addStep}
          />
        </div>
      )}

      {/* AST Debug Panel */}
      <ASTDebugPanel
        expression={currentExpression}
        isVisible={showASTDebug}
        onToggle={() => setShowASTDebug(!showASTDebug)}
      />
    </div>
  );
}

function AssumptionsPanel({ assumptions }: { assumptions: Assumption[] }) {
  if (assumptions.length === 0) {
    return null;
  }

  return (
    <div style={{
      marginBottom: '24px',
      padding: '16px',
      backgroundColor: '#f8f9fa',
      borderRadius: '8px',
      border: '1px solid #e9ecef'
    }}>
      <h4 style={{ margin: '0 0 12px 0', color: '#495057', fontSize: '16px' }}>
        📋 Given:
      </h4>
      <div style={{ display: 'flex', flexDirection: 'column', gap: '8px' }}>
        {assumptions.map((assumption, index) => (
          <div key={assumption.id} style={{
            fontSize: '15px',
            color: '#495057',
            paddingLeft: '16px'
          }}>
            <strong>({index + 1})</strong> {assumption.description}
          </div>
        ))}
      </div>
    </div>
  )
}

function ProofComment({ element }: { element: CommentElement }) {
  return (
    <div key={element.id} style={{
      margin: '16px 0',
      padding: '12px 16px',
      backgroundColor: '#e8f4f8',
      borderLeft: '4px solid #17a2b8',
      borderRadius: '0 6px 6px 0',
      color: '#0c5460',
      fontSize: '14px',
      fontStyle: 'italic'
    }}>
      {element.content}
    </div>
  );
}

function RulesPanel({
  rulesByCategory,
  focusedNode,
  currentExpression,
  context,
  addStep
}: {
  rulesByCategory: Record<string, EnhancedFocusRule[]>;
  focusedNode: ExpressionNode | null;
  currentExpression: ExpressionNode;
  context: ProofContext;
  addStep: (rule: EnhancedFocusRule, params?: any) => void;
}) {
  return (
    <div style={{
      backgroundColor: '#f8f9fa',
      border: '1px solid #e9ecef',
      borderRadius: '8px',
      padding: '20px',
      maxHeight: '600px',
      overflowY: 'auto'
    }}>
      <h3 style={{ marginTop: 0, color: '#495057' }}>Available Rules</h3>
      {Object.keys(rulesByCategory).length > 0 ? (
        Object.entries(rulesByCategory).map(([category, rules]) => (
          <div key={category} style={{ marginBottom: '20px' }}>
            <h4 style={{
              margin: '0 0 12px 0',
              fontSize: '14px',
              textTransform: 'capitalize',
              color: '#666',
              borderBottom: '1px solid #dee2e6',
              paddingBottom: '4px'
            }}>
              {category} Rules ({rules.length})
            </h4>
            <div style={{ display: 'flex', flexDirection: 'column', gap: '8px' }}>
              {rules.map(rule => (
                <EnhancedRuleApplication
                  key={rule.id}
                  rule={rule}
                  focusedNode={focusedNode}
                  rootExpression={currentExpression}
                  context={context}
                  onApply={addStep}
                />
              ))}
            </div>
          </div>
        ))
      ) : (
        <div style={{
          padding: '16px',
          backgroundColor: '#fff3cd',
          borderRadius: '6px',
          color: '#856404',
          fontStyle: 'italic',
          textAlign: 'center'
        }}>
          Click on part of the expression to see available rules
        </div>
      )}
    </div>
  )
}

// Helper function to generate comprehensive Lean proof terms
function generateEnhancedLeanProof(steps: EnhancedProofStep[], context: ProofContext): string {
  if (steps.length === 0) return '';

  const assumptions = context.assumptions.map((assumption, index) =>
    `variable (h_${index + 1} : ${assumption.expression})`
  ).join('\n');

  const proofTerms = steps.map((step, index) => {
    const stepVar = `h${index + 1}`;
    if (!step.rule) return `${stepVar} : ${astToString(step.expression)} := sorry`;

    switch (step.rule.id) {
      case 'symmetry':
        return `${stepVar} : ${astToString(step.expression)} := Eq.symm h${index}`;
      case 'add_comm':
        return `${stepVar} : ${astToString(step.expression)} := by rw [add_comm]`;
      case 'mul_comm':
        return `${stepVar} : ${astToString(step.expression)} := by rw [mul_comm]`;
      case 'add_assoc_left':
      case 'add_assoc_right':
        return `${stepVar} : ${astToString(step.expression)} := by rw [add_assoc]`;
      case 'distribute_mul_left':
        return `${stepVar} : ${astToString(step.expression)} := by rw [mul_add]`;
      case 'distribute_mul_right':
        return `${stepVar} : ${astToString(step.expression)} := by rw [add_mul]`;
      case 'add_both_sides':
        return `${stepVar} : ${astToString(step.expression)} := by rw [← add_right_cancel_iff]; exact h${index}`;
      case 'subtract_both_sides':
        return `${stepVar} : ${astToString(step.expression)} := by rw [← sub_right_inj]; exact h${index}`;
      case 'multiply_both_sides':
        return `${stepVar} : ${astToString(step.expression)} := by rw [← mul_right_inj]; exact h${index}`;
      case 'divide_both_sides':
        return `${stepVar} : ${astToString(step.expression)} := by rw [← div_right_inj]; exact h${index}`;
      case 'add_zero':
        return `${stepVar} : ${astToString(step.expression)} := by rw [add_zero]`;
      case 'mul_one':
        return `${stepVar} : ${astToString(step.expression)} := by rw [mul_one]`;
      case 'mul_zero':
        return `${stepVar} : ${astToString(step.expression)} := by rw [mul_zero]`;
      default:
        return `${stepVar} : ${astToString(step.expression)} := sorry`;
    }
  });

  const initialExpr = steps[0] ? astToString(steps[0].expression) : 'initial_expr';

  return `-- Generated enhanced proof
${assumptions}
variable (h0 : ${initialExpr})

${proofTerms.join('\n')}`;
}