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
  CommentElement,
  EquationElement,
  ProofElement
} from '../types/enhanced-focus';
import { FocusBreadcrumbs } from './FocusedExpressionRenderer';
import { MathJaxExpressionRenderer, MathJaxExpressionRendererRaw } from './MathJaxExpressionRenderer';
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
            <MathJaxExpressionRendererRaw
              expression={(rule as any).displayDescription}
              readonly={true}
              inline={false}
            />
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

function createDerivativeExpression(): ExpressionNode {
  return {
    id: crypto.randomUUID(),
    type: 'application',
    children: [
      {
        id: crypto.randomUUID(),
        type: 'variable',
        value: 'sum',
        children: [],
        raw: 'sum'
      },
      {
        id: crypto.randomUUID(),
        type: 'variable',
        value: 'i',
        children: [],
        raw: 'i'
      },
      {
        id: crypto.randomUUID(),
        type: 'literal',
        value: 0,
        children: [],
        raw: '0'
      },
      {
        id: crypto.randomUUID(),
        type: 'binop',
        operator: '+',
        children: [
          {
            id: crypto.randomUUID(),
            type: 'variable',
            value: 'k',
            children: [],
            raw: 'k'
          },
          {
            id: crypto.randomUUID(),
            type: 'literal',
            value: 1,
            children: [],
            raw: '1'
          }
        ],
        raw: 'k + 1'
      },
      {
        id: crypto.randomUUID(),
        type: 'variable',
        value: 'i',
        children: [],
        raw: 'i'
      }
    ],
    raw: 'sum i 0 (k + 1) i'
  };
}

export function EnhancedProofWorkspace() {
  const [currentExpression, setCurrentExpression] = useState<ExpressionNode>(
    createDerivativeExpression()
  );
  const [focusPath, setFocusPath] = useState<FocusPath>([]);
  const [context, setContext] = useState<ProofContext>({
    assumptions: [{
      id: crypto.randomUUID(),
      name: 'h_sum_formula',
      expression: 'sum i 0 k i = (k * (k + 1)) / 2',
      description: 'Sum formula: ∑_{i=0}^{k} i = k(k+1)/2'
    }],
    variables: new Map([
      ['i', 'ℕ'],
      ['k', 'ℕ']
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
      const result = rule.applyRule(focusedNode, currentExpression, params, context);
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
        applyRule: (node: any, expression: any, params: any, ctx: any) => rule.applyToFocus(node, expression, params, ctx)
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
          applyRule: (node: any, expression: any, params: any, ctx: any) => rule.applyReverse!(node, expression, params, ctx)
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

  const currentEquationElement = <MathJaxExpressionRenderer
    expression={currentExpression}
    focusPath={focusPath}
    onFocusChange={setFocusPath}
    isActive={true}
    readonly={false}
  />

  const currentEquationIsChained = elementIsChained(structuredProof.elements[structuredProof.elements.length - 1], currentExpression);

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
              <table>
                <tbody>
                  {structuredProof.elements.map((element, index) => {
                    if (element.type === 'equation') {
                      const eq = element as EquationElement;
                      const isChained = elementIsChained(structuredProof.elements[index - 1], eq.leftSide);

                      const right = index === structuredProof.elements.length - 1 && eq.rightSide.id === currentExpression.id ? currentEquationElement : <MathJaxExpressionRenderer
                        expression={eq.rightSide}
                      />

                      return (
                        <tr key={element.id}>
                          <td>
                            <div style={{ display: 'flex', flexDirection: 'row', justifyContent: 'flex-end' }}>
                              {isChained ? null : <MathJaxExpressionRenderer
                                expression={eq.leftSide}
                              />}
                            </div>
                          </td>
                          <td><MathJaxExpressionRendererRaw expression={'='} /></td>
                          <td>
                            <div style={{ display: 'flex', flexDirection: 'row', justifyContent: 'flex-start' }}>
                              {right}
                            </div>
                          </td>
                          {eq.justification && (
                            <td>
                              <div style={{
                                fontSize: '13px',
                                color: '#7f8c8d',
                                fontStyle: 'italic',
                                marginTop: '6px'
                              }}>
                                ({eq.justification})
                              </div>
                            </td>
                          )}
                        </tr>
                      )
                    } else if (element.type === 'comment') {
                      return <ProofComment element={element as CommentElement} />;
                    }
                    return null;
                  })}
                  <tr>
                    <td>{currentEquationIsChained ? null : currentEquationElement}</td>
                  </tr>
                </tbody>
              </table>
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

function elementIsChained(previousElement: ProofElement, currentElement: ExpressionNode) {
  if (previousElement?.type !== 'equation') {
    return false;
  }

  const previousEquation = previousElement as EquationElement;
  return previousEquation.rightSide === currentElement;
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
        {assumptions.map((assumption, index) => {
          let renderedAssumption;
          try {
            const parsedExpr = parseExpressionToAST(assumption.expression);
            renderedAssumption = (
              <MathJaxExpressionRenderer
                expression={parsedExpr}
                readonly={true}
              />
            );
          } catch {
            renderedAssumption = <span>{assumption.description}</span>;
          }

          return (
            <div key={assumption.id} style={{
              fontSize: '15px',
              color: '#495057',
              paddingLeft: '16px',
              display: 'flex',
              alignItems: 'center',
              gap: '8px'
            }}>
              <strong>({index + 1})</strong>
              {renderedAssumption}
            </div>
          );
        })}
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