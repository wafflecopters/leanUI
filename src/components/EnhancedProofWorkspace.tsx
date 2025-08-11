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
  ENHANCED_FOCUS_RULES
} from '../types/enhanced-focus';
import { FocusBreadcrumbs } from './FocusedExpressionRenderer';
import { KaTeXRenderer } from './KaTeXRenderer';
import { ExpressionEditor } from './ExpressionRenderer';

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
  focusedNode: ExpressionNode;
  rootExpression: ExpressionNode;
  context: ProofContext;
  onApply: (rule: EnhancedFocusRule, params?: any) => void;
}

function EnhancedRuleApplication({ rule, focusedNode, rootExpression, context, onApply }: EnhancedRuleApplicationProps) {
  const [params, setParams] = useState<any>({});
  const [showParams, setShowParams] = useState(false);

  const isApplicable = rule.isApplicableToFocus(focusedNode, rootExpression, context);

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
            <strong style={{ color: categoryColors[rule.category] }}>{rule.name}</strong>
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
            {rule.description}
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

interface AssumptionDisplayProps {
  assumptions: Assumption[];
}

function AssumptionDisplay({ assumptions }: AssumptionDisplayProps) {
  if (assumptions.length === 0) {
    return (
      <div style={{ 
        padding: '12px', 
        backgroundColor: '#e8f5e8', 
        borderRadius: '6px',
        border: '1px solid #c3e6c3'
      }}>
        <strong style={{ color: '#155724' }}>No assumptions needed</strong>
      </div>
    );
  }

  return (
    <div style={{ 
      padding: '12px', 
      backgroundColor: '#fff3cd', 
      borderRadius: '6px',
      border: '1px solid #ffeaa7'
    }}>
      <strong style={{ color: '#856404', marginBottom: '8px', display: 'block' }}>
        Current Assumptions:
      </strong>
      {assumptions.map((assumption, index) => (
        <div key={assumption.id} style={{ 
          marginBottom: '4px',
          fontSize: '13px',
          fontFamily: 'monospace'
        }}>
          <span style={{ color: '#856404' }}>{index + 1}. </span>
          <span style={{ backgroundColor: '#ffeaa7', padding: '1px 4px', borderRadius: '2px' }}>
            {assumption.expression}
          </span>
          <span style={{ color: '#666', fontSize: '11px', marginLeft: '8px' }}>
            ({assumption.description})
          </span>
        </div>
      ))}
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
          
          {step.focusPath.length > 0 && (
            <div style={{ fontSize: '11px', color: '#888', marginBottom: '4px' }}>
              Focus: {getNodeAtPath(step.expression, step.focusPath).raw}
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

export function EnhancedProofWorkspace() {
  const [currentExpression, setCurrentExpression] = useState<ExpressionNode>(
    parseExpressionToAST('x^2 + 2/3 = (y + 1)^2')
  );
  const [focusPath, setFocusPath] = useState<FocusPath>([]);
  const [context, setContext] = useState<ProofContext>({
    assumptions: [],
    variables: new Map([['x', 'ℝ'], ['p', 'ℝ'], ['y', 'ℝ']])
  });
  const [steps, setSteps] = useState<EnhancedProofStep[]>([]);
  const [editingExpression, setEditingExpression] = useState(false);
  const [newExpressionText, setNewExpressionText] = useState('');

  const focusedNode = getNodeAtPath(currentExpression, focusPath);

  const addStep = useCallback((rule: EnhancedFocusRule, params?: any) => {
    try {
      const result = rule.applyToFocus(focusedNode, currentExpression, params);
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
        description: `Applied ${rule.name} to "${focusedNode.raw}"`
      };
      
      setCurrentExpression(newExpression);
      setSteps(prev => [...prev, newStep]);
      
      // Add new assumptions to context
      if (result.newAssumptions && result.newAssumptions.length > 0) {
        setContext(prev => ({
          ...prev,
          assumptions: [...prev.assumptions, ...result.newAssumptions!]
        }));
      }
      
    } catch (error) {
      console.error('Error applying rule:', error);
      alert(`Error applying rule: ${error instanceof Error ? error.message : 'Unknown error'}`);
    }
  }, [currentExpression, focusPath, focusedNode]);

  const setCurrentStep = useCallback((step: EnhancedProofStep) => {
    setCurrentExpression(step.expression);
    setFocusPath(step.focusPath);
    
    // Rebuild assumptions up to this step
    const stepsUpToCurrent = steps.slice(0, steps.indexOf(step) + 1);
    const allAssumptions = stepsUpToCurrent.flatMap(s => s.newAssumptions || []);
    setContext(prev => ({ ...prev, assumptions: allAssumptions }));
  }, [steps]);

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

  const applicableRules = ENHANCED_FOCUS_RULES.filter(rule => 
    rule.isApplicableToFocus(focusedNode, currentExpression, context)
  );

  // Group rules by category
  const rulesByCategory = applicableRules.reduce((acc, rule) => {
    if (!acc[rule.category]) acc[rule.category] = [];
    acc[rule.category].push(rule);
    return acc;
  }, {} as Record<string, EnhancedFocusRule[]>);

  return (
    <div style={{ 
      display: 'grid', 
      gridTemplateColumns: '1fr 380px', 
      gap: '24px', 
      padding: '20px',
      fontFamily: 'system-ui, sans-serif'
    }}>
      {/* Main workspace */}
      <div>
        <div style={{ 
          display: 'flex', 
          justifyContent: 'space-between', 
          alignItems: 'center', 
          marginBottom: '16px' 
        }}>
          <h2 style={{ margin: 0 }}>Enhanced Proof Workspace</h2>
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

        {editingExpression ? (
          <div style={{ marginBottom: '24px' }}>
            <h3>Enter New Expression:</h3>
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
          <div style={{ marginBottom: '24px' }}>
            <h3>Current Expression:</h3>
            <FocusBreadcrumbs
              expression={currentExpression}
              focusPath={focusPath}
              onFocusChange={setFocusPath}
            />
            <KaTeXRenderer
              expression={currentExpression}
              focusPath={focusPath}
              onFocusChange={setFocusPath}
              isActive={true}
            />
          </div>
        )}

        <div style={{ marginBottom: '20px' }}>
          <AssumptionDisplay assumptions={context.assumptions} />
        </div>

        <div>
          <h3>Available Rules for Current Focus:</h3>
          {Object.keys(rulesByCategory).length > 0 ? (
            Object.entries(rulesByCategory).map(([category, rules]) => (
              <div key={category} style={{ marginBottom: '16px' }}>
                <h4 style={{ 
                  margin: '0 0 8px 0', 
                  fontSize: '14px',
                  textTransform: 'capitalize',
                  color: '#666'
                }}>
                  {category} Rules ({rules.length})
                </h4>
                <div style={{ display: 'grid', gap: '6px' }}>
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
              backgroundColor: '#f8f9fa', 
              borderRadius: '6px',
              color: '#666',
              fontStyle: 'italic'
            }}>
              No rules available for the current focus. Try focusing on a different subexpression.
            </div>
          )}
        </div>
      </div>

      {/* Sidebar with history and proof */}
      <div style={{ 
        backgroundColor: '#f8f9fa', 
        padding: '16px', 
        borderRadius: '8px',
        border: '1px solid #e9ecef'
      }}>
        <EnhancedProofHistory
          steps={steps}
          currentStepId={steps.length > 0 ? steps[steps.length - 1].id : undefined}
          onStepClick={setCurrentStep}
        />

        {steps.length > 0 && (
          <div style={{ 
            marginTop: '16px', 
            padding: '12px', 
            backgroundColor: 'white', 
            borderRadius: '6px',
            border: '1px solid #e0e0e0'
          }}>
            <h4 style={{ margin: '0 0 8px 0', fontSize: '14px' }}>Generated Lean Proof:</h4>
            <pre style={{ 
              fontSize: '10px', 
              margin: 0, 
              wordWrap: 'break-word',
              whiteSpace: 'pre-wrap',
              backgroundColor: '#f5f5f5',
              padding: '8px',
              borderRadius: '4px'
            }}>
              {generateEnhancedLeanProof(steps, context)}
            </pre>
          </div>
        )}
      </div>
    </div>
  );
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