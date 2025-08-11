import { useState, useCallback } from 'react';
import { 
  ExpressionNode, 
  FocusPath, 
  FocusRule, 
  parseExpressionToAST, 
  getNodeAtPath, 
  setNodeAtPath, 
  astToString,
  FOCUS_RULES
} from '../types/focus';
import { FocusedExpressionRenderer, FocusBreadcrumbs } from './FocusedExpressionRenderer';
import { ExpressionEditor } from './ExpressionRenderer';

interface FocusedProofStep {
  id: string;
  expression: ExpressionNode;
  focusPath: FocusPath;
  rule?: FocusRule;
  ruleParams?: any;
  timestamp: number;
  description: string;
}

interface FocusRuleApplicationProps {
  rule: FocusRule;
  focusedNode: ExpressionNode;
  rootExpression: ExpressionNode;
  onApply: (rule: FocusRule, params?: any) => void;
}

function FocusRuleApplication({ rule, focusedNode, rootExpression, onApply }: FocusRuleApplicationProps) {
  const [params] = useState<any>({});

  const isApplicable = rule.isApplicableToFocus(focusedNode, rootExpression);

  const handleApply = () => {
    onApply(rule, params);
  };

  if (!isApplicable) {
    return null;
  }

  return (
    <div style={{ 
      margin: '6px 0', 
      padding: '12px', 
      border: '1px solid #e0e0e0', 
      borderRadius: '6px',
      backgroundColor: '#f9f9f9'
    }}>
      <div style={{ display: 'flex', justifyContent: 'space-between', alignItems: 'flex-start', marginBottom: '8px' }}>
        <div style={{ flex: 1 }}>
          <strong style={{ color: '#007acc' }}>{rule.name}</strong>
          <div style={{ fontSize: '13px', color: '#666', marginTop: '2px' }}>
            {rule.description}
          </div>
          <div style={{ fontSize: '12px', color: '#888', marginTop: '4px', fontFamily: 'monospace' }}>
            On: <span style={{ backgroundColor: '#e6f3ff', padding: '1px 4px', borderRadius: '2px' }}>
              {focusedNode.raw}
            </span>
          </div>
        </div>
        <button
          onClick={handleApply}
          style={{
            padding: '6px 14px',
            backgroundColor: '#007acc',
            color: 'white',
            border: 'none',
            borderRadius: '4px',
            cursor: 'pointer',
            fontSize: '13px',
            fontWeight: 'bold'
          }}
        >
          Apply
        </button>
      </div>
    </div>
  );
}

interface FocusedProofHistoryProps {
  steps: FocusedProofStep[];
  currentStepId?: string;
  onStepClick: (step: FocusedProofStep) => void;
}

function FocusedProofHistory({ steps, currentStepId, onStepClick }: FocusedProofHistoryProps) {
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
            padding: '8px',
            border: step.id === currentStepId ? '2px solid #007acc' : '1px solid #e0e0e0',
            borderRadius: '4px',
            backgroundColor: step.id === currentStepId ? '#f8fcff' : 'white',
            cursor: 'pointer'
          }}
          onClick={() => onStepClick(step)}
        >
          <div style={{ 
            fontSize: '12px', 
            color: '#666',
            marginBottom: '4px',
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
            padding: '6px',
            borderRadius: '3px'
          }}>
            {astToString(step.expression)}
          </div>
          {step.focusPath.length > 0 && (
            <div style={{ fontSize: '11px', color: '#888', marginTop: '4px' }}>
              Focus: {getNodeAtPath(step.expression, step.focusPath).raw}
            </div>
          )}
        </div>
      ))}
    </div>
  );
}

export function FocusedProofWorkspace() {
  const [currentExpression, setCurrentExpression] = useState<ExpressionNode>(
    parseExpressionToAST('x + 4 = 5')
  );
  const [focusPath, setFocusPath] = useState<FocusPath>([]);
  const [steps, setSteps] = useState<FocusedProofStep[]>([]);
  const [editingExpression, setEditingExpression] = useState(false);
  const [newExpressionText, setNewExpressionText] = useState('');

  const focusedNode = getNodeAtPath(currentExpression, focusPath);

  const addStep = useCallback((rule: FocusRule, params?: any) => {
    try {
      const newFocusedNode = rule.applyToFocus(focusedNode, currentExpression, params);
      const newExpression = setNodeAtPath(currentExpression, focusPath, newFocusedNode);
      
      // Update the raw string of the new expression
      newExpression.raw = astToString(newExpression);
      
      const newStep: FocusedProofStep = {
        id: crypto.randomUUID(),
        expression: newExpression,
        focusPath: [...focusPath],
        rule,
        ruleParams: params,
        timestamp: Date.now(),
        description: `Applied ${rule.name} to "${focusedNode.raw}"`
      };
      
      setCurrentExpression(newExpression);
      setSteps(prev => [...prev, newStep]);
      
      // Keep focus on the same path (the transformed node)
      // Note: the path stays the same, but the node at that path has changed
      
    } catch (error) {
      console.error('Error applying rule:', error);
      alert(`Error applying rule: ${error instanceof Error ? error.message : 'Unknown error'}`);
    }
  }, [currentExpression, focusPath, focusedNode]);

  const setCurrentStep = useCallback((step: FocusedProofStep) => {
    setCurrentExpression(step.expression);
    setFocusPath(step.focusPath);
  }, []);

  const handleNewExpression = () => {
    if (!newExpressionText.trim()) return;
    
    try {
      const newExpression = parseExpressionToAST(newExpressionText.trim());
      setCurrentExpression(newExpression);
      setFocusPath([]);
      setSteps([]);
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

  const applicableRules = FOCUS_RULES.filter(rule => 
    rule.isApplicableToFocus(focusedNode, currentExpression)
  );

  return (
    <div style={{ 
      display: 'grid', 
      gridTemplateColumns: '1fr 350px', 
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
          <h2 style={{ margin: 0 }}>Focused Proof Workspace</h2>
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
              placeholder="Enter expression (e.g., x + 4 = 5)"
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
            <FocusedExpressionRenderer
              expression={currentExpression}
              focusPath={focusPath}
              onFocusChange={setFocusPath}
              isActive={true}
            />
          </div>
        )}

        <div>
          <h3>Available Rules for Current Focus:</h3>
          {applicableRules.length > 0 ? (
            <div style={{ display: 'grid', gap: '8px' }}>
              {applicableRules.map(rule => (
                <FocusRuleApplication
                  key={rule.id}
                  rule={rule}
                  focusedNode={focusedNode}
                  rootExpression={currentExpression}
                  onApply={addStep}
                />
              ))}
            </div>
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

      {/* Sidebar with history */}
      <div style={{ 
        backgroundColor: '#f8f9fa', 
        padding: '16px', 
        borderRadius: '8px',
        border: '1px solid #e9ecef'
      }}>
        <FocusedProofHistory
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
              {generateFocusedLeanProof(steps)}
            </pre>
          </div>
        )}
      </div>
    </div>
  );
}

// Helper function to generate Lean proof terms for focused rules
function generateFocusedLeanProof(steps: FocusedProofStep[]): string {
  if (steps.length === 0) return '';
  
  const proofTerms = steps.map((step, index) => {
    const stepVar = `h${index + 1}`;
    if (!step.rule) return `${stepVar} : ${astToString(step.expression)} := sorry`;
    
    switch (step.rule.id) {
      case 'add_comm':
        return `${stepVar} : ${astToString(step.expression)} := by rw [add_comm]`;
      case 'mul_comm':
        return `${stepVar} : ${astToString(step.expression)} := by rw [mul_comm]`;
      case 'add_assoc_left':
        return `${stepVar} : ${astToString(step.expression)} := by rw [add_assoc]`;
      case 'distribute_mul':
        return `${stepVar} : ${astToString(step.expression)} := by rw [mul_add]`;
      default:
        return `${stepVar} : ${astToString(step.expression)} := sorry`;
    }
  });
  
  const initialExpr = steps[0] ? astToString(steps[0].expression) : 'initial_expr';
  return `-- Generated focused proof\nvariable (h0 : ${initialExpr})\n\n${proofTerms.join('\n')}`;
}