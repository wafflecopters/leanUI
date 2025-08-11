import { useState, useCallback } from 'react';
import { Expression, ProofStep, ProofRule, ProofContext, parseExpression, PROOF_RULES } from '../types/proof';
import { ExpressionRenderer, ExpressionEditor } from './ExpressionRenderer';

interface RuleApplicationProps {
  rule: ProofRule;
  currentExpression: Expression;
  context: ProofContext;
  onApply: (rule: ProofRule, params?: any) => void;
}

function RuleApplication({ rule, currentExpression, context, onApply }: RuleApplicationProps) {
  const [params, setParams] = useState<any>({});
  const [showParams, setShowParams] = useState(false);

  const needsParams = ['add_both_sides', 'subtract_both_sides', 'multiply_both_sides'].includes(rule.id);
  const isApplicable = rule.isApplicable(currentExpression, context);

  const handleApply = () => {
    if (needsParams && !showParams) {
      setShowParams(true);
      return;
    }
    onApply(rule, needsParams ? params : undefined);
    setShowParams(false);
    setParams({});
  };

  if (!isApplicable) {
    return null;
  }

  return (
    <div style={{ 
      margin: '4px 0', 
      padding: '8px', 
      border: '1px solid #e0e0e0', 
      borderRadius: '4px',
      backgroundColor: '#f9f9f9'
    }}>
      <div style={{ display: 'flex', justifyContent: 'space-between', alignItems: 'center' }}>
        <div>
          <strong>{rule.name}</strong>
          <div style={{ fontSize: '12px', color: '#666' }}>{rule.description}</div>
        </div>
        <button
          onClick={handleApply}
          style={{
            padding: '4px 12px',
            backgroundColor: '#007acc',
            color: 'white',
            border: 'none',
            borderRadius: '4px',
            cursor: 'pointer'
          }}
        >
          Apply
        </button>
      </div>
      
      {showParams && needsParams && (
        <div style={{ marginTop: '8px' }}>
          <input
            type="text"
            placeholder="Enter value..."
            value={params.value || ''}
            onChange={(e) => setParams({ ...params, value: e.target.value })}
            style={{
              width: '100%',
              padding: '4px 8px',
              fontFamily: 'monospace',
              border: '1px solid #ccc',
              borderRadius: '4px'
            }}
          />
        </div>
      )}
    </div>
  );
}

interface ProofStepHistoryProps {
  steps: ProofStep[];
  currentStepId?: string;
  onStepClick: (step: ProofStep) => void;
}

function ProofStepHistory({ steps, currentStepId, onStepClick }: ProofStepHistoryProps) {
  if (steps.length === 0) {
    return (
      <div style={{ padding: '16px', color: '#666', fontStyle: 'italic' }}>
        No proof steps yet. Start by entering an expression.
      </div>
    );
  }

  return (
    <div style={{ maxHeight: '300px', overflowY: 'auto' }}>
      <h3 style={{ margin: '0 0 12px 0', fontSize: '16px' }}>Proof Steps:</h3>
      {steps.map((step, index) => (
        <div key={step.id} style={{ marginBottom: '8px' }}>
          <div style={{ 
            fontSize: '12px', 
            color: '#666',
            marginBottom: '2px',
            display: 'flex',
            justifyContent: 'space-between'
          }}>
            <span>Step {index + 1}: {step.rule.name}</span>
            {step.ruleParams && (
              <span>({JSON.stringify(step.ruleParams)})</span>
            )}
          </div>
          <ExpressionRenderer
            expression={step.expression}
            isActive={step.id === currentStepId}
            onClick={() => onStepClick(step)}
          />
        </div>
      ))}
    </div>
  );
}

export function ProofWorkspace() {
  const [context, setContext] = useState<ProofContext>({
    currentExpression: parseExpression('x + 4 = 5'),
    steps: [],
    variables: new Map([['x', 'ℕ']]),
    hypotheses: []
  });
  
  const [editingExpression, setEditingExpression] = useState(false);
  const [newExpressionText, setNewExpressionText] = useState('');

  const addStep = useCallback((rule: ProofRule, params?: any) => {
    const newStep = rule.apply(context.currentExpression, params);
    newStep.previousStep = context.steps.length > 0 ? context.steps[context.steps.length - 1].id : undefined;
    
    setContext(prev => ({
      ...prev,
      currentExpression: newStep.expression,
      steps: [...prev.steps, newStep]
    }));
  }, [context.currentExpression, context.steps]);

  const setCurrentStep = useCallback((step: ProofStep) => {
    setContext(prev => ({
      ...prev,
      currentExpression: step.expression
    }));
  }, []);

  const handleNewExpression = () => {
    if (!newExpressionText.trim()) return;
    
    const newExpression = parseExpression(newExpressionText.trim());
    setContext(prev => ({
      ...prev,
      currentExpression: newExpression,
      steps: []
    }));
    
    setEditingExpression(false);
    setNewExpressionText('');
  };

  const startEditing = () => {
    setEditingExpression(true);
    setNewExpressionText(context.currentExpression.raw);
  };

  return (
    <div style={{ 
      display: 'grid', 
      gridTemplateColumns: '1fr 300px', 
      gap: '20px', 
      padding: '20px',
      fontFamily: 'system-ui, sans-serif'
    }}>
      {/* Main workspace */}
      <div>
        <div style={{ display: 'flex', justifyContent: 'space-between', alignItems: 'center', marginBottom: '16px' }}>
          <h2 style={{ margin: 0 }}>Proof Workspace</h2>
          <button
            onClick={startEditing}
            style={{
              padding: '6px 12px',
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
          <div style={{ marginBottom: '20px' }}>
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
          <div style={{ marginBottom: '20px' }}>
            <h3>Current Expression:</h3>
            <ExpressionRenderer expression={context.currentExpression} isActive={true} />
          </div>
        )}

        <div>
          <h3>Available Rules:</h3>
          <div style={{ display: 'grid', gap: '8px' }}>
            {PROOF_RULES.map(rule => (
              <RuleApplication
                key={rule.id}
                rule={rule}
                currentExpression={context.currentExpression}
                context={context}
                onApply={addStep}
              />
            ))}
          </div>
        </div>
      </div>

      {/* Sidebar with history */}
      <div style={{ 
        backgroundColor: '#f8f9fa', 
        padding: '16px', 
        borderRadius: '8px',
        border: '1px solid #e9ecef'
      }}>
        <ProofStepHistory
          steps={context.steps}
          currentStepId={context.steps.length > 0 ? context.steps[context.steps.length - 1].id : undefined}
          onStepClick={setCurrentStep}
        />

        {context.steps.length > 0 && (
          <div style={{ marginTop: '16px', padding: '12px', backgroundColor: 'white', borderRadius: '4px' }}>
            <h4 style={{ margin: '0 0 8px 0', fontSize: '14px' }}>Lean Proof Term:</h4>
            <pre style={{ 
              fontSize: '10px', 
              margin: 0, 
              wordWrap: 'break-word',
              whiteSpace: 'pre-wrap'
            }}>
              {generateLeanProof(context.steps)}
            </pre>
          </div>
        )}
      </div>
    </div>
  );
}

// Helper function to generate Lean proof terms
function generateLeanProof(steps: ProofStep[]): string {
  if (steps.length === 0) return '';
  
  const proofTerms = steps.map((step, index) => {
    const stepVar = `h${index + 1}`;
    switch (step.rule.id) {
      case 'symmetry':
        return `${stepVar} : ${step.expression.raw} := Eq.symm h${index}`;
      case 'add_both_sides':
        return `${stepVar} : ${step.expression.raw} := by rw [← add_right_cancel_iff]; exact h${index}`;
      case 'subtract_both_sides':
        return `${stepVar} : ${step.expression.raw} := by rw [← sub_right_inj]; exact h${index}`;
      case 'multiply_both_sides':
        return `${stepVar} : ${step.expression.raw} := by rw [← mul_right_inj]; exact h${index}`;
      case 'transitivity':
        return `${stepVar} : ${step.expression.raw} := Eq.trans h${index} h_other`;
      default:
        return `${stepVar} : ${step.expression.raw} := sorry`;
    }
  });
  
  return `-- Generated proof\nvariable (h0 : ${steps[0]?.previousStep ? 'previous_expr' : steps[0]?.expression.raw})\n\n${proofTerms.join('\n')}`;
}