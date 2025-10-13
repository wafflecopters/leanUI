import { useState, useEffect } from 'react';
import {
  ExpressionNode,
  LetElement,
  parseExpressionToAST
} from '../types/enhanced-focus';
import { extractFreeVariables } from '../types/let-system';
import { MathJaxExpressionRenderer } from './MathJaxExpressionRenderer';

interface InstantiationDialogProps {
  letBinding: LetElement;
  onInstantiate: (letId: string, substitutions: Map<string, ExpressionNode>) => void;
  onClose: () => void;
}

export function InstantiationDialog({
  letBinding,
  onInstantiate,
  onClose
}: InstantiationDialogProps) {
  const [freeVars, setFreeVars] = useState<string[]>([]);
  const [substitutions, setSubstitutions] = useState<Map<string, string>>(new Map());
  const [errors, setErrors] = useState<Map<string, string>>(new Map());

  useEffect(() => {
    const vars = Array.from(extractFreeVariables(letBinding.value));
    setFreeVars(vars);

    const initialSubs = new Map<string, string>();
    vars.forEach(v => initialSubs.set(v, ''));
    setSubstitutions(initialSubs);
  }, [letBinding]);

  const handleSubstitutionChange = (varName: string, value: string) => {
    const newSubs = new Map(substitutions);
    newSubs.set(varName, value);
    setSubstitutions(newSubs);

    // Clear error for this variable
    const newErrors = new Map(errors);
    newErrors.delete(varName);
    setErrors(newErrors);
  };

  const handleInstantiate = () => {
    const newErrors = new Map<string, string>();
    const parsedSubs = new Map<string, ExpressionNode>();

    let hasErrors = false;
    for (const [varName, value] of substitutions) {
      if (!value.trim()) {
        newErrors.set(varName, 'Value is required');
        hasErrors = true;
      } else {
        try {
          const expr = parseExpressionToAST(value);
          parsedSubs.set(varName, expr);
        } catch (error) {
          newErrors.set(varName, `Invalid expression: ${error}`);
          hasErrors = true;
        }
      }
    }

    if (hasErrors) {
      setErrors(newErrors);
      return;
    }

    onInstantiate(letBinding.id, parsedSubs);
    onClose();
  };

  return (
    <div style={{
      position: 'fixed',
      top: 0,
      left: 0,
      right: 0,
      bottom: 0,
      backgroundColor: 'rgba(0, 0, 0, 0.5)',
      display: 'flex',
      alignItems: 'center',
      justifyContent: 'center',
      zIndex: 1000
    }}>
      <div style={{
        backgroundColor: 'white',
        borderRadius: '8px',
        padding: '24px',
        maxWidth: '600px',
        width: '90%',
        maxHeight: '80vh',
        overflowY: 'auto'
      }}>
        <h3 style={{ marginTop: 0, marginBottom: '20px' }}>
          Instantiate: {letBinding.name}
        </h3>

        <div style={{
          backgroundColor: '#f8f9fa',
          padding: '12px',
          borderRadius: '4px',
          marginBottom: '20px'
        }}>
          <div style={{ fontWeight: 'bold', marginBottom: '8px' }}>Expression:</div>
          <MathJaxExpressionRenderer
            expression={letBinding.value}
            readonly={true}
          />
        </div>

        {freeVars.length === 0 ? (
          <div style={{
            padding: '16px',
            backgroundColor: '#fff3cd',
            border: '1px solid #ffc107',
            borderRadius: '4px',
            marginBottom: '20px'
          }}>
            This expression has no free variables to instantiate.
          </div>
        ) : (
          <>
            <div style={{ marginBottom: '20px' }}>
              <h4 style={{ marginBottom: '12px' }}>
                Substitute values for the following variables:
              </h4>
              {freeVars.map(varName => (
                <div key={varName} style={{ marginBottom: '16px' }}>
                  <label style={{
                    display: 'block',
                    fontWeight: 'bold',
                    marginBottom: '4px'
                  }}>
                    {varName}:
                  </label>
                  <input
                    type="text"
                    value={substitutions.get(varName) || ''}
                    onChange={(e) => handleSubstitutionChange(varName, e.target.value)}
                    placeholder={`Enter value for ${varName}`}
                    style={{
                      width: '100%',
                      padding: '8px',
                      border: `1px solid ${errors.has(varName) ? '#dc3545' : '#ced4da'}`,
                      borderRadius: '4px',
                      fontSize: '14px'
                    }}
                  />
                  {errors.has(varName) && (
                    <div style={{
                      color: '#dc3545',
                      fontSize: '12px',
                      marginTop: '4px'
                    }}>
                      {errors.get(varName)}
                    </div>
                  )}
                </div>
              ))}
            </div>

            <div style={{
              backgroundColor: '#e9ecef',
              padding: '12px',
              borderRadius: '4px',
              marginBottom: '20px'
            }}>
              <div style={{ fontWeight: 'bold', marginBottom: '8px' }}>Preview:</div>
              <div style={{ fontStyle: 'italic', color: '#6c757d' }}>
                The instantiated expression will be computed after substitution
              </div>
            </div>
          </>
        )}

        <div style={{
          display: 'flex',
          gap: '12px',
          justifyContent: 'flex-end'
        }}>
          <button
            onClick={onClose}
            style={{
              padding: '8px 16px',
              backgroundColor: '#6c757d',
              color: 'white',
              border: 'none',
              borderRadius: '4px',
              cursor: 'pointer',
              fontSize: '14px'
            }}
          >
            Cancel
          </button>
          {freeVars.length > 0 && (
            <button
              onClick={handleInstantiate}
              style={{
                padding: '8px 16px',
                backgroundColor: '#28a745',
                color: 'white',
                border: 'none',
                borderRadius: '4px',
                cursor: 'pointer',
                fontSize: '14px'
              }}
            >
              Instantiate
            </button>
          )}
        </div>
      </div>
    </div>
  );
}