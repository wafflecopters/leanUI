import { ProofContext } from '../types/enhanced-focus';

interface AssumptionsDisplayProps {
  context: ProofContext;
}

export function AssumptionsDisplay({ context }: AssumptionsDisplayProps) {
  const hasVariables = context.variables.size > 0;
  const hasAssumptions = context.assumptions.length > 0;

  if (!hasVariables && !hasAssumptions) {
    return null;
  }

  return (
    <div style={{
      backgroundColor: '#f8f9fa',
      border: '1px solid #e9ecef',
      borderRadius: '8px',
      padding: '12px 16px',
      margin: '8px 0',
      fontSize: '14px',
      fontFamily: 'system-ui, sans-serif'
    }}>
      <div style={{
        fontWeight: 'bold',
        marginBottom: '8px',
        color: '#495057',
        fontSize: '12px',
        textTransform: 'uppercase',
        letterSpacing: '0.5px'
      }}>
        Context
      </div>

      {hasVariables && (
        <div style={{ marginBottom: hasAssumptions ? '8px' : '0' }}>
          <div style={{
            fontSize: '12px',
            color: '#6c757d',
            marginBottom: '4px',
            fontWeight: '500'
          }}>
            Variables:
          </div>
          <div style={{
            display: 'flex',
            flexWrap: 'wrap',
            gap: '8px'
          }}>
            {Array.from(context.variables.entries()).map(([variable, type]) => (
              <span
                key={variable}
                style={{
                  backgroundColor: '#e7f3ff',
                  color: '#0066cc',
                  padding: '2px 8px',
                  borderRadius: '4px',
                  fontSize: '13px',
                  fontFamily: 'monospace',
                  border: '1px solid #b3d9ff'
                }}
              >
                {variable} : {type}
              </span>
            ))}
          </div>
        </div>
      )}

      {hasAssumptions && (
        <div>
          <div style={{
            fontSize: '12px',
            color: '#6c757d',
            marginBottom: '4px',
            fontWeight: '500'
          }}>
            Assumptions:
          </div>
          <div style={{
            display: 'flex',
            flexDirection: 'column',
            gap: '4px'
          }}>
            {context.assumptions.map((assumption, index) => (
              <span
                key={index}
                style={{
                  backgroundColor: '#fff3cd',
                  color: '#856404',
                  padding: '4px 8px',
                  borderRadius: '4px',
                  fontSize: '13px',
                  fontFamily: 'monospace',
                  border: '1px solid #ffeaa7'
                }}
              >
                {assumption.name}: {assumption.expression}
              </span>
            ))}
          </div>
        </div>
      )}
    </div>
  );
}