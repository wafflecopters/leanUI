import React from 'react';
import { Expression } from '../types/proof';

interface ExpressionRendererProps {
  expression: Expression;
  isActive?: boolean;
  onClick?: () => void;
}

export function ExpressionRenderer({ expression, isActive = false, onClick }: ExpressionRendererProps) {
  const baseStyle = {
    padding: '12px 16px',
    margin: '4px 0',
    borderRadius: '6px',
    fontFamily: 'monospace',
    fontSize: '16px',
    border: '2px solid',
    borderColor: isActive ? '#007acc' : '#e0e0e0',
    backgroundColor: isActive ? '#f0f8ff' : '#fafafa',
    cursor: onClick ? 'pointer' : 'default',
    transition: 'all 0.2s ease'
  };

  const operatorStyle = {
    color: '#d73a49',
    fontWeight: 'bold',
    margin: '0 8px'
  };

  const termStyle = {
    color: '#032f62'
  };

  const handleClick = () => {
    if (onClick) onClick();
  };

  const renderContent = () => {
    switch (expression.type) {
      case 'equality':
      case 'inequality':
        return (
          <span>
            <span style={termStyle}>{String(expression.left)}</span>
            <span style={operatorStyle}>{expression.operator}</span>
            <span style={termStyle}>{String(expression.right)}</span>
          </span>
        );
      case 'proposition':
        return <span style={termStyle}>{expression.value || expression.raw}</span>;
      default:
        return <span style={termStyle}>{expression.raw}</span>;
    }
  };

  return (
    <div style={baseStyle} onClick={handleClick}>
      {renderContent()}
    </div>
  );
}

// Shared expression input component that can be used in various contexts
export interface ExpressionInputProps {
  value: string;
  onChange: (value: string) => void;
  placeholder?: string;
  autoFocus?: boolean;
  onKeyPress?: (e: React.KeyboardEvent) => void;
  style?: React.CSSProperties;
  showExamples?: boolean;
}

export function ExpressionInput({
  value,
  onChange,
  placeholder = "Enter expression...",
  autoFocus = false,
  onKeyPress,
  style,
  showExamples = false
}: ExpressionInputProps) {
  return (
    <div style={{ display: 'flex', gap: '8px', alignItems: 'center', ...style }}>
      <input
        type="text"
        value={value}
        onChange={(e) => onChange(e.target.value)}
        onKeyPress={onKeyPress}
        placeholder={placeholder}
        autoFocus={autoFocus}
        style={{
          flex: 1,
          padding: '8px 12px',
          fontFamily: 'monospace',
          fontSize: '14px',
          border: '1px solid #ccc',
          borderRadius: '4px',
          outline: 'none'
        }}
      />
      {showExamples && (
        <select
          value={'Example'}
          onChange={(e) => {
            if (e.target.value !== 'Example') {
              onChange(e.target.value);
            }
          }}
          style={{
            padding: '8px',
            borderRadius: '4px',
            border: '1px solid #ccc'
          }}
        >
          <option value={'Example'}>Examples</option>
          {ExampleExpressions.map((expr, i) => (
            <option key={i} value={expr.contents}>{expr.contents}</option>
          ))}
        </select>
      )}
    </div>
  );
}

interface ExpressionEditorProps {
  value: string;
  onChange: (value: string) => void;
  onSubmit: () => void;
  placeholder?: string;
}

export type WorkspaceExample = {
  contents: string,
  assumptions: string[],
}

const ExampleExpressions: WorkspaceExample[] = [
  {
    contents: 'deriv (c * (f x)) x',
    assumptions: ['c: ℝ', 'f: ℝ → ℝ'],
  },
  {
    contents: 'x+2*y',
    assumptions: ['x: ℝ', 'y: ℝ'],
  },
  {
    contents: 'sum i 0 k i',
    assumptions: ['i: ℕ', 'k: ℕ'],
  },
]

export function ExpressionEditor({ value, onChange, onSubmit, placeholder = "Enter expression..." }: ExpressionEditorProps) {
  const handleKeyPress = (e: React.KeyboardEvent) => {
    if (e.key === 'Enter' && !e.shiftKey) {
      e.preventDefault();
      onSubmit();
    }
  };

  return (
    <div style={{ margin: '8px 0' }}>
      <ExpressionInput
        value={value}
        onChange={onChange}
        placeholder={placeholder}
        autoFocus={true}
        onKeyPress={handleKeyPress}
        showExamples={true}
        style={{ width: '100%' }}
      />
      <button
        onClick={onSubmit}
        disabled={!value.trim()}
        style={{
          marginTop: '8px',
          padding: '8px 16px',
          backgroundColor: '#007acc',
          color: 'white',
          border: 'none',
          borderRadius: '4px',
          cursor: value.trim() ? 'pointer' : 'not-allowed',
          opacity: value.trim() ? 1 : 0.5
        }}
      >
        Set Expression
      </button>
    </div>
  );
}