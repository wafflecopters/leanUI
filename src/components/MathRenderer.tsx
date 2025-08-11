import { useState } from 'react';
import { ExpressionNode, FocusPath } from '../types/enhanced-focus';

interface MathRendererProps {
  expression: ExpressionNode;
  focusPath: FocusPath;
  onFocusChange: (newPath: FocusPath) => void;
  isActive?: boolean;
}

interface MathNodeProps {
  node: ExpressionNode;
  currentPath: FocusPath;
  focusPath: FocusPath;
  onFocusChange: (newPath: FocusPath) => void;
  onMouseEnter: (path: FocusPath) => void;
  onMouseLeave: () => void;
  hoveredPath: FocusPath | null;
}

function arraysEqual(a: FocusPath, b: FocusPath): boolean {
  return a.length === b.length && a.every((val, i) => val === b[i]);
}

function MathNode({ 
  node, 
  currentPath, 
  focusPath, 
  onFocusChange, 
  onMouseEnter, 
  onMouseLeave,
  hoveredPath 
}: MathNodeProps) {
  const isFocused = arraysEqual(currentPath, focusPath);
  const isHovered = hoveredPath && arraysEqual(currentPath, hoveredPath);
  
  const handleClick = (e: React.MouseEvent) => {
    e.stopPropagation();
    onFocusChange(currentPath);
  };

  const baseStyle = {
    cursor: 'pointer',
    borderRadius: '3px',
    padding: '2px 3px',
    margin: '0 1px',
    display: 'inline-block',
    backgroundColor: isFocused ? '#007acc' : isHovered ? '#e6f3ff' : 'transparent',
    color: isFocused ? 'white' : '#000',
    border: isFocused ? '2px solid #005a9e' : isHovered ? '1px solid #cce7ff' : '1px solid transparent',
    transition: 'all 0.15s ease',
    fontFamily: 'KaTeX_Main, "Times New Roman", serif',
    fontSize: '18px'
  };

  const renderFraction = (numerator: ExpressionNode, denominator: ExpressionNode) => (
    <span
      style={{
        ...baseStyle,
        display: 'inline-flex',
        flexDirection: 'column',
        alignItems: 'center',
        minWidth: '20px'
      }}
      onClick={handleClick}
      onMouseEnter={() => onMouseEnter(currentPath)}
      onMouseLeave={onMouseLeave}
    >
      <span style={{ borderBottom: '1px solid currentColor', paddingBottom: '2px', fontSize: '16px' }}>
        <MathNode 
          node={numerator}
          currentPath={[...currentPath, 0]}
          focusPath={focusPath}
          onFocusChange={onFocusChange}
          onMouseEnter={onMouseEnter}
          onMouseLeave={onMouseLeave}
          hoveredPath={hoveredPath}
        />
      </span>
      <span style={{ paddingTop: '2px', fontSize: '16px' }}>
        <MathNode 
          node={denominator}
          currentPath={[...currentPath, 1]}
          focusPath={focusPath}
          onFocusChange={onFocusChange}
          onMouseEnter={onMouseEnter}
          onMouseLeave={onMouseLeave}
          hoveredPath={hoveredPath}
        />
      </span>
    </span>
  );

  const renderExponent = (base: ExpressionNode, exponent: ExpressionNode) => (
    <span
      style={baseStyle}
      onClick={handleClick}
      onMouseEnter={() => onMouseEnter(currentPath)}
      onMouseLeave={onMouseLeave}
    >
      <MathNode 
        node={base}
        currentPath={[...currentPath, 0]}
        focusPath={focusPath}
        onFocusChange={onFocusChange}
        onMouseEnter={onMouseEnter}
        onMouseLeave={onMouseLeave}
        hoveredPath={hoveredPath}
      />
      <span style={{ fontSize: '12px', verticalAlign: 'super', marginLeft: '1px' }}>
        <MathNode 
          node={exponent}
          currentPath={[...currentPath, 1]}
          focusPath={focusPath}
          onFocusChange={onFocusChange}
          onMouseEnter={onMouseEnter}
          onMouseLeave={onMouseLeave}
          hoveredPath={hoveredPath}
        />
      </span>
    </span>
  );

  const renderBinaryOp = (left: ExpressionNode, operator: string, right: ExpressionNode) => {
    // Special rendering for division as fraction
    if (operator === '/') {
      return renderFraction(left, right);
    }

    // Special rendering for exponentiation
    if (operator === '^') {
      return renderExponent(left, right);
    }

    // Regular binary operations
    const opSymbol = {
      '+': '+',
      '-': '−', // Use proper minus sign
      '*': '×', // Use proper multiplication sign
      '=': '=',
      '≠': '≠',
      '<': '<',
      '>': '>',
      '≤': '≤',
      '≥': '≥'
    }[operator] || operator;

    return (
      <span
        style={baseStyle}
        onClick={handleClick}
        onMouseEnter={() => onMouseEnter(currentPath)}
        onMouseLeave={onMouseLeave}
      >
        <MathNode 
          node={left}
          currentPath={[...currentPath, 0]}
          focusPath={focusPath}
          onFocusChange={onFocusChange}
          onMouseEnter={onMouseEnter}
          onMouseLeave={onMouseLeave}
          hoveredPath={hoveredPath}
        />
        <span style={{ 
          margin: '0 6px', 
          fontWeight: operator === '=' ? 'normal' : 'normal',
          color: isFocused ? 'white' : '#333'
        }}>
          {opSymbol}
        </span>
        <MathNode 
          node={right}
          currentPath={[...currentPath, 1]}
          focusPath={focusPath}
          onFocusChange={onFocusChange}
          onMouseEnter={onMouseEnter}
          onMouseLeave={onMouseLeave}
          hoveredPath={hoveredPath}
        />
      </span>
    );
  };

  switch (node.type) {
    case 'equality':
    case 'inequality':
    case 'binop':
      if (node.children.length === 2 && node.operator) {
        return renderBinaryOp(node.children[0], node.operator, node.children[1]);
      }
      break;
      
    case 'unop':
      if (node.children.length === 1) {
        return (
          <span
            style={baseStyle}
            onClick={handleClick}
            onMouseEnter={() => onMouseEnter(currentPath)}
            onMouseLeave={onMouseLeave}
          >
            <span style={{ color: isFocused ? 'white' : '#333' }}>
              {node.operator}
            </span>
            <MathNode 
              node={node.children[0]}
              currentPath={[...currentPath, 0]}
              focusPath={focusPath}
              onFocusChange={onFocusChange}
              onMouseEnter={onMouseEnter}
              onMouseLeave={onMouseLeave}
              hoveredPath={hoveredPath}
            />
          </span>
        );
      }
      break;
      
    case 'literal':
      return (
        <span
          style={baseStyle}
          onClick={handleClick}
          onMouseEnter={() => onMouseEnter(currentPath)}
          onMouseLeave={onMouseLeave}
        >
          {String(node.value)}
        </span>
      );
      
    case 'variable':
      return (
        <span
          style={{
            ...baseStyle,
            fontStyle: 'italic',
            fontFamily: 'KaTeX_Math, "Times New Roman", serif'
          }}
          onClick={handleClick}
          onMouseEnter={() => onMouseEnter(currentPath)}
          onMouseLeave={onMouseLeave}
        >
          {String(node.value)}
        </span>
      );
      
    case 'application':
      return (
        <span
          style={baseStyle}
          onClick={handleClick}
          onMouseEnter={() => onMouseEnter(currentPath)}
          onMouseLeave={onMouseLeave}
        >
          {node.children.map((child, index) => (
            <span key={child.id}>
              {index > 0 && ' '}
              <MathNode 
                node={child}
                currentPath={[...currentPath, index]}
                focusPath={focusPath}
                onFocusChange={onFocusChange}
                onMouseEnter={onMouseEnter}
                onMouseLeave={onMouseLeave}
                hoveredPath={hoveredPath}
              />
            </span>
          ))}
        </span>
      );
  }
  
  // Fallback
  return (
    <span
      style={baseStyle}
      onClick={handleClick}
      onMouseEnter={() => onMouseEnter(currentPath)}
      onMouseLeave={onMouseLeave}
    >
      {node.raw}
    </span>
  );
}

export function MathRenderer({ expression, focusPath, onFocusChange, isActive = false }: MathRendererProps) {
  const [hoveredPath, setHoveredPath] = useState<FocusPath | null>(null);

  const containerStyle = {
    padding: '20px 24px',
    margin: '8px 0',
    borderRadius: '8px',
    fontSize: '20px',
    border: '3px solid',
    borderColor: isActive ? '#007acc' : '#e0e0e0',
    backgroundColor: isActive ? '#f8fcff' : '#fafafa',
    minHeight: '80px',
    display: 'flex',
    alignItems: 'center',
    position: 'relative' as const,
    fontFamily: 'KaTeX_Main, "Times New Roman", serif'
  };

  const focusedNode = getCurrentNode(expression, focusPath);

  return (
    <div style={containerStyle}>
      <div style={{ flex: 1, textAlign: 'center' }}>
        <MathNode
          node={expression}
          currentPath={[]}
          focusPath={focusPath}
          onFocusChange={onFocusChange}
          onMouseEnter={setHoveredPath}
          onMouseLeave={() => setHoveredPath(null)}
          hoveredPath={hoveredPath}
        />
      </div>
      
      {focusPath.length > 0 && focusedNode && (
        <div style={{
          position: 'absolute',
          top: '-12px',
          right: '12px',
          backgroundColor: '#007acc',
          color: 'white',
          padding: '4px 12px',
          borderRadius: '12px',
          fontSize: '12px',
          fontWeight: 'bold',
          fontFamily: 'system-ui, sans-serif'
        }}>
          Focus: {focusedNode.raw}
        </div>
      )}
      
      <div style={{ 
        marginLeft: '20px',
        display: 'flex',
        flexDirection: 'column',
        gap: '6px'
      }}>
        <button
          onClick={() => onFocusChange([])}
          disabled={focusPath.length === 0}
          style={{
            padding: '6px 12px',
            backgroundColor: focusPath.length === 0 ? '#ccc' : '#6c757d',
            color: 'white',
            border: 'none',
            borderRadius: '4px',
            cursor: focusPath.length === 0 ? 'not-allowed' : 'pointer',
            fontSize: '12px',
            fontFamily: 'system-ui, sans-serif'
          }}
        >
          Root
        </button>
        
        {focusPath.length > 0 && (
          <button
            onClick={() => onFocusChange(focusPath.slice(0, -1))}
            style={{
              padding: '6px 12px',
              backgroundColor: '#6c757d',
              color: 'white',
              border: 'none',
              borderRadius: '4px',
              cursor: 'pointer',
              fontSize: '12px',
              fontFamily: 'system-ui, sans-serif'
            }}
          >
            Up
          </button>
        )}
      </div>
    </div>
  );
}

// Helper function to get current node at focus path
function getCurrentNode(root: ExpressionNode, path: FocusPath): ExpressionNode | null {
  try {
    let current = root;
    for (const index of path) {
      if (index >= current.children.length) {
        return null;
      }
      current = current.children[index];
    }
    return current;
  } catch {
    return null;
  }
}