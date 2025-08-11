import { useState } from 'react';
import { ExpressionNode, FocusPath, getNodeAtPath } from '../types/focus';

interface FocusedExpressionRendererProps {
  expression: ExpressionNode;
  focusPath: FocusPath;
  onFocusChange: (newPath: FocusPath) => void;
  isActive?: boolean;
}

export function FocusedExpressionRenderer({ 
  expression, 
  focusPath, 
  onFocusChange, 
  isActive = false 
}: FocusedExpressionRendererProps) {
  const [hoveredPath, setHoveredPath] = useState<FocusPath | null>(null);
  
  const getStyleForPath = (path: FocusPath) => {
    const isFocused = arraysEqual(path, focusPath);
    const isHovered = hoveredPath && arraysEqual(path, hoveredPath);
    
    return {
      cursor: 'pointer',
      borderRadius: '3px',
      padding: '2px 4px',
      margin: '0 1px',
      backgroundColor: isFocused ? '#007acc' : isHovered ? '#e6f3ff' : 'transparent',
      color: isFocused ? 'white' : '#032f62',
      border: isFocused ? '2px solid #005a9e' : isHovered ? '1px solid #cce7ff' : '1px solid transparent',
      transition: 'all 0.15s ease'
    };
  };

  const handleNodeClick = (path: FocusPath) => {
    onFocusChange(path);
  };

  const renderNode = (node: ExpressionNode, currentPath: FocusPath): JSX.Element => {
    const nodeStyle = getStyleForPath(currentPath);
    
    const handleClick = (e: React.MouseEvent) => {
      e.stopPropagation();
      handleNodeClick(currentPath);
    };
    
    const handleMouseEnter = () => {
      setHoveredPath(currentPath);
    };
    
    const handleMouseLeave = () => {
      setHoveredPath(null);
    };

    switch (node.type) {
      case 'equality':
      case 'inequality':
      case 'binop':
        if (node.children.length === 2) {
          return (
            <span
              style={nodeStyle}
              onClick={handleClick}
              onMouseEnter={handleMouseEnter}
              onMouseLeave={handleMouseLeave}
            >
              {renderNode(node.children[0], [...currentPath, 0])}
              <span style={{ 
                color: arraysEqual(currentPath, focusPath) ? 'white' : '#d73a49', 
                fontWeight: 'bold', 
                margin: '0 4px' 
              }}>
                {node.operator}
              </span>
              {renderNode(node.children[1], [...currentPath, 1])}
            </span>
          );
        }
        break;
        
      case 'unop':
        if (node.children.length === 1) {
          return (
            <span
              style={nodeStyle}
              onClick={handleClick}
              onMouseEnter={handleMouseEnter}
              onMouseLeave={handleMouseLeave}
            >
              <span style={{ color: arraysEqual(currentPath, focusPath) ? 'white' : '#d73a49', fontWeight: 'bold' }}>
                {node.operator}
              </span>
              {renderNode(node.children[0], [...currentPath, 0])}
            </span>
          );
        }
        break;
        
      case 'literal':
      case 'variable':
        return (
          <span
            style={nodeStyle}
            onClick={handleClick}
            onMouseEnter={handleMouseEnter}
            onMouseLeave={handleMouseLeave}
          >
            {String(node.value)}
          </span>
        );
        
      case 'application':
        return (
          <span
            style={nodeStyle}
            onClick={handleClick}
            onMouseEnter={handleMouseEnter}
            onMouseLeave={handleMouseLeave}
          >
            {node.children.map((child, index) => (
              <span key={child.id}>
                {index > 0 && ' '}
                {renderNode(child, [...currentPath, index])}
              </span>
            ))}
          </span>
        );
    }
    
    return (
      <span
        style={nodeStyle}
        onClick={handleClick}
        onMouseEnter={handleMouseEnter}
        onMouseLeave={handleMouseLeave}
      >
        {node.raw}
      </span>
    );
  };

  const containerStyle = {
    padding: '16px 20px',
    margin: '8px 0',
    borderRadius: '8px',
    fontFamily: 'monospace',
    fontSize: '18px',
    border: '3px solid',
    borderColor: isActive ? '#007acc' : '#e0e0e0',
    backgroundColor: isActive ? '#f8fcff' : '#fafafa',
    minHeight: '60px',
    display: 'flex',
    alignItems: 'center',
    position: 'relative' as const
  };

  const focusedNode = getNodeAtPath(expression, focusPath);

  return (
    <div style={containerStyle}>
      <div style={{ flex: 1 }}>
        {renderNode(expression, [])}
      </div>
      
      {focusPath.length > 0 && (
        <div style={{
          position: 'absolute',
          top: '-12px',
          right: '12px',
          backgroundColor: '#007acc',
          color: 'white',
          padding: '2px 8px',
          borderRadius: '12px',
          fontSize: '12px',
          fontWeight: 'bold'
        }}>
          Focus: {focusedNode.raw}
        </div>
      )}
      
      <div style={{ 
        marginLeft: '16px',
        display: 'flex',
        flexDirection: 'column',
        gap: '4px'
      }}>
        <button
          onClick={() => onFocusChange([])}
          disabled={focusPath.length === 0}
          style={{
            padding: '4px 8px',
            backgroundColor: focusPath.length === 0 ? '#ccc' : '#6c757d',
            color: 'white',
            border: 'none',
            borderRadius: '4px',
            cursor: focusPath.length === 0 ? 'not-allowed' : 'pointer',
            fontSize: '12px'
          }}
        >
          Root
        </button>
        
        {focusPath.length > 0 && (
          <button
            onClick={() => onFocusChange(focusPath.slice(0, -1))}
            style={{
              padding: '4px 8px',
              backgroundColor: '#6c757d',
              color: 'white',
              border: 'none',
              borderRadius: '4px',
              cursor: 'pointer',
              fontSize: '12px'
            }}
          >
            Up
          </button>
        )}
      </div>
    </div>
  );
}

// Helper function to compare arrays
function arraysEqual(a: FocusPath, b: FocusPath): boolean {
  return a.length === b.length && a.every((val, i) => val === b[i]);
}

interface FocusBreadcrumbsProps {
  expression: ExpressionNode;
  focusPath: FocusPath;
  onFocusChange: (newPath: FocusPath) => void;
}

export function FocusBreadcrumbs({ expression, focusPath, onFocusChange }: FocusBreadcrumbsProps) {
  const breadcrumbs = [];
  let currentPath: FocusPath = [];
  
  // Add root
  breadcrumbs.push({
    label: 'Root',
    path: [],
    node: expression
  });
  
  // Add each step in the path
  for (let i = 0; i < focusPath.length; i++) {
    currentPath = [...currentPath, focusPath[i]];
    const node = getNodeAtPath(expression, currentPath);
    breadcrumbs.push({
      label: node.raw,
      path: [...currentPath],
      node
    });
  }
  
  return (
    <div style={{ 
      padding: '8px 0',
      fontFamily: 'monospace',
      fontSize: '14px',
      color: '#666'
    }}>
      <strong>Focus Path: </strong>
      {breadcrumbs.map((crumb, index) => (
        <span key={index}>
          <button
            onClick={() => onFocusChange(crumb.path)}
            style={{
              background: 'none',
              border: 'none',
              color: arraysEqual(crumb.path, focusPath) ? '#007acc' : '#666',
              textDecoration: 'underline',
              cursor: 'pointer',
              fontFamily: 'monospace',
              fontSize: '14px'
            }}
          >
            {crumb.label}
          </button>
          {index < breadcrumbs.length - 1 && ' > '}
        </span>
      ))}
    </div>
  );
}