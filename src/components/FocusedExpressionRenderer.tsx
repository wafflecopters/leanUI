/**
 * FocusedExpressionRenderer - Reusable Term Editor Component
 * 
 * This component provides an interactive editor for expression trees with focus-based navigation.
 * It's designed to be reusable for multiple purposes:
 * 
 * 1. Creating terms from scratch (building new expressions)
 * 2. Iterating on existing terms (editing/transforming expressions)
 * 3. Proof construction (applying rules at focused subexpressions)
 * 
 * Key features:
 * - Focus path tracking for precise subexpression selection
 * - Click-to-focus navigation through the expression tree
 * - Hover highlighting for better UX
 * - Breadcrumb navigation for current focus location
 * 
 * The component is stateless w.r.t. the expression and focus - all state
 * is managed by the parent, making it easy to embed in different contexts.
 */

import { useMemo, useState } from 'react';
import { ExpressionNode, FocusPath, getNodeAtPath } from '../types/enhanced-focus';
import { expressionNodeToTTerm, expressionPathToTTermPath } from '../compiler/bridge';
import { asLambdaByExtractingTermAtIndexPaths, prettyPrint, TContext, TTerm } from '../compiler/surface';
import { inferType, TTKContext } from '../compiler/kernel';

// Helper to convert TContext to Maps for expressionNodeToTTerm
function contextToMaps(context: TContext): { varContext: Map<string, number>; typeContext: Map<string, TTerm> } {
  const varContext = new Map<string, number>();
  const typeContext = new Map<string, TTerm>();

  context.forEach((binding, index) => {
    // De Bruijn indices are 0 = most recent, so we reverse the index
    const debruijnIndex = context.length - 1 - index;
    varContext.set(binding.name, debruijnIndex);
    typeContext.set(binding.name, binding.type);
  });

  return { varContext, typeContext };
}

interface FocusedExpressionRendererProps {
  expression: ExpressionNode;
  focusPath: FocusPath;
  onFocusChange: (newPath: FocusPath) => void;
  isActive?: boolean;
  showFocusAsBetaRedux?: boolean;
  showFocusType?: boolean;
  typeContext?: TContext;
}

export function FocusedExpressionRenderer({
  expression,
  focusPath,
  onFocusChange,
  isActive = false,
  showFocusAsBetaRedux = false,
  showFocusType = false,
  typeContext = []
}: FocusedExpressionRendererProps) {
  const [hoveredPath, setHoveredPath] = useState<FocusPath | null>(null);

  // Compute type of focused term if enabled
  const focusedTypeResult = useMemo(() => {
    if (!showFocusType || focusPath.length === 0) {
      return null;
    }

    try {
      const focusedNode = getNodeAtPath(expression, focusPath);
      if (!focusedNode) {
        return { error: 'Invalid focus path' };
      }

      const { varContext, typeContext: typeCtxMap } = contextToMaps(typeContext);
      const focusedTTerm = expressionNodeToTTerm(focusedNode, varContext, typeCtxMap);
      const typeResult = inferType(focusedTTerm, typeContext);

      if (!typeResult.ok) {
        return { error: typeResult.error };
      }

      return { type: prettyPrint(typeResult.type) };
    } catch (error) {
      return { error: String(error) };
    }
  }, [expression, focusPath, showFocusType, typeContext]);

  // Compute beta-redux representation if enabled
  const betaReduxResult = useMemo(() => {
    if (!showFocusAsBetaRedux || focusPath.length === 0) {
      return null;
    }

    try {
      // Convert ExpressionNode to TTerm
      const ttermExpr = expressionNodeToTTerm(expression);

      // Convert ExpressionNode path to TTerm path
      const ttermPath = expressionPathToTTermPath(expression, focusPath);

      // Extract the term at the focus path
      const result = asLambdaByExtractingTermAtIndexPaths(ttermExpr, [ttermPath]);

      if ('error' in result) {
        return { error: result.error };
      }

      return {
        lambda: prettyPrint(result.lambda),
        extracted: prettyPrint(result.extracted),
        application: `(${prettyPrint(result.lambda)}) ${prettyPrint(result.extracted)}`
      };
    } catch (error) {
      return { error: error instanceof Error ? error.message : 'Unknown error' };
    }
  }, [expression, focusPath, showFocusAsBetaRedux]);

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

      case 'hole':
        // Render as a bright yellow badge containing the expression we're working on
        return (
          <span
            style={{
              ...nodeStyle,
              backgroundColor: arraysEqual(currentPath, focusPath) ? '#ffc107' : '#ffeb3b',
              color: '#000',
              padding: '4px 8px',
              borderRadius: '4px',
              fontWeight: 'bold',
              border: '2px solid #ffc107'
            }}
            onClick={handleClick}
            onMouseEnter={handleMouseEnter}
            onMouseLeave={handleMouseLeave}
          >
            HOLE(
            {node.children.length > 0 && renderNode(node.children[0], [...currentPath, 0])}
            )
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

      {focusPath.length > 0 && focusedNode && (
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

      {/* Type Inference Footer */}
      {focusedTypeResult && (
        <div style={{
          marginTop: '12px',
          padding: '12px',
          backgroundColor: '#f0fff0',
          border: '2px solid #28a745',
          borderRadius: '6px',
          fontSize: '14px',
          fontFamily: 'monospace'
        }}>
          <div style={{
            fontWeight: 'bold',
            color: '#28a745',
            marginBottom: '8px',
            fontSize: '12px',
            textTransform: 'uppercase',
            letterSpacing: '0.5px'
          }}>
            Inferred Type
          </div>

          {'error' in focusedTypeResult ? (
            <div style={{ color: '#d73a49', fontSize: '13px' }}>
              Error: {focusedTypeResult.error}
            </div>
          ) : (
            <div style={{ color: '#155724' }}>
              {focusedTypeResult.type}
            </div>
          )}
        </div>
      )}

      {/* Beta-Redux Footer */}
      {betaReduxResult && (
        <div style={{
          marginTop: '12px',
          padding: '12px',
          backgroundColor: '#f0f8ff',
          border: '2px solid #007acc',
          borderRadius: '6px',
          fontSize: '14px',
          fontFamily: 'monospace'
        }}>
          <div style={{
            fontWeight: 'bold',
            color: '#007acc',
            marginBottom: '8px',
            fontSize: '12px',
            textTransform: 'uppercase',
            letterSpacing: '0.5px'
          }}>
            Focus as β-Redux
          </div>

          {'error' in betaReduxResult ? (
            <div style={{ color: '#d73a49', fontSize: '13px' }}>
              Error: {betaReduxResult.error}
            </div>
          ) : (
            <div style={{ color: '#032f62' }}>
              {betaReduxResult.application}
            </div>
          )}
        </div>
      )}
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
    if (node) {
      breadcrumbs.push({
        label: node.raw,
        path: [...currentPath],
        node
      });
    }
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