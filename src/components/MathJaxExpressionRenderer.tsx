import { useEffect, useRef, useMemo } from 'react';
import { ExpressionNode, FocusPath } from '../types/enhanced-focus';
import { findSyntaxRule } from '../config/syntax-mapping';
import katex from 'katex';
import 'katex/dist/katex.min.css';
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

interface MathJaxExpressionRendererProps<T> {
  expression: T;
  focusPath?: FocusPath;
  onFocusChange?: (newPath: FocusPath) => void;
  isActive?: boolean;
  readonly?: boolean;
  inline?: boolean;
  showFocusAsBetaRedux?: boolean;
  showFocusType?: boolean;
  typeContext?: TContext;
}


// Helper function to check if a node needs parentheses when used as exponent base
function needsParensForExponentBase(node: ExpressionNode): boolean {
  return node.type === 'binop' && (node.operator === '+' || node.operator === '-' || node.operator === '*' || node.operator === '/');
}

// Helper function to check if a node needs parentheses in other contexts
function needsParensForMultiplication(node: ExpressionNode): boolean {
  return node.type === 'binop' && (node.operator === '+' || node.operator === '-');
}

// Helper function to check if a node is a "big" operator (sum, integral, limit, etc.)
function isBigOperator(node: ExpressionNode): boolean {
  if (node.type !== 'application' || !node.children || node.children.length < 1) return false;
  const firstChild = node.children[0];
  if (firstChild?.type !== 'variable') return false;
  return ['sum', 'integral', 'limit', '∫', 'prod'].includes(firstChild.value as string);
}

// Convert AST to clean LaTeX with unique IDs and proper parentheses
function astToCleanLaTeX(node: ExpressionNode, path: FocusPath = []): string {
  const pathId = path.join('-') || 'root';

  // Helper function to wrap in parentheses if needed
  const maybeWrap = (childLatex: string, needsParens: boolean): string => {
    return needsParens ? `\\left(${childLatex}\\right)` : childLatex;
  };

  // Child renderer function for syntax rules
  const childRenderer = (child: ExpressionNode, childPath: number[]): string => {
    return astToCleanLaTeX(child, [...path, ...childPath]);
  };

  // Check for syntax mapping rules first
  const syntaxRule = findSyntaxRule(node);
  if (syntaxRule) {
    const latex = syntaxRule.toLatex(node, childRenderer, path);
    return `\\htmlId{expr-${pathId}}{${latex}}`;
  }

  switch (node.type) {
    case 'equality':
    case 'inequality':
      if (node.children.length === 2 && node.operator) {
        const leftChild = node.children[0];
        const rightChild = node.children[1];

        const leftLatex = astToCleanLaTeX(leftChild, [...path, 0]);
        const rightLatex = astToCleanLaTeX(rightChild, [...path, 1]);

        const leftWrapped = leftLatex; // Equality operators generally don't need parens
        const rightWrapped = rightLatex;

        const opSymbol = {
          '=': '=',
          '≠': '\\\\neq',
          '<': '<',
          '>': '>',
          '≤': '\\\\leq',
          '≥': '\\\\geq'
        }[node.operator] || node.operator;

        return `\\htmlId{expr-${pathId}}{${leftWrapped} ${opSymbol} ${rightWrapped}}`;
      }
      break;

    case 'binop':
      if (node.children.length === 2 && node.operator) {
        const leftChild = node.children[0];
        const rightChild = node.children[1];

        const leftLatex = astToCleanLaTeX(leftChild, [...path, 0]);
        const rightLatex = astToCleanLaTeX(rightChild, [...path, 1]);

        // Check if we need to wrap left side due to big operator
        const needsBigOpParens = isBigOperator(leftChild) && !isBigOperator(rightChild);

        switch (node.operator) {
          case '/':
            // Fractions don't need parentheses since they're visually grouped
            return `\\htmlId{expr-${pathId}}{\\frac{${leftLatex}}{${rightLatex}}}`;
          case '^':
            // For exponentiation, wrap base if it's a binop (like y+1)
            const baseWrapped = maybeWrap(leftLatex, needsParensForExponentBase(leftChild));
            return `\\htmlId{expr-${pathId}}{{${baseWrapped}}^{${rightLatex}}}`;
          case '*':
            const leftMulWrapped = maybeWrap(leftLatex, needsParensForMultiplication(leftChild) || needsBigOpParens);
            const rightMulWrapped = maybeWrap(rightLatex, needsParensForMultiplication(rightChild));
            return `\\htmlId{expr-${pathId}}{${leftMulWrapped} \\cdot ${rightMulWrapped}}`;
          case '+':
            const leftAddWrapped = maybeWrap(leftLatex, needsBigOpParens);
            return `\\htmlId{expr-${pathId}}{${leftAddWrapped} + ${rightLatex}}`;
          case '-':
            const leftSubWrapped = maybeWrap(leftLatex, needsBigOpParens);
            const rightSubWrapped = maybeWrap(rightLatex, needsParensForMultiplication(rightChild));
            return `\\htmlId{expr-${pathId}}{${leftSubWrapped} - ${rightSubWrapped}}`;
          default:
            return `\\htmlId{expr-${pathId}}{${leftLatex} ${node.operator} ${rightLatex}}`;
        }
      }
      break;

    case 'unop':
      if (node.children.length === 1) {
        const childNode = node.children[0];
        const operandLatex = astToCleanLaTeX(childNode, [...path, 0]);
        const operandWrapped = maybeWrap(operandLatex, needsParensForExponentBase(childNode));
        return `\\htmlId{expr-${pathId}}{${node.operator}${operandWrapped}}`;
      }
      break;

    case 'literal':
      return `\\htmlId{expr-${pathId}}{${String(node.value)}}`;

    case 'variable':
      return `\\htmlId{expr-${pathId}}{${String(node.value)}}`;

    case 'application':
      const parts = node.children.map((child, index) => astToCleanLaTeX(child, [...path, index]));
      return `\\htmlId{expr-${pathId}}{${parts.join(' ')}}`;
  }

  return `\\htmlId{expr-${pathId}}{${node.raw}}`;
}

export function MathJaxExpressionRenderer(props: MathJaxExpressionRendererProps<ExpressionNode>) {
  return <MathJaxExpressionRendererRaw {...props} expression={astToCleanLaTeX(props.expression)} raw={props.expression.raw} exprNode={props.expression} />;
}

export function MathJaxExpressionRendererRaw({ expression, focusPath = [], onFocusChange, readonly = true, inline = false, raw, showFocusAsBetaRedux = false, showFocusType = false, typeContext = [], exprNode }: MathJaxExpressionRendererProps<string> & { raw?: string; exprNode?: ExpressionNode }) {
  const containerRef = useRef<HTMLDivElement>(null);

  // Debug: suppress TypeScript warning
  console.debug('MathJax readonly mode:', readonly);

  // Compute type of focused term if enabled
  const focusedTypeResult = useMemo(() => {
    if (!showFocusType || !exprNode || focusPath.length === 0) {
      return null;
    }

    try {
      // Get the focused node
      const pathIndices = focusPath.map(p => typeof p === 'string' ? parseInt(p, 10) : p);
      let focusedNode: ExpressionNode | undefined = exprNode;
      for (const idx of pathIndices) {
        if (!focusedNode?.children || idx >= focusedNode.children.length) {
          return { error: 'Invalid focus path' };
        }
        focusedNode = focusedNode.children[idx];
      }

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
  }, [exprNode, focusPath, showFocusType, typeContext]);

  // Compute beta-redux representation if enabled
  const betaReduxResult = useMemo(() => {
    if (!showFocusAsBetaRedux || !exprNode || focusPath.length === 0) {
      return null;
    }

    try {
      // Convert ExpressionNode to TTerm
      const ttermExpr = expressionNodeToTTerm(exprNode);

      // Convert ExpressionNode path to TTerm path
      const ttermPath = expressionPathToTTermPath(exprNode, focusPath);

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
  }, [exprNode, focusPath, showFocusAsBetaRedux]);

  // Render KaTeX
  useEffect(() => {
    if (!containerRef.current) return;

    const latex = expression;

    try {
      katex.render(latex, containerRef.current, {
        displayMode: !inline,
        throwOnError: false,
        trust: (context) => ['\\htmlId', '\\class'].includes(context.command),
        strict: false
      });

      // Disable KaTeX interactions
      const katexContainer = containerRef.current?.querySelector('.katex');

      if (katexContainer) {
        // Disable all pointer events on KaTeX
        (katexContainer as HTMLElement).style.pointerEvents = 'none';
        (katexContainer as HTMLElement).style.userSelect = 'none';

        // Prevent all KaTeX events
        ['contextmenu', 'click', 'mousedown', 'mouseup'].forEach(eventType => {
          (katexContainer as HTMLElement).addEventListener(eventType, (e) => {
            e.preventDefault();
            e.stopPropagation();
            e.stopImmediatePropagation();
            return false;
          }, true);
        });
      }

      // Create overlay elements for interaction (only if not readonly)
      if (containerRef.current && !readonly) {
        createHoverOverlays();
        applyFocusHighlighting();
      }
    } catch (error) {
      console.error('KaTeX rendering error:', error);
      if (containerRef.current) {
        containerRef.current.innerHTML = `<span style="color: red;">LaTeX Error: ${raw ?? expression}</span>`;
      }
    }
  }, [expression, readonly, inline, raw]);

  // Apply blue highlighting to the currently focused element
  const applyFocusHighlighting = () => {
    if (!containerRef.current || readonly) return;

    // Remove any existing focus styling
    const allElements = containerRef.current.querySelectorAll('[id^="expr-"]');
    allElements.forEach((element) => {
      (element as HTMLElement).classList.remove('focus-highlighted');
      (element as HTMLElement).style.backgroundColor = '';
      (element as HTMLElement).style.outline = '';
      (element as HTMLElement).style.outlineOffset = '';
      (element as HTMLElement).style.margin = '';
      (element as HTMLElement).style.padding = '';
      (element as HTMLElement).style.borderRadius = '';
    });

    // Apply focus styling to the current focus
    if (focusPath.length > 0) {
      const focusId = `expr-${focusPath.join('-')}`;
      const focusElement = containerRef.current.querySelector(`#${focusId}`);
      if (focusElement) {
        (focusElement as HTMLElement).classList.add('focus-highlighted');
        (focusElement as HTMLElement).style.backgroundColor = 'rgba(0, 122, 204, 0.3)';
        (focusElement as HTMLElement).style.borderRadius = '2px';
        (focusElement as HTMLElement).style.outline = '1px solid transparent';
        (focusElement as HTMLElement).style.outlineOffset = '1px';
      }
    } else {
      // Root focus - highlight the entire expression
      const rootElement = containerRef.current.querySelector('#expr-root');
      if (rootElement) {
        (rootElement as HTMLElement).classList.add('focus-highlighted');
        (rootElement as HTMLElement).style.backgroundColor = 'rgba(0, 122, 204, 0.3)';
        (rootElement as HTMLElement).style.borderRadius = '2px';
        (rootElement as HTMLElement).style.outline = '1px solid transparent';
        (rootElement as HTMLElement).style.outlineOffset = '1px';
      }
    }
  };

  // Re-apply focus highlighting when focusPath changes
  useEffect(() => {
    if (containerRef.current && !readonly) {
      applyFocusHighlighting();
    }
  }, [focusPath, readonly]);

  // Create invisible overlay elements for interaction
  const createHoverOverlays = () => {
    if (!containerRef.current || readonly) return;

    // Remove any existing overlays
    const existingOverlays = containerRef.current.querySelectorAll('.hover-overlay');
    existingOverlays.forEach(overlay => overlay.remove());

    const allElements = containerRef.current.querySelectorAll('[id^="expr-"]');

    allElements.forEach((element) => {
      const id = element.id;
      const pathStr = id.replace('expr-', '');
      const path: FocusPath = pathStr === 'root' ? [] : pathStr.split('-').map(Number);

      // Get element's position and size
      const rect = element.getBoundingClientRect();
      const containerRect = containerRef.current!.getBoundingClientRect();

      // Create an invisible overlay element
      const overlay = document.createElement('div');
      overlay.className = 'hover-overlay';
      overlay.style.position = 'absolute';
      overlay.style.left = `${rect.left - containerRect.left}px`;
      overlay.style.top = `${rect.top - containerRect.top}px`;
      overlay.style.width = `${rect.width}px`;
      overlay.style.height = `${rect.height}px`;
      overlay.style.pointerEvents = 'auto';
      overlay.style.backgroundColor = 'transparent';
      overlay.style.zIndex = '10';
      overlay.style.cursor = 'pointer';

      const handleMouseEnter = () => {
        // Only apply hover effect if this element is not currently focused
        if (!(element as HTMLElement).classList.contains('focus-highlighted')) {
          (element as HTMLElement).style.backgroundColor = 'rgba(255, 193, 7, 0.3)';
          (element as HTMLElement).style.borderRadius = '2px';
          (element as HTMLElement).style.outline = '1px solid transparent';
          (element as HTMLElement).style.outlineOffset = '1px';
        }
        overlay.style.backgroundColor = 'rgba(255, 193, 7, 0.1)';
      };

      const handleMouseLeave = () => {
        // Only remove hover effect if this element is not currently focused
        if (!(element as HTMLElement).classList.contains('focus-highlighted')) {
          (element as HTMLElement).style.backgroundColor = '';
          (element as HTMLElement).style.borderRadius = '';
          (element as HTMLElement).style.outline = '';
          (element as HTMLElement).style.outlineOffset = '';
        }
        overlay.style.backgroundColor = 'transparent';
      };

      const handleClick = () => {
        // Change focus to the clicked element's path
        onFocusChange?.(path);
      };

      overlay.addEventListener('mouseenter', handleMouseEnter);
      overlay.addEventListener('mouseleave', handleMouseLeave);
      overlay.addEventListener('click', handleClick);

      // Add the overlay to the container
      containerRef.current!.appendChild(overlay);
    });
  };

  return (
    <>
      <div ref={containerRef} style={{ width: 'max-content', position: 'relative', fontSize: '18px' }} />

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
    </>
  );
}