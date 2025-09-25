import { useState, useEffect, useRef } from 'react';
import { ExpressionNode, FocusPath } from '../types/enhanced-focus';
import { findSyntaxRule } from '../config/syntax-mapping';

declare global {
  interface Window {
    MathJax: any;
  }
}

interface MathJaxExpressionRendererProps<T> {
  expression: T;
  focusPath?: FocusPath;
  onFocusChange?: (newPath: FocusPath) => void;
  isActive?: boolean;
  readonly?: boolean;
}


// Helper function to check if a node needs parentheses when used as exponent base
function needsParensForExponentBase(node: ExpressionNode): boolean {
  return node.type === 'binop' && (node.operator === '+' || node.operator === '-' || node.operator === '*' || node.operator === '/');
}

// Helper function to check if a node needs parentheses in other contexts
function needsParensForMultiplication(node: ExpressionNode): boolean {
  return node.type === 'binop' && (node.operator === '+' || node.operator === '-');
}

// Convert AST to clean LaTeX with unique IDs and proper parentheses
function astToCleanLaTeX(node: ExpressionNode, path: FocusPath = []): string {
  const pathId = path.join('-') || 'root';

  // Helper function to wrap in parentheses if needed
  const maybeWrap = (childLatex: string, needsParens: boolean): string => {
    return needsParens ? `(${childLatex})` : childLatex;
  };

  // Child renderer function for syntax rules
  const childRenderer = (child: ExpressionNode, childPath: number[]): string => {
    return astToCleanLaTeX(child, [...path, ...childPath]);
  };

  // Check for syntax mapping rules first
  const syntaxRule = findSyntaxRule(node);
  if (syntaxRule) {
    const latex = syntaxRule.toLatex(node, childRenderer, path);
    return `\\cssId{expr-${pathId}}{${latex}}`;
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

        return `\\cssId{expr-${pathId}}{${leftWrapped} ${opSymbol} ${rightWrapped}}`;
      }
      break;

    case 'binop':
      if (node.children.length === 2 && node.operator) {
        const leftChild = node.children[0];
        const rightChild = node.children[1];

        const leftLatex = astToCleanLaTeX(leftChild, [...path, 0]);
        const rightLatex = astToCleanLaTeX(rightChild, [...path, 1]);

        switch (node.operator) {
          case '/':
            // Fractions don't need parentheses since they're visually grouped
            return `\\cssId{expr-${pathId}}{\\frac{${leftLatex}}{${rightLatex}}}`;
          case '^':
            // For exponentiation, wrap base if it's a binop (like y+1)
            const baseWrapped = maybeWrap(leftLatex, needsParensForExponentBase(leftChild));
            return `\\cssId{expr-${pathId}}{{${baseWrapped}}^{${rightLatex}}}`;
          case '*':
            const leftMulWrapped = maybeWrap(leftLatex, needsParensForMultiplication(leftChild));
            const rightMulWrapped = maybeWrap(rightLatex, needsParensForMultiplication(rightChild));
            return `\\cssId{expr-${pathId}}{${leftMulWrapped} \\cdot ${rightMulWrapped}}`;
          case '+':
            return `\\cssId{expr-${pathId}}{${leftLatex} + ${rightLatex}}`;
          case '-':
            const rightSubWrapped = maybeWrap(rightLatex, needsParensForMultiplication(rightChild));
            return `\\cssId{expr-${pathId}}{${leftLatex} - ${rightSubWrapped}}`;
          default:
            return `\\cssId{expr-${pathId}}{${leftLatex} ${node.operator} ${rightLatex}}`;
        }
      }
      break;

    case 'unop':
      if (node.children.length === 1) {
        const childNode = node.children[0];
        const operandLatex = astToCleanLaTeX(childNode, [...path, 0]);
        const operandWrapped = maybeWrap(operandLatex, needsParensForExponentBase(childNode));
        return `\\cssId{expr-${pathId}}{${node.operator}${operandWrapped}}`;
      }
      break;

    case 'literal':
      return `\\cssId{expr-${pathId}}{${String(node.value)}}`;

    case 'variable':
      return `\\cssId{expr-${pathId}}{${String(node.value)}}`;

    case 'application':
      const parts = node.children.map((child, index) => astToCleanLaTeX(child, [...path, index]));
      return `\\cssId{expr-${pathId}}{${parts.join(' ')}}`;
  }

  return `\\cssId{expr-${pathId}}{${node.raw}}`;
}

export function MathJaxExpressionRenderer(props: MathJaxExpressionRendererProps<ExpressionNode>) {
  return <MathJaxExpressionRendererRaw {...props} expression={astToCleanLaTeX(props.expression)} raw={props.expression.raw} />;
}

export function MathJaxExpressionRendererRaw({ expression, focusPath = [], onFocusChange, readonly = true, raw }: MathJaxExpressionRendererProps<string> & { raw?: string }) {
  const containerRef = useRef<HTMLDivElement>(null);
  const [mathJaxReady, setMathJaxReady] = useState(false);

  // Debug: suppress TypeScript warning
  console.debug('MathJax readonly mode:', readonly);

  useEffect(() => {
    const loadMathJax = () => {
      if (!window.MathJax) {
        // Configure MathJax before loading
        window.MathJax = {
          tex: {
            inlineMath: [['$', '$']],
            displayMath: [['$$', '$$']],
          },
          chtml: {
            fontURL: 'https://cdn.jsdelivr.net/npm/mathjax@3/es5/output/chtml/fonts/woff-v2'
          },
          startup: {
            ready: () => {
              window.MathJax.startup.defaultReady();
              // Wait for typesetPromise to be available
              const checkReady = () => {
                if (window.MathJax.typesetPromise) {
                  setMathJaxReady(true);
                } else {
                  setTimeout(checkReady, 50);
                }
              };
              checkReady();
            }
          }
        };

        // Load MathJax from CDN
        const script = document.createElement('script');
        script.src = 'https://cdn.jsdelivr.net/npm/mathjax@3/es5/tex-chtml.js';
        script.async = true;
        document.head.appendChild(script);
      } else {
        setMathJaxReady(true);
      }
    };

    loadMathJax();
  }, []);

  // Render MathJax when ready
  useEffect(() => {
    if (!mathJaxReady || !containerRef.current) return;

    const latex = expression;

    try {
      containerRef.current.innerHTML = `$$${latex}$$`;

      const performTypesetting = () => {
        if (window.MathJax && window.MathJax.typesetPromise) {
          window.MathJax.typesetPromise([containerRef.current]).then(() => {
            // Disable MathJax interactions
            const mathJaxContainer = containerRef.current?.querySelector('.MathJax');

            if (mathJaxContainer) {
              // Disable all pointer events on MathJax
              (mathJaxContainer as HTMLElement).style.pointerEvents = 'none';
              (mathJaxContainer as HTMLElement).style.userSelect = 'none';

              // Prevent all MathJax events
              ['contextmenu', 'click', 'mousedown', 'mouseup'].forEach(eventType => {
                (mathJaxContainer as HTMLElement).addEventListener(eventType, (e) => {
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
          }).catch((err: any) => {
            console.error('MathJax rendering error:', err);
          });
        } else {
          setTimeout(performTypesetting, 100);
        }
      };

      performTypesetting();
    } catch (error) {
      console.error('MathJax rendering error:', error);
      containerRef.current.innerHTML = `<span style="color: red;">LaTeX Error: ${raw ?? expression}</span>`;
    }
  }, [mathJaxReady, expression, readonly]);

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
    if (mathJaxReady && containerRef.current && !readonly) {
      applyFocusHighlighting();
    }
  }, [focusPath, mathJaxReady, readonly]);

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

  if (!mathJaxReady) {
    return (
      <div style={{ textAlign: 'center', color: '#666', fontSize: '18px', }}>
        Loading MathJax...
      </div>
    );
  }

  return (
    <div ref={containerRef} style={{ width: 'max-content', position: 'relative', fontSize: '18px' }} />
  );
}