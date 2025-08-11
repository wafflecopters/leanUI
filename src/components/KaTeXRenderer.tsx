import { useState, useEffect, useRef } from 'react';
import { ExpressionNode, FocusPath } from '../types/enhanced-focus';

// Declare KaTeX as global since we're loading it via CDN
declare global {
  interface Window {
    katex: {
      render: (tex: string, element: HTMLElement, options?: any) => void;
      renderToString: (tex: string, options?: any) => string;
    };
  }
}

interface KaTeXRendererProps {
  expression: ExpressionNode;
  focusPath: FocusPath;
  onFocusChange: (newPath: FocusPath) => void;
  isActive?: boolean;
}

function arraysEqual(a: FocusPath, b: FocusPath): boolean {
  return a.length === b.length && a.every((val, i) => val === b[i]);
}

// Convert AST to clean LaTeX
function astToCleanLaTeX(node: ExpressionNode): string {
  switch (node.type) {
    case 'equality':
    case 'inequality':
      if (node.children.length === 2 && node.operator) {
        const left = astToCleanLaTeX(node.children[0]);
        const right = astToCleanLaTeX(node.children[1]);
        const opSymbol = {
          '=': '=',
          '≠': '\\neq',
          '<': '<',
          '>': '>',
          '≤': '\\leq',
          '≥': '\\geq'
        }[node.operator] || node.operator;
        
        return `${left} ${opSymbol} ${right}`;
      }
      break;
      
    case 'binop':
      if (node.children.length === 2 && node.operator) {
        const left = astToCleanLaTeX(node.children[0]);
        const right = astToCleanLaTeX(node.children[1]);
        
        switch (node.operator) {
          case '/':
            return `\\frac{${left}}{${right}}`;
          case '^':
            return `{${left}}^{${right}}`;
          case '*':
            return `${left} \\cdot ${right}`;
          case '+':
            return `${left} + ${right}`;
          case '-':
            return `${left} - ${right}`;
          default:
            return `${left} ${node.operator} ${right}`;
        }
      }
      break;
      
    case 'unop':
      if (node.children.length === 1) {
        const operand = astToCleanLaTeX(node.children[0]);
        return `${node.operator}${operand}`;
      }
      break;
      
    case 'literal':
      return String(node.value);
      
    case 'variable':
      return String(node.value);
      
    case 'application':
      const parts = node.children.map(child => astToCleanLaTeX(child));
      return parts.join(' ');
  }
  
  return node.raw;
}

// Map KaTeX elements to our AST paths
function mapKaTeXElementsToAST(container: HTMLElement, expression: ExpressionNode): Map<HTMLElement, FocusPath> {
  const elementMap = new Map<HTMLElement, FocusPath>();
  
  // Get all text-containing elements from KaTeX
  const allElements = container.querySelectorAll('*');
  
  // Create a mapping of expression content to paths
  function createContentMap(node: ExpressionNode, path: FocusPath = []): Map<string, FocusPath> {
    const contentMap = new Map();
    
    // Add this node's content
    if (node.type === 'variable' || node.type === 'literal') {
      contentMap.set(String(node.value), path);
    }
    
    // Recursively add children
    node.children.forEach((child, index) => {
      const childMap = createContentMap(child, [...path, index]);
      childMap.forEach((childPath, content) => {
        contentMap.set(content, childPath);
      });
    });
    
    return contentMap;
  }
  
  const contentMap = createContentMap(expression);
  
  // Map KaTeX elements to paths based on their text content
  allElements.forEach(element => {
    const textContent = element.textContent?.trim();
    if (textContent && contentMap.has(textContent)) {
      elementMap.set(element as HTMLElement, contentMap.get(textContent)!);
    }
  });
  
  // Special handling for common math structures
  const fractions = container.querySelectorAll('.frac');
  fractions.forEach((frac) => {
    // Assume first fraction maps to [0, 1] for our example
    elementMap.set(frac as HTMLElement, [0, 1]);
  });
  
  const supElements = container.querySelectorAll('.msupsub');
  supElements.forEach((sup) => {
    // Map superscripts appropriately
    const supContent = sup.textContent?.trim();
    if (supContent === '2') {
      elementMap.set(sup as HTMLElement, [0, 0, 1]);
    }
  });
  
  return elementMap;
}

export function KaTeXRenderer({ expression, focusPath, onFocusChange, isActive = false }: KaTeXRendererProps) {
  const containerRef = useRef<HTMLDivElement>(null);
  const [katexReady, setKatexReady] = useState(false);
  const [elementMap, setElementMap] = useState<Map<HTMLElement, FocusPath>>(new Map());

  // Check if KaTeX is loaded
  useEffect(() => {
    const checkKaTeX = () => {
      if (window.katex) {
        setKatexReady(true);
      } else {
        setTimeout(checkKaTeX, 100);
      }
    };
    checkKaTeX();
  }, []);

  // Render KaTeX and set up element mapping
  useEffect(() => {
    if (!katexReady || !containerRef.current) return;

    const latex = astToCleanLaTeX(expression);
    
    try {
      // Clear previous content and styles
      containerRef.current.innerHTML = '';
      
      // Render with KaTeX
      window.katex.render(latex, containerRef.current, {
        displayMode: true,
        throwOnError: false,
        trust: false,
        strict: false
      });

      // Create element mapping
      const newElementMap = mapKaTeXElementsToAST(containerRef.current, expression);
      setElementMap(newElementMap);

      // Add click handlers to all mapped elements
      newElementMap.forEach((path, element) => {
        element.style.cursor = 'pointer';
        element.style.transition = 'background-color 0.15s ease, border-radius 0.15s ease';
        element.style.padding = '2px 4px';
        element.style.margin = '0 1px';
        element.style.borderRadius = '3px';
        
        const handleClick = (e: Event) => {
          e.stopPropagation();
          onFocusChange(path);
        };
        
        element.addEventListener('click', handleClick);
        
        // Store cleanup function
        (element as any).__clickHandler = handleClick;
      });

      // Add fallback click handler for unmapped areas
      const handleContainerClick = (e: MouseEvent) => {
        const target = e.target as HTMLElement;
        
        // If we clicked on an unmapped element, try to determine focus from position
        if (!newElementMap.has(target)) {
          const rect = containerRef.current!.getBoundingClientRect();
          const relativeX = (e.clientX - rect.left) / rect.width;
          
          if (relativeX < 0.5) {
            onFocusChange([0]); // Left side
          } else {
            onFocusChange([1]); // Right side  
          }
        }
      };

      containerRef.current.addEventListener('click', handleContainerClick);
      
      return () => {
        // Cleanup event listeners
        newElementMap.forEach((_, element) => {
          const handler = (element as any).__clickHandler;
          if (handler) {
            element.removeEventListener('click', handler);
          }
        });
        
        if (containerRef.current) {
          containerRef.current.removeEventListener('click', handleContainerClick);
        }
      };

    } catch (error) {
      console.error('KaTeX rendering error:', error);
      containerRef.current.innerHTML = `<span style="color: red;">LaTeX Error: ${expression.raw}</span>`;
    }
  }, [katexReady, expression, onFocusChange]);

  // Apply focus styling to KaTeX elements
  useEffect(() => {
    if (!containerRef.current) return;

    // Remove all focus styling first
    elementMap.forEach((_, element) => {
      element.style.backgroundColor = '';
      element.style.border = '';
      element.style.boxShadow = '';
    });

    // Apply focus styling to the current focus
    elementMap.forEach((path, element) => {
      if (arraysEqual(path, focusPath)) {
        element.style.backgroundColor = '#007acc';
        element.style.color = 'white';
        element.style.borderRadius = '4px';
        element.style.boxShadow = '0 0 0 2px rgba(0, 122, 204, 0.3)';
      }
    });

    // Add hover effects
    elementMap.forEach((path, element) => {
      const handleMouseEnter = () => {
        if (!arraysEqual(path, focusPath)) {
          element.style.backgroundColor = 'rgba(230, 243, 255, 0.8)';
        }
      };
      
      const handleMouseLeave = () => {
        if (!arraysEqual(path, focusPath)) {
          element.style.backgroundColor = '';
        }
      };

      element.addEventListener('mouseenter', handleMouseEnter);
      element.addEventListener('mouseleave', handleMouseLeave);
      
      // Store for cleanup
      (element as any).__hoverHandlers = { handleMouseEnter, handleMouseLeave };
    });

    return () => {
      // Cleanup hover handlers
      elementMap.forEach((_, element) => {
        const handlers = (element as any).__hoverHandlers;
        if (handlers) {
          element.removeEventListener('mouseenter', handlers.handleMouseEnter);
          element.removeEventListener('mouseleave', handlers.handleMouseLeave);
        }
      });
    };
  }, [focusPath, elementMap]);

  const containerStyle = {
    padding: '20px 24px',
    margin: '8px 0',
    borderRadius: '8px',
    border: '3px solid',
    borderColor: isActive ? '#007acc' : '#e0e0e0',
    backgroundColor: isActive ? '#f8fcff' : '#fafafa',
    minHeight: '80px',
    display: 'flex',
    alignItems: 'center',
    position: 'relative' as const,
    fontSize: '18px'
  };

  const getCurrentNode = (root: ExpressionNode, path: FocusPath): ExpressionNode | null => {
    try {
      let current = root;
      for (const index of path) {
        if (index >= current.children.length) return null;
        current = current.children[index];
      }
      return current;
    } catch {
      return null;
    }
  };

  const focusedNode = getCurrentNode(expression, focusPath);

  if (!katexReady) {
    return (
      <div style={containerStyle}>
        <div style={{ flex: 1, textAlign: 'center', color: '#666' }}>
          Loading KaTeX...
        </div>
      </div>
    );
  }

  return (
    <div style={containerStyle}>
      <div style={{ flex: 1, textAlign: 'center', position: 'relative' }}>
        <div ref={containerRef} />
        
        {/* Add custom CSS for focus styling */}
        <style>{`
          .katex .focus-highlight {
            background-color: #007acc !important;
            color: white !important;
            border-radius: 4px !important;
            padding: 2px 4px !important;
            box-shadow: 0 0 0 2px rgba(0, 122, 204, 0.3) !important;
          }
          
          .katex .hover-highlight {
            background-color: rgba(230, 243, 255, 0.8) !important;
            border-radius: 3px !important;
          }
        `}</style>
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