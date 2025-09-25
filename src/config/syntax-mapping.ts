import { ExpressionNode } from '../types/enhanced-focus';

export interface SyntaxRule {
  id: string;
  name: string;
  description: string;

  // Pattern matching
  matches: (node: ExpressionNode) => boolean;

  // LaTeX rendering
  toLatex: (node: ExpressionNode, childRenderer: (child: ExpressionNode, path: number[]) => string, path: number[]) => string;

  // Priority for rule ordering (higher = more specific, checked first)
  priority: number;
}

export const SYNTAX_RULES: SyntaxRule[] = [
  {
    id: 'lambda',
    name: 'Lambda Expression',
    description: 'lambda x expr → λ x, expr',
    priority: 100,
    matches: (node) => {
      return node.type === 'application' &&
             node.children.length >= 3 &&
             node.children[0]?.type === 'variable' &&
             (node.children[0]?.value === 'lambda' || node.children[0]?.value === 'λ');
    },
    toLatex: (node, childRenderer, _path) => {
      if (node.children.length < 3) return node.raw;

      const variable = childRenderer(node.children[1], [1]);
      const expression = childRenderer(node.children[2], [2]);
      return `\\lambda ${variable}, ${expression}`;
    }
  },

  {
    id: 'type_annotation',
    name: 'Type Annotation',
    description: 'x : T → x : T',
    priority: 110,
    matches: (node) => {
      return node.type === 'binop' && node.operator === ':';
    },
    toLatex: (node, childRenderer, _path) => {
      if (node.children.length !== 2) return node.raw;

      const variable = childRenderer(node.children[0], [0]);
      const type = childRenderer(node.children[1], [1]);
      return `${variable} : ${type}`;
    }
  },

  {
    id: 'function_type',
    name: 'Function Type',
    description: 'A → B',
    priority: 100,
    matches: (node) => {
      return node.type === 'binop' && node.operator === '→';
    },
    toLatex: (node, childRenderer, _path) => {
      if (node.children.length !== 2) return node.raw;

      const domain = childRenderer(node.children[0], [0]);
      const codomain = childRenderer(node.children[1], [1]);
      return `${domain} \\to ${codomain}`;
    }
  },

  {
    id: 'integral_interval',
    name: 'Integral with Interval',
    description: '∫ t in a..b, f t → ∫ₐᵇ f(t) dt',
    priority: 110,
    matches: (node) => {
      return node.type === 'application' &&
             node.children.length >= 4 &&
             node.children[0]?.type === 'variable' &&
             node.children[0]?.value === '∫' &&
             node.children[2]?.type === 'application' &&
             node.children[2]?.children[0]?.value === 'in';
    },
    toLatex: (node, childRenderer, _path) => {
      if (node.children.length < 5) return node.raw;

      const variable = childRenderer(node.children[1], [1]);
      // node.children[2] is 'in', node.children[3] should be the interval
      const interval = node.children[3];
      const expression = childRenderer(node.children[4], [4]);

      // Handle interval notation a..b
      if (interval.type === 'binop' && interval.operator === '..') {
        const lower = childRenderer(interval.children[0], [3, 0]);
        const upper = childRenderer(interval.children[1], [3, 1]);
        return `\\int_{${lower}}^{${upper}} ${expression} \\, d${variable}`;
      }

      return `\\int ${expression} \\, d${variable}`;
    }
  },
  {
    id: 'deriv_total',
    name: 'Total Derivative',
    description: 'deriv f x → \\frac{df}{dx}',
    priority: 100,
    matches: (node) => {
      return node.type === 'application' &&
             node.children.length >= 2 &&
             node.children[0]?.type === 'variable' &&
             node.children[0]?.value === 'deriv';
    },
    toLatex: (node, childRenderer, _path) => {
      if (node.children.length < 2) return node.raw;

      // Pattern: deriv f x - function application with args
      if (node.children.length === 3) {
        const f = childRenderer(node.children[1], [1]);
        const x = childRenderer(node.children[2], [2]);

        // If f is a simple variable, use df/dx notation
        if (node.children[1]?.type === 'variable') {
          return `\\frac{d${f}}{d${x}}`;
        }
        // Otherwise use d/dx (expression) notation for complex expressions
        return `\\frac{d}{d${x}}\\left(${f}\\right)`;
      }

      // Fallback for simple case deriv f (derivative of f with respect to implicit variable)
      const f = childRenderer(node.children[1], [1]);
      if (node.children[1]?.type === 'variable') {
        return `\\frac{d${f}}{dx}`;
      }
      return `\\frac{d}{dx}\\left(${f}\\right)`;
    }
  },

  {
    id: 'partial_deriv',
    name: 'Partial Derivative',
    description: 'pderiv f x → \\frac{\\partial f}{\\partial x}',
    priority: 100,
    matches: (node) => {
      return node.type === 'application' &&
             node.children.length >= 2 &&
             node.children[0]?.type === 'variable' &&
             node.children[0]?.value === 'pderiv';
    },
    toLatex: (node, childRenderer, _path) => {
      if (node.children.length < 3) return node.raw;

      const f = childRenderer(node.children[1], [..._path, 1]);
      const x = childRenderer(node.children[2], [..._path, 2]);
      return `\\frac{\\partial ${f}}{\\partial ${x}}`;
    }
  },

  {
    id: 'integral_definite',
    name: 'Definite Integral',
    description: 'integral a b f → \\int_a^b f dx',
    priority: 100,
    matches: (node) => {
      return node.type === 'application' &&
             node.children.length >= 3 &&
             node.children[0]?.type === 'variable' &&
             node.children[0]?.value === 'integral';
    },
    toLatex: (node, childRenderer, _path) => {
      if (node.children.length < 4) return node.raw;

      const lower = childRenderer(node.children[1], [..._path, 1]);
      const upper = childRenderer(node.children[2], [..._path, 2]);
      const integrand = childRenderer(node.children[3], [..._path, 3]);

      return `\\int_{${lower}}^{${upper}} ${integrand} \\, dx`;
    }
  },

  {
    id: 'integral_indefinite',
    name: 'Indefinite Integral',
    description: 'integral f → \\int f dx',
    priority: 90,
    matches: (node) => {
      return node.type === 'application' &&
             node.children.length === 2 &&
             node.children[0]?.type === 'variable' &&
             node.children[0]?.value === 'integral';
    },
    toLatex: (node, childRenderer, _path) => {
      const integrand = childRenderer(node.children[1], [..._path, 1]);
      return `\\int ${integrand} \\, dx`;
    }
  },

  {
    id: 'limit',
    name: 'Limit',
    description: 'limit f x a → \\lim_{x \\to a} f',
    priority: 100,
    matches: (node) => {
      return node.type === 'application' &&
             node.children.length >= 3 &&
             node.children[0]?.type === 'variable' &&
             node.children[0]?.value === 'limit';
    },
    toLatex: (node, childRenderer, _path) => {
      if (node.children.length < 4) return node.raw;

      const func = childRenderer(node.children[1], [..._path, 1]);
      const variable = childRenderer(node.children[2], [..._path, 2]);
      const approach = childRenderer(node.children[3], [..._path, 3]);

      return `\\lim_{${variable} \\to ${approach}} ${func}`;
    }
  },

  {
    id: 'summation',
    name: 'Summation',
    description: 'sum i a b f → \\sum_{i=a}^{b} f',
    priority: 100,
    matches: (node) => {
      return node.type === 'application' &&
             node.children.length >= 4 &&
             node.children[0]?.type === 'variable' &&
             node.children[0]?.value === 'sum';
    },
    toLatex: (node, childRenderer, _path) => {
      if (node.children.length < 5) return node.raw;

      const variable = childRenderer(node.children[1], [..._path, 1]);
      const lower = childRenderer(node.children[2], [..._path, 2]);
      const upper = childRenderer(node.children[3], [..._path, 3]);
      const expression = childRenderer(node.children[4], [..._path, 4]);

      return `\\sum_{${variable}=${lower}}^{${upper}} ${expression}`;
    }
  },

  {
    id: 'sqrt',
    name: 'Square Root',
    description: 'sqrt x → \\sqrt{x}',
    priority: 100,
    matches: (node) => {
      return node.type === 'application' &&
             node.children.length === 2 &&
             node.children[0]?.type === 'variable' &&
             node.children[0]?.value === 'sqrt';
    },
    toLatex: (node, childRenderer, _path) => {
      const arg = childRenderer(node.children[1], [..._path, 1]);
      return `\\sqrt{${arg}}`;
    }
  },

  {
    id: 'log',
    name: 'Logarithm',
    description: 'log x → \\log x, log b x → \\log_b x',
    priority: 100,
    matches: (node) => {
      return node.type === 'application' &&
             node.children.length >= 2 &&
             node.children[0]?.type === 'variable' &&
             node.children[0]?.value === 'log';
    },
    toLatex: (node, childRenderer, _path) => {
      if (node.children.length === 2) {
        // Natural log: log x
        const arg = childRenderer(node.children[1], [..._path, 1]);
        return `\\log ${arg}`;
      } else if (node.children.length === 3) {
        // Log with base: log b x
        const base = childRenderer(node.children[1], [..._path, 1]);
        const arg = childRenderer(node.children[2], [..._path, 2]);
        return `\\log_{${base}} ${arg}`;
      }
      return node.raw;
    }
  },

  {
    id: 'limit_with_slope',
    name: 'Limit (Derivative Definition)',
    description: 'limit (slope function) variable approach → \\lim_{var \\to approach} function',
    priority: 120, // Higher priority for derivative limit definition
    matches: (node) => {
      return node.type === 'application' &&
             node.children.length >= 4 &&
             node.children[0]?.type === 'variable' &&
             node.children[0]?.value === 'limit' &&
             // Check if this looks like a derivative limit (slope with h and difference quotient)
             node.children[1]?.type === 'binop' &&
             node.children[1]?.operator === '/' &&
             node.children[2]?.type === 'variable' &&
             node.children[2]?.value === 'h' &&
             node.children[3]?.type === 'literal' &&
             node.children[3]?.value === 0;
    },
    toLatex: (node, childRenderer, _path) => {
      if (node.children.length < 4) return node.raw;

      const slopeExpr = node.children[1]; // The slope expression [g(x+h)-g(x)]/h
      const variable = childRenderer(node.children[2], [..._path, 2]); // h
      const approach = childRenderer(node.children[3], [..._path, 3]); // 0

      // Render the slope expression (difference quotient)
      const numeratorDenominator = childRenderer(slopeExpr, [..._path, 1]);

      return `\\lim_{${variable} \\to ${approach}} ${numeratorDenominator}`;
    }
  },

  {
    id: 'function_application',
    name: 'Function Application',
    description: 'f x → f(x) for function applications',
    priority: 90,
    matches: (node) => {
      return node.type === 'application' &&
             node.children.length >= 2 &&
             node.children[0]?.type === 'variable' &&
             // Don't match special functions that have their own rules
             !['deriv', 'integral', 'limit', 'sum', 'log', 'sqrt', 'pderiv', '∫'].includes(node.children[0]?.value as string);
    },
    toLatex: (node, childRenderer, _path) => {
      if (node.children.length < 2) return node.raw;

      const func = childRenderer(node.children[0], [..._path, 0]);
      const args = node.children.slice(1).map((arg, index) => {
        const rendered = childRenderer(arg, [..._path, index + 1]);
        // Only add parentheses for nested function applications, not for simple binops
        // Function arguments like (x + h) don't need extra parentheses
        if (arg.type === 'application' && arg.children.length > 1) {
          return `(${rendered})`;
        }
        return rendered;
      });

      if (args.length === 1) {
        return `${func}(${args[0]})`;
      } else {
        return `${func}(${args.join(', ')})`;
      }
    }
  }
];

// Function to find the best matching rule for a node
export function findSyntaxRule(node: ExpressionNode): SyntaxRule | null {
  // Sort by priority (highest first) and find first match
  const sortedRules = [...SYNTAX_RULES].sort((a, b) => b.priority - a.priority);

  for (const rule of sortedRules) {
    if (rule.matches(node)) {
      return rule;
    }
  }

  return null;
}