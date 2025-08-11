// Enhanced focus system with assumptions and comprehensive real number rules

export interface ExpressionNode {
  id: string;
  type: 'equality' | 'inequality' | 'binop' | 'unop' | 'literal' | 'variable' | 'application';
  value?: string | number;
  operator?: string;
  children: ExpressionNode[];
  raw: string;
  parent?: string;
}

export type FocusPath = number[];

export interface Assumption {
  id: string;
  expression: string; // e.g., "p ≠ 3"
  description: string; // e.g., "p is not equal to 3"
  introducedBy?: string; // Rule ID that introduced this assumption
}

export interface ProofContext {
  assumptions: Assumption[];
  variables: Map<string, string>; // variable name -> type
}

export interface EnhancedFocusRule {
  id: string;
  name: string;
  description: string;
  category: 'equality' | 'arithmetic' | 'algebraic' | 'substitution' | 'introduction';
  
  // Check if rule applies to the focused node
  isApplicableToFocus: (focusedNode: ExpressionNode, rootExpression: ExpressionNode, context: ProofContext) => boolean;
  
  // Apply rule and return new node + any new assumptions
  applyToFocus: (focusedNode: ExpressionNode, rootExpression: ExpressionNode, params?: any) => {
    newNode: ExpressionNode;
    newAssumptions?: Assumption[];
  };
  
  // Parameters this rule needs
  requiresParams?: boolean;
  paramTemplate?: { [key: string]: string }; // param name -> description
}

// Helper functions (keeping existing ones)
export function getNodeAtPath(root: ExpressionNode, path: FocusPath): ExpressionNode {
  let current = root;
  for (const index of path) {
    if (index >= current.children.length) {
      throw new Error(`Invalid path: index ${index} out of bounds`);
    }
    current = current.children[index];
  }
  return current;
}

export function setNodeAtPath(root: ExpressionNode, path: FocusPath, newNode: ExpressionNode): ExpressionNode {
  if (path.length === 0) {
    return newNode;
  }
  
  const newRoot = { ...root, children: [...root.children] };
  let current = newRoot;
  
  for (let i = 0; i < path.length - 1; i++) {
    const index = path[i];
    current.children[index] = { ...current.children[index], children: [...current.children[index].children] };
    current = current.children[index];
  }
  
  const lastIndex = path[path.length - 1];
  current.children[lastIndex] = newNode;
  
  return newRoot;
}

export function parseExpressionToAST(expr: string): ExpressionNode {
  const id = crypto.randomUUID();
  expr = expr.trim();
  
  // Handle equality and inequality
  for (const op of ['=', '≠', '<', '>', '≤', '≥']) {
    const index = expr.lastIndexOf(op);
    if (index > 0) {
      const left = parseExpressionToAST(expr.substring(0, index).trim());
      const right = parseExpressionToAST(expr.substring(index + op.length).trim());
      return {
        id,
        type: op === '=' || op === '≠' ? 'equality' : 'inequality',
        operator: op,
        children: [left, right],
        raw: expr
      };
    }
  }
  
  // Handle binary operations with proper precedence (lowest to highest)
  // Addition and subtraction (lowest precedence)
  for (const op of ['+', '-']) {
    const index = findLastOperatorOutsideParens(expr, op);
    if (index > 0) {
      const left = parseExpressionToAST(expr.substring(0, index).trim());
      const right = parseExpressionToAST(expr.substring(index + 1).trim());
      return {
        id,
        type: 'binop',
        operator: op,
        children: [left, right],
        raw: expr
      };
    }
  }
  
  // Multiplication and division (higher precedence)
  for (const op of ['*', '/']) {
    const index = findLastOperatorOutsideParens(expr, op);
    if (index > 0) {
      const left = parseExpressionToAST(expr.substring(0, index).trim());
      const right = parseExpressionToAST(expr.substring(index + 1).trim());
      return {
        id,
        type: 'binop',
        operator: op,
        children: [left, right],
        raw: expr
      };
    }
  }
  
  // Exponentiation (highest precedence, right-associative)
  for (const op of ['^']) {
    const index = findFirstOperatorOutsideParens(expr, op); // Right-associative
    if (index > 0) {
      const left = parseExpressionToAST(expr.substring(0, index).trim());
      const right = parseExpressionToAST(expr.substring(index + 1).trim());
      return {
        id,
        type: 'binop',
        operator: op,
        children: [left, right],
        raw: expr
      };
    }
  }
  
  // Handle parentheses
  if (expr.startsWith('(') && expr.endsWith(')') && isMatchingParens(expr)) {
    const inner = parseExpressionToAST(expr.substring(1, expr.length - 1));
    return {
      ...inner,
      id,
      raw: expr
    };
  }
  
  // Handle fractions in the form \frac{a}{b}
  const fracMatch = expr.match(/^\\frac\{([^}]+)\}\{([^}]+)\}$/);
  if (fracMatch) {
    const numerator = parseExpressionToAST(fracMatch[1]);
    const denominator = parseExpressionToAST(fracMatch[2]);
    return {
      id,
      type: 'binop',
      operator: '/',
      children: [numerator, denominator],
      raw: expr
    };
  }
  
  // Handle numbers
  if (/^-?\d+(\.\d+)?$/.test(expr)) {
    return {
      id,
      type: 'literal',
      value: parseFloat(expr),
      children: [],
      raw: expr
    };
  }
  
  // Handle variables
  if (/^[a-zA-Z][a-zA-Z0-9_]*$/.test(expr)) {
    return {
      id,
      type: 'variable',
      value: expr,
      children: [],
      raw: expr
    };
  }
  
  // Default case
  return {
    id,
    type: 'literal',
    value: expr,
    children: [],
    raw: expr
  };
}

// Helper function to find operator outside parentheses
function findLastOperatorOutsideParens(expr: string, op: string): number {
  let parenCount = 0;
  for (let i = expr.length - 1; i >= 0; i--) {
    if (expr[i] === ')') parenCount++;
    else if (expr[i] === '(') parenCount--;
    else if (expr[i] === op && parenCount === 0) {
      return i;
    }
  }
  return -1;
}

function findFirstOperatorOutsideParens(expr: string, op: string): number {
  let parenCount = 0;
  for (let i = 0; i < expr.length; i++) {
    if (expr[i] === '(') parenCount++;
    else if (expr[i] === ')') parenCount--;
    else if (expr[i] === op && parenCount === 0) {
      return i;
    }
  }
  return -1;
}

function isMatchingParens(expr: string): boolean {
  let count = 0;
  for (let i = 0; i < expr.length; i++) {
    if (expr[i] === '(') count++;
    else if (expr[i] === ')') count--;
    if (count === 0 && i < expr.length - 1) return false;
  }
  return count === 0;
}

export function astToString(node: ExpressionNode): string {
  switch (node.type) {
    case 'equality':
    case 'inequality':
    case 'binop':
      if (node.children.length === 2) {
        const left = astToString(node.children[0]);
        const right = astToString(node.children[1]);
        return `${left} ${node.operator} ${right}`;
      }
      break;
    case 'unop':
      if (node.children.length === 1) {
        return `${node.operator}${astToString(node.children[0])}`;
      }
      break;
    case 'literal':
    case 'variable':
      return String(node.value);
    case 'application':
      if (node.children.length > 0) {
        const func = astToString(node.children[0]);
        const args = node.children.slice(1).map(astToString).join(' ');
        return `${func} ${args}`;
      }
      break;
  }
  return node.raw;
}

// Comprehensive real number rules
export const ENHANCED_FOCUS_RULES: EnhancedFocusRule[] = [
  // Equality rules (work at top level)
  {
    id: 'symmetry',
    name: 'Symmetry',
    description: 'If a = b, then b = a',
    category: 'equality',
    isApplicableToFocus: (node) => node.type === 'equality' && node.operator === '=',
    applyToFocus: (node) => ({
      newNode: {
        ...node,
        id: crypto.randomUUID(),
        children: [node.children[1], node.children[0]],
        raw: `${astToString(node.children[1])} = ${astToString(node.children[0])}`
      }
    })
  },
  
  {
    id: 'reflexivity',
    name: 'Reflexivity',
    description: 'a = a is always true',
    category: 'equality',
    isApplicableToFocus: () => true, // Can always be applied
    applyToFocus: (node) => ({
      newNode: {
        id: crypto.randomUUID(),
        type: 'equality',
        operator: '=',
        children: [node, node],
        raw: `${astToString(node)} = ${astToString(node)}`
      }
    })
  },

  // Arithmetic commutativity
  {
    id: 'add_comm',
    name: 'Addition Commutativity',
    description: 'a + b = b + a',
    category: 'arithmetic',
    isApplicableToFocus: (node) => node.type === 'binop' && node.operator === '+',
    applyToFocus: (node) => ({
      newNode: {
        ...node,
        id: crypto.randomUUID(),
        children: [node.children[1], node.children[0]],
        raw: `${astToString(node.children[1])} + ${astToString(node.children[0])}`
      }
    })
  },

  {
    id: 'mul_comm',
    name: 'Multiplication Commutativity',
    description: 'a * b = b * a',
    category: 'arithmetic',
    isApplicableToFocus: (node) => node.type === 'binop' && node.operator === '*',
    applyToFocus: (node) => ({
      newNode: {
        ...node,
        id: crypto.randomUUID(),
        children: [node.children[1], node.children[0]],
        raw: `${astToString(node.children[1])} * ${astToString(node.children[0])}`
      }
    })
  },

  // Associativity rules
  {
    id: 'add_assoc_left',
    name: 'Addition Associativity (Left)',
    description: '(a + b) + c = a + (b + c)',
    category: 'arithmetic',
    isApplicableToFocus: (node) => {
      return node.type === 'binop' && node.operator === '+' && 
             node.children[0].type === 'binop' && node.children[0].operator === '+';
    },
    applyToFocus: (node) => {
      const a = node.children[0].children[0];
      const b = node.children[0].children[1];
      const c = node.children[1];
      
      const newRight: ExpressionNode = {
        id: crypto.randomUUID(),
        type: 'binop',
        operator: '+',
        children: [b, c],
        raw: `${astToString(b)} + ${astToString(c)}`
      };
      
      return {
        newNode: {
          ...node,
          id: crypto.randomUUID(),
          children: [a, newRight],
          raw: `${astToString(a)} + (${astToString(newRight)})`
        }
      };
    }
  },

  {
    id: 'add_assoc_right',
    name: 'Addition Associativity (Right)',
    description: 'a + (b + c) = (a + b) + c',
    category: 'arithmetic',
    isApplicableToFocus: (node) => {
      return node.type === 'binop' && node.operator === '+' && 
             node.children[1].type === 'binop' && node.children[1].operator === '+';
    },
    applyToFocus: (node) => {
      const a = node.children[0];
      const b = node.children[1].children[0];
      const c = node.children[1].children[1];
      
      const newLeft: ExpressionNode = {
        id: crypto.randomUUID(),
        type: 'binop',
        operator: '+',
        children: [a, b],
        raw: `${astToString(a)} + ${astToString(b)}`
      };
      
      return {
        newNode: {
          ...node,
          id: crypto.randomUUID(),
          children: [newLeft, c],
          raw: `(${astToString(newLeft)}) + ${astToString(c)}`
        }
      };
    }
  },

  // Distribution
  {
    id: 'distribute_mul_left',
    name: 'Left Distributivity',
    description: 'a * (b + c) = a * b + a * c',
    category: 'algebraic',
    isApplicableToFocus: (node) => {
      return node.type === 'binop' && node.operator === '*' &&
             node.children[1].type === 'binop' && node.children[1].operator === '+';
    },
    applyToFocus: (node) => {
      const a = node.children[0];
      const b = node.children[1].children[0];
      const c = node.children[1].children[1];
      
      const left: ExpressionNode = {
        id: crypto.randomUUID(),
        type: 'binop',
        operator: '*',
        children: [a, b],
        raw: `${astToString(a)} * ${astToString(b)}`
      };
      
      const right: ExpressionNode = {
        id: crypto.randomUUID(),
        type: 'binop',
        operator: '*',
        children: [a, c],
        raw: `${astToString(a)} * ${astToString(c)}`
      };
      
      return {
        newNode: {
          id: crypto.randomUUID(),
          type: 'binop',
          operator: '+',
          children: [left, right],
          raw: `${astToString(left)} + ${astToString(right)}`
        }
      };
    }
  },

  {
    id: 'distribute_mul_right',
    name: 'Right Distributivity',
    description: '(a + b) * c = a * c + b * c',
    category: 'algebraic',
    isApplicableToFocus: (node) => {
      return node.type === 'binop' && node.operator === '*' &&
             node.children[0].type === 'binop' && node.children[0].operator === '+';
    },
    applyToFocus: (node) => {
      const a = node.children[0].children[0];
      const b = node.children[0].children[1];
      const c = node.children[1];
      
      const left: ExpressionNode = {
        id: crypto.randomUUID(),
        type: 'binop',
        operator: '*',
        children: [a, c],
        raw: `${astToString(a)} * ${astToString(c)}`
      };
      
      const right: ExpressionNode = {
        id: crypto.randomUUID(),
        type: 'binop',
        operator: '*',
        children: [b, c],
        raw: `${astToString(b)} * ${astToString(c)}`
      };
      
      return {
        newNode: {
          id: crypto.randomUUID(),
          type: 'binop',
          operator: '+',
          children: [left, right],
          raw: `${astToString(left)} + ${astToString(right)}`
        }
      };
    }
  },

  // Substitution rules with parameters
  {
    id: 'add_both_sides',
    name: 'Add to Both Sides',
    description: 'If a = b, then a + c = b + c',
    category: 'substitution',
    requiresParams: true,
    paramTemplate: { value: 'Value to add' },
    isApplicableToFocus: (node) => node.type === 'equality' && node.operator === '=',
    applyToFocus: (node, _, params) => {
      const { value } = params || {};
      if (!value) throw new Error('Value parameter required');
      
      const newLeft: ExpressionNode = {
        id: crypto.randomUUID(),
        type: 'binop',
        operator: '+',
        children: [node.children[0], parseExpressionToAST(value)],
        raw: `${astToString(node.children[0])} + ${value}`
      };
      
      const newRight: ExpressionNode = {
        id: crypto.randomUUID(),
        type: 'binop',
        operator: '+',
        children: [node.children[1], parseExpressionToAST(value)],
        raw: `${astToString(node.children[1])} + ${value}`
      };
      
      return {
        newNode: {
          ...node,
          id: crypto.randomUUID(),
          children: [newLeft, newRight],
          raw: `${astToString(newLeft)} = ${astToString(newRight)}`
        }
      };
    }
  },

  {
    id: 'subtract_both_sides',
    name: 'Subtract from Both Sides',
    description: 'If a = b, then a - c = b - c',
    category: 'substitution',
    requiresParams: true,
    paramTemplate: { value: 'Value to subtract' },
    isApplicableToFocus: (node) => node.type === 'equality' && node.operator === '=',
    applyToFocus: (node, _, params) => {
      const { value } = params || {};
      if (!value) throw new Error('Value parameter required');
      
      const newLeft: ExpressionNode = {
        id: crypto.randomUUID(),
        type: 'binop',
        operator: '-',
        children: [node.children[0], parseExpressionToAST(value)],
        raw: `${astToString(node.children[0])} - ${value}`
      };
      
      const newRight: ExpressionNode = {
        id: crypto.randomUUID(),
        type: 'binop',
        operator: '-',
        children: [node.children[1], parseExpressionToAST(value)],
        raw: `${astToString(node.children[1])} - ${value}`
      };
      
      return {
        newNode: {
          ...node,
          id: crypto.randomUUID(),
          children: [newLeft, newRight],
          raw: `${astToString(newLeft)} = ${astToString(newRight)}`
        }
      };
    }
  },

  {
    id: 'multiply_both_sides',
    name: 'Multiply Both Sides',
    description: 'If a = b, then a * c = b * c',
    category: 'substitution',
    requiresParams: true,
    paramTemplate: { value: 'Value to multiply by' },
    isApplicableToFocus: (node) => node.type === 'equality' && node.operator === '=',
    applyToFocus: (node, _, params) => {
      const { value } = params || {};
      if (!value) throw new Error('Value parameter required');
      
      const newLeft: ExpressionNode = {
        id: crypto.randomUUID(),
        type: 'binop',
        operator: '*',
        children: [node.children[0], parseExpressionToAST(value)],
        raw: `${astToString(node.children[0])} * ${value}`
      };
      
      const newRight: ExpressionNode = {
        id: crypto.randomUUID(),
        type: 'binop',
        operator: '*',
        children: [node.children[1], parseExpressionToAST(value)],
        raw: `${astToString(node.children[1])} * ${value}`
      };
      
      return {
        newNode: {
          ...node,
          id: crypto.randomUUID(),
          children: [newLeft, newRight],
          raw: `${astToString(newLeft)} = ${astToString(newRight)}`
        }
      };
    }
  },

  // Division with assumptions
  {
    id: 'divide_both_sides',
    name: 'Divide Both Sides',
    description: 'If a = b and c ≠ 0, then a/c = b/c',
    category: 'introduction',
    requiresParams: true,
    paramTemplate: { value: 'Value to divide by' },
    isApplicableToFocus: (node) => node.type === 'equality' && node.operator === '=',
    applyToFocus: (node, _, params) => {
      const { value } = params || {};
      if (!value) throw new Error('Value parameter required');
      
      const newLeft: ExpressionNode = {
        id: crypto.randomUUID(),
        type: 'binop',
        operator: '/',
        children: [node.children[0], parseExpressionToAST(value)],
        raw: `${astToString(node.children[0])} / ${value}`
      };
      
      const newRight: ExpressionNode = {
        id: crypto.randomUUID(),
        type: 'binop',
        operator: '/',
        children: [node.children[1], parseExpressionToAST(value)],
        raw: `${astToString(node.children[1])} / ${value}`
      };
      
      const newAssumption: Assumption = {
        id: crypto.randomUUID(),
        expression: `${value} ≠ 0`,
        description: `${value} is not equal to zero`,
        introducedBy: 'divide_both_sides'
      };
      
      return {
        newNode: {
          ...node,
          id: crypto.randomUUID(),
          children: [newLeft, newRight],
          raw: `${astToString(newLeft)} = ${astToString(newRight)}`
        },
        newAssumptions: [newAssumption]
      };
    }
  },

  // Zero properties
  {
    id: 'add_zero',
    name: 'Addition Identity',
    description: 'a + 0 = a',
    category: 'arithmetic',
    isApplicableToFocus: (node) => {
      return node.type === 'binop' && node.operator === '+' &&
             ((node.children[1].type === 'literal' && node.children[1].value === 0) ||
              (node.children[0].type === 'literal' && node.children[0].value === 0));
    },
    applyToFocus: (node) => {
      const nonZeroChild = node.children[0].type === 'literal' && node.children[0].value === 0 
        ? node.children[1] 
        : node.children[0];
      
      return {
        newNode: {
          ...nonZeroChild,
          id: crypto.randomUUID()
        }
      };
    }
  },

  {
    id: 'mul_one',
    name: 'Multiplication Identity',
    description: 'a * 1 = a',
    category: 'arithmetic',
    isApplicableToFocus: (node) => {
      return node.type === 'binop' && node.operator === '*' &&
             ((node.children[1].type === 'literal' && node.children[1].value === 1) ||
              (node.children[0].type === 'literal' && node.children[0].value === 1));
    },
    applyToFocus: (node) => {
      const nonOneChild = node.children[0].type === 'literal' && node.children[0].value === 1 
        ? node.children[1] 
        : node.children[0];
      
      return {
        newNode: {
          ...nonOneChild,
          id: crypto.randomUUID()
        }
      };
    }
  },

  {
    id: 'mul_zero',
    name: 'Multiplication by Zero',
    description: 'a * 0 = 0',
    category: 'arithmetic',
    isApplicableToFocus: (node) => {
      return node.type === 'binop' && node.operator === '*' &&
             (node.children[0].type === 'literal' && node.children[0].value === 0) ||
             (node.children[1].type === 'literal' && node.children[1].value === 0);
    },
    applyToFocus: () => ({
      newNode: {
        id: crypto.randomUUID(),
        type: 'literal',
        value: 0,
        children: [],
        raw: '0'
      }
    })
  }
];