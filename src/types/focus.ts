// Enhanced expression types with proper AST structure for focus navigation

export interface ExpressionNode {
  id: string;
  type: 'equality' | 'inequality' | 'binop' | 'unop' | 'literal' | 'variable' | 'application';
  value?: string | number;
  operator?: string;
  children: ExpressionNode[];
  raw: string;
  parent?: string; // ID of parent node
}

export type FocusPath = number[]; // Path through the tree (indices of children)

export interface FocusContext {
  focusPath: FocusPath;
  focusedNode: ExpressionNode;
  rootExpression: ExpressionNode;
}

// Enhanced expression type that includes the tree structure
export interface FocusableExpression {
  id: string;
  root: ExpressionNode;
  focusPath: FocusPath;
  raw: string;
}

// Rules that can be applied based on the focused node
export interface FocusRule {
  id: string;
  name: string;
  description: string;
  // Check if rule applies to the focused node specifically
  isApplicableToFocus: (focusedNode: ExpressionNode, rootExpression: ExpressionNode) => boolean;
  // Apply rule to the focused node and return new root expression
  applyToFocus: (focusedNode: ExpressionNode, rootExpression: ExpressionNode, params?: any) => ExpressionNode;
}

// Helper functions for focus navigation
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

export function getAllSubexpressionPaths(root: ExpressionNode): Array<{ path: FocusPath; node: ExpressionNode }> {
  const result: Array<{ path: FocusPath; node: ExpressionNode }> = [];
  
  function traverse(node: ExpressionNode, path: FocusPath) {
    result.push({ path: [...path], node });
    
    node.children.forEach((child, index) => {
      traverse(child, [...path, index]);
    });
  }
  
  traverse(root, []);
  return result;
}

// Parse a string expression into a proper AST
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
  
  // Handle binary operations (right-associative parsing)
  for (const op of ['+', '-']) {
    const index = expr.lastIndexOf(op);
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
  
  for (const op of ['*', '/']) {
    const index = expr.lastIndexOf(op);
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
  if (expr.startsWith('(') && expr.endsWith(')')) {
    return parseExpressionToAST(expr.substring(1, expr.length - 1));
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

// Convert AST back to string
export function astToString(node: ExpressionNode): string {
  switch (node.type) {
    case 'equality':
    case 'inequality':
    case 'binop':
      if (node.children.length === 2) {
        const left = astToString(node.children[0]);
        const right = astToString(node.children[1]);
        const needsParens = shouldAddParens(node, node.children[0]) || shouldAddParens(node, node.children[1]);
        return needsParens ? `(${left} ${node.operator} ${right})` : `${left} ${node.operator} ${right}`;
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

function shouldAddParens(parent: ExpressionNode, child: ExpressionNode): boolean {
  // Add parentheses based on operator precedence
  const precedence = {
    '=': 1, '≠': 1, '<': 1, '>': 1, '≤': 1, '≥': 1,
    '+': 2, '-': 2,
    '*': 3, '/': 3
  };
  
  if (!parent.operator || !child.operator) return false;
  
  const parentPrec = precedence[parent.operator as keyof typeof precedence] || 0;
  const childPrec = precedence[child.operator as keyof typeof precedence] || 0;
  
  return childPrec < parentPrec;
}

// Focus-specific rules
export const FOCUS_RULES: FocusRule[] = [
  {
    id: 'add_comm',
    name: 'Addition Commutativity',
    description: 'Change a + b to b + a',
    isApplicableToFocus: (node) => node.type === 'binop' && node.operator === '+',
    applyToFocus: (node) => ({
      ...node,
      id: crypto.randomUUID(),
      children: [node.children[1], node.children[0]],
      raw: `${astToString(node.children[1])} + ${astToString(node.children[0])}`
    })
  },
  {
    id: 'mul_comm',
    name: 'Multiplication Commutativity', 
    description: 'Change a * b to b * a',
    isApplicableToFocus: (node) => node.type === 'binop' && node.operator === '*',
    applyToFocus: (node) => ({
      ...node,
      id: crypto.randomUUID(),
      children: [node.children[1], node.children[0]],
      raw: `${astToString(node.children[1])} * ${astToString(node.children[0])}`
    })
  },
  {
    id: 'add_assoc_left',
    name: 'Addition Associativity (Left)',
    description: 'Change (a + b) + c to a + (b + c)',
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
        ...node,
        id: crypto.randomUUID(),
        children: [a, newRight],
        raw: `${astToString(a)} + (${astToString(newRight)})`
      };
    }
  },
  {
    id: 'distribute_mul',
    name: 'Distribute Multiplication',
    description: 'Change a * (b + c) to a * b + a * c',
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
        id: crypto.randomUUID(),
        type: 'binop',
        operator: '+',
        children: [left, right],
        raw: `${astToString(left)} + ${astToString(right)}`
      };
    }
  }
];