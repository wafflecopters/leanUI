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
  name: string; // e.g., "hf", "h1"
  expression: string; // e.g., "p ≠ 3"
  description: string; // e.g., "p is not equal to 3"
  introducedBy?: string; // Rule ID that introduced this assumption
}

export interface ProofContext {
  assumptions: Assumption[];
  variables: Map<string, string>; // variable name -> type
}

// Structured proof rendering types
export interface ProofElement {
  id: string;
  type: 'equation' | 'comment' | 'case_split' | 'sublemma' | 'reasoning_block';
  content: string | ExpressionNode;
  timestamp: number;
  depth?: number; // For nested structures
  parentId?: string; // For sublemmas/cases
}

export interface EquationElement extends ProofElement {
  type: 'equation';
  content: ExpressionNode;
  leftSide: ExpressionNode;
  rightSide: ExpressionNode;
  justification?: string; // Rule or reasoning for this step
  ruleId?: string;
}

export interface CommentElement extends ProofElement {
  type: 'comment';
  content: string;
  commentType: 'explanation' | 'assumption' | 'goal' | 'strategy';
}

export interface CaseSplitElement extends ProofElement {
  type: 'case_split';
  content: string;
  cases: ProofElement[];
  variable?: string; // Variable being split on
  conditions?: string[]; // Conditions for each case
}

export interface SublemmaElement extends ProofElement {
  type: 'sublemma';
  content: string;
  statement: ExpressionNode;
  proof: ProofElement[];
}

export interface StructuredProof {
  elements: ProofElement[];
  metadata: {
    theorem?: string;
    assumptions: Assumption[];
    goal: ExpressionNode;
  };
}

// Helper functions for structured proof conversion
export function createEquationElement(
  expression: ExpressionNode,
  justification?: string,
  ruleId?: string
): EquationElement {
  // Extract left and right sides from equality
  let leftSide: ExpressionNode = expression;
  let rightSide: ExpressionNode = expression;

  if (expression.type === 'equality' || (expression.type === 'binop' && expression.operator === '=')) {
    if (expression.children.length >= 2) {
      leftSide = expression.children[0];
      rightSide = expression.children[1];
    }
  }

  return {
    id: crypto.randomUUID(),
    type: 'equation',
    content: expression,
    leftSide,
    rightSide,
    justification,
    ruleId,
    timestamp: Date.now()
  };
}

// Create equation element showing transformation from previous to current expression
export function createTransformationEquationElement(
  previousExpression: ExpressionNode,
  currentExpression: ExpressionNode,
  justification?: string,
  ruleId?: string
): EquationElement {
  return {
    id: crypto.randomUUID(),
    type: 'equation',
    content: currentExpression,
    leftSide: previousExpression,
    rightSide: currentExpression,
    justification,
    ruleId,
    timestamp: Date.now()
  };
}

export function createCommentElement(
  content: string,
  commentType: CommentElement['commentType'] = 'explanation'
): CommentElement {
  return {
    id: crypto.randomUUID(),
    type: 'comment',
    content,
    commentType,
    timestamp: Date.now()
  };
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

  // Bidirectional rules - can work in reverse direction
  bidirectional?: boolean;
  reverseName?: string;
  reverseDescription?: string;

  // Check if reverse rule applies (only needed if bidirectional)
  isApplicableReverse?: (focusedNode: ExpressionNode, rootExpression: ExpressionNode, context: ProofContext) => boolean;

  // Apply reverse rule (only needed if bidirectional)
  applyReverse?: (focusedNode: ExpressionNode, rootExpression: ExpressionNode, params?: any) => {
    newNode: ExpressionNode;
    newAssumptions?: Assumption[];
  };
}

// Helper functions (keeping existing ones)
export function getNodeAtPath(root: ExpressionNode, path: FocusPath): ExpressionNode | null {
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

// Helper function to substitute a variable in an expression
export function substituteVariableInExpression(
  expr: ExpressionNode,
  varName: string,
  replacement: ExpressionNode
): ExpressionNode {
  // If this is the variable we're substituting, return the replacement
  if (expr.type === 'variable' && expr.value === varName) {
    return {
      ...replacement,
      id: crypto.randomUUID()
    };
  }

  // If this node has children, recursively substitute in each child
  if (expr.children && expr.children.length > 0) {
    const newChildren = expr.children.map(child =>
      substituteVariableInExpression(child, varName, replacement)
    );

    return {
      ...expr,
      id: crypto.randomUUID(),
      children: newChildren,
      raw: astToString({
        ...expr,
        children: newChildren
      })
    };
  }

  // No substitution needed, return a copy
  return {
    ...expr,
    id: crypto.randomUUID()
  };
}

// Comprehensive real number rules
export const ENHANCED_FOCUS_RULES: EnhancedFocusRule[] = [
  // Equality rules (work at top level)
  {
    id: 'symmetry',
    name: 'Symmetry',
    description: 'If a = b, then b = a',
    category: 'equality',
    isApplicableToFocus: (node) => node && node.type === 'equality' && node.operator === '=',
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
    isApplicableToFocus: (node) => node && node.type === 'binop' && node.operator === '+',
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
    isApplicableToFocus: (node) => node && node.type === 'binop' && node.operator === '*',
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
      if (!node || !node.children) return false;
      return node.type === 'binop' && node.operator === '+' &&
             node.children[0]?.type === 'binop' && node.children[0].operator === '+';
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
      if (!node || !node.children) return false;
      return node.type === 'binop' && node.operator === '+' &&
             node.children[1]?.type === 'binop' && node.children[1].operator === '+';
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
      if (!node || !node.children) return false;
      return node.type === 'binop' && node.operator === '*' &&
             node.children[1]?.type === 'binop' && node.children[1].operator === '+';
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
      if (!node || !node.children) return false;
      return node.type === 'binop' && node.operator === '*' &&
             node.children[0]?.type === 'binop' && node.children[0].operator === '+';
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

  // Factoring (reverse of distribution)
  {
    id: 'factor_common_mul',
    name: 'Factor Common Multiplier',
    description: 'a * x - a * y = a * (x - y)',
    category: 'algebraic',
    isApplicableToFocus: (node) => {
      if (!node || !node.children || node.children.length !== 2) return false;

      // Check if this is a subtraction: term1 - term2
      if (node.type !== 'binop' || node.operator !== '-') return false;

      const left = node.children[0];  // a * x
      const right = node.children[1]; // a * y

      // Both terms must be multiplications
      if (left.type !== 'binop' || left.operator !== '*' ||
          right.type !== 'binop' || right.operator !== '*') return false;

      // Check if they have the same first factor (a)
      if (!left.children || !right.children ||
          left.children.length !== 2 || right.children.length !== 2) return false;

      const leftFactor = astToString(left.children[0]);
      const rightFactor = astToString(right.children[0]);

      return leftFactor === rightFactor;
    },
    applyToFocus: (node) => {
      const left = node.children[0];   // a * x
      const right = node.children[1];  // a * y

      const commonFactor = left.children[0]; // a
      const leftTerm = left.children[1];     // x
      const rightTerm = right.children[1];   // y

      // Create (x - y)
      const difference: ExpressionNode = {
        id: crypto.randomUUID(),
        type: 'binop',
        operator: '-',
        children: [leftTerm, rightTerm],
        raw: `${astToString(leftTerm)} - ${astToString(rightTerm)}`
      };

      // Create a * (x - y)
      return {
        newNode: {
          id: crypto.randomUUID(),
          type: 'binop',
          operator: '*',
          children: [commonFactor, difference],
          raw: `${astToString(commonFactor)} * (${astToString(difference)})`
        }
      };
    }
  },

  {
    id: 'factor_from_fraction',
    name: 'Factor from Fraction Numerator',
    description: '(a * b) / c = a * (b / c)',
    category: 'algebraic',
    isApplicableToFocus: (node) => {
      if (!node || !node.children || node.children.length !== 2) return false;

      // Check if this is a division: numerator / denominator
      if (node.type !== 'binop' || node.operator !== '/') return false;

      const numerator = node.children[0];   // a * b

      // Numerator must be a multiplication
      if (numerator.type !== 'binop' || numerator.operator !== '*') return false;

      // Must have exactly two factors in the numerator
      return numerator.children && numerator.children.length === 2;
    },
    applyToFocus: (node) => {
      const numerator = node.children[0];   // a * b
      const denominator = node.children[1]; // c

      const factorA = numerator.children[0]; // a
      const factorB = numerator.children[1]; // b

      // Create b / c
      const newFraction: ExpressionNode = {
        id: crypto.randomUUID(),
        type: 'binop',
        operator: '/',
        children: [factorB, denominator],
        raw: `${astToString(factorB)} / ${astToString(denominator)}`
      };

      // Create a * (b / c)
      return {
        newNode: {
          id: crypto.randomUUID(),
          type: 'binop',
          operator: '*',
          children: [factorA, newFraction],
          raw: `${astToString(factorA)} * (${astToString(newFraction)})`
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
    isApplicableToFocus: (node) => node && node.type === 'equality' && node.operator === '=',
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
    isApplicableToFocus: (node) => node && node.type === 'equality' && node.operator === '=',
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
    isApplicableToFocus: (node) => node && node.type === 'equality' && node.operator === '=',
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
    isApplicableToFocus: (node) => node && node.type === 'equality' && node.operator === '=',
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
        name: `h_${value}_neq_zero`,
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
      if (!node || !node.children) return false;
      return node.type === 'binop' && node.operator === '+' &&
             ((node.children[1]?.type === 'literal' && node.children[1].value === 0) ||
              (node.children[0]?.type === 'literal' && node.children[0].value === 0));
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
      if (!node || !node.children) return false;
      return node.type === 'binop' && node.operator === '*' &&
             ((node.children[1]?.type === 'literal' && node.children[1].value === 1) ||
              (node.children[0]?.type === 'literal' && node.children[0].value === 1));
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
      if (!node || !node.children) return false;
      return node.type === 'binop' && node.operator === '*' &&
             (node.children[0]?.type === 'literal' && node.children[0].value === 0) ||
             (node.children[1]?.type === 'literal' && node.children[1].value === 0);
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
  },

  // Derivative limit definition rule (using Lean's hasDerivAt_iff_tendsto_slope)
  {
    id: 'deriv_limit_def',
    name: 'Derivative Limit Definition',
    description: 'dg/dx = lim_{h→0} [g(x+h)-g(x)]/h (using hasDerivAt_iff_tendsto_slope)',
    category: 'algebraic',
    bidirectional: true,
    reverseName: 'Limit to Derivative',
    reverseDescription: 'lim_{h→0} [g(x+h)-g(x)]/h = dg/dx',

    isApplicableToFocus: (node) => {
      // Check if this is a derivative expression: deriv g x
      if (!node || node.type !== 'application' || !node.children || node.children.length < 3) return false;
      return node.children[0]?.type === 'variable' && node.children[0]?.value === 'deriv';
    },

    isApplicableReverse: (node) => {
      // Check if this is a limit expression that looks like derivative definition
      if (!node || node.type !== 'application' || !node.children || node.children.length < 4) return false;

      // Must be a limit
      if (node.children[0]?.type !== 'variable' || node.children[0]?.value !== 'limit') return false;

      // Must be limit with h → 0
      const variable = node.children[2];
      const approach = node.children[3];
      if (variable?.type !== 'variable' || variable.value !== 'h') return false;
      if (approach?.type !== 'literal' || approach.value !== 0) return false;

      // The function should be a fraction: [...] / h
      const func = node.children[1];
      if (func.type !== 'binop' || func.operator !== '/') return false;

      const denominator = func.children[1];
      if (denominator?.type !== 'variable' || denominator.value !== 'h') return false;

      // The numerator should be a difference: g(x+h) - g(x)
      const numerator = func.children[0];
      if (numerator.type !== 'binop' || numerator.operator !== '-') return false;

      return true;
    },
    applyToFocus: (node) => {
      // Extract function g and variable x from deriv g x
      const g = node.children[1]; // The function being differentiated (e.g., c * f x)
      const x = node.children[2]; // The variable w.r.t. differentiation

      // Create the limit expression: lim_{h→0} [g(x+h)-g(x)]/h
      // This corresponds to Lean's hasDerivAt_iff_tendsto_slope theorem

      // For g(x+h), we need to substitute x+h into the expression g
      // If g = "c * f x", then g(x+h) = "c * f (x+h)"
      const h: ExpressionNode = {
        id: crypto.randomUUID(),
        type: 'variable',
        value: 'h',
        children: [],
        raw: 'h'
      };

      const xPlusH: ExpressionNode = {
        id: crypto.randomUUID(),
        type: 'binop',
        operator: '+',
        children: [x, h],
        raw: `${astToString(x)} + h`
      };

      // Substitute x with (x+h) in the function g to get g(x+h)
      const gAtXPlusH = substituteVariableInExpression(g, astToString(x), xPlusH);

      // g(x) is just the original function g
      const gAtX = g;

      // g(x+h) - g(x) - numerator
      const numerator: ExpressionNode = {
        id: crypto.randomUUID(),
        type: 'binop',
        operator: '-',
        children: [gAtXPlusH, gAtX],
        raw: `${astToString(gAtXPlusH)} - ${astToString(gAtX)}`
      };

      // h is already defined above as denominator

      // [g(x+h) - g(x)] / h - the slope
      const slope: ExpressionNode = {
        id: crypto.randomUUID(),
        type: 'binop',
        operator: '/',
        children: [numerator, h],
        raw: `(${astToString(numerator)}) / ${astToString(h)}`
      };

      // 0 - the limit point
      const zero: ExpressionNode = {
        id: crypto.randomUUID(),
        type: 'literal',
        value: 0,
        children: [],
        raw: '0'
      };

      // lim_{h→0} [g(x+h)-g(x)]/h - the complete limit expression
      const limitExpr: ExpressionNode = {
        id: crypto.randomUUID(),
        type: 'application',
        children: [
          { id: crypto.randomUUID(), type: 'variable', value: 'limit', children: [], raw: 'limit' },
          slope,  // the function (slope)
          h,      // the variable (h)
          zero    // the approach point (0)
        ],
        raw: `limit (fun h => (${astToString(numerator)}) / h) h 0`
      };

      const newAssumption: Assumption = {
        id: crypto.randomUUID(),
        name: 'h_deriv_exists',
        expression: `HasDerivAt ${astToString(g)} (deriv ${astToString(g)} ${astToString(x)}) ${astToString(x)}`,
        description: `${astToString(g)} is differentiable at ${astToString(x)} (from hasDerivAt_iff_tendsto_slope)`,
        introducedBy: 'deriv_limit_def'
      };

      return {
        newNode: limitExpr,
        newAssumptions: [newAssumption]
      };
    },

    applyReverse: (node) => {
      // Extract components from limit expression: limit ([g(x+h) - g(x)] / h) h 0
      const func = node.children[1]; // [g(x+h) - g(x)] / h

      const numerator = func.children[0]; // g(x+h) - g(x)
      const rightTerm = numerator.children[1]; // g(x)

      // We need to extract the base function and variable from the difference
      // This is complex because we need to "un-substitute" x+h back to x

      // For now, let's handle the simple case where we can identify the pattern
      // We'll extract the variable from the limit (h) and infer x from the structure

      // Find the main variable (not h) by looking at the right term g(x)
      let mainVariable: ExpressionNode;
      let baseFunction: ExpressionNode;

      // Simple case: if right term is a function application like f(x)
      if (rightTerm.type === 'application' && rightTerm.children.length >= 2) {
        baseFunction = rightTerm.children[0]; // f
        mainVariable = rightTerm.children[1]; // x
      } else {
        // More complex case: extract from the structure
        // For now, assume x as the main variable
        mainVariable = {
          id: crypto.randomUUID(),
          type: 'variable',
          value: 'x',
          children: [],
          raw: 'x'
        };
        baseFunction = rightTerm;
      }

      // Create the derivative expression: deriv baseFunction mainVariable
      const derivativeExpr: ExpressionNode = {
        id: crypto.randomUUID(),
        type: 'application',
        children: [
          { id: crypto.randomUUID(), type: 'variable', value: 'deriv', children: [], raw: 'deriv' },
          baseFunction,
          mainVariable
        ],
        raw: `deriv ${astToString(baseFunction)} ${astToString(mainVariable)}`
      };

      return {
        newNode: derivativeExpr
      };
    }
  },

  // Limit constant factoring rule
  {
    id: 'limit_const_factor',
    name: 'Limit Constant Factoring',
    description: 'lim_{a→b} n*g(a) = n * lim_{a→b} g(a)',
    category: 'algebraic',
    bidirectional: true,
    reverseName: 'Factor into Limit',
    reverseDescription: 'n * lim_{a→b} g(a) = lim_{a→b} n*g(a)',

    isApplicableToFocus: (node) => {
      // Check if this is a limit expression: limit (n * g(a)) a b
      if (!node || node.type !== 'application' || !node.children || node.children.length < 4) return false;

      // Must be a limit
      if (node.children[0]?.type !== 'variable' || node.children[0]?.value !== 'limit') return false;

      const func = node.children[1]; // The function inside the limit (should be n * g(a))

      // The function inside the limit must be a multiplication
      return func.type === 'binop' && func.operator === '*';
    },

    isApplicableReverse: (node) => {
      // Check if this is a multiplication: n * limit(g(a), a, b)
      if (!node || node.type !== 'binop' || node.operator !== '*') return false;
      if (!node.children || node.children.length !== 2) return false;

      const limitExpr = node.children[1]; // lim_{a→b} g(a)

      // Second part must be a limit
      if (limitExpr.type !== 'application' || !limitExpr.children || limitExpr.children.length < 4) return false;
      if (limitExpr.children[0]?.type !== 'variable' || limitExpr.children[0]?.value !== 'limit') return false;

      return true;
    },
    applyToFocus: (node) => {
      const limitFunc = node.children[1]; // n * g(a)
      const variable = node.children[2];  // a
      const approach = node.children[3];  // b

      const constant = limitFunc.children[0]; // n
      const innerFunc = limitFunc.children[1]; // g(a)

      // Create lim_{a→b} g(a)
      const innerLimit: ExpressionNode = {
        id: crypto.randomUUID(),
        type: 'application',
        children: [
          { id: crypto.randomUUID(), type: 'variable', value: 'limit', children: [], raw: 'limit' },
          innerFunc,
          variable,
          approach
        ],
        raw: `limit ${astToString(innerFunc)} ${astToString(variable)} ${astToString(approach)}`
      };

      // Create n * lim_{a→b} g(a)
      return {
        newNode: {
          id: crypto.randomUUID(),
          type: 'binop',
          operator: '*',
          children: [constant, innerLimit],
          raw: `${astToString(constant)} * (${astToString(innerLimit)})`
        }
      };
    },

    applyReverse: (node) => {
      const constant = node.children[0];     // n
      const limitExpr = node.children[1];   // lim_{a→b} g(a)

      const innerFunc = limitExpr.children[1]; // g(a)
      const variable = limitExpr.children[2];  // a
      const approach = limitExpr.children[3];  // b

      // Create n * g(a)
      const newLimitFunc: ExpressionNode = {
        id: crypto.randomUUID(),
        type: 'binop',
        operator: '*',
        children: [constant, innerFunc],
        raw: `${astToString(constant)} * ${astToString(innerFunc)}`
      };

      // Create lim_{a→b} n*g(a)
      return {
        newNode: {
          id: crypto.randomUUID(),
          type: 'application',
          children: [
            { id: crypto.randomUUID(), type: 'variable', value: 'limit', children: [], raw: 'limit' },
            newLimitFunc,
            variable,
            approach
          ],
          raw: `limit (${astToString(newLimitFunc)}) ${astToString(variable)} ${astToString(approach)}`
        }
      };
    }
  }
];