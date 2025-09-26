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
  displayName?: string;  // Optional display name for UI
  description: string;
  category: 'equality' | 'arithmetic' | 'algebraic' | 'substitution' | 'introduction';

  // Check if rule applies to the focused node
  isApplicableToFocus: (focusedNode: ExpressionNode, rootExpression: ExpressionNode, context: ProofContext) => boolean;

  // Apply rule and return new node + any new assumptions
  applyToFocus: (focusedNode: ExpressionNode, rootExpression: ExpressionNode, params?: any, context?: ProofContext) => {
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
  applyReverse?: (focusedNode: ExpressionNode, rootExpression: ExpressionNode, params?: any, context?: ProofContext) => {
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

  // Handle function application (space-separated tokens)
  const tokens = tokenize(expr);
  if (tokens.length > 1) {
    const children = tokens.map(token => parseExpressionToAST(token));
    return {
      id,
      type: 'application',
      children,
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

// Tokenize expression by splitting on spaces, respecting parentheses
function tokenize(expr: string): string[] {
  const tokens: string[] = [];
  let current = '';
  let parenCount = 0;

  for (let i = 0; i < expr.length; i++) {
    const char = expr[i];

    if (char === '(') {
      parenCount++;
      current += char;
    } else if (char === ')') {
      parenCount--;
      current += char;
    } else if (char === ' ' && parenCount === 0) {
      if (current.trim()) {
        tokens.push(current.trim());
        current = '';
      }
    } else {
      current += char;
    }
  }

  if (current.trim()) {
    tokens.push(current.trim());
  }

  return tokens;
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

// Pattern-based rule creation system for easier rule definition
type PatternElement = string | number | PatternNode;
type PatternNode = [string, ...PatternElement[]]; // [operator, ...operands]

interface PatternRuleConfig {
  id: string;
  name: string;
  description: string;
  category?: 'equality' | 'arithmetic' | 'algebraic' | 'substitution' | 'introduction';
  from: PatternElement;
  to: PatternElement;
  bidirectional?: boolean;
  reverseName?: string;
  reverseDescription?: string;
  // Optional: specify which variables should match (for complex patterns)
  variableConstraints?: { [varName: string]: (node: ExpressionNode) => boolean };
}

// Helper to check if a string is a pattern variable (starts with lowercase letter)
function isPatternVariable(s: any): boolean {
  return typeof s === 'string' && /^[a-z]/.test(s);
}

// Helper to match a pattern against an AST node
function matchPattern(pattern: PatternElement, node: ExpressionNode, bindings: Map<string, ExpressionNode>): boolean {
  // Handle literals (numbers)
  if (typeof pattern === 'number') {
    return node.type === 'literal' && node.value === pattern;
  }

  // Handle pattern variables (single lowercase letters or words)
  if (isPatternVariable(pattern)) {
    const varName = pattern as string;

    // Check if we've already bound this variable
    if (bindings.has(varName)) {
      // Must match the existing binding
      const existing = bindings.get(varName)!;
      return astToString(existing) === astToString(node);
    } else {
      // Bind this variable to the node
      bindings.set(varName, node);
      return true;
    }
  }

  // Handle specific constants/operators (uppercase or special chars)
  if (typeof pattern === 'string') {
    return node.type === 'variable' && node.value === pattern;
  }

  // Handle pattern nodes [operator, ...operands]
  if (Array.isArray(pattern)) {
    const [operator, ...operands] = pattern;

    // Check operator match
    if (node.type === 'binop' && node.operator === operator) {
      if (operands.length !== 2 || !node.children || node.children.length !== 2) {
        return false;
      }

      return matchPattern(operands[0], node.children[0], bindings) &&
             matchPattern(operands[1], node.children[1], bindings);
    }

    // Check for unary operations
    if (node.type === 'unop' && node.operator === operator) {
      if (operands.length !== 1 || !node.children || node.children.length !== 1) {
        return false;
      }
      return matchPattern(operands[0], node.children[0], bindings);
    }

    // Check for function applications (like 'sum')
    if (operator === 'sum' && node.type === 'application') {
      if (node.children && node.children[0]?.type === 'variable' && node.children[0]?.value === 'sum') {
        // For sum, we expect: ['sum', variable, lower, upper, expression]
        if (operands.length !== 4 || node.children.length !== 5) {
          return false;
        }

        return matchPattern(operands[0], node.children[1], bindings) &&
               matchPattern(operands[1], node.children[2], bindings) &&
               matchPattern(operands[2], node.children[3], bindings) &&
               matchPattern(operands[3], node.children[4], bindings);
      }
    }

    return false;
  }

  return false;
}

// Helper to build AST from pattern using bindings
function buildFromPattern(pattern: PatternElement, bindings: Map<string, ExpressionNode>): ExpressionNode {
  // Handle literals
  if (typeof pattern === 'number') {
    return {
      id: crypto.randomUUID(),
      type: 'literal',
      value: pattern,
      children: [],
      raw: String(pattern)
    };
  }

  // Handle pattern variables
  if (isPatternVariable(pattern)) {
    const varName = pattern as string;
    if (bindings.has(varName)) {
      const node = bindings.get(varName)!;
      return { ...node, id: crypto.randomUUID() };
    }
    // If not bound, treat as a variable
    return {
      id: crypto.randomUUID(),
      type: 'variable',
      value: varName,
      children: [],
      raw: varName
    };
  }

  // Handle specific constants
  if (typeof pattern === 'string') {
    return {
      id: crypto.randomUUID(),
      type: 'variable',
      value: pattern,
      children: [],
      raw: pattern
    };
  }

  // Handle pattern nodes
  if (Array.isArray(pattern)) {
    const [operator, ...operands] = pattern;

    // Handle binary operations
    if (['+', '-', '*', '/', '^'].includes(operator)) {
      if (operands.length !== 2) {
        throw new Error(`Binary operator ${operator} requires exactly 2 operands`);
      }

      const left = buildFromPattern(operands[0], bindings);
      const right = buildFromPattern(operands[1], bindings);

      return {
        id: crypto.randomUUID(),
        type: 'binop',
        operator,
        children: [left, right],
        raw: `${astToString(left)} ${operator} ${astToString(right)}`
      };
    }

    // Handle unary operations
    if (operator === '-' && operands.length === 1) {
      const operand = buildFromPattern(operands[0], bindings);
      return {
        id: crypto.randomUUID(),
        type: 'unop',
        operator: '-',
        children: [operand],
        raw: `-${astToString(operand)}`
      };
    }

    // Handle sum
    if (operator === 'sum' && operands.length === 4) {
      const variable = buildFromPattern(operands[0], bindings);
      const lower = buildFromPattern(operands[1], bindings);
      const upper = buildFromPattern(operands[2], bindings);
      const expression = buildFromPattern(operands[3], bindings);

      return {
        id: crypto.randomUUID(),
        type: 'application',
        children: [
          { id: crypto.randomUUID(), type: 'variable', value: 'sum', children: [], raw: 'sum' },
          variable,
          lower,
          upper,
          expression
        ],
        raw: `sum ${astToString(variable)} ${astToString(lower)} ${astToString(upper)} ${astToString(expression)}`
      };
    }
  }

  throw new Error(`Unknown pattern type: ${JSON.stringify(pattern)}`);
}

// Create a rule from pattern configuration
export function createPatternRule(config: PatternRuleConfig): EnhancedFocusRule {
  const rule: EnhancedFocusRule = {
    id: config.id,
    name: config.name,
    displayName: config.name,
    description: config.description,
    category: config.category || 'algebraic',
    bidirectional: config.bidirectional || false,

    isApplicableToFocus: (node) => {
      if (!node) return false;
      const bindings = new Map<string, ExpressionNode>();
      return matchPattern(config.from, node, bindings);
    },

    applyToFocus: (node) => {
      const bindings = new Map<string, ExpressionNode>();

      if (!matchPattern(config.from, node, bindings)) {
        throw new Error('Pattern does not match');
      }

      const newNode = buildFromPattern(config.to, bindings);
      return { newNode };
    }
  };

  // Add reverse rule if bidirectional
  if (config.bidirectional) {
    rule.reverseName = config.reverseName || `Reverse ${config.name}`;
    rule.reverseDescription = config.reverseDescription || `Reverse: ${config.description}`;

    rule.isApplicableReverse = (node) => {
      if (!node) return false;
      const bindings = new Map<string, ExpressionNode>();
      return matchPattern(config.to, node, bindings);
    };

    rule.applyReverse = (node, _rootExpression, params) => {
      const bindings = new Map<string, ExpressionNode>();

      // For reverse, we need to handle cases where 'to' pattern has fewer variables
      // For example: a -> a*1, we need to introduce the '1'
      if (!matchPattern(config.to, node, bindings)) {
        throw new Error('Reverse pattern does not match');
      }

      // If 'from' pattern has variables not in 'to', we need params
      const fromVars = extractPatternVariables(config.from);
      const toVars = extractPatternVariables(config.to);
      const missingVars = fromVars.filter(v => !toVars.includes(v));

      // Add parameter values to bindings
      for (const varName of missingVars) {
        if (params && params[varName]) {
          const paramNode = parseExpressionToAST(params[varName]);
          bindings.set(varName, paramNode);
        }
      }

      const newNode = buildFromPattern(config.from, bindings);
      return { newNode };
    };

    // Check if reverse needs parameters
    const fromVars = extractPatternVariables(config.from);
    const toVars = extractPatternVariables(config.to);
    const missingVars = fromVars.filter(v => !toVars.includes(v));

    if (missingVars.length > 0) {
      rule.requiresParams = true;
      rule.paramTemplate = {};
      for (const varName of missingVars) {
        rule.paramTemplate[varName] = `Enter value for ${varName}`;
      }
    }
  }

  return rule;
}

// Helper to extract all pattern variables from a pattern
function extractPatternVariables(pattern: PatternElement): string[] {
  const vars: string[] = [];

  function extract(p: PatternElement) {
    if (isPatternVariable(p)) {
      const varName = p as string;
      if (!vars.includes(varName)) {
        vars.push(varName);
      }
    } else if (Array.isArray(p)) {
      const [_operator, ...operands] = p;
      operands.forEach(extract);
    }
  }

  extract(pattern);
  return vars;
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
    description: 'a \\cdot b = b \\cdot a',
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
    description: 'a \\cdot (b + c) = a \\cdot b + a \\cdot c',
    category: 'algebraic',
    bidirectional: true,
    reverseName: 'Factor Left',
    reverseDescription: 'a \\cdot b + a \\cdot c = a \\cdot (b + c)',
    isApplicableToFocus: (node) => {
      if (!node || !node.children) return false;
      return node.type === 'binop' && node.operator === '*' &&
        node.children[1]?.type === 'binop' && node.children[1].operator === '+';
    },
    isApplicableReverse: (node) => {
      if (!node || !node.children || node.children.length !== 2) return false;
      if (node.type !== 'binop' || node.operator !== '+') return false;

      const left = node.children[0];
      const right = node.children[1];

      // Both terms must be multiplications
      if (left.type !== 'binop' || left.operator !== '*' ||
        right.type !== 'binop' || right.operator !== '*') return false;

      // Check if they have the same first factor
      if (!left.children || !right.children ||
        left.children.length !== 2 || right.children.length !== 2) return false;

      const leftFactor = astToString(left.children[0]);
      const rightFactor = astToString(right.children[0]);

      return leftFactor === rightFactor;
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
    },
    applyReverse: (node) => {
      const left = node.children[0];
      const right = node.children[1];

      const commonFactor = left.children[0];
      const b = left.children[1];
      const c = right.children[1];

      const sum: ExpressionNode = {
        id: crypto.randomUUID(),
        type: 'binop',
        operator: '+',
        children: [b, c],
        raw: `${astToString(b)} + ${astToString(c)}`
      };

      return {
        newNode: {
          id: crypto.randomUUID(),
          type: 'binop',
          operator: '*',
          children: [commonFactor, sum],
          raw: `${astToString(commonFactor)} * (${astToString(sum)})`
        }
      };
    }
  },

  {
    id: 'distribute_mul_right',
    name: 'Right Distributivity',
    description: '(a + b) \\cdot c = \\, a \\cdot c + b \\cdot c',
    category: 'algebraic',
    bidirectional: true,
    reverseName: 'Factor Right',
    reverseDescription: 'a \\cdot c + b \\cdot c = (a + b) \\cdot c',
    isApplicableToFocus: (node) => {
      if (!node || !node.children) return false;
      return node.type === 'binop' && node.operator === '*' &&
        node.children[0]?.type === 'binop' && node.children[0].operator === '+';
    },
    isApplicableReverse: (node) => {
      if (!node || !node.children || node.children.length !== 2) return false;
      if (node.type !== 'binop' || node.operator !== '+') return false;

      const left = node.children[0];
      const right = node.children[1];

      // Both terms must be multiplications
      if (left.type !== 'binop' || left.operator !== '*' ||
        right.type !== 'binop' || right.operator !== '*') return false;

      // Check if they have the same second factor
      if (!left.children || !right.children ||
        left.children.length !== 2 || right.children.length !== 2) return false;

      const leftFactor = astToString(left.children[1]);
      const rightFactor = astToString(right.children[1]);

      return leftFactor === rightFactor;
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
    },
    applyReverse: (node) => {
      const left = node.children[0];
      const right = node.children[1];

      const a = left.children[0];
      const b = right.children[0];
      const commonFactor = left.children[1];

      const sum: ExpressionNode = {
        id: crypto.randomUUID(),
        type: 'binop',
        operator: '+',
        children: [a, b],
        raw: `${astToString(a)} + ${astToString(b)}`
      };

      return {
        newNode: {
          id: crypto.randomUUID(),
          type: 'binop',
          operator: '*',
          children: [sum, commonFactor],
          raw: `(${astToString(sum)}) * ${astToString(commonFactor)}`
        }
      };
    }
  },

  // Factoring (reverse of distribution)
  {
    id: 'factor_common_mul',
    name: 'Factor Common Multiplier',
    description: 'a \\cdot x - a \\cdot y = a \\cdot (x - y)',
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
    description: '(a \\cdot b) / c = a \\cdot (b / c)',
    category: 'algebraic',
    bidirectional: true,
    reverseName: 'Combine into Fraction',
    reverseDescription: 'a \\cdot (b / c) = (a \\cdot b) / c',
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
    isApplicableReverse: (node) => {
      if (!node || !node.children || node.children.length !== 2) return false;

      // Check if this is a multiplication: a * (b/c)
      if (node.type !== 'binop' || node.operator !== '*') return false;

      const rightChild = node.children[1];

      // Right child must be a division
      if (rightChild.type !== 'binop' || rightChild.operator !== '/') return false;

      return rightChild.children && rightChild.children.length === 2;
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
    },
    applyReverse: (node) => {
      const factorA = node.children[0];     // a
      const fraction = node.children[1];    // b/c

      const factorB = fraction.children[0]; // b
      const denominator = fraction.children[1]; // c

      // Create a * b
      const newNumerator: ExpressionNode = {
        id: crypto.randomUUID(),
        type: 'binop',
        operator: '*',
        children: [factorA, factorB],
        raw: `${astToString(factorA)} * ${astToString(factorB)}`
      };

      // Create (a * b) / c
      return {
        newNode: {
          id: crypto.randomUUID(),
          type: 'binop',
          operator: '/',
          children: [newNumerator, denominator],
          raw: `(${astToString(newNumerator)}) / ${astToString(denominator)}`
        }
      };
    }
  },

  {
    id: 'combine_fractions',
    name: 'Combine Fractions',
    description: '\\frac{a}{c} + \\frac{b}{c} = \\frac{a + b}{c}',
    category: 'algebraic',
    bidirectional: true,
    reverseName: 'Split Fraction',
    reverseDescription: '\\frac{a + b}{c} = \\frac{a}{c} + \\frac{b}{c}',
    isApplicableToFocus: (node) => {
      if (!node || !node.children || node.children.length !== 2) return false;

      // Check if this is an addition: frac1 + frac2
      if (node.type !== 'binop' || node.operator !== '+') return false;

      const left = node.children[0];
      const right = node.children[1];

      // Both terms must be fractions
      if (left.type !== 'binop' || left.operator !== '/' ||
        right.type !== 'binop' || right.operator !== '/') return false;

      // Check if they have the same denominator
      if (!left.children || !right.children ||
        left.children.length !== 2 || right.children.length !== 2) return false;

      const leftDenom = astToString(left.children[1]);
      const rightDenom = astToString(right.children[1]);

      return leftDenom === rightDenom;
    },
    isApplicableReverse: (node) => {
      if (!node || !node.children || node.children.length !== 2) return false;

      // Check if this is a fraction: (a+b)/c
      if (node.type !== 'binop' || node.operator !== '/') return false;

      const numerator = node.children[0];

      // Numerator must be an addition
      if (numerator.type !== 'binop' || numerator.operator !== '+') return false;

      return numerator.children && numerator.children.length === 2;
    },
    applyToFocus: (node) => {
      const left = node.children[0];  // a/c
      const right = node.children[1]; // b/c

      const a = left.children[0];
      const b = right.children[0];
      const c = left.children[1]; // Same as right.children[1]

      // Create a + b
      const newNumerator: ExpressionNode = {
        id: crypto.randomUUID(),
        type: 'binop',
        operator: '+',
        children: [a, b],
        raw: `${astToString(a)} + ${astToString(b)}`
      };

      // Create (a + b) / c
      return {
        newNode: {
          id: crypto.randomUUID(),
          type: 'binop',
          operator: '/',
          children: [newNumerator, c],
          raw: `(${astToString(newNumerator)}) / ${astToString(c)}`
        }
      };
    },
    applyReverse: (node) => {
      const numerator = node.children[0]; // a + b
      const denominator = node.children[1]; // c

      const a = numerator.children[0];
      const b = numerator.children[1];

      // Create a/c
      const leftFraction: ExpressionNode = {
        id: crypto.randomUUID(),
        type: 'binop',
        operator: '/',
        children: [a, { ...denominator, id: crypto.randomUUID() }],
        raw: `${astToString(a)} / ${astToString(denominator)}`
      };

      // Create b/c
      const rightFraction: ExpressionNode = {
        id: crypto.randomUUID(),
        type: 'binop',
        operator: '/',
        children: [b, { ...denominator, id: crypto.randomUUID() }],
        raw: `${astToString(b)} / ${astToString(denominator)}`
      };

      // Create a/c + b/c
      return {
        newNode: {
          id: crypto.randomUUID(),
          type: 'binop',
          operator: '+',
          children: [leftFraction, rightFraction],
          raw: `${astToString(leftFraction)} + ${astToString(rightFraction)}`
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
    description: 'If a = b, then a \\cdot c = b \\cdot c',
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
    description: 'If a = b and c \\neq 0, then a/c = b/c',
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
    bidirectional: true,
    reverseName: 'Add Zero',
    reverseDescription: 'a = a + 0',
    isApplicableToFocus: (node) => {
      if (!node || !node.children) return false;
      return node.type === 'binop' && node.operator === '+' &&
        ((node.children[1]?.type === 'literal' && node.children[1].value === 0) ||
          (node.children[0]?.type === 'literal' && node.children[0].value === 0));
    },
    isApplicableReverse: (node) => {
      // Can apply to any expression to add zero
      return node !== null;
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
    },
    applyReverse: (node) => {
      const zero: ExpressionNode = {
        id: crypto.randomUUID(),
        type: 'literal',
        value: 0,
        children: [],
        raw: '0'
      };

      return {
        newNode: {
          id: crypto.randomUUID(),
          type: 'binop',
          operator: '+',
          children: [node, zero],
          raw: `${astToString(node)} + 0`
        }
      };
    }
  },

  {
    id: 'mul_one',
    name: 'Multiplication Identity',
    description: 'a \\cdot 1 = a',
    category: 'arithmetic',
    bidirectional: true,
    reverseName: 'Multiply by One',
    reverseDescription: 'a = a \\cdot 1',
    isApplicableToFocus: (node) => {
      if (!node || !node.children) return false;
      return node.type === 'binop' && node.operator === '*' &&
        ((node.children[1]?.type === 'literal' && node.children[1].value === 1) ||
          (node.children[0]?.type === 'literal' && node.children[0].value === 1));
    },
    isApplicableReverse: (node) => {
      // Can apply to any expression to multiply by one
      return node !== null;
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
    },
    applyReverse: (node) => {
      const one: ExpressionNode = {
        id: crypto.randomUUID(),
        type: 'literal',
        value: 1,
        children: [],
        raw: '1'
      };

      return {
        newNode: {
          id: crypto.randomUUID(),
          type: 'binop',
          operator: '*',
          children: [node, one],
          raw: `${astToString(node)} * 1`
        }
      };
    }
  },

  {
    id: 'mul_zero',
    name: 'Multiplication by Zero',
    description: 'a \\cdot 0 = 0',
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

  {
    id: 'div_self',
    name: 'Division by Self',
    description: 'x/x = 1 (\\text{where} x \\neq 0)',
    category: 'arithmetic',
    bidirectional: true,
    reverseName: 'Expand One as Fraction',
    reverseDescription: '1 = \\frac{x}{x}\\, \\text{ (specify $x$)}',
    requiresParams: false,  // Forward doesn't need params
    isApplicableToFocus: (node) => {
      if (!node || node.type !== 'binop' || node.operator !== '/') return false;
      if (!node.children || node.children.length !== 2) return false;

      const numerator = astToString(node.children[0]);
      const denominator = astToString(node.children[1]);

      return numerator === denominator;
    },
    isApplicableReverse: (node) => {
      return node?.type === 'literal' && node.value === 1;
    },
    applyToFocus: (node) => {
      const divisor = astToString(node.children[0]);

      const newAssumption: Assumption = {
        id: crypto.randomUUID(),
        name: `h_${divisor}_neq_zero`,
        expression: `${divisor} ≠ 0`,
        description: `${divisor} is not equal to zero`,
        introducedBy: 'div_self'
      };

      return {
        newNode: {
          id: crypto.randomUUID(),
          type: 'literal',
          value: 1,
          children: [],
          raw: '1'
        },
        newAssumptions: [newAssumption]
      };
    },
    applyReverse: (_node, _rootExpression, params) => {
      const { expression } = params || {};
      if (!expression) throw new Error('Expression parameter required (what should x be in x/x?)');

      let xNode: ExpressionNode;
      try {
        xNode = parseExpressionToAST(expression);
      } catch (error) {
        throw new Error(`Invalid expression: ${expression}`);
      }

      const newAssumption: Assumption = {
        id: crypto.randomUUID(),
        name: `h_${expression}_neq_zero`,
        expression: `${expression} ≠ 0`,
        description: `${expression} is not equal to zero`,
        introducedBy: 'div_self_reverse'
      };

      return {
        newNode: {
          id: crypto.randomUUID(),
          type: 'binop',
          operator: '/',
          children: [xNode, { ...xNode, id: crypto.randomUUID() }],
          raw: `${astToString(xNode)} / ${astToString(xNode)}`
        },
        newAssumptions: [newAssumption]
      };
    }
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
    description: 'lim_{a→b} n\\cdotg(a) = n \\cdot lim_{a→b} g(a)',
    category: 'algebraic',
    bidirectional: true,
    reverseName: 'Factor into Limit',
    reverseDescription: 'n \\cdot lim_{a→b} g(a) = lim_{a→b} n\\cdot g(a)',

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
  },

  {
    id: 'subst_from_assumption',
    name: 'Substitute from Assumption',
    description: '\\text{Replace using equality from assumptions}',
    category: 'substitution',
    bidirectional: false,
    isApplicableToFocus: (node, _rootExpression, context) => {
      if (!node) return false;

      const nodeStr = astToString(node);

      return context.assumptions.some(assumption => {
        try {
          const assumptionExpr = parseExpressionToAST(assumption.expression);
          if (assumptionExpr.type !== 'equality' || assumptionExpr.operator !== '=') return false;

          const leftStr = astToString(assumptionExpr.children[0]);
          const rightStr = astToString(assumptionExpr.children[1]);

          return nodeStr === leftStr || nodeStr === rightStr;
        } catch {
          return false;
        }
      });
    },
    applyToFocus: (node, _rootExpression, _params, context?: ProofContext) => {
      if (!context) throw new Error('Context required for substitution');

      const nodeStr = astToString(node);

      // Find the first matching assumption
      for (const assumption of context.assumptions) {
        try {
          const assumptionExpr = parseExpressionToAST(assumption.expression);
          if (assumptionExpr.type !== 'equality' || assumptionExpr.operator !== '=') continue;

          const leftNode = assumptionExpr.children[0];
          const rightNode = assumptionExpr.children[1];
          const leftStr = astToString(leftNode);
          const rightStr = astToString(rightNode);

          if (nodeStr === leftStr) {
            // Replace with right side
            return {
              newNode: {
                ...rightNode,
                id: crypto.randomUUID()
              }
            };
          } else if (nodeStr === rightStr) {
            // Replace with left side
            return {
              newNode: {
                ...leftNode,
                id: crypto.randomUUID()
              }
            };
          }
        } catch {
          continue;
        }
      }

      throw new Error('No matching assumption found');
    }
  },

  {
    id: 'sum_singleton',
    name: 'Singleton Summation',
    description: '\\sum_{i=a}^{a} f(i) = f(a)',
    category: 'algebraic',
    bidirectional: false,
    isApplicableToFocus: (node) => {
      if (!node || node.type !== 'application' || !node.children || node.children.length < 5) return false;

      if (node.children[0]?.type !== 'variable' || node.children[0]?.value !== 'sum') return false;

      const lowerBound = node.children[2];
      const upperBound = node.children[3];

      return astToString(lowerBound) === astToString(upperBound);
    },
    applyToFocus: (node) => {
      const variable = node.children[1];
      const bound = node.children[2];
      const expression = node.children[4];

      const substituted = substituteVariableInExpression(
        expression,
        astToString(variable),
        bound
      );

      return {
        newNode: substituted
      };
    }
  },

  {
    id: 'sum_split',
    name: 'Split Summation',
    description: '\\sum_{i=a}^{b+c} f(i) = \\sum_{i=a}^{b} f(i) + \\sum_{i=b+1}^{b+c} f(i)',
    category: 'algebraic',
    bidirectional: false,
    isApplicableToFocus: (node) => {
      if (!node || node.type !== 'application' || !node.children || node.children.length < 5) return false;

      if (node.children[0]?.type !== 'variable' || node.children[0]?.value !== 'sum') return false;

      const upperBound = node.children[3];
      return upperBound.type === 'binop' && upperBound.operator === '+';
    },
    applyToFocus: (node) => {
      const variable = node.children[1];
      const lowerBound = node.children[2];
      const upperBound = node.children[3];
      const expression = node.children[4];

      const b = upperBound.children[0];

      const bPlusOne: ExpressionNode = {
        id: crypto.randomUUID(),
        type: 'binop',
        operator: '+',
        children: [
          b,
          {
            id: crypto.randomUUID(),
            type: 'literal',
            value: 1,
            children: [],
            raw: '1'
          }
        ],
        raw: `${astToString(b)} + 1`
      };

      const firstSum: ExpressionNode = {
        id: crypto.randomUUID(),
        type: 'application',
        children: [
          { id: crypto.randomUUID(), type: 'variable', value: 'sum', children: [], raw: 'sum' },
          variable,
          lowerBound,
          b,
          expression
        ],
        raw: `sum ${astToString(variable)} ${astToString(lowerBound)} ${astToString(b)} ${astToString(expression)}`
      };

      const secondSum: ExpressionNode = {
        id: crypto.randomUUID(),
        type: 'application',
        children: [
          { id: crypto.randomUUID(), type: 'variable', value: 'sum', children: [], raw: 'sum' },
          variable,
          bPlusOne,
          upperBound,
          expression
        ],
        raw: `sum ${astToString(variable)} ${astToString(bPlusOne)} ${astToString(upperBound)} ${astToString(expression)}`
      };

      return {
        newNode: {
          id: crypto.randomUUID(),
          type: 'binop',
          operator: '+',
          children: [firstSum, secondSum],
          raw: `${astToString(firstSum)} + ${astToString(secondSum)}`
        }
      };
    }
  },

  // Pattern-based rules for identity and algebraic simplifications
  createPatternRule({
    id: 'add_zero_left',
    name: 'Add Zero (Left)',
    description: '0 + a = a',
    from: ['+', 0, 'a'],
    to: 'a',
    bidirectional: true,
    reverseName: 'Introduce Zero (Left)',
    reverseDescription: 'a = 0 + a'
  }),

  createPatternRule({
    id: 'add_zero_right',
    name: 'Add Zero (Right)',
    description: 'a + 0 = a',
    from: ['+', 'a', 0],
    to: 'a',
    bidirectional: true,
    reverseName: 'Introduce Zero (Right)',
    reverseDescription: 'a = a + 0'
  }),

  createPatternRule({
    id: 'mul_one_left',
    name: 'Multiply by One (Left)',
    description: '1 \\cdot a = a',
    from: ['*', 1, 'a'],
    to: 'a',
    bidirectional: true,
    reverseName: 'Introduce One (Left)',
    reverseDescription: 'a = 1 \\cdot a'
  }),

  createPatternRule({
    id: 'mul_one_right',
    name: 'Multiply by One (Right)',
    description: 'a \\cdot 1 = a',
    from: ['*', 'a', 1],
    to: 'a',
    bidirectional: true,
    reverseName: 'Introduce One (Right)',
    reverseDescription: 'a = a \\cdot 1'
  }),

  createPatternRule({
    id: 'exponent_one',
    name: 'Exponent of One',
    description: 'a^1 = a',
    from: ['^', 'a', 1],
    to: 'a',
    bidirectional: true,
    reverseName: 'Introduce Exponent One',
    reverseDescription: 'a = a^1'
  }),

  // Exponent product rule: a^b * a^c = a^(b+c)
  {
    id: 'exponent_product',
    name: 'Exponent Product Rule',
    description: 'a^b \\cdot a^c = a^{b+c}',
    displayName: 'Exponent Product Rule',
    category: 'algebraic',
    bidirectional: true,
    reverseName: 'Split Exponent',
    reverseDescription: 'a^{b+c} = a^b \\cdot a^c',

    isApplicableToFocus: (node) => {
      if (!node || node.type !== 'binop' || node.operator !== '*') return false;
      if (!node.children || node.children.length !== 2) return false;

      const left = node.children[0];
      const right = node.children[1];

      // Both must be exponentiation with the same base
      if (left.type !== 'binop' || left.operator !== '^') return false;
      if (right.type !== 'binop' || right.operator !== '^') return false;
      if (!left.children || !right.children || left.children.length !== 2 || right.children.length !== 2) return false;

      // Check if bases are the same
      const leftBase = astToString(left.children[0]);
      const rightBase = astToString(right.children[0]);

      return leftBase === rightBase;
    },

    applyToFocus: (node) => {
      const left = node.children[0];  // a^b
      const right = node.children[1]; // a^c

      const base = left.children[0];  // a
      const leftExp = left.children[1]; // b
      const rightExp = right.children[1]; // c

      // Create b + c
      const newExponent: ExpressionNode = {
        id: crypto.randomUUID(),
        type: 'binop',
        operator: '+',
        children: [leftExp, rightExp],
        raw: `${astToString(leftExp)} + ${astToString(rightExp)}`
      };

      // Create a^(b+c)
      return {
        newNode: {
          id: crypto.randomUUID(),
          type: 'binop',
          operator: '^',
          children: [base, newExponent],
          raw: `${astToString(base)} ^ (${astToString(newExponent)})`
        }
      };
    },

    isApplicableReverse: (node) => {
      if (!node || node.type !== 'binop' || node.operator !== '^') return false;
      if (!node.children || node.children.length !== 2) return false;

      const exponent = node.children[1];

      // Exponent must be an addition
      return exponent.type === 'binop' && exponent.operator === '+' &&
             exponent.children && exponent.children.length === 2;
    },

    applyReverse: (node) => {
      const base = node.children[0];     // a
      const exponent = node.children[1]; // b+c

      const leftExp = exponent.children[0]; // b
      const rightExp = exponent.children[1]; // c

      // Create a^b
      const leftPower: ExpressionNode = {
        id: crypto.randomUUID(),
        type: 'binop',
        operator: '^',
        children: [{ ...base, id: crypto.randomUUID() }, leftExp],
        raw: `${astToString(base)} ^ ${astToString(leftExp)}`
      };

      // Create a^c
      const rightPower: ExpressionNode = {
        id: crypto.randomUUID(),
        type: 'binop',
        operator: '^',
        children: [{ ...base, id: crypto.randomUUID() }, rightExp],
        raw: `${astToString(base)} ^ ${astToString(rightExp)}`
      };

      // Create a^b * a^c
      return {
        newNode: {
          id: crypto.randomUUID(),
          type: 'binop',
          operator: '*',
          children: [leftPower, rightPower],
          raw: `${astToString(leftPower)} * ${astToString(rightPower)}`
        }
      };
    }
  },

  // Constant simplification rule for arithmetic operations
  {
    id: 'constant_simplification',
    name: 'Simplify Constants',
    description: 'Evaluate arithmetic operations on constants',
    displayName: 'Simplify Constants',
    category: 'algebraic',

    isApplicableToFocus: (node) => {
      if (!node || node.type !== 'binop') return false;
      if (!node.children || node.children.length !== 2) return false;

      // Check if both operands are literals (constants)
      const left = node.children[0];
      const right = node.children[1];

      if (left.type !== 'literal' || right.type !== 'literal') return false;
      if (typeof left.value !== 'number' || typeof right.value !== 'number') return false;

      // Support +, -, *, / for now
      return ['+', '-', '*', '/'].includes(node.operator!);
    },

    applyToFocus: (node) => {
      const left = node.children[0];
      const right = node.children[1];

      const leftVal = left.value as number;
      const rightVal = right.value as number;

      let result: number;

      switch (node.operator) {
        case '+':
          result = leftVal + rightVal;
          break;
        case '-':
          result = leftVal - rightVal;
          break;
        case '*':
          result = leftVal * rightVal;
          break;
        case '/':
          if (rightVal === 0) {
            throw new Error('Division by zero');
          }
          result = leftVal / rightVal;
          break;
        default:
          throw new Error(`Unsupported operation: ${node.operator}`);
      }

      return {
        newNode: {
          id: crypto.randomUUID(),
          type: 'literal',
          value: result,
          children: [],
          raw: String(result)
        }
      };
    }
  }
];