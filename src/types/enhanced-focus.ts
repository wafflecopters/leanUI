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
  type: 'equation' | 'comment' | 'case_split' | 'sublemma' | 'reasoning_block' | 'claim' | 'induction' | 'let';
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

export type ProofMethod = 'equality' | 'induction' | 'cases' | 'contradiction';

export interface ClaimElement extends ProofElement {
  type: 'claim';
  statement: ExpressionNode;  // The claim to be proven
  proofMethod?: ProofMethod;  // How we'll prove it
  proof?: ProofElement[];     // The nested proof
  status: 'unproven' | 'proving' | 'proven';
}

export interface InductionProofElement extends ProofElement {
  type: 'induction';
  inductionVariable: string;  // e.g., 'n'
  inductionType: string;      // e.g., 'ℕ' (natural numbers)
  statement: ExpressionNode;  // P(n) - the property to prove
  baseCase?: {
    value: number | string;   // e.g., 0 or 1
    proof: ProofElement[];    // Proof of P(base)
    status: 'unproven' | 'proving' | 'proven';
  };
  inductiveStep?: {
    assumption: ExpressionNode;  // P(n)
    goal: ExpressionNode;        // P(n+1)
    proof: ProofElement[];       // Proof that P(n) → P(n+1)
    status: 'unproven' | 'proving' | 'proven';
  };
}

/**
 * Term editor modes for let-bindings.
 * Each mode determines how the term's value is edited and constructed.
 */
export type TermEditorMode =
  | { tag: 'value' }  // Hand-written term (text input)
  | { tag: 'equality-left'; startExpr: ExpressionNode }   // Equality chain starting from left side of goal
  | { tag: 'equality-right'; startExpr: ExpressionNode }  // Equality chain starting from right side of goal
  | { tag: 'cases'; eliminator: 'nat' | 'bool' };         // Case split (nat_elim or bool_elim)

export interface LetElement extends ProofElement {
  type: 'let';
  name: string;                   // Variable name (auto-generated if not provided: _val0, _val1, etc.)
  value: ExpressionNode;          // The term (can be a complex proof term)
  typeAnnotation?: string;        // Optional type annotation (inferred if omitted)
  derivedFrom?: string[];         // IDs of other let-bindings this depends on

  // Term editor configuration
  editorMode: TermEditorMode;     // How to edit this term
  editorExpanded?: boolean;       // Is the term editor UI currently visible?

  // For equality chaining mode
  equalityChain?: ProofElement[]; // The chain of proof steps (for equality modes)

  // Legacy fields (will be removed as refactor progresses)
  isClaim?: boolean;              // DEPRECATED: Use editorMode instead
  proofMethod?: ProofMethod;      // DEPRECATED
  proofStatus?: 'pending' | 'in-progress' | 'completed';  // DEPRECATED
  goal?: ExpressionNode;          // DEPRECATED
  proofElements?: ProofElement[]; // DEPRECATED: Use equalityChain instead
  localHypotheses?: Assumption[]; // DEPRECATED
}


export interface StructuredProof {
  elements: ProofElement[];
  metadata: {
    theorem?: string;
    assumptions: Assumption[];
    goal: ExpressionNode | null;
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

export function createClaimElement(
  statement: ExpressionNode,
  proofMethod?: ProofMethod
): ClaimElement {
  return {
    id: crypto.randomUUID(),
    type: 'claim',
    content: statement,
    statement,
    proofMethod,
    proof: [],
    status: 'unproven',
    timestamp: Date.now()
  };
}

export function createInductionProofElement(
  statement: ExpressionNode,
  inductionVariable: string,
  inductionType: string = 'ℕ'
): InductionProofElement {
  // Parse the statement to create base case and inductive step
  // For example, if statement is "sum_{i=1}^n i = n*(n+1)/2"
  // Base case: n=1, sum_{i=1}^1 i = 1*(1+1)/2
  // Inductive step: assume P(n), prove P(n+1)

  return {
    id: crypto.randomUUID(),
    type: 'induction',
    content: `Proof by induction on ${inductionVariable}`,
    inductionVariable,
    inductionType,
    statement,
    timestamp: Date.now()
  };
}

/**
 * Create a let-binding element.
 *
 * For new code, use the editorMode-based approach.
 * For legacy code, uses isClaim/proofMethod (deprecated).
 */
export function createLetElement(
  name: string,
  value: ExpressionNode,
  typeAnnotation?: string,
  derivedFrom?: string[],
  isClaim?: boolean,
  proofMethod?: ProofMethod,
  editorMode?: TermEditorMode
): LetElement {
  // Determine editor mode
  const mode: TermEditorMode = editorMode || { tag: 'value' };

  return {
    id: crypto.randomUUID(),
    type: 'let',
    content: value,
    name,
    value,
    typeAnnotation,
    derivedFrom,
    editorMode: mode,
    editorExpanded: false,

    // Legacy fields (for backward compatibility)
    isClaim,
    proofMethod,
    proofStatus: isClaim ? 'pending' : undefined,
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

  // Handle unary negation (before parentheses to catch -x correctly)
  if (expr.startsWith('-') && expr.length > 1) {
    // Check if this is actually subtraction by looking for a preceding operand
    const restExpr = expr.substring(1).trim();
    // If the rest doesn't start with a binary operator, it's unary negation
    if (!restExpr.startsWith('+') && !restExpr.startsWith('-') &&
        !restExpr.startsWith('*') && !restExpr.startsWith('/')) {
      const operand = parseExpressionToAST(restExpr);
      return {
        id,
        type: 'unop',
        operator: '-',
        children: [operand],
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

// Helper to determine if parentheses are needed
function needsParens(parent: ExpressionNode, child: ExpressionNode, isLeft: boolean): boolean {
  if (!parent.operator || !child.operator) return false;
  if (child.type !== 'binop') return false;

  const precedence: { [op: string]: number } = {
    '=': 0,
    '≠': 0,
    '<': 0,
    '>': 0,
    '≤': 0,
    '≥': 0,
    '+': 1,
    '-': 1,
    '*': 2,
    '/': 2,
    '^': 3
  };

  const parentPrec = precedence[parent.operator] ?? 0;
  const childPrec = precedence[child.operator] ?? 0;

  // Need parens if child has lower precedence
  if (childPrec < parentPrec) return true;

  // For division, always wrap the numerator if it's not a simple term
  if (parent.operator === '/' && isLeft && child.type === 'binop') return true;

  // For subtraction and division (non-associative), need parens on right if same precedence
  if (!isLeft && childPrec === parentPrec && (parent.operator === '-' || parent.operator === '/')) return true;

  return false;
}

export function astToString(node: ExpressionNode): string {
  switch (node.type) {
    case 'equality':
    case 'inequality':
    case 'binop':
      if (node.children.length === 2) {
        const leftChild = node.children[0];
        const rightChild = node.children[1];

        let left = astToString(leftChild);
        let right = astToString(rightChild);

        // Add parentheses if needed
        if (needsParens(node, leftChild, true)) {
          left = `(${left})`;
        }
        if (needsParens(node, rightChild, false)) {
          right = `(${right})`;
        }

        return `${left} ${node.operator} ${right}`;
      }
      break;
    case 'unop':
      if (node.children.length === 1) {
        return `(${node.operator}${astToString(node.children[0])})`;
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
export type PatternElement = string | number | PatternNode | PatternSpecial;
export type PatternNode = [string, ...PatternElement[]]; // [operator, ...operands]
export type PatternSpecial =
  | { type: 'literal'; check: (n: ExpressionNode) => boolean }  // Custom check
  | { type: 'compute'; fn: (bindings: Map<string, ExpressionNode>) => ExpressionNode };  // Compute expression

export interface PatternRuleConfig {
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
  // Optional: only apply at certain node types
  nodeType?: 'equality' | 'binop' | 'any';
}

// Helper to check if a string is a pattern variable (starts with lowercase letter)
function isPatternVariable(s: any): boolean {
  return typeof s === 'string' && /^[a-z]/.test(s);
}

// Helper to match a pattern against an AST node
function matchPattern(pattern: PatternElement, node: ExpressionNode, bindings: Map<string, ExpressionNode>): boolean {
  // Handle special patterns
  if (typeof pattern === 'object' && !Array.isArray(pattern)) {
    const special = pattern as PatternSpecial;
    if (special.type === 'literal') {
      // Custom check function
      const matches = special.check(node);
      if (matches) {
        // Store the matched node with a unique key
        const key = `_literal_${bindings.size}`;
        bindings.set(key, node);
      }
      return matches;
    } else if (special.type === 'compute') {
      // Computed patterns always match, they're used for building
      return true;
    }
  }

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

    // Check for unary negation pattern
    if (operator === '-' && operands.length === 1 && node.type === 'unop' && node.operator === '-') {
      if (!node.children || node.children.length !== 1) {
        return false;
      }
      return matchPattern(operands[0], node.children[0], bindings);
    }

    // Special case for equality operator
    if (operator === '=' && node.type === 'equality' && node.operator === '=') {
      if (operands.length !== 2 || !node.children || node.children.length !== 2) {
        return false;
      }
      return matchPattern(operands[0], node.children[0], bindings) &&
        matchPattern(operands[1], node.children[1], bindings);
    }

    // Check operator match for binary operations
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
// Returns null if unbound variables are found
function buildFromPattern(pattern: PatternElement, bindings: Map<string, ExpressionNode>): ExpressionNode | null {
  // Handle special patterns
  if (typeof pattern === 'object' && !Array.isArray(pattern)) {
    const special = pattern as PatternSpecial;
    if (special.type === 'compute') {
      // Compute the expression
      return special.fn(bindings);
    } else if (special.type === 'literal') {
      // For literal check patterns, we need to return the matched node from bindings
      // This is a bit tricky - we need to find which binding matched this pattern
      // For now, return first binding that matches the check
      for (const node of bindings.values()) {
        if (special.check(node)) {
          return { ...node, id: crypto.randomUUID() };
        }
      }
    }
    // If can't resolve special pattern, return null
    return null;
  }

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
    // Unbound variable - return null to indicate we need user input
    return null;
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

    // Handle unary negation
    if (operator === '-' && operands.length === 1) {
      const operand = buildFromPattern(operands[0], bindings);
      if (!operand) return null;

      return {
        id: crypto.randomUUID(),
        type: 'unop',
        operator: '-',
        children: [operand],
        raw: `(${operator}${astToString(operand)})`
      };
    }

    // Handle binary operations
    if (['+', '-', '*', '/', '^'].includes(operator)) {
      if (operands.length !== 2) {
        throw new Error(`Binary operator ${operator} requires exactly 2 operands, got ${operands.length}. Pattern: ${JSON.stringify(pattern)}`);
      }

      const left = buildFromPattern(operands[0], bindings);
      const right = buildFromPattern(operands[1], bindings);
      if (!left || !right) return null;

      return {
        id: crypto.randomUUID(),
        type: 'binop',
        operator,
        children: [left, right],
        raw: `${astToString(left)} ${operator} ${astToString(right)}`
      };
    }

    // Handle equality operator
    if (operator === '=') {
      if (operands.length !== 2) {
        throw new Error('Equality operator requires exactly 2 operands');
      }

      const left = buildFromPattern(operands[0], bindings);
      const right = buildFromPattern(operands[1], bindings);
      if (!left || !right) return null;

      return {
        id: crypto.randomUUID(),
        type: 'equality',
        operator: '=',
        children: [left, right],
        raw: `${astToString(left)} = ${astToString(right)}`
      };
    }

    // Handle unary operations
    if (operator === '-' && operands.length === 1) {
      const operand = buildFromPattern(operands[0], bindings);
      if (!operand) return null;
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
      if (!variable || !lower || !upper || !expression) return null;

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

  return null; // Unknown pattern
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
      // Check node type constraint if specified
      if (config.nodeType === 'equality' && node.type !== 'equality') return false;
      if (config.nodeType === 'binop' && node.type !== 'binop') return false;

      const bindings = new Map<string, ExpressionNode>();
      return matchPattern(config.from, node, bindings);
    },

    applyToFocus: (node, _rootExpression, params) => {
      const bindings = new Map<string, ExpressionNode>();

      if (!matchPattern(config.from, node, bindings)) {
        throw new Error('Pattern does not match');
      }

      // Try to build with current bindings
      let newNode = buildFromPattern(config.to, bindings);

      // If we have unbound variables, check if params were provided
      if (!newNode && params) {
        // Add params to bindings and try again
        for (const [key, value] of Object.entries(params)) {
          if (!bindings.has(key)) {
            bindings.set(key, parseExpressionToAST(String(value)));
          }
        }
        newNode = buildFromPattern(config.to, bindings);
      }

      if (!newNode) {
        // Still have unbound variables - need user input
        const unboundVars = extractUnboundVariables(config.to, bindings);
        throw new Error(`Need values for: ${unboundVars.join(', ')}`);
      }

      return { newNode };
    }
  };

  // Add reverse rule if bidirectional
  if (config.bidirectional) {
    rule.reverseName = config.reverseName || `Reverse ${config.name}`;
    rule.reverseDescription = config.reverseDescription || `Reverse: ${config.description}`;

    rule.isApplicableReverse = (node) => {
      if (!node) return false;
      // Check node type constraint if specified
      if (config.nodeType === 'equality' && node.type !== 'equality') return false;
      if (config.nodeType === 'binop' && node.type !== 'binop') return false;

      const bindings = new Map<string, ExpressionNode>();
      return matchPattern(config.to, node, bindings);
    };

    rule.applyReverse = (node, _rootExpression, params) => {
      const bindings = new Map<string, ExpressionNode>();

      // Match the node against the 'to' pattern to extract bindings
      if (!matchPattern(config.to, node, bindings)) {
        throw new Error('Reverse pattern does not match');
      }

      // Try to build with current bindings first
      let newNode = buildFromPattern(config.from, bindings);

      // If we have unbound variables, try to use params
      if (!newNode && params) {
        // Add params to bindings and try again
        for (const [key, value] of Object.entries(params)) {
          if (!bindings.has(key)) {
            bindings.set(key, parseExpressionToAST(String(value)));
          }
        }
        newNode = buildFromPattern(config.from, bindings);
      }

      if (!newNode) {
        // Still have unbound variables - need user input
        const unboundVars = extractUnboundVariables(config.from, bindings);
        throw new Error(`Need values for: ${unboundVars.join(', ')}`);
      }

      return { newNode };
    };

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

// Helper to extract unbound variables from a pattern
function extractUnboundVariables(pattern: PatternElement, bindings: Map<string, ExpressionNode>): string[] {
  const allVars = extractPatternVariables(pattern);
  return allVars.filter(v => !bindings.has(v));
}

// ============================================================================
// Utility Functions for Let-Binding Creation
// ============================================================================

/**
 * Generate an auto-name for a let-binding.
 * Returns the lowest available _val{i} name that's not already in use.
 *
 * @param existingNames - Array of names already in use
 * @returns A name like "_val0", "_val1", etc.
 */
export function generateLetName(existingNames: string[]): string {
  const nameSet = new Set(existingNames);
  let i = 0;
  while (nameSet.has(`_val${i}`)) {
    i++;
  }
  return `_val${i}`;
}

/**
 * Parse a goal expression to check if it's an equality of the form "A = B".
 * Returns the left and right sides if it is, null otherwise.
 *
 * @param goal - The goal expression to parse
 * @returns { left, right } or null if not an equality
 */
export function parseGoalEquality(goal: string | null): { left: ExpressionNode; right: ExpressionNode } | null {
  if (!goal) return null;

  try {
    const goalExpr = parseExpressionToAST(goal);

    // Check if the goal is an equality
    if (goalExpr.type === 'equality' && goalExpr.children && goalExpr.children.length === 2) {
      return {
        left: goalExpr.children[0],
        right: goalExpr.children[1]
      };
    }

    return null;
  } catch (error) {
    // If parsing fails, not a valid equality
    return null;
  }
}

// Import rules from separate file
import { ENHANCED_FOCUS_RULES } from './pattern-rules';
export { ENHANCED_FOCUS_RULES };
