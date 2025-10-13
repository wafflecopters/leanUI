// Let-expression system for proof construction
import { ExpressionNode, Assumption } from './enhanced-focus';

// Type annotations for expressions
export type ExpressionType =
  | 'Real'           // Real numbers
  | 'Nat'            // Natural numbers
  | 'Int'            // Integers
  | 'Bool'           // Boolean (for propositions)
  | 'Set'            // Sets
  | { func: [ExpressionType, ExpressionType] }  // Function type
  | { custom: string };  // Custom type string

// A let-binding in the proof
export interface LetBinding {
  id: string;
  name: string;                    // Variable name (e.g., "x", "eq1")
  type?: ExpressionType;           // Optional type annotation
  value: ExpressionNode;           // The expression bound to this name
  description?: string;            // Human-readable description
  derivedFrom?: string[];          // IDs of let-bindings this depends on
  isHypothesis?: boolean;          // Whether this is a hypothesis (given)
  timestamp: number;
}

// The complete let-context for a proof
export interface LetContext {
  bindings: LetBinding[];          // All let-bindings in order
  hypotheses: Assumption[];        // Current hypotheses (can be added/removed)
  goal?: ExpressionNode;          // Optional goal we're working towards
}

// Operations on let-bindings
export interface LetOperation {
  type: 'add_let' | 'delete_let' | 'add_hypothesis' | 'delete_hypothesis' | 'instantiate';
  targetId?: string;              // For delete/instantiate operations
  binding?: LetBinding;           // For add_let
  hypothesis?: Assumption;        // For add_hypothesis
  instantiation?: {               // For instantiate operation
    letId: string;                // Which let-binding to instantiate
    substitutions: Map<string, ExpressionNode>;  // Variable substitutions
  };
}

// Helper to create a new let-binding
export function createLetBinding(
  name: string,
  value: ExpressionNode,
  type?: ExpressionType,
  description?: string,
  derivedFrom?: string[]
): LetBinding {
  return {
    id: crypto.randomUUID(),
    name,
    type,
    value,
    description,
    derivedFrom,
    timestamp: Date.now()
  };
}

// Helper to create a hypothesis (a special kind of let-binding)
export function createHypothesis(
  name: string,
  expression: ExpressionNode,
  description?: string
): LetBinding {
  return {
    id: crypto.randomUUID(),
    name,
    type: 'Bool',  // Hypotheses are propositions
    value: expression,
    description,
    isHypothesis: true,
    timestamp: Date.now()
  };
}

// Convert an Assumption to a LetBinding hypothesis
export function assumptionToLetBinding(assumption: Assumption): LetBinding {
  // We need to parse the expression string to ExpressionNode
  // This is a placeholder - would need actual implementation
  const expressionNode: ExpressionNode = {
    id: crypto.randomUUID(),
    type: 'variable',
    value: assumption.expression,
    children: [],
    raw: assumption.expression
  };

  return createHypothesis(
    assumption.name,
    expressionNode,
    assumption.description
  );
}

// Check if a let-binding can be instantiated with given substitutions
export function canInstantiate(
  binding: LetBinding,
  substitutions: Map<string, ExpressionNode>
): boolean {
  // Check if all free variables in the binding's value have substitutions
  const freeVars = extractFreeVariables(binding.value);
  for (const varName of freeVars) {
    if (!substitutions.has(varName)) {
      return false;
    }
  }
  return true;
}

// Extract free variables from an expression
export function extractFreeVariables(expr: ExpressionNode): Set<string> {
  const vars = new Set<string>();

  function traverse(node: ExpressionNode) {
    if (node.type === 'variable' && typeof node.value === 'string') {
      vars.add(node.value);
    }
    if (node.children) {
      for (const child of node.children) {
        traverse(child);
      }
    }
  }

  traverse(expr);
  return vars;
}

// Instantiate a let-binding with substitutions
export function instantiateLetBinding(
  binding: LetBinding,
  substitutions: Map<string, ExpressionNode>,
  newName?: string
): LetBinding {
  // Substitute variables in the binding's value
  let newValue = binding.value;
  for (const [varName, replacement] of substitutions) {
    newValue = substituteInExpression(newValue, varName, replacement);
  }

  return createLetBinding(
    newName || `${binding.name}_inst`,
    newValue,
    binding.type,
    `Instantiation of ${binding.name}`,
    [binding.id]
  );
}

// Helper function to substitute variables in an expression
export function substituteInExpression(
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
      substituteInExpression(child, varName, replacement)
    );

    return {
      ...expr,
      id: crypto.randomUUID(),
      children: newChildren
    };
  }

  // No substitution needed, return a copy
  return {
    ...expr,
    id: crypto.randomUUID()
  };
}