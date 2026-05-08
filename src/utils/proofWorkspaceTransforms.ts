import {
  type Assumption,
  astToString,
  createTransformationEquationElement,
  type EquationElement,
  type ExpressionNode,
  type FocusPath,
  type ProofContext,
  setNodeAtPath,
} from '../types/enhanced-focus';
import type { LetElement } from '../types/enhanced-focus';

export interface FocusedExpressionRule {
  id?: string;
  displayName: string;
  applyRule: (
    node: ExpressionNode,
    expression: ExpressionNode,
    params?: unknown,
    ctx?: ProofContext
  ) => {
    newNode: ExpressionNode;
    newAssumptions?: Assumption[];
  };
}

export interface FocusedTransformationResult {
  newExpression: ExpressionNode;
  equationElement: EquationElement;
  newAssumptions?: Assumption[];
  description: string;
}

export function applyFocusedExpressionRule(
  rule: FocusedExpressionRule,
  focusedNode: ExpressionNode,
  currentExpression: ExpressionNode,
  focusPath: FocusPath,
  metadata: ProofContext,
  params?: unknown
): FocusedTransformationResult {
  const result = rule.applyRule(focusedNode, currentExpression, params, metadata);
  const transformedExpression = setNodeAtPath(currentExpression, focusPath, result.newNode);
  const newExpression = {
    ...transformedExpression,
    raw: astToString(transformedExpression),
  };

  return {
    newExpression,
    equationElement: createTransformationEquationElement(
      currentExpression,
      newExpression,
      rule.displayName,
      rule.id
    ),
    newAssumptions: result.newAssumptions,
    description: `Applied ${rule.displayName} to "${focusedNode.raw}"`,
  };
}

export function updateLetBindingAfterTransformation(
  letBindings: LetElement[],
  letId: string,
  newExpression: ExpressionNode,
  equationElement: EquationElement
): LetElement[] {
  return letBindings.map(letBinding => {
    if (letBinding.id !== letId) {
      return letBinding;
    }

    return {
      ...letBinding,
      value: newExpression,
      content: newExpression,
      equalityChain: [...(letBinding.equalityChain ?? []), equationElement],
    };
  });
}
