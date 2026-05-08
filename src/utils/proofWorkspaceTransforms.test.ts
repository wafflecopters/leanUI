import { describe, expect, test } from 'vitest';
import {
  type Assumption,
  createLetElement,
  createTransformationEquationElement,
  parseExpressionToAST,
  type ProofContext,
} from '../types/enhanced-focus';
import {
  applyFocusedExpressionRule,
  updateLetBindingAfterTransformation,
} from './proofWorkspaceTransforms';

describe('applyFocusedExpressionRule', () => {
  const metadata: ProofContext = { assumptions: [] };

  test('rewrites a nested focused node and refreshes the parent raw string', () => {
    const expression = parseExpressionToAST('x + (y - y)');
    const focusedNode = expression.children[1];

    const result = applyFocusedExpressionRule(
      {
        displayName: 'Subtract self',
        applyRule: () => ({
          newNode: parseExpressionToAST('0'),
        }),
      },
      focusedNode,
      expression,
      [1],
      metadata
    );

    expect(result.newExpression.raw).toBe('x + 0');
    expect(result.newExpression.children[1].raw).toBe('0');
    expect(result.equationElement.leftSide.raw).toBe('x + (y - y)');
    expect(result.equationElement.rightSide.raw).toBe('x + 0');
    expect(result.description).toBe('Applied Subtract self to "(y - y)"');
  });

  test('preserves new assumptions returned by the rule', () => {
    const expression = parseExpressionToAST('x = x');
    const focusedNode = expression;
    const newAssumptions: Assumption[] = [{
      id: 'h1',
      name: 'h1',
      type: parseExpressionToAST('x = x'),
      description: 'Reflexive equality',
    }];

    const result = applyFocusedExpressionRule(
      {
        displayName: 'Introduce assumption',
        applyRule: () => ({
          newNode: parseExpressionToAST('x = x'),
          newAssumptions,
        }),
      },
      focusedNode,
      expression,
      [],
      metadata
    );

    expect(result.newAssumptions).toEqual(newAssumptions);
    expect(result.newExpression.raw).toBe('x = x');
  });
});

describe('updateLetBindingAfterTransformation', () => {
  test('updates only the selected let-binding and initializes proof history', () => {
    const first = createLetElement('foo', parseExpressionToAST('a + 0'));
    const second = createLetElement('bar', parseExpressionToAST('b + 0'));
    const equationElement = createTransformationEquationElement(
      parseExpressionToAST('a + 0'),
      parseExpressionToAST('a'),
      'Simplify'
    );
    const newExpression = parseExpressionToAST('a');

    const updated = updateLetBindingAfterTransformation(
      [first, second],
      first.id,
      newExpression,
      equationElement
    );

    expect(updated[0].value.raw).toBe('a');
    expect(updated[0].content).toEqual(newExpression);
    expect(updated[0].equalityChain).toEqual([equationElement]);
    expect(updated[1]).toEqual(second);
  });

  test('appends to existing equality history when present', () => {
    const letBinding = createLetElement('foo', parseExpressionToAST('a + 0'));
    const priorElement = createTransformationEquationElement(
      parseExpressionToAST('a + 0'),
      parseExpressionToAST('a'),
      'Earlier'
    );
    const nextElement = createTransformationEquationElement(
      parseExpressionToAST('a'),
      parseExpressionToAST('a'),
      'Later'
    );
    letBinding.equalityChain = [priorElement];

    const updated = updateLetBindingAfterTransformation(
      [letBinding],
      letBinding.id,
      parseExpressionToAST('a'),
      nextElement
    );

    expect(updated[0].equalityChain).toEqual([priorElement, nextElement]);
  });
});
