import { describe, test, expect } from 'vitest';
import { parseExpressionToAST, astToString, ENHANCED_FOCUS_RULES } from './enhanced-focus';

// Helper function to apply a rule and get the result
function applyRule(ruleId: string, expression: string, isReverse: boolean = false) {
  const rule = ENHANCED_FOCUS_RULES.find(r => r.id === ruleId);
  if (!rule) throw new Error(`Rule ${ruleId} not found`);

  const expr = parseExpressionToAST(expression);

  const context = {
    assumptions: [],
    variables: new Map<string, string>()
  };

  let result;
  if (isReverse && rule.applyReverse) {
    result = rule.applyReverse(expr, expr, {}, context);
  } else {
    result = rule.applyToFocus(expr, expr, {}, context);
  }

  if (!result) return null;
  return astToString(result.newNode);
}

describe('Pattern Rules', () => {
  test('Division by self', () => {
    const result = applyRule('div_self', 'x / x');
    expect(result).toBe('1');
  });

  test('Subtraction by self', () => {
    const result = applyRule('sub_self', 'a - a');
    expect(result).toBe('0');
  });

  test('Subtraction as addition of negation', () => {
    const result = applyRule('sub_as_add_neg', 'a - b');
    expect(result).toBe('a + (-b)');
  });

  test('Subtraction as addition (complex expression)', () => {
    const result = applyRule('sub_as_add_neg', '(a + a) - a');
    // Parentheses are lost in AST parsing
    expect(result).toBe('a + a + (-a)');
  });

  test('Reverse: Addition as subtraction', () => {
    const result = applyRule('sub_as_add_neg', 'x + (-y)', true);
    expect(result).toBe('x - y');
  });
});
