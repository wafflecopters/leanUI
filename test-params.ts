// Test the simplified parameter system
import { createPatternRule } from './src/types/enhanced-focus';

// Test the divide_both_sides rule with simple parameter variable
const testDivideRule = createPatternRule({
  id: 'test_divide_both_sides',
  name: 'Test Divide Both Sides',
  description: 'If a = b and c ≠ 0, then a/c = b/c',
  category: 'introduction',
  nodeType: 'equality',
  from: ['=', 'a', 'b'],
  to: ['=', ['/', 'a', 'c'], ['/', 'b', 'c']],  // 'c' is just a regular variable
  requiresParams: true,
  paramTemplate: { c: 'Value to divide by' },
  paramVariables: ['c'],  // Specify that 'c' comes from parameters
  introduceAssumptions: (_bindings, params) => {
    const value = params?.c;
    if (!value) return [];
    return [{
      id: 'test-id',
      name: `h_${value}_neq_zero`,
      expression: `${value} ≠ 0`,
      description: `${value} is not equal to zero`,
      introducedBy: 'test_divide_both_sides'
    }];
  }
});

// Test the div_self rule (bidirectional with params for reverse)
const testDivSelfRule = createPatternRule({
  id: 'test_div_self',
  name: 'Test Division by Self',
  description: 'x/x = 1',
  category: 'arithmetic',
  from: ['/', 'x', 'x'],  // Simple repeated variable
  to: 1,
  bidirectional: true,
  reverseName: 'Expand One as Fraction',
  reverseDescription: '1 = x/x',
  requiresParams: true,
  paramTemplate: { x: 'Enter expression for x' },
  paramVariables: ['x']  // For reverse direction
});

console.log('Rules created successfully!');
console.log('Test divide rule:', testDivideRule.name);
console.log('Requires params:', testDivideRule.requiresParams);
console.log('Param template:', testDivideRule.paramTemplate);

console.log('\nTest div_self rule:', testDivSelfRule.name);
console.log('Bidirectional:', testDivSelfRule.bidirectional);
console.log('Param variables:', testDivSelfRule.paramVariables);