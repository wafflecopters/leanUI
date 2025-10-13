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

// Test cases
const tests = [
  {
    name: 'Division by self',
    ruleId: 'div_self',
    input: 'x / x',
    expected: '1'
  },
  {
    name: 'Subtraction by self',
    ruleId: 'sub_self',
    input: 'a - a',
    expected: '0'
  },
  {
    name: 'Subtraction as addition of negation',
    ruleId: 'sub_as_add_neg',
    input: 'a - b',
    expected: 'a + (-b)'
  },
  {
    name: 'Subtraction as addition (complex expression)',
    ruleId: 'sub_as_add_neg',
    input: '(a + a) - a',
    expected: 'a + a + (-a)'  // Parentheses are lost in AST parsing
  },
  {
    name: 'Reverse: Addition as subtraction',
    ruleId: 'sub_as_add_neg',
    input: 'x + (-y)',
    expected: 'x - y',
    isReverse: true
  }
];

// Run tests
console.log('Running pattern rule tests...\n');

let passed = 0;
let failed = 0;

for (const test of tests) {
  try {
    const result = applyRule(test.ruleId, test.input, test.isReverse);

    if (result === test.expected) {
      console.log(`✅ ${test.name}`);
      console.log(`   Input: ${test.input}`);
      console.log(`   Output: ${result}`);
      passed++;
    } else {
      console.log(`❌ ${test.name}`);
      console.log(`   Input: ${test.input}`);
      console.log(`   Expected: ${test.expected}`);
      console.log(`   Got: ${result}`);
      failed++;
    }
  } catch (error) {
    console.log(`❌ ${test.name}`);
    console.log(`   Input: ${test.input}`);
    console.log(`   Error: ${error instanceof Error ? error.message : 'Unknown error'}`);
    failed++;
  }
  console.log('');
}

console.log(`\nResults: ${passed} passed, ${failed} failed`);

// Export for potential use in Jest or other test runners
export { tests, applyRule };