import { parseExpressionToAST, astToString, substituteVariableInExpression } from './types/enhanced-focus';

// Test suite for induction proof functionality
console.log("=== COMPREHENSIVE INDUCTION PROOF TEST SUITE ===\n");

// Test 1: Base case substitution
function testBaseCaseSubstitution() {
  console.log("TEST 1: Base Case Substitution");
  console.log("-------------------------------");

  const claim = 'sum i 1 n i = (n * (n + 1)) / 2';
  const claimAST = parseExpressionToAST(claim);
  claimAST.raw = claim;

  // Substitute n=1 for base case
  const baseCase = substituteVariableInExpression(
    claimAST,
    'n',
    { id: 'test', type: 'literal', value: 1, children: [], raw: '1' }
  );

  // Extract left and right sides
  let leftSide = baseCase;
  let rightSide = baseCase;
  if (baseCase.type === 'equality' && baseCase.children.length >= 2) {
    leftSide = baseCase.children[0];
    rightSide = baseCase.children[1];
  }

  const leftStr = astToString(leftSide);
  const rightStr = astToString(rightSide);

  console.log(`Original claim: ${claim}`);
  console.log(`Base case (n=1): ${astToString(baseCase)}`);
  console.log(`  LEFT (expression): ${leftStr}`);
  console.log(`  RIGHT (goal): ${rightStr}`);

  // Assertions
  const expectedLeft = 'sum i 1 1 i';
  const expectedRight = '(1 * (1 + 1)) / 2';

  console.log(`\nAssertion checks:`);
  console.log(`  LEFT should be '${expectedLeft}': ${leftStr === expectedLeft ? '✅' : '❌'}`);
  console.log(`  RIGHT should be '${expectedRight}': ${rightStr === expectedRight ? '✅' : '❌'}`);

  return leftStr === expectedLeft && rightStr === expectedRight;
}

// Test 2: Inductive step substitution
function testInductiveStepSubstitution() {
  console.log("\n\nTEST 2: Inductive Step Substitution");
  console.log("------------------------------------");

  const claim = 'sum i 1 n i = (n * (n + 1)) / 2';
  const claimAST = parseExpressionToAST(claim);
  claimAST.raw = claim;

  // Create n+1 expression
  const nPlusOne = {
    id: 'test',
    type: 'binop' as const,
    operator: '+',
    children: [
      { id: 'test1', type: 'variable' as const, value: 'n', children: [], raw: 'n' },
      { id: 'test2', type: 'literal' as const, value: 1, children: [], raw: '1' }
    ],
    raw: 'n + 1'
  };

  // Substitute n+1 for inductive step
  const inductiveStep = substituteVariableInExpression(
    claimAST,
    'n',
    nPlusOne
  );

  // Extract left and right sides
  let leftSide = inductiveStep;
  let rightSide = inductiveStep;
  if (inductiveStep.type === 'equality' && inductiveStep.children.length >= 2) {
    leftSide = inductiveStep.children[0];
    rightSide = inductiveStep.children[1];
  }

  const leftStr = astToString(leftSide);
  const rightStr = astToString(rightSide);

  console.log(`Original claim: ${claim}`);
  console.log(`Inductive step (n→n+1): ${astToString(inductiveStep)}`);
  console.log(`  LEFT (expression): ${leftStr}`);
  console.log(`  RIGHT (goal): ${rightStr}`);

  // The inductive hypothesis is the original claim
  console.log(`\nInductive Hypothesis (IH): ${claim}`);

  // Assertions
  const expectedLeft = 'sum i 1 n + 1 i';
  const expectedRight = '((n + 1) * (n + 1 + 1)) / 2';

  console.log(`\nAssertion checks:`);
  console.log(`  LEFT should be '${expectedLeft}': ${leftStr === expectedLeft ? '✅' : '❌'}`);
  console.log(`  RIGHT should be '${expectedRight}': ${rightStr === expectedRight ? '✅' : '❌'}`);

  return leftStr === expectedLeft && rightStr === expectedRight;
}

// Test 3: Goal tracking simulation
function testGoalTracking() {
  console.log("\n\nTEST 3: Goal Tracking Simulation");
  console.log("---------------------------------");

  interface ProofState {
    currentExpression: any | null;
    goal: any | null;
  }

  // Initial state - should start with null
  const initialState: ProofState = {
    currentExpression: null,
    goal: null
  };

  console.log("Initial state:");
  console.log(`  currentExpression: ${initialState.currentExpression}`);
  console.log(`  goal: ${initialState.goal}`);
  console.log(`  ✅ Both should be null initially`);

  // When starting base case
  const claim = 'sum i 1 n i = (n * (n + 1)) / 2';
  const claimAST = parseExpressionToAST(claim);
  claimAST.raw = claim;

  const baseCase = substituteVariableInExpression(
    claimAST,
    'n',
    { id: 'test', type: 'literal', value: 1, children: [], raw: '1' }
  );

  let leftSide = baseCase;
  let rightSide = baseCase;
  if (baseCase.type === 'equality' && baseCase.children.length >= 2) {
    leftSide = baseCase.children[0];
    rightSide = baseCase.children[1];
  }

  // Update state when starting base case
  const baseCaseState: ProofState = {
    currentExpression: leftSide,
    goal: rightSide
  };

  console.log("\nAfter starting base case:");
  console.log(`  currentExpression: ${astToString(baseCaseState.currentExpression)}`);
  console.log(`  goal: ${astToString(baseCaseState.goal)}`);

  // Verify the goal is NOT the same as currentExpression
  const goalMatchesExpression = astToString(baseCaseState.goal) === astToString(baseCaseState.currentExpression);
  console.log(`\n  Goal should NOT equal currentExpression: ${!goalMatchesExpression ? '✅' : '❌'}`);

  return !goalMatchesExpression;
}

// Test 4: Multiple variable substitution
function testMultipleVariables() {
  console.log("\n\nTEST 4: Expression with Multiple Variables");
  console.log("------------------------------------------");

  const expr = 'a * n + b * n = (a + b) * n';
  const exprAST = parseExpressionToAST(expr);
  exprAST.raw = expr;

  // Substitute n=5
  const substituted = substituteVariableInExpression(
    exprAST,
    'n',
    { id: 'test', type: 'literal', value: 5, children: [], raw: '5' }
  );

  const result = astToString(substituted);
  const expected = 'a * 5 + b * 5 = (a + b) * 5';

  console.log(`Original: ${expr}`);
  console.log(`After n=5: ${result}`);
  console.log(`Expected: ${expected}`);
  console.log(`  Correct: ${result === expected ? '✅' : '❌'}`);

  return result === expected;
}

// Test 5: Nested substitutions
function testNestedSubstitutions() {
  console.log("\n\nTEST 5: Nested Expression Substitution");
  console.log("---------------------------------------");

  const expr = 'f(n + 1) = f(n) + (n + 1)';
  const exprAST = parseExpressionToAST(expr);
  exprAST.raw = expr;

  // Substitute n=k
  const substituted = substituteVariableInExpression(
    exprAST,
    'n',
    { id: 'test', type: 'variable', value: 'k', children: [], raw: 'k' }
  );

  const result = astToString(substituted);
  const expected = 'f(k + 1) = f(k) + (k + 1)';

  console.log(`Original: ${expr}`);
  console.log(`After n=k: ${result}`);
  console.log(`Expected: ${expected}`);
  console.log(`  Correct: ${result === expected ? '✅' : '❌'}`);

  return result === expected;
}

// Run all tests
console.log("Running all tests...\n");

const results = {
  baseCaseSubstitution: testBaseCaseSubstitution(),
  inductiveStepSubstitution: testInductiveStepSubstitution(),
  goalTracking: testGoalTracking(),
  multipleVariables: testMultipleVariables(),
  nestedSubstitutions: testNestedSubstitutions()
};

// Summary
console.log("\n\n=== TEST SUMMARY ===");
console.log("-------------------");

let passed = 0;
let failed = 0;

for (const [testName, result] of Object.entries(results)) {
  if (result) {
    passed++;
    console.log(`✅ ${testName}`);
  } else {
    failed++;
    console.log(`❌ ${testName}`);
  }
}

console.log(`\nTotal: ${passed + failed} tests`);
console.log(`Passed: ${passed}`);
console.log(`Failed: ${failed}`);

if (failed === 0) {
  console.log("\n🎉 All tests passed!");
} else {
  console.log(`\n⚠️ ${failed} test(s) failed`);
}