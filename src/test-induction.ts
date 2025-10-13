import { parseExpressionToAST, astToString, substituteVariableInExpression } from './types/enhanced-focus';

/**
 * INDUCTION PROOF WORKFLOW TEST
 *
 * Tests the complete induction proof workflow for:
 *   sum i 1 k i = (k * (k + 1)) / 2
 *
 * WORKFLOW:
 * 1. User creates a let statement with the claim and selects "induction on ℕ" as proof method
 * 2. User clicks "Start Proof" button
 * 3. System prompts for:
 *    - Induction variable (detected: k, or user can specify)
 *    - Base case value (default: 1)
 * 4. System creates TWO child let statements:
 *    a) Base case: claim_base = P(1) [to be proved]
 *    b) Inductive case: claim_inductive = P(k+1) [to be proved]
 *       - Has local hypothesis IH: P(k)
 * 5. User proves each case independently by clicking "Start Proof" on each
 * 6. When both are complete, the original claim is marked as proved
 */

// Test the induction proof flow for sum i 1 k i = (k * (k + 1)) / 2
console.log("=".repeat(80));
console.log("INDUCTION PROOF WORKFLOW TEST");
console.log("Testing: sum i 1 k i = (k * (k + 1)) / 2");
console.log("=".repeat(80));
console.log();

// Parse the original claim
const claimText = 'sum i 1 k i = (k * (k + 1)) / 2';
console.log("Original claim:", claimText);

const claimExpression = parseExpressionToAST(claimText);
claimExpression.raw = claimText;

console.log("\nParsed AST:");
console.log(JSON.stringify(claimExpression, null, 2));

console.log("\nastToString of parsed claim:");
console.log(astToString(claimExpression));

// Test base case substitution (k = 1)
console.log("\n" + "=".repeat(80));
console.log("STEP 4a: BASE CASE (k = 1)");
console.log("=".repeat(80));
const baseCaseStatement = substituteVariableInExpression(
  claimExpression,
  'k',
  { id: 'test', type: 'literal', value: 1, children: [], raw: '1' }
);

console.log("\nBase case full statement (thm_base):");
console.log(astToString(baseCaseStatement));

console.log("\nBase case AST structure:");
console.log(JSON.stringify(baseCaseStatement, null, 2));

// Extract left and right sides
let leftSide = baseCaseStatement;
let rightSide = baseCaseStatement;
if (baseCaseStatement.type === 'equality' && baseCaseStatement.children.length >= 2) {
  leftSide = baseCaseStatement.children[0];
  rightSide = baseCaseStatement.children[1];

  console.log("\nBase case LEFT side (current expression):");
  console.log(astToString(leftSide));
  console.log("Left AST:", JSON.stringify(leftSide, null, 2));

  console.log("\nBase case RIGHT side (GOAL):");
  console.log(astToString(rightSide));
  console.log("Right AST:", JSON.stringify(rightSide, null, 2));
}

// Test inductive step substitution (k -> k+1)
console.log("\n" + "=".repeat(80));
console.log("STEP 4b: INDUCTIVE CASE (k -> k+1)");
console.log("=".repeat(80));
const kPlusOne = {
  id: 'test',
  type: 'binop' as const,
  operator: '+',
  children: [
    { id: 'test1', type: 'variable' as const, value: 'k', children: [], raw: 'k' },
    { id: 'test2', type: 'literal' as const, value: 1, children: [], raw: '1' }
  ],
  raw: 'k + 1'
};

const inductiveGoal = substituteVariableInExpression(
  claimExpression,
  'k',
  kPlusOne
);

console.log("\nInductive step full statement (thm_inductive):");
console.log(astToString(inductiveGoal));

console.log("\nInductive step AST structure:");
console.log(JSON.stringify(inductiveGoal, null, 2));

// Extract left and right sides
let indLeftSide = inductiveGoal;
let indRightSide = inductiveGoal;
if (inductiveGoal.type === 'equality' && inductiveGoal.children.length >= 2) {
  indLeftSide = inductiveGoal.children[0];
  indRightSide = inductiveGoal.children[1];

  console.log("\nInductive step LEFT side (current expression):");
  console.log(astToString(indLeftSide));

  console.log("\nInductive step RIGHT side (GOAL):");
  console.log(astToString(indRightSide));
}

console.log("\n" + "=".repeat(80));
console.log("INDUCTIVE HYPOTHESIS (attached to thm_inductive)");
console.log("=".repeat(80));
console.log("IH expression (original claim with k):");
console.log(claimExpression.raw || astToString(claimExpression));
console.log("\nThis hypothesis is attached as a localHypothesis to thm_inductive");
console.log("It will be available in the proof context when proving the inductive case");

// Check what sum i 1 1 i should evaluate to
console.log("\n--- EVALUATING sum i 1 1 i ---");
const sumExpr = parseExpressionToAST('sum i 1 1 i');
console.log("Parsed sum AST:");
console.log(JSON.stringify(sumExpr, null, 2));
console.log("astToString result:", astToString(sumExpr));