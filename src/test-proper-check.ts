import { compileSource, summarizeResults } from './test-utils';

// Test case from user: Vec with wrong args
const brokenVec = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Vec : Nat -> Type 1 where
  VNil : (A: Type) -> Vec Zero
  VCons : (A : Type) -> (n : Nat) -> A -> Vec A n -> Vec Zero
`;

console.log('Testing broken Vec (wrong args):');
console.log(brokenVec);
console.log('---');

const results = compileSource(brokenVec);
const summary = summarizeResults(results);

console.log('Summary:', summary);

for (const result of results) {
  if (!result.parseSuccess) {
    console.log(`Block ${result.blockIndex}: Parse errors:`, result.parseErrors.map(e => e.message));
  } else if (!result.nameResolutionSuccess) {
    console.log(`Block ${result.blockIndex}: Name resolution errors:`, result.nameResolutionErrors.map(e => e.message));
  } else if (!result.checkSuccess) {
    console.log(`Block ${result.blockIndex}: Check errors:`, result.checkErrors.map(e => e.message));
  } else {
    console.log(`Block ${result.blockIndex}: SUCCESS`);
  }
}
