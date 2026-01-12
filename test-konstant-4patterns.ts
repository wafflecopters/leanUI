import { checkSourceBlocks } from './src/parser/block-checker';

// Test 2: 2 TYPE patterns + 2 VALUE patterns, no lambdas in RHS
const source = `
konstant : (A : Type) -> (B : Type) -> A -> B -> A
konstant A B x y = x
`;

console.log('=== Testing konstant with 4 patterns ===');
const results = checkSourceBlocks(source);
const result = results.find(r => r.name === "konstant");

console.log('\nCheck success:', result?.checkSuccess);
if (!result?.checkSuccess) {
  console.log('Error:', result?.checkErrors[0]?.error.message);
}
