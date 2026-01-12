import { checkSourceBlocks } from './src/parser/block-checker';

// Simplest case with 2 patterns
const source = `
konstant : (A : Type) -> (B : Type) -> A -> B -> A
konstant A B = \\(x: A) (y: B) => x
`;

console.log('=== Testing konstant (2 patterns + lambdas) ===');
const results = checkSourceBlocks(source);
const test = results.find(r => r.name === "konstant");

console.log('Check success:', test?.checkSuccess);
if (!test?.checkSuccess) {
  console.log('Error:', test?.checkErrors[0]?.error.message);
}
