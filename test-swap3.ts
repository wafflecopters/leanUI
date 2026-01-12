import { checkSourceBlocks } from './src/parser/block-checker';

const source = `
swap''' : (A : Type) -> (f : A -> A -> A) -> (A -> A -> A)
swap''' a f x y = f y x
`;

console.log('=== Testing swap\'\'\' (4 patterns, no lambdas) ===');
const results = checkSourceBlocks(source);
const swap3 = results.find(r => r.name === "swap'''");

console.log('Check success:', swap3?.checkSuccess);
if (!swap3?.checkSuccess) {
  console.log('Error:', swap3?.checkErrors[0]?.error.message);
}
