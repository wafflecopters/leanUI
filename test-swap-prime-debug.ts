import { checkSourceBlocks } from './src/parser/block-checker';

const source = `
swap' : (A : Type) -> (f : A -> A -> A) -> (A -> A -> A)
swap' a f = \\x y => f y x
`;

const results = checkSourceBlocks(source);
const swap = results.find(r => r.name === "swap'");

console.log('\n=== SWAP\' DEBUG ===');
console.log('Check success:', swap?.checkSuccess);
if (!swap?.checkSuccess) {
  console.log('Error:', swap?.checkErrors[0]?.error.message);
}
