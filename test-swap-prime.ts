import { checkSourceBlocks } from './src/parser/block-checker';

const source = `
swap' : (A : Type) -> (f : A -> A -> A) -> (A -> A -> A)
swap' a f = \\x y => f y x
`;

const results = checkSourceBlocks(source);
const swap = results.find(r => r.name === "swap'");

console.log('\n=== SWAP\' RESULT ===');
console.log('Check success:', swap?.checkSuccess);
console.log('Errors:', swap?.checkErrors.map(e => e.error.message));
