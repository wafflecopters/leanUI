import { checkSourceBlocks } from './src/parser/block-checker';

const source = `
swap : (A : Type) -> (f : A -> A -> A) -> (A -> A -> A)
swap A = \\f => \\(x: A) (y: A) => f y x
`;

const results = checkSourceBlocks(source);
const swap = results.find(r => r.name === 'swap');

console.log('\n=== SWAP RESULT ===');
console.log('Check success:', swap?.checkSuccess);
console.log('Errors:', swap?.checkErrors.map(e => e.error.message));

if (swap?.typeQueryData) {
  console.log('\n=== TYPE QUERY DATA ===');
  console.log('kernelType:', JSON.stringify(swap.typeQueryData.kernelType, null, 2));
  console.log('\nkernelValue:', JSON.stringify(swap.typeQueryData.kernelValue, null, 2));
}
