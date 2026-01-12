import { checkSourceBlocks } from './src/parser/block-checker';

// This one PASSES (all pattern args, no lambdas)
const source1 = `
swap''' : (A : Type) -> (f : A -> A -> A) -> (A -> A -> A)
swap''' a f x y = f y x
`;

// This one FAILS (pattern args + lambdas)
const source2 = `
swap' : (A : Type) -> (f : A -> A -> A) -> (A -> A -> A)
swap' a f = \\x y => f y x
`;

console.log('=== Testing swap\'\'\' (should pass) ===');
const results1 = checkSourceBlocks(source1);
const swap1 = results1.find(r => r.name === "swap'''");
console.log('Success:', swap1?.checkSuccess);
if (!swap1?.checkSuccess) {
  console.log('Error:', swap1?.checkErrors[0]?.error.message);
}

console.log('\n=== Testing swap\' (should fail) ===');
const results2 = checkSourceBlocks(source2);
const swap2 = results2.find(r => r.name === "swap'");
console.log('Success:', swap2?.checkSuccess);
if (!swap2?.checkSuccess) {
  console.log('Error:', swap2?.checkErrors[0]?.error.message);
}

// Check the clauses
console.log('\n=== Clause comparison ===');
console.log('swap\'\'\' patterns:', swap1?.typeQueryData?.kernelValue?.tag === 'Match' ? swap1.typeQueryData.kernelValue.clauses[0].patterns.length : 'N/A');
console.log('swap\' patterns:', swap2?.typeQueryData?.kernelValue?.tag === 'Match' ? swap2.typeQueryData.kernelValue.clauses[0].patterns.length : 'N/A');

console.log('\nswap\'\'\' RHS:', swap1?.typeQueryData?.kernelValue?.tag === 'Match' ? swap1.typeQueryData.kernelValue.clauses[0].rhs.tag : 'N/A');
console.log('swap\' RHS:', swap2?.typeQueryData?.kernelValue?.tag === 'Match' ? swap2.typeQueryData.kernelValue.clauses[0].rhs.tag : 'N/A');
