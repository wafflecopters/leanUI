import { checkSourceBlocks } from './src/parser/block-checker';

function testCase(name: string, source: string): boolean {
  console.log(`\n=== ${name} ===`);
  const results = checkSourceBlocks(source);
  const result = results[0];

  const success = result?.checkSuccess ?? false;
  console.log(success ? '✅ PASS' : '❌ FAIL');
  if (!success) {
    console.log('Error:', result?.checkErrors[0]?.error.message);
  }
  return success;
}

// Test 1: Simplest case - 1 pattern, no lambdas in RHS
const test1 = testCase('1 pattern, no lambda', `
id : (A : Type) -> A -> A
id A = \\(x: A) => x
`);

// Test 2: 2 patterns, no lambdas in RHS
const test2 = testCase('2 patterns, no lambda', `
konstant : (A : Type) -> (B : Type) -> A -> B -> A
konstant A B x y = x
`);

// Test 3: 2 patterns with lambdas
const test3 = testCase('2 patterns with lambdas', `
konstant : (A : Type) -> (B : Type) -> A -> B -> A
konstant A B = \\(x: A) (y: B) => x
`);

// Test 4: 3 patterns, no lambdas
const test4 = testCase('3 patterns, no lambda', `
flip : (A : Type) -> (B : Type) -> (C : Type) -> (A -> B -> C) -> (B -> A -> C)
flip A B C f x y = f y x
`);

// Summary
console.log('\n=== SUMMARY ===');
console.log(`Test 1 (1 pattern, no lambda): ${test1 ? '✅' : '❌'}`);
console.log(`Test 2 (2 patterns, no lambda): ${test2 ? '✅' : '❌'}`);
console.log(`Test 3 (2 patterns with lambdas): ${test3 ? '✅' : '❌'}`);
console.log(`Test 4 (3 patterns, no lambda): ${test4 ? '✅' : '❌'}`);
console.log(`Passing: ${[test1, test2, test3, test4].filter(Boolean).length}/4`);
