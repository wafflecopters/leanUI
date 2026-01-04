/**
 * Demo: Name Resolution Integration
 *
 * This demonstrates the complete name resolution pipeline working correctly.
 */

import { checkSourceBlocks } from './src/parser/block-checker';

console.log('\n' + '='.repeat(80));
console.log('NAME RESOLUTION INTEGRATION DEMO');
console.log('='.repeat(80) + '\n');

// Test 1: Valid code with proper symbol definitions
console.log('Test 1: Valid code (Nat definition + plus function)');
console.log('-'.repeat(80));

const validCode = `inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

plus : Nat -> Nat -> Nat`;

const validResults = checkSourceBlocks(validCode);

console.log(`Blocks: ${validResults.length}`);
validResults.forEach((result, i) => {
  console.log(`\nBlock ${i + 1}: ${result.name || '(unnamed)'}`);
  console.log(`  Parse: ${result.parseSuccess ? '✓' : '✗'}`);
  console.log(`  Name Resolution: ${result.nameResolutionSuccess ? '✓' : '✗'}`);
  if (!result.nameResolutionSuccess) {
    result.nameResolutionErrors.forEach(err => {
      console.log(`    Error: ${err.message}`);
    });
  }
});

// Test 2: Code with typo (Na instead of Nat)
console.log('\n\nTest 2: Code with typo (Na instead of Nat)');
console.log('-'.repeat(80));

const typoCode = `inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

plus : Nat -> Nat -> Na`;

const typoResults = checkSourceBlocks(typoCode);

console.log(`Blocks: ${typoResults.length}`);
typoResults.forEach((result, i) => {
  console.log(`\nBlock ${i + 1}: ${result.name || '(unnamed)'}`);
  console.log(`  Parse: ${result.parseSuccess ? '✓' : '✗'}`);
  console.log(`  Name Resolution: ${result.nameResolutionSuccess ? '✓' : '✗'}`);
  if (!result.nameResolutionSuccess) {
    console.log(`  Errors found:`);
    result.nameResolutionErrors.forEach(err => {
      console.log(`    - ${err.error.message}`);
    });
  }
});

// Test 3: Undefined symbol
console.log('\n\nTest 3: Completely undefined symbol');
console.log('-'.repeat(80));

const undefinedCode = `f : A -> B -> C`;

const undefinedResults = checkSourceBlocks(undefinedCode);

console.log(`Blocks: ${undefinedResults.length}`);
undefinedResults.forEach((result, i) => {
  console.log(`\nBlock ${i + 1}: ${result.name || '(unnamed)'}`);
  console.log(`  Parse: ${result.parseSuccess ? '✓' : '✗'}`);
  console.log(`  Name Resolution: ${result.nameResolutionSuccess ? '✓' : '✗'}`);
  if (!result.nameResolutionSuccess) {
    console.log(`  Errors found (${result.nameResolutionErrors.length} total):`);
    result.nameResolutionErrors.forEach(err => {
      console.log(`    - ${err.error.message}`);
    });
  }
});

console.log('\n' + '='.repeat(80));
console.log('DEMO COMPLETE');
console.log('='.repeat(80) + '\n');
