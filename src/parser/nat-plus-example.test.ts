/**
 * Test for the exact user example: Nat inductive + plus function
 */

import { checkSourceBlocks } from './block-checker';

function test(description: string, fn: () => void): void {
  try {
    fn();
    console.log(`✓ ${description}`);
  } catch (error) {
    console.error(`✗ ${description}`);
    throw error;
  }
}

function assert(condition: boolean, message?: string): void {
  if (!condition) {
    throw new Error(message || 'Assertion failed');
  }
}

console.log('\n' + '='.repeat(80));
console.log('NAT + PLUS EXAMPLE TEST');
console.log('='.repeat(80) + '\n');

test('Full example: Nat inductive + plus function with pattern matching', () => {
  const source = `-- Natural Numbers
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

plus : Nat -> Nat -> Nat
plus Zero b = b
plus (Succ a) b = Succ (plus a b)`;

  const results = checkSourceBlocks(source);

  console.log(`  Found ${results.length} blocks`);
  
  // Should have 2 blocks: Nat inductive and plus function
  assert(results.length === 2, `Should have 2 blocks, got ${results.length}`);
  
  // Block 0: Nat inductive
  console.log(`  Block 0: ${results[0].name} (parse: ${results[0].parseSuccess}, check: ${results[0].checkSuccess})`);
  assert(results[0].name === 'Nat', 'First block should be Nat');
  assert(results[0].parseSuccess === true, 'Nat should parse successfully');
  
  if (results[0].parseErrors.length > 0) {
    console.log('  Parse errors in block 0:');
    results[0].parseErrors.forEach(err => {
      console.log(`    Line ${err.line}, Col ${err.col}: ${err.message}`);
    });
  }
  
  // Block 1: plus function
  console.log(`  Block 1: ${results[1].name} (parse: ${results[1].parseSuccess}, check: ${results[1].checkSuccess})`);
  assert(results[1].name === 'plus', 'Second block should be plus');
  assert(results[1].parseSuccess === true, 'plus should parse successfully');
  
  if (results[1].parseErrors.length > 0) {
    console.log('  Parse errors in block 1:');
    results[1].parseErrors.forEach(err => {
      console.log(`    Line ${err.line}, Col ${err.col}: ${err.message}`);
    });
    throw new Error('plus function failed to parse!');
  }
  
  // Verify the plus function has pattern matching
  assert(results[1].declarations?.length === 1, 'plus should have 1 declaration');
  const plusDecl = results[1].declarations![0];
  assert(plusDecl.value?.tag === 'Match', 'plus should have Match value');
  if (plusDecl.value?.tag === 'Match') {
    console.log(`  plus has ${plusDecl.value.clauses.length} pattern clauses`);
    assert(plusDecl.value.clauses.length === 2, 'plus should have 2 clauses');
  }
});

console.log('\n' + '='.repeat(80));
console.log('NAT + PLUS EXAMPLE TEST PASSED! ✓');
console.log('='.repeat(80) + '\n');
