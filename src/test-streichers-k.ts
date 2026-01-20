import { compileSource, summarizeResults } from './test-utils';

// Test nested Pi types with applications in the signature
const source = `
inductive Equal : (A: Type) -> A -> A -> Type where
  refl : (A : Type) -> (x : A) -> Equal A x x

-- Test 1: P (refl A a) in return position - used to fail!
test1 : (A : Type) -> (a : A) -> (P : Equal A a a -> Type) -> P (refl A a)
test1 A a P = ?

-- Test 2: P (refl A a) in domain position
test2 : (A : Type) -> (a : A) -> (P : Equal A a a -> Type) -> P (refl A a) -> P (refl A a)
test2 A a P p = p

-- Test 3: The full streichersK signature (won't typecheck body, but signature should parse)
streichersK : (A : Type) -> (a : A) -> (P : Equal A a a -> Type) -> (p : P (refl A a)) -> (e : Equal A a a) -> P e
streichersK A a P p (refl _ _) = p

-- Test 4: Using refl in body works
makeRefl : (A : Type) -> (a : A) -> Equal A a a
makeRefl A a = refl A a

-- Test 5: Pattern matching on Equal
eqReflOnly : (A : Type) -> (a : A) -> (e : Equal A a a) -> Equal A a a
eqReflOnly A a (refl A a) = refl A a
`;

console.log('Testing nested Pi types with applications in signature:');
console.log(source);
console.log('---');

const results = compileSource(source);
const summary = summarizeResults(results);

console.log('Summary:', summary);

let allPassed = true;
for (const result of results) {
  if (!result.parseSuccess) {
    console.log(`Block ${result.blockIndex} (${result.name || 'unnamed'}): Parse errors:`, result.parseErrors.map(e => e.message));
    allPassed = false;
  } else if (!result.nameResolutionSuccess) {
    console.log(`Block ${result.blockIndex} (${result.name || 'unnamed'}): Name resolution errors:`, result.nameResolutionErrors.map(e => e.message));
    allPassed = false;
  } else if (!result.checkSuccess) {
    console.log(`Block ${result.blockIndex} (${result.name || 'unnamed'}): Check errors:`);
    for (const e of result.checkErrors) {
      console.log(`  - ${e.message}`);
    }
    allPassed = false;
  } else {
    console.log(`Block ${result.blockIndex} (${result.name || 'unnamed'}): SUCCESS`);
  }
}

if (allPassed) {
  console.log('\n✓ All tests passed!');
} else {
  console.log('\n✗ Some tests failed');
  process.exit(1);
}
