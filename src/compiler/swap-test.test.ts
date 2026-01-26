import { describe, test, expect } from 'vitest';
import { compileSource } from '../test-utils';

describe('swap bug fix', () => {
  test('swap should reject wrong argument order', () => {
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Bool : Type where
  True : Bool
  False : Bool

swap : {A : Type} -> {B : Type} -> {C : Type} -> (f : A -> B -> C) -> (B -> A -> C)
swap f b a = f a b

myFunc : Nat -> Bool -> Bool
myFunc n b = b

-- swap myFunc : Bool -> Nat -> Bool
-- So swap myFunc n True should FAIL (n : Nat passed where Bool expected)
test : Nat -> Bool
test n = swap myFunc n True
`;

    const results = compileSource(source);
    const testResult = results.find(r => r.name === "test");

    console.log('test checkSuccess:', testResult?.checkSuccess);
    if (!testResult?.checkSuccess) {
      console.log('Errors:', testResult?.checkErrors);
    }

    // This SHOULD fail - wrong argument order
    expect(testResult?.checkSuccess).toBe(false);
  });
});
