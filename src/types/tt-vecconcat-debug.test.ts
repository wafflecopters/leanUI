/**
 * Debug test for vecConcat type errors
 */

import { describe, it, expect } from 'vitest';
import { checkSourceBlocks } from '../parser/block-checker';

describe('vecConcat debugging', () => {
  it('should diagnose the clause 1 error (id v needs type argument)', () => {
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

plus : Nat -> Nat -> Nat
plus Zero b = b
plus (Succ a) b = Succ (plus a b)

inductive Vec : Type -> Nat -> Type where
  VNil : (A: Type) -> Vec A Zero
  VCons : (A : Type) -> (n : Nat) -> A -> Vec A n -> Vec A (Succ n)

id : (A : Type) -> A -> A
id A x = x

-- This should FAIL because 'id v' is missing the type argument
-- id : (A : Type) -> A -> A
-- When we write 'id v', we're applying id to v directly
-- But id expects Type first, not Vec A b!
vecConcat : (A : Type) -> (a : Nat) -> (b : Nat) -> Vec A a -> Vec A b -> Vec A (plus a b)
vecConcat _ _ _ (VNil _) v = id v
`;

    const results = checkSourceBlocks(source);
    const vecConcatResult = results.find(r => r.name === 'vecConcat');

    console.log('vecConcat errors:', vecConcatResult?.checkErrors);

    expect(vecConcatResult?.checkSuccess).toBe(false);
    expect(vecConcatResult?.checkErrors?.length).toBeGreaterThan(0);

    // The error should mention Type mismatch
    const errorMsg = vecConcatResult?.checkErrors?.[0]?.error?.message || '';
    console.log('Error message:', errorMsg);
    expect(errorMsg).toContain('Type mismatch');
  });

  it('should work when type argument is explicitly provided', () => {
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

plus : Nat -> Nat -> Nat
plus Zero b = b
plus (Succ a) b = Succ (plus a b)

inductive Vec : Type -> Nat -> Type where
  VNil : (A: Type) -> Vec A Zero
  VCons : (A : Type) -> (n : Nat) -> A -> Vec A n -> Vec A (Succ n)

id : (A : Type) -> A -> A
id A x = x

-- With explicit type argument, this should work (or at least get further)
-- We provide the type Vec A b to id
vecConcatFixed : (A : Type) -> (a : Nat) -> (b : Nat) -> Vec A a -> Vec A b -> Vec A (plus a b)
vecConcatFixed A Zero b (VNil _) v = id (Vec A b) v
`;

    const results = checkSourceBlocks(source);
    const vecConcatResult = results.find(r => r.name === 'vecConcatFixed');

    console.log('vecConcatFixed checkSuccess:', vecConcatResult?.checkSuccess);
    console.log('vecConcatFixed errors:', vecConcatResult?.checkErrors);

    // This might still fail for other reasons (dependent type refinement)
    // but the 'Type mismatch' for id should be gone
  });

  it('should diagnose clause 2 error', () => {
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

plus : Nat -> Nat -> Nat
plus Zero b = b
plus (Succ a) b = Succ (plus a b)

inductive Vec : Type -> Nat -> Type where
  VNil : (A: Type) -> Vec A Zero
  VCons : (A : Type) -> (n : Nat) -> A -> Vec A n -> Vec A (Succ n)

vecConcat2 : (A : Type) -> (a : Nat) -> (b : Nat) -> Vec A a -> Vec A b -> Vec A (plus a b)
vecConcat2 _ _ _ (VCons _ _ h tail) v = VCons _ _ h (vecConcat2 _ _ _ tail v)
`;

    const results = checkSourceBlocks(source);
    const result = results.find(r => r.name === 'vecConcat2');

    console.log('vecConcat2 checkSuccess:', result?.checkSuccess);
    console.log('vecConcat2 errors:', result?.checkErrors);

    // Analyze the error
    if (result?.checkErrors && result.checkErrors.length > 0) {
      for (const err of result.checkErrors) {
        console.log('Error:', err.error.message);
      }
    }
  });
});
