/**
 * Test case: wildcard that CANNOT be solved should fail
 */
import { describe, test, expect } from 'vitest';
import { compileTTFromText } from './compile';

describe('Unsolvable wildcard detection', () => {
  test('sigmaSum with unsolvable wildcard correctly fails', () => {
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

plus : Nat -> Nat -> Nat
plus Zero m = m
plus (Succ n) m = Succ (plus n m)

sigmaSum : (count : Nat) -> (fn: (index: Nat) -> Nat) -> Nat
sigmaSum Zero _ = Zero
sigmaSum (Succ k) fn = plus _ (Succ k)
`;

    const result = compileTTFromText(source);

    // EXPECTED: This should FAIL because the underscore in "plus _ (Succ k)"
    // cannot be solved. There's no way to know what Nat to pass to plus.
    expect(result.success).toBe(false);

    const sigmaSumDecl = result.blocks
      .flatMap(b => b.declarations)
      .find(d => d.name === 'sigmaSum');

    expect(sigmaSumDecl).toBeDefined();
    expect(sigmaSumDecl!.checkSuccess).toBe(false);
    expect(sigmaSumDecl!.checkErrors.length).toBeGreaterThan(0);
    expect(sigmaSumDecl!.checkErrors[0].message).toContain('unsolved wildcards');
  });
});
