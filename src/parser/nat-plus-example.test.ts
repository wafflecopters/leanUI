/**
 * Test for the exact user example: Nat inductive + plus function
 */

import { describe, test, expect } from 'vitest';
import { compileSource } from '../test-utils';

describe('Nat + Plus Example', () => {
  test('full example: Nat inductive + plus function with pattern matching', () => {
    const source = `-- Natural Numbers
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

plus : Nat -> Nat -> Nat
plus Zero b = b
plus (Succ a) b = Succ (plus a b)`;

    const results = compileSource(source);

    // Should have 2 blocks: Nat inductive and plus function
    expect(results.length).toBe(2);

    // Block 0: Nat inductive
    expect(results[0].name).toBe('Nat');
    expect(results[0].parseSuccess).toBe(true);

    // Block 1: plus function
    expect(results[1].name).toBe('plus');
    expect(results[1].parseSuccess).toBe(true);

    // Verify the plus function has pattern matching
    expect(results[1].declarations?.length).toBe(1);
    const plusDecl = results[1].declarations![0];
    expect(plusDecl.surfaceValue?.tag).toBe('Match');
    if (plusDecl.surfaceValue?.tag === 'Match') {
      expect(plusDecl.surfaceValue.clauses.length).toBe(2);
    }
  });
});
