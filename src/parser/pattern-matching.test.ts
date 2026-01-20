/**
 * Tests for pattern matching syntax parsing
 */

import { describe, test, expect } from 'vitest';
import { compileSource } from '../test-utils';

describe('Pattern Matching', () => {
  test('simple function with type signature', () => {
    const source = `plus : Nat -> Nat -> Nat
plus Zero b = b
plus (Succ a) b = Succ (plus a b)`;

    const results = compileSource(source);

    expect(results.length).toBe(1);
    expect(results[0].parseSuccess).toBe(true);
    expect(results[0].name).toBe('plus');
    expect(results[0].declarations?.length).toBe(1);
  });

  test('multiple clauses', () => {
    const source = `isZero : Nat -> Bool
isZero Zero = True
isZero (Succ n) = False`;

    const results = compileSource(source);

    expect(results.length).toBe(1);
    expect(results[0].parseSuccess).toBe(true);
    expect(results[0].name).toBe('isZero');
  });

  test('nested patterns', () => {
    const source = `add : Nat -> Nat -> Nat
add Zero n = n
add (Succ m) n = Succ (add m n)`;

    const results = compileSource(source);

    expect(results.length).toBe(1);
    expect(results[0].parseSuccess).toBe(true);
  });

  test('underscore patterns', () => {
    const source = `const : A -> B -> A
const x _ = x`;

    const results = compileSource(source);

    expect(results.length).toBe(1);
    expect(results[0].parseSuccess).toBe(true);
  });

  test('variable patterns', () => {
    const source = `id : A -> A
id x = x`;

    const results = compileSource(source);

    expect(results.length).toBe(1);
    expect(results[0].parseSuccess).toBe(true);
  });
});
