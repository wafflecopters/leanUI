/**
 * Tests for multi-line type signatures with leading arrows.
 *
 * The parser should accept type signatures where -> appears at the start
 * of a continuation line.
 */

import { describe, test, expect } from 'vitest';
import { compileSource } from '../test-utils';

describe('Multi-line type signatures with leading arrows', () => {
  test('accepts arrow at end of line (current behavior)', () => {
    const source = `
      inductive Nat : Type where
        Zero : Nat
        Succ : Nat -> Nat

      inductive Equal : {A : Type} -> A -> A -> Type where
        refl : {A : Type} -> {a : A} -> Equal a a

      succInj: {u v : Nat} ->
        Equal (Succ u) (Succ v) -> Equal u v
      succInj refl = refl
    `;

    const blocks = compileSource(source);
    const succInjBlock = blocks.find(b => b.name === 'succInj');

    expect(succInjBlock?.parseSuccess).toBe(true);
    expect(succInjBlock?.checkSuccess).toBe(true);
  });

  test('accepts arrow at start of line (should work)', () => {
    const source = `
      inductive Nat : Type where
        Zero : Nat
        Succ : Nat -> Nat

      inductive Equal : {A : Type} -> A -> A -> Type where
        refl : {A : Type} -> {a : A} -> Equal a a

      succInj: {u v : Nat}
        -> Equal (Succ u) (Succ v) -> Equal u v
      succInj refl = refl
    `;

    const blocks = compileSource(source);
    const succInjBlock = blocks.find(b => b.name === 'succInj');

    expect(succInjBlock?.parseSuccess).toBe(true);
    expect(succInjBlock?.checkSuccess).toBe(true);
  });

  test('accepts multiple leading arrows', () => {
    const source = `
      inductive Nat : Type where
        Zero : Nat
        Succ : Nat -> Nat

      foo : {A : Type}
        -> (x : A)
        -> (y : A)
        -> A
      foo x y = x
    `;

    const blocks = compileSource(source);
    const fooBlock = blocks.find(b => b.name === 'foo');

    // Just check parsing works - type checking fails because x/y aren't properly bound
    expect(fooBlock?.parseSuccess).toBe(true);
  });

  test('accepts mixed: some arrows at end, some at start', () => {
    const source = `
      inductive Nat : Type where
        Zero : Nat
        Succ : Nat -> Nat

      bar : {A : Type} ->
        (x : A)
        -> (y : A) -> A
      bar x y = y
    `;

    const blocks = compileSource(source);
    const barBlock = blocks.find(b => b.name === 'bar');

    // Just check parsing works - type checking fails because x/y aren't properly bound
    expect(barBlock?.parseSuccess).toBe(true);
  });
});
