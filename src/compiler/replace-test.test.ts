import { describe, test, expect } from 'vitest';
import { compileSource } from '../test-utils';

describe('term used as type - error messages', () => {
  // These tests verify that using a term where a type is expected
  // produces a clear error message. The pattern `-> f x` puts `f x`
  // in return type position, but `f x` is a term (not a type).

  test('appNat: f x in return position is rejected with clear error', () => {
    // f : Nat -> Nat, so f x : Nat (a term, not a type)
    const source = `
inductive Nat : Type where
  | Zero : Nat
  | Succ : Nat -> Nat

appNat : (f : Nat -> Nat) -> (x : Nat) -> f x
appNat f x = f x
`;

    const results = compileSource(source);
    const appResult = results.find(r => r.name === 'appNat');
    expect(appResult?.checkSuccess).toBe(false);
    expect(appResult?.checkErrors[0]?.message).toContain('is a term of type Nat');
    expect(appResult?.checkErrors[0]?.message).toContain('but a type was expected');
  });

  test('app: polymorphic version also rejected', () => {
    // f : A -> A, so f x : A (a term, not a type)
    const source = `
app : (A B : Type) -> (f : A -> A) -> (x : A) -> f x
app _ _ f x = f x
`;

    const results = compileSource(source);
    const appResult = results.find(r => r.name === 'app');
    expect(appResult?.checkSuccess).toBe(false);
    expect(appResult?.checkErrors[0]?.message).toContain('is a term of type A');
  });

  test('replace with f : A -> B is rejected (f x is a term)', () => {
    // f : A -> B, so f x : B and f y : B (terms, not types)
    // This is a common mistake when trying to write transport/replace
    const source = `
inductive Equal : {A : Type} -> A -> A -> Type where
  | refl : {A : Type} -> {x : A} -> Equal x x

replace : {A B : Type} -> {x y : A} -> {f : A -> B} -> Equal x y -> f x -> f y
replace refl fx = fx
`;

    const results = compileSource(source);
    const replaceResult = results.find(r => r.name === 'replace');
    expect(replaceResult?.checkSuccess).toBe(false);
    expect(replaceResult?.checkErrors[0]?.message).toContain('is a term of type B');
  });

  test('replace with P : A -> Type works (P x is a type)', () => {
    // P : A -> Type is a type family, so P x : Type and P y : Type
    // This is the correct way to write transport/replace
    const source = `
inductive Equal : {A : Type} -> A -> A -> Type where
  | refl : {A : Type} -> {x : A} -> Equal x x

replace : {A : Type} -> {P : A -> Type} -> {x y : A} -> Equal x y -> P x -> P y
replace refl px = px
`;

    const results = compileSource(source);
    const replaceResult = results.find(r => r.name === 'replace');
    expect(replaceResult?.checkSuccess).toBe(true);
  });
});
