import { describe, test, expect } from 'vitest';
import { compileSource } from '../test-utils';

describe('inline lambda in named arguments', () => {
  const preamble = `
inductive Nat : Type where
  | Zero : Nat
  | Succ : Nat -> Nat

inductive Vec : Type -> Nat -> Type where
  | VNil : {A : Type} -> Vec A Zero
  | VCons : {A : Type} -> {n : Nat} -> A -> Vec A n -> Vec A (Succ n)

plus : Nat -> Nat -> Nat
plus Zero n = n
plus (Succ m) n = Succ (plus m n)
`;

  test('vecConcat with plain variable works', () => {
    const source = preamble + `
vecConcat : {A : Type} -> {a b : Nat} -> Vec A a -> Vec A b -> Vec A (plus a b)
vecConcat VNil v = v
vecConcat {a:=Succ p} (VCons h tail) v = VCons h (vecConcat {a:=p} tail v)
`;
    const results = compileSource(source);
    const result = results.find(r => r.name === 'vecConcat');
    if (!result?.checkSuccess) {
      console.log('errors:', result?.checkErrors?.map(e => e.message));
    }
    expect(result?.checkSuccess).toBe(true);
  });

  test('simple recursive call with lambda in named arg', () => {
    const source = `
inductive Nat : Type where
  | Zero : Nat
  | Succ : Nat -> Nat

foo : {n : Nat} -> Nat -> Nat
foo {n := Zero} x = x
foo {n := Succ m} x = foo {n := m} (Succ x)

bar : {n : Nat} -> Nat -> Nat
bar {n := Zero} x = x
bar {n := Succ m} x = bar {n := (\\(y : Nat) => y) m} (Succ x)
`;
    const results = compileSource(source);

    const fooResult = results.find(r => r.name === 'foo');
    expect(fooResult?.checkSuccess).toBe(true);

    const barResult = results.find(r => r.name === 'bar');
    if (!barResult?.checkSuccess) {
      console.log('bar errors:', barResult?.checkErrors?.map(e => e.message));
    }
    expect(barResult?.checkSuccess).toBe(true);
  });

  test('vecConcat with annotated identity lambda should work', () => {
    const source = preamble + `
vecConcat : {A : Type} -> {a b : Nat} -> Vec A a -> Vec A b -> Vec A (plus a b)
vecConcat VNil v = v
vecConcat {a:=Succ p} (VCons h tail) v = VCons h (vecConcat {a:=(\\(x: Nat) => x) p} tail v)
`;
    const results = compileSource(source);
    const result = results.find(r => r.name === 'vecConcat');
    if (!result?.checkSuccess) {
      console.log('errors:', result?.checkErrors?.map(e => e.message));
    }
    expect(result?.checkSuccess).toBe(true);
  });

  test('vecConcat with unannotated identity lambda should work', () => {
    const source = preamble + `
vecConcat : {A : Type} -> {a b : Nat} -> Vec A a -> Vec A b -> Vec A (plus a b)
vecConcat VNil v = v
vecConcat {a:=Succ p} (VCons h tail) v = VCons h (vecConcat {a:=(\\x => x) p} tail v)
`;
    const results = compileSource(source);
    const result = results.find(r => r.name === 'vecConcat');
    if (!result?.checkSuccess) {
      console.log('errors:', result?.checkErrors?.map(e => e.message));
    }
    expect(result?.checkSuccess).toBe(true);
  });

  test('simple beta reduction works in unification', () => {
    // Simpler test case
    const source = `
inductive Nat : Type where
  | Zero : Nat
  | Succ : Nat -> Nat

id : Nat -> Nat
id x = x

-- This should work: (\\x => x) Zero has type Nat
test1 : Nat
test1 = (\\(x : Nat) => x) Zero

-- This should work too
test2 : Nat
test2 = (\\x => x) Zero
`;
    const results = compileSource(source);

    const test1 = results.find(r => r.name === 'test1');
    if (!test1?.checkSuccess) {
      console.log('test1 errors:', test1?.checkErrors?.map(e => e.message));
    }
    expect(test1?.checkSuccess).toBe(true);

    const test2 = results.find(r => r.name === 'test2');
    if (!test2?.checkSuccess) {
      console.log('test2 errors:', test2?.checkErrors?.map(e => e.message));
    }
    expect(test2?.checkSuccess).toBe(true);
  });

  test('lambda in return type position', () => {
    // Super simple: return type has a lambda applied to a parameter
    const source = `
inductive Nat : Type where
  | Zero : Nat
  | Succ : Nat -> Nat

idNat : Nat -> Nat
idNat x = x

testReturnType : (n : Nat) -> Nat
testReturnType n = (\\(x : Nat) => x) n
`;
    const results = compileSource(source);
    const result = results.find(r => r.name === 'testReturnType');
    if (!result?.checkSuccess) {
      console.log('testReturnType errors:', result?.checkErrors?.map(e => e.message));
    }
    expect(result?.checkSuccess).toBe(true);
  });

  test('beta reduction in indexed type', () => {
    // Test that Vec A ((\x=>x)p) unifies with Vec A p
    const source = `
inductive Nat : Type where
  | Zero : Nat
  | Succ : Nat -> Nat

inductive Vec : Type -> Nat -> Type where
  | VNil : {A : Type} -> Vec A Zero
  | VCons : {A : Type} -> {n : Nat} -> A -> Vec A n -> Vec A (Succ n)

testBeta : {A : Type} -> {p : Nat} -> Vec A p -> Vec A ((\\(x : Nat) => x) p)
testBeta v = v
`;
    const results = compileSource(source);
    const result = results.find(r => r.name === 'testBeta');
    if (!result?.checkSuccess) {
      console.log('testBeta errors:', result?.checkErrors?.map(e => e.message));
    }
    expect(result?.checkSuccess).toBe(true);
  });

  test('identity lambda in named argument position', () => {
    // Simpler version: just using a named argument with an identity lambda
    const source = `
inductive Nat : Type where
  | Zero : Nat
  | Succ : Nat -> Nat

foo : {n : Nat} -> Nat
foo {n := x} = x

-- Using plain variable - should work
test1 : Nat
test1 = foo {n := Zero}

-- Using annotated identity lambda - should work (beta reduces to Zero)
test2 : Nat
test2 = foo {n := (\\(x : Nat) => x) Zero}

-- Using unannotated identity lambda - should work
test3 : Nat
test3 = foo {n := (\\x => x) Zero}
`;
    const results = compileSource(source);

    const test1 = results.find(r => r.name === 'test1');
    if (!test1?.checkSuccess) {
      console.log('test1 errors:', test1?.checkErrors?.map(e => e.message));
    }
    expect(test1?.checkSuccess).toBe(true);

    const test2 = results.find(r => r.name === 'test2');
    if (!test2?.checkSuccess) {
      console.log('test2 errors:', test2?.checkErrors?.map(e => e.message));
    }
    expect(test2?.checkSuccess).toBe(true);

    const test3 = results.find(r => r.name === 'test3');
    if (!test3?.checkSuccess) {
      console.log('test3 errors:', test3?.checkErrors?.map(e => e.message));
    }
    expect(test3?.checkSuccess).toBe(true);
  });
});
