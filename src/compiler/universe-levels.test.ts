import { describe, test, expect } from 'vitest';
import { compileSource } from '../test-utils';

describe('undefined identifier in type level', () => {
  test('Type uhoh should be rejected - undefined level identifier', () => {
    const source = `
inductive Equal : {A : Type uhoh} -> A -> A -> Type where
  refl : {A : Type} -> {a : A} -> Equal a a
`;

    const results = compileSource(source);

    // This should fail during elaboration - 'uhoh' is not a valid level name
    expect(results[0]?.checkSuccess).toBe(false);
    const errors = results[0]?.checkErrors ?? [];
    expect(errors.some(e => e.message.includes("Undefined level variable 'uhoh'"))).toBe(true);
  });

  test('Type 0 should be valid - numeric universe level', () => {
    const source = `
inductive Equal : {A : Type 0} -> A -> A -> Type where
  refl : {A : Type} -> {a : A} -> Equal a a
`;
    const results = compileSource(source);
    expect(results[0]?.checkSuccess).toBe(true);
  });

  test('Universe polymorphic Equal with {u : ULevel} should parse u as Var', () => {
    const source = `
inductive Equal : {u : ULevel} -> {A : Type u} -> A -> A -> Type where
  refl : {u : ULevel} -> {A : Type u} -> {a : A} -> Equal a a
`;
    const results = compileSource(source);
    // The key test: u should be parsed as Var (bound), not Const
    const surfaceType = results[0]?.declarations?.[0]?.surfaceType;
    const aBinderDomain = (surfaceType as any)?.body?.domain;
    expect(aBinderDomain?.tag).toBe('Sort');
    expect(aBinderDomain?.level?.arg?.tag).toBe('Var');
    expect(aBinderDomain?.level?.arg?.index).toBe(0);
  });
});

describe('universe level inference - mismatched Type vs Type u should FAIL', () => {
  // These tests verify that a mismatch between inductive type's {A : Type} (= Type 0)
  // and constructor's {A : Type u} is correctly rejected.

  test('Type mismatch: inductive has Type, constructor has Type u - should FAIL', () => {
    const source = `
inductive Equal_ : {u : ULevel} -> {A : Type} -> A -> A -> Type where
  refl_ : {u : ULevel} -> {A : Type u} -> {a : A} -> Equal_ {u} a a
`;
    const results = compileSource(source);
    // This should fail: inductive has A : Type (= Type 0), constructor has A : Type u
    // When u is passed explicitly, we're saying Equal_ uses level u, but A in the inductive
    // is always at level 0, not u.
    expect(results[0]?.checkSuccess).toBe(false);
  });
});

describe('universe level inference - matching types should PASS', () => {
  // These tests verify that when both inductive and constructor have matching
  // universe levels (e.g., both use Type u), the definition is accepted.

  test('Type match: both have Type u - should PASS', () => {
    const source = `
inductive Equal_ : {u : ULevel} -> {A : Type u} -> A -> A -> Type where
  refl_ : {u : ULevel} -> {A : Type u} -> {a : A} -> Equal_ {u} a a
`;
    const results = compileSource(source);
    if (!results[0]?.checkSuccess) {
      console.log('Equal_ errors:', results[0]?.checkErrors?.map(e => e.message));
    }
    expect(results[0]?.checkSuccess).toBe(true);
  });

  test('Type match with implicit u - should PASS', () => {
    const source = `
inductive Equal' : {u : ULevel} -> {A : Type u} -> A -> A -> Type where
  refl' : {u : ULevel} -> {A : Type u} -> {a : A} -> Equal' a a
`;
    const results = compileSource(source);
    if (!results[0]?.checkSuccess) {
      console.log("Equal' a a errors:", results[0]?.checkErrors?.map(e => e.message));
    }
    expect(results[0]?.checkSuccess).toBe(true);
  });

  test('Type match with explicit {u} {A} - should PASS', () => {
    const source = `
inductive Equal'' : {u : ULevel} -> {A : Type u} -> A -> A -> Type where
  refl'' : {u : ULevel} -> {A : Type u} -> {a : A} -> Equal'' {u} {A} a a
`;
    const results = compileSource(source);
    if (!results[0]?.checkSuccess) {
      console.log("Equal'' errors:", results[0]?.checkErrors?.map(e => e.message));
    }
    expect(results[0]?.checkSuccess).toBe(true);
  });

  test('Infer u=0 when constructor has {A : Type} (matching inductive Type 0)', () => {
    // Here the inductive has {A : Type} (= Type 0), and the constructor also has {A : Type} (= Type 0)
    // So u should be inferred as level 0
    const source = `
inductive Equal''' : {u : ULevel} -> {A : Type} -> A -> A -> Type where
  refl0''' : {A : Type} -> {a : A} -> Equal''' a a
`;
    const results = compileSource(source);
    if (!results[0]?.checkSuccess) {
      console.log("Equal''' errors:", results[0]?.checkErrors?.map(e => e.message));
    }
    expect(results[0]?.checkSuccess).toBe(true);
  });

  test('Infer u=0 when constructor has {A : Type} and inductive has {A : Type u} - should PASS', () => {
    // The constructor has {A : Type} (= Type 0), but the inductive has {A : Type u}
    // When we apply Equal a a, u should be inferred as 0 because A : Type 0
    const source = `
inductive Equal : {u : ULevel} -> {A : Type u} -> A -> A -> Type where
  refl : {A : Type} -> {a : A} -> Equal a a
`;
    const results = compileSource(source);
    if (!results[0]?.checkSuccess) {
      console.log("Equal errors:", results[0]?.checkErrors?.map(e => e.message));
    }
    expect(results[0]?.checkSuccess).toBe(true);
  });

  test('Straightforward universe-polymorphic Equal with explicit u - should PASS', () => {
    // This is the standard way to define Equal with universe polymorphism
    // Both inductive and constructor have explicit u parameter
    const source = `
inductive Equal : {u : ULevel} -> {A : Type u} -> A -> A -> Type where
  refl : {u : ULevel} -> {A : Type u} -> {a : A} -> Equal a a
`;
    const results = compileSource(source);
    if (!results[0]?.checkSuccess) {
      console.log("Equal with explicit u errors:", results[0]?.checkErrors?.map(e => e.message));
    }
    expect(results[0]?.checkSuccess).toBe(true);
  });
});

describe('replace0 with non-universe-polymorphic Equal', () => {
  test('replace0 using Equal0 without universe polymorphism - should PASS', () => {
    const source = `
inductive Equal0 : {A : Type} -> A -> A -> Type where
  refl0 : {A : Type} -> {x : A} -> Equal0 x x

replace0 : {x y : Type} -> {f : Type -> Type} -> Equal0 x y -> f x -> f y
replace0 refl0 fx = fx
`;
    const results = compileSource(source);
    const equal0Result = results.find(r => r.name === 'Equal0');
    const replace0Result = results.find(r => r.name === 'replace0');

    if (!equal0Result?.checkSuccess) {
      console.log('Equal0 errors:', equal0Result?.checkErrors?.map(e => e.message));
    }
    if (!replace0Result?.checkSuccess) {
      console.log('replace0 errors:', replace0Result?.checkErrors?.map(e => e.message));
    }

    expect(equal0Result?.checkSuccess).toBe(true);
    expect(replace0Result?.checkSuccess).toBe(true);
  });
});

describe('inductive constructor universe level constraints', () => {
  test('constructor storing Type 1 value in Type result should FAIL', () => {
    // BadList takes A : Type 1 but returns Type (= Type 0)
    // BCons stores a value of type A, which requires universe level 2
    // But the result type BadList A is only at level 1
    // This violates: stored data must be at level ≤ result level
    const source = `
inductive BadList : Type 1 -> Type where
  BNil : {A : Type 1} -> BadList A
  BCons : {A : Type 1} -> A -> BadList A -> BadList A
`;
    const results = compileSource(source);

    if (results[0]?.checkSuccess) {
      console.log('BadList should have failed but passed!');
    }

    expect(results[0]?.checkSuccess).toBe(false);
    // The error should mention universe level violation
    const errors = results[0]?.checkErrors ?? [];
    expect(errors.some(e =>
      e.message.includes('universe') ||
      e.message.includes('level')
    )).toBe(true);
  });

  test('constructor NOT storing the Type 1 value should PASS', () => {
    // BNil just passes A through to BadList A without storing anything of type A
    // This is valid because we're not actually storing a Type 1 value
    const source = `
inductive OkList : Type 1 -> Type where
  ONil : {A : Type 1} -> OkList A
`;
    const results = compileSource(source);

    if (!results[0]?.checkSuccess) {
      console.log('OkList errors:', results[0]?.checkErrors?.map(e => e.message));
    }

    expect(results[0]?.checkSuccess).toBe(true);
  });

  test('constructor storing Type 0 value in Type result should PASS', () => {
    // GoodList takes A : Type (= Type 0) and returns Type (= Type 0)
    // GCons stores a value of type A, which requires universe level 1
    // The result type GoodList A is at level 1 (Type = Type 0, values at level 1)
    // This is valid: 1 ≤ 1
    const source = `
inductive GoodList : Type -> Type where
  GNil : {A : Type} -> GoodList A
  GCons : {A : Type} -> A -> GoodList A -> GoodList A
`;
    const results = compileSource(source);

    if (!results[0]?.checkSuccess) {
      console.log('GoodList errors:', results[0]?.checkErrors?.map(e => e.message));
    }

    expect(results[0]?.checkSuccess).toBe(true);
  });
});
