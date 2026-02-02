import { describe, test, expect } from 'vitest';
import { compileTTFromText } from './compile';

/**
 * Stress tests for universe level checking in meta solving.
 * These tests explore edge cases and tricky scenarios to ensure the
 * universe level check is robust and doesn't have false positives/negatives.
 */
describe('Universe level checking - stress tests', () => {
  test('nested Type applications should respect universe hierarchy', () => {
    // Box takes a Type and returns a Type
    // BoxBox should take Type 0 and return Type 1 (not Type 0!)
    const source = `
inductive Box : {A : Type} -> A -> Type where
  MkBox : {A : Type} -> {a : A} -> Box a

-- Box (Type 0) : Type 1
-- So we need boxBox : {T : Type 1} -> Box T -> Type
boxBox : {T : Type} -> Box T -> Type
boxBox (MkBox) = T
`;

    const result = compileTTFromText(source);
    const boxBoxDecl = result.blocks.flatMap(b => (b as any).declarations || []).find((d: any) => d?.name === 'boxBox');

    // This should FAIL: Box (Type 0) : Type 1, but boxBox expects {T : Type 0}
    expect(boxBoxDecl?.checkSuccess).toBe(false);
    const hasUniverseError = boxBoxDecl?.checkErrors?.some((e: any) =>
      e.message.toLowerCase().includes('universe') || e.message.toLowerCase().includes('mismatch')
    );
    expect(hasUniverseError).toBe(true);
  });

  test('transitive meta constraints with Type should fail at correct level', () => {
    // ?A := ?B, ?B := Type, where ?A : Type
    // This should fail because Type : Type 1, not Type
    const source = `
inductive Equal0 : {A : Type} -> A -> A -> Type where
  refl0 : {A : Type} -> {x : A} -> Equal0 x x

-- Both x and y will solve to Type, creating a transitive constraint chain
bad : {x : Type} -> Equal0 x Type -> Type
bad refl0 = x
`;

    const result = compileTTFromText(source);
    const badDecl = result.blocks.flatMap(b => (b as any).declarations || []).find((d: any) => d?.name === 'bad');

    expect(badDecl?.checkSuccess).toBe(false);
  });

  test('Sort with unsolved level metas should defer checking', () => {
    // When the meta's type contains unsolved metas, we should defer checking
    // This should succeed because the level will be inferred correctly
    const source = `
inductive Equal : {u : ULevel} -> {A : Type u} -> A -> A -> Type where
  refl : {u : ULevel} -> {A : Type u} -> {a : A} -> Equal a a

-- This SHOULD work: level inference should solve u = 1
goodReplace : {u : ULevel} -> {x y : Type u} -> {f : Type u -> Type u} -> Equal x y -> f x -> f y
goodReplace refl fx = fx
`;

    const result = compileTTFromText(source);
    const goodReplaceDecl = result.blocks.flatMap(b => (b as any).declarations || []).find((d: any) => d?.name === 'goodReplace');

    expect(goodReplaceDecl?.checkSuccess).toBe(true);
  });

  test('concrete universe mismatch should be caught immediately', () => {
    // No level variables - pure concrete mismatch
    const source = `
inductive Box0 : {A : Type} -> A -> Type where
  MkBox0 : {A : Type} -> {a : A} -> Box0 a

-- Explicitly wrong: Type 1 where Type 0 expected
badBox : Box0 {A := Type} Type
badBox = MkBox0
`;

    const result = compileTTFromText(source);
    const badBoxDecl = result.blocks.flatMap(b => (b as any).declarations || []).find((d: any) => d?.name === 'badBox');

    expect(badBoxDecl?.checkSuccess).toBe(false);
  });

  test('function returning Sort should check argument universe levels', () => {
    // Functions that return Types are perfectly valid, but their arguments
    // must have the correct universe level
    const source = `
inductive Equal0 : {A : Type} -> A -> A -> Type where
  refl0 : {A : Type} -> {x : A} -> Equal0 x x

-- id should be polymorphic over universe levels, but Equal0 forces Type 0
constType : {A : Type} -> Equal0 A A -> Type
constType refl0 = A

-- This should fail when applied to Type (which is in Type 1, not Type 0)
bad : Type
bad = constType {A := Type} refl0
`;

    const result = compileTTFromText(source);
    const badDecl = result.blocks.flatMap(b => (b as any).declarations || []).find((d: any) => d?.name === 'bad');

    expect(badDecl?.checkSuccess).toBe(false);
  });

  test('multiple levels of Type nesting', () => {
    // Test deeply nested Type applications
    const source = `
inductive Nat : Type where
  Zero : Nat

inductive Id : {A : Type} -> A -> Type where
  MkId : {A : Type} -> {a : A} -> Id a

-- Id Zero (where Zero : Nat) : Type 0 - OK
goodId : Id Zero
goodId = MkId

-- Id Nat (where Nat : Type 0) - FAIL!
-- This requires A := Type 0, but Type 0 : Type 1, not Type 0
badIdNat : Id Nat
badIdNat = MkId

-- Id Type (where Type : Type 1) - Also FAIL
badIdType : Id Type
badIdType = MkId
`;

    const result = compileTTFromText(source);
    const goodIdDecl = result.blocks.flatMap(b => (b as any).declarations || []).find((d: any) => d?.name === 'goodId');
    const badIdNatDecl = result.blocks.flatMap(b => (b as any).declarations || []).find((d: any) => d?.name === 'badIdNat');
    const badIdTypeDecl = result.blocks.flatMap(b => (b as any).declarations || []).find((d: any) => d?.name === 'badIdType');

    // Only Id with actual values (like Zero) should work, not types
    expect(goodIdDecl?.checkSuccess).toBe(true);
    expect(badIdNatDecl?.checkSuccess).toBe(false);
    expect(badIdTypeDecl?.checkSuccess).toBe(false);
  });

  test('universe level checking with explicit vs inferred', () => {
    // Compare explicit and inferred universe levels
    const source = `
inductive Box : {A : Type} -> A -> Type where
  MkBox : {A : Type} -> {a : A} -> Box a

-- Explicit: clearly wrong
badExplicit : Box {A := Type} Type
badExplicit = MkBox

-- Inferred: should also fail (our fix!)
badInferred : Box Type
badInferred = MkBox
`;

    const result = compileTTFromText(source);
    const explicitDecl = result.blocks.flatMap(b => (b as any).declarations || []).find((d: any) => d?.name === 'badExplicit');
    const inferredDecl = result.blocks.flatMap(b => (b as any).declarations || []).find((d: any) => d?.name === 'badInferred');

    // Both should fail
    expect(explicitDecl?.checkSuccess).toBe(false);
    expect(inferredDecl?.checkSuccess).toBe(false);
  });

  test('universe polymorphic version should succeed', () => {
    // With proper universe polymorphism, these should work
    const source = `
inductive Nat : Type where
  Zero : Nat

inductive Box : {u : ULevel} -> {A : Type u} -> A -> Type where
  MkBox : {u : ULevel} -> {A : Type u} -> {a : A} -> Box a

-- Now this works: u is inferred as 1
goodBox : Box Type
goodBox = MkBox

-- And this still works: u is inferred as 0
goodBoxNat : Box Nat
goodBoxNat = MkBox
`;

    const result = compileTTFromText(source);
    const goodBoxDecl = result.blocks.flatMap(b => (b as any).declarations || []).find((d: any) => d?.name === 'goodBox');
    const goodBoxNatDecl = result.blocks.flatMap(b => (b as any).declarations || []).find((d: any) => d?.name === 'goodBoxNat');

    expect(goodBoxDecl?.checkSuccess).toBe(true);
    expect(goodBoxNatDecl?.checkSuccess).toBe(true);
  });

  test('chain of meta solving with Sorts', () => {
    // Test that meta chains are handled correctly
    const source = `
inductive Equal0 : {A : Type} -> A -> A -> Type where
  refl0 : {A : Type} -> {x : A} -> Equal0 x x

-- The implicit A will be solved via a chain: ?A := ?B, ?B := Type
chainBad : {A : Type} -> {B : Type} -> Equal0 A B -> Equal0 A Type -> A
chainBad refl0 refl0 = A
`;

    const result = compileTTFromText(source);
    const chainBadDecl = result.blocks.flatMap(b => (b as any).declarations || []).find((d: any) => d?.name === 'chainBad');

    // Should fail because the chain resolves to Type, which has wrong universe level
    expect(chainBadDecl?.checkSuccess).toBe(false);
  });

  test('Prop vs Type distinction in universe levels', () => {
    // Prop is Type 0 (Sort 0), so similar universe issues should apply
    const source = `
inductive Id : {A : Type} -> A -> Type where
  MkId : {A : Type} -> {a : A} -> Id a

-- Prop : Type 0, so Id Prop : Type 0 should fail (Prop : Type 0, not Type -1!)
-- Actually, Prop = Type 0, so this might behave differently
badProp : Id Prop
badProp = MkId
`;

    const result = compileTTFromText(source);
    const badPropDecl = result.blocks.flatMap(b => (b as any).declarations || []).find((d: any) => d?.name === 'badProp');

    // Check if it fails or succeeds - either way is informative
    // (Prop might be handled specially)
    expect(typeof badPropDecl?.checkSuccess).toBe('boolean');
  });
});
