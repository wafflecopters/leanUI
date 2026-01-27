/**
 * Test universe checking for inductives.
 *
 * Universe level checking now supports symbolic comparison of universe levels,
 * properly detecting violations even when universe variables are involved.
 */

import { describe, test, expect } from 'vitest';
import { compileTTFromText } from './compile';

describe('Universe Checking for Inductives', () => {
  test('DPair with single universe variable should fail (Type at result, but A at level u)', () => {
    const source = `
inductive DPair1 : {u : ULevel} -> (A : Type u) -> (B : A -> Type) -> Type where
  MkDPair1: {u : ULevel} -> {A : Type u} -> {B : A -> Type} -> (a : A) -> B a -> DPair1 A B
`;
    const result = compileTTFromText(source);
    const decl = result.blocks[0]?.declarations[0];

    // This SHOULD fail because result is Type (level 0) but constructor arg `a : A` is at level u
    // If u > 0, the inductive is too small
    expect(decl?.checkSuccess).toBe(false);
  });

  test('DPair with two universe variables should fail (Type at result, but args at u and v)', () => {
    const source = `
inductive DPair2 : {u v : ULevel} -> (A : Type u) -> (B : A -> Type v) -> Type where
  MkDPair2: {u v : ULevel} -> {A : Type u} -> {B : A -> Type v} -> (a : A) -> B a -> DPair2 A B
`;
    const result = compileTTFromText(source);
    const decl = result.blocks[0]?.declarations[0];

    // This SHOULD fail - result is Type (level 0) but args are at levels u and v
    expect(decl?.checkSuccess).toBe(false);
  });

  test('DPair with UMax should pass', () => {
    const source = `
inductive DPair3 : {u v : ULevel} -> (A : Type u) -> (B : A -> Type v) -> Type (UMax u v) where
  MkDPair3: {u v : ULevel} -> {A : Type u} -> {B : A -> Type v} -> (a : A) -> B a -> DPair3 A B
`;
    const result = compileTTFromText(source);
    const decl = result.blocks[0]?.declarations[0];

    // This SHOULD pass - result level is UMax u v which covers both argument universes
    expect(decl?.checkSuccess).toBe(true);
  });

  test('DPair with Type u result should fail (second arg is at level v)', () => {
    // This tests that the de Bruijn index shifting is correct when comparing
    // data argument levels to the result level
    const source = `
inductive DPair4 : {u v : ULevel} -> (A : Type u) -> (B : A -> Type v) -> Type u where
  MkDPair4: {u v : ULevel} -> {A : Type u} -> {B : A -> Type v} -> (a : A) -> B a -> DPair4 A B
`;
    const result = compileTTFromText(source);
    const decl = result.blocks[0]?.declarations[0];

    // This SHOULD fail - result is Type u but B a is at Type v, and v might be > u
    expect(decl?.checkSuccess).toBe(false);
  });

  // Concrete universe levels should still be checked correctly
  test('concrete level violation is caught', () => {
    // List stores values at level 0, so List must be at Type (level 1), not Prop (level 0)
    const source = `
inductive BadList : Type -> Prop where
  BNil : {A : Type} -> BadList A
  BCons : {A : Type} -> A -> BadList A -> BadList A
`;
    const result = compileTTFromText(source);
    const decl = result.blocks[0]?.declarations[0];

    // This should fail because A : Type means values of A are at level 0,
    // but Prop is Sort 0 which can only contain proof-irrelevant data
    expect(decl?.checkSuccess).toBe(false);
  });
});
