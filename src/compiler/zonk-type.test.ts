/**
 * Tests for zonking type signatures.
 *
 * Ensures that implicit arguments in type signatures are properly resolved
 * and don't show up as unsolved metas in the pretty-printed output.
 */

import { describe, test, expect } from 'vitest';
import { compileTTFromText } from './compile';

describe('Type signature zonking', () => {
  test('zeroNeqSucc should not have unsolved metas in type', () => {
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Void : Type where

inductive Equal : {u : ULevel} -> {A : Type u} -> A -> A -> Type where
  refl : {u : ULevel} -> {A : Type u} -> {a : A} -> Equal a a

zeroNeqSucc : {n : Nat} -> Equal Zero (Succ n) -> Void
zeroNeqSucc refl = #absurd
`;
    const result = compileTTFromText(source);
    const allDecls = result.blocks.flatMap(b => (b as any).declarations ?? []);

    const znsDecl = allDecls.find((d: any) => d?.name === 'zeroNeqSucc');

    console.log('checkSuccess:', znsDecl?.checkSuccess);
    console.log('checkErrors:', znsDecl?.checkErrors?.map((e: any) => e?.message));
    console.log('prettyType:', znsDecl?.prettyType);
    console.log('prettyValue:', znsDecl?.prettyValue);

    // The type should NOT have unsolved metas
    const prettyType = znsDecl?.prettyType || '';
    const hasUnsolvedMeta = prettyType.includes('?_implicit') || prettyType.includes('?m');

    if (hasUnsolvedMeta) {
      console.log('BUG: Unsolved metas in prettyType');
      // Check if the metas are in the raw kernel type
      console.log('kernelType:', JSON.stringify(znsDecl?.kernelType, null, 2));
    }

    expect(hasUnsolvedMeta).toBe(false);
  });

  test('simple Equal usage should infer implicits', () => {
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Equal : {u : ULevel} -> {A : Type u} -> A -> A -> Type where
  refl : {u : ULevel} -> {A : Type u} -> {a : A} -> Equal a a

-- Simple test: Equal Zero Zero should infer u and A
test : Equal Zero Zero
test = refl
`;
    const result = compileTTFromText(source);
    const allDecls = result.blocks.flatMap(b => (b as any).declarations ?? []);

    const testDecl = allDecls.find((d: any) => d?.name === 'test');

    console.log('simple Equal - checkSuccess:', testDecl?.checkSuccess);
    console.log('simple Equal - prettyType:', testDecl?.prettyType);
    console.log('simple Equal - prettyValue:', testDecl?.prettyValue);

    // Should not have unsolved metas
    const prettyType = testDecl?.prettyType || '';
    expect(prettyType).not.toContain('?_implicit');
  });

  test('Equal in function signature should infer implicits', () => {
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Equal : {u : ULevel} -> {A : Type u} -> A -> A -> Type where
  refl : {u : ULevel} -> {A : Type u} -> {a : A} -> Equal a a

-- Function with Equal in signature
foo : Equal Zero Zero -> Nat
foo refl = Zero
`;
    const result = compileTTFromText(source);
    const allDecls = result.blocks.flatMap(b => (b as any).declarations ?? []);

    const fooDecl = allDecls.find((d: any) => d?.name === 'foo');

    console.log('foo - checkSuccess:', fooDecl?.checkSuccess);
    console.log('foo - prettyType:', fooDecl?.prettyType);

    const prettyType = fooDecl?.prettyType || '';
    expect(prettyType).not.toContain('?_implicit');
  });

  test('Equal with implicit n in signature', () => {
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Void : Type where

inductive Equal : {u : ULevel} -> {A : Type u} -> A -> A -> Type where
  refl : {u : ULevel} -> {A : Type u} -> {a : A} -> Equal a a

-- This is the problematic case
bar : {n : Nat} -> Equal Zero (Succ n) -> Void
bar refl = #absurd
`;
    const result = compileTTFromText(source);
    const allDecls = result.blocks.flatMap(b => (b as any).declarations ?? []);

    const barDecl = allDecls.find((d: any) => d?.name === 'bar');

    console.log('bar - checkSuccess:', barDecl?.checkSuccess);
    console.log('bar - checkErrors:', barDecl?.checkErrors?.map((e: any) => e?.message));
    console.log('bar - prettyType:', barDecl?.prettyType);

    const prettyType = barDecl?.prettyType || '';

    // The type should be fully resolved:
    // {n : Nat} -> Equal {u:=0} {A:=Nat} Zero (Succ n) -> Void
    console.log('Has unsolved metas:', prettyType.includes('?_implicit'));

    expect(prettyType).not.toContain('?_implicit');
  });
});
