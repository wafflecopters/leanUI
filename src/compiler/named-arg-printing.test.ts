/**
 * Tests for named argument pretty printing in elaborated terms.
 *
 * When we print an elaborated App term, implicit arguments should
 * be displayed with their parameter names, e.g., `Foo {K:=a} b {Lp:=y}`.
 */

import { describe, test, expect } from 'vitest';
import { compileTTFromText } from './compile';

describe('Named argument pretty printing', () => {
  test('implicit args in elaborated term show parameter names', () => {
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Equal : {A : Type} -> A -> A -> Type where
  refl : {A : Type} -> {a : A} -> Equal a a

-- Test: refl's implicit args should be labeled in prettyValue
test : Equal Zero Zero
test = refl
`;
    const result = compileTTFromText(source);
    const allDecls = result.blocks.flatMap(b => (b as any).declarations ?? []);
    const testDecl = allDecls.find((d: any) => d?.name === 'test');

    expect(testDecl?.checkSuccess).toBe(true);

    // The prettyValue should show refl with named implicit args
    // e.g., "(refl {A:=Nat} {a:=Zero})" instead of just "(refl Nat Zero)"
    const prettyValue = testDecl?.prettyValue || '';
    console.log('prettyValue:', prettyValue);

    expect(prettyValue).toContain('{A:=');
    expect(prettyValue).toContain('{a:=');
  });

  test('mixed implicit and explicit args show correct labels', () => {
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Bool : Type where
  True : Bool
  False : Bool

-- Function with mixed implicit/explicit args
idPair : {A : Type} -> A -> {B : Type} -> B -> A
idPair {A} a {B} b = a

test : Nat
test = idPair {A:=Nat} Zero {B:=Bool} True
`;
    const result = compileTTFromText(source);
    const allDecls = result.blocks.flatMap(b => (b as any).declarations ?? []);
    const testDecl = allDecls.find((d: any) => d?.name === 'test');

    expect(testDecl?.checkSuccess).toBe(true);

    // Should show the implicit args with their names
    const prettyValue = testDecl?.prettyValue || '';
    console.log('prettyValue:', prettyValue);

    expect(prettyValue).toContain('{A:=');
    expect(prettyValue).toContain('{B:=');
  });

  test('inductive constructor with implicits shows named args', () => {
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Equal : {A : Type} -> A -> A -> Type where
  refl : {A : Type} -> {a : A} -> Equal a a

-- cong has implicits: {A B : Type} -> {x y : A} -> (f : A -> B) -> Equal x y -> Equal (f x) (f y)
cong : {A B : Type} -> {x y : A} -> (f : A -> B) -> Equal x y -> Equal (f x) (f y)
cong f refl = refl

test : Equal (Succ Zero) (Succ Zero)
test = cong Succ (refl {A:=Nat} {a:=Zero})
`;
    const result = compileTTFromText(source);
    const allDecls = result.blocks.flatMap(b => (b as any).declarations ?? []);
    const testDecl = allDecls.find((d: any) => d?.name === 'test');

    expect(testDecl?.checkSuccess).toBe(true);

    const prettyValue = testDecl?.prettyValue || '';
    console.log('prettyValue:', prettyValue);

    // cong should show its implicit args
    expect(prettyValue).toContain('{A:=');
    expect(prettyValue).toContain('{B:=');
  });

  test('explicit args do not get braces', () => {
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

plus : Nat -> Nat -> Nat
plus Zero n = n
plus (Succ m) n = Succ (plus m n)

test : Nat
test = plus Zero (Succ Zero)
`;
    const result = compileTTFromText(source);
    const allDecls = result.blocks.flatMap(b => (b as any).declarations ?? []);
    const testDecl = allDecls.find((d: any) => d?.name === 'test');

    expect(testDecl?.checkSuccess).toBe(true);

    const prettyValue = testDecl?.prettyValue || '';
    console.log('prettyValue:', prettyValue);

    // plus has no implicit args, so no braces
    // Should be something like "(plus Zero (Succ Zero))"
    expect(prettyValue).not.toContain('{');
    expect(prettyValue).not.toContain(':=');
  });
});
