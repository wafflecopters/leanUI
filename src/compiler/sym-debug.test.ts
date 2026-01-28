/**
 * Debug test for sym zonking issue
 */

import { describe, test, expect } from 'vitest';
import { compileTTFromText } from './compile';

describe('sym zonking debug', () => {
  test('sym should not have unsolved holes in value', () => {
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Equal : {A : Type} -> A -> A -> Type where
  refl : {A : Type} -> {a : A} -> Equal a a

sym : {A : Type} -> {u v : A} -> Equal u v -> Equal v u
sym refl = refl
`;
    const result = compileTTFromText(source);
    const allDecls = result.blocks.flatMap(b => (b as any).declarations ?? []);

    const symDecl = allDecls.find((d: any) => d?.name === 'sym');

    console.log('sym checkSuccess:', symDecl?.checkSuccess);
    console.log('sym checkErrors:', symDecl?.checkErrors?.map((e: any) => e?.message));
    console.log('sym prettyType:', symDecl?.prettyType);
    console.log('sym prettyValue:', symDecl?.prettyValue);

    expect(symDecl?.checkSuccess).toBe(true);

    // Check for unsolved holes in value
    const prettyValue = symDecl?.prettyValue || '';

    // These specific patterns indicate unsolved holes:
    const hasUnsolvedHoles =
      prettyValue.includes('?_implicit') ||  // Implicit arg holes
      prettyValue.includes('_pad') ||        // Pattern padding holes
      (prettyValue.match(/\?\d+/) !== null); // Numeric hole IDs like ?27, ?29

    if (hasUnsolvedHoles) {
      console.log('BUG: Unsolved holes in prettyValue');
    }

    expect(hasUnsolvedHoles).toBe(false);
  });

  test('simple pattern match should zonk properly', () => {
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Equal : {A : Type} -> A -> A -> Type where
  refl : {A : Type} -> {a : A} -> Equal a a

-- Simpler case: just return the proof unchanged
idProof : {A : Type} -> {x : A} -> Equal x x -> Equal x x
idProof refl = refl
`;
    const result = compileTTFromText(source);
    const allDecls = result.blocks.flatMap(b => (b as any).declarations ?? []);

    const idProofDecl = allDecls.find((d: any) => d?.name === 'idProof');

    console.log('idProof checkSuccess:', idProofDecl?.checkSuccess);
    console.log('idProof prettyValue:', idProofDecl?.prettyValue);

    expect(idProofDecl?.checkSuccess).toBe(true);
  });
});
