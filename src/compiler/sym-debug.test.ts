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

    // Debug: print raw value JSON
    const kernelValue = symDecl?.kernelValue;
    if (kernelValue?.tag === 'Match' && kernelValue.clauses?.[0]) {
      const clause = kernelValue.clauses[0];
      console.log('clause.rhs JSON:', JSON.stringify(clause.rhs, null, 2));
      console.log('clause.contextNames:', clause.contextNames);
      console.log('clause.metaVars keys:', clause.metaVars ? Array.from(clause.metaVars.keys()) : 'none');
      // Check if any metaVar has a solution for _implicit2
      if (clause.metaVars) {
        for (const [key, val] of clause.metaVars) {
          console.log(`  metaVar ${key}:`, val.solution ? 'SOLVED' : 'UNSOLVED', val.type?.tag);
        }
      }
    }

    expect(symDecl?.checkSuccess).toBe(true);

    // Check for unsolved holes in value
    const prettyValue = symDecl?.prettyValue || '';

    // These specific patterns indicate unsolved holes:
    // Note: ?0, ?1, etc. are pattern variable names, NOT unsolved holes
    const hasUnsolvedHoles =
      prettyValue.includes('?_implicit') ||  // Implicit arg holes (like ?_implicit2)
      prettyValue.includes('_pad');          // Pattern padding holes (like _pad0)

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
