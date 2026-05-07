/**
 * Comprehensive tests for axiom K soundness.
 *
 * Axiom K (deletion rule) allows pattern matching on indexed families
 * where indices need to be unified. Without K, such matches should be rejected.
 *
 * Key test: UIP (Uniqueness of Identity Proofs) requires axiom K.
 */

import { describe, test, expect } from 'vitest';
import { compileTTFromText } from './compile';

const equalityPreamble = `
inductive Equal : {A : Type} -> A -> A -> Type where
  refl : {A : Type} -> {a : A} -> Equal a a
`;

const natPreamble = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat
`;

describe('Axiom K soundness', () => {

  // ============================================================================
  // UIP Tests - The canonical axiom K example
  // ============================================================================

  test('UIP should FAIL without axiom K', () => {
    const source = `${equalityPreamble}

-- UIP requires axiom K because it matches refl : Equal x x against Equal x y
-- This unifies x with y, requiring the deletion rule
uip : {A : Type} -> {x y : A} -> (p q : Equal x y) -> Equal p q
uip refl refl = refl
`;

    const result = compileTTFromText(source, { assumeK: false });
    const uipDecl = result.blocks.flatMap(b => (b as any).declarations).find((d: any) => d?.name === 'uip');

    expect(uipDecl?.checkSuccess).toBe(false);
    expect(uipDecl?.checkErrors?.[0]?.message).toContain('axiom K');
  });

  test('UIP should SUCCEED with @assumeK', () => {
    const source = `${equalityPreamble}

@assumeK

uip : {A : Type} -> {x y : A} -> (p q : Equal x y) -> Equal p q
uip refl refl = refl
`;

    const result = compileTTFromText(source);
    const uipDecl = result.blocks.flatMap(b => (b as any).declarations).find((d: any) => d?.name === 'uip');

    expect(uipDecl?.checkSuccess).toBe(true);
  });

  // ============================================================================
  // Sym and Trans - Should work WITHOUT K (indices already match)
  // ============================================================================

  test('sym should work WITHOUT axiom K (indices already equal)', () => {
    const source = `${equalityPreamble}

-- sym matches refl : Equal x x against Equal x y
-- After matching, we know x = y, so both sides have Equal x x
-- The indices already match definitionally, no deletion rule needed
sym : {A : Type} -> {x y : A} -> Equal x y -> Equal y x
sym refl = refl
`;

    const result = compileTTFromText(source, { assumeK: false });
    const symDecl = result.blocks.flatMap(b => (b as any).declarations).find((d: any) => d?.name === 'sym');

    expect(symDecl?.checkSuccess).toBe(true);
  });

  test('trans should work WITHOUT axiom K', () => {
    const source = `${equalityPreamble}

trans : {A : Type} -> {x y z : A} -> Equal x y -> Equal y z -> Equal x z
trans refl refl = refl
`;

    const result = compileTTFromText(source, { assumeK: false });
    const transDecl = result.blocks.flatMap(b => (b as any).declarations).find((d: any) => d?.name === 'trans');

    expect(transDecl?.checkSuccess).toBe(true);
  });

  // ============================================================================
  // Multiple refl patterns with DIFFERENT indices (should work)
  // ============================================================================

  test('Multiple refl patterns on different Equal types should work', () => {
    const source = `${equalityPreamble}
${natPreamble}

-- Two separate equality proofs on different indices
test : {A : Type} -> {x : A} -> Equal x x -> Equal x x -> Nat
test refl refl = Zero
`;

    const result = compileTTFromText(source);
    const testDecl = result.blocks.flatMap(b => (b as any).declarations).find((d: any) => d?.name === 'test');

    expect(testDecl?.checkSuccess).toBe(true);
  });

  // ============================================================================
  // Streicher's K - Another formulation that requires axiom K
  // ============================================================================

  test('Streicher K should FAIL without axiom K', () => {
    const source = `${equalityPreamble}
${natPreamble}

-- Streicher's K: matching refl against (p : Equal x x) requires K
-- because we're matching a concrete constructor against a variable
streichK : {A : Type} -> {x : A} -> (p : Equal x x) -> Equal p refl
streichK refl = refl
`;

    const result = compileTTFromText(source, { assumeK: false });
    const kDecl = result.blocks.flatMap(b => (b as any).declarations).find((d: any) => d?.name === 'streichK');

    expect(kDecl?.checkSuccess).toBe(false);
    expect(kDecl?.checkErrors?.[0]?.message).toContain('axiom K');
  });

  test('Streicher K should SUCCEED with @assumeK', () => {
    const source = `${equalityPreamble}
${natPreamble}

streichK : {A : Type} -> {x : A} -> (p : Equal x x) -> Equal p refl
streichK refl = refl
`;

    const result = compileTTFromText(source, { assumeK: true });
    const kDecl = result.blocks.flatMap(b => (b as any).declarations).find((d: any) => d?.name === 'streichK');

    expect(kDecl?.checkSuccess).toBe(true);
  });

  // ============================================================================
  // Non-dependent elimination (returning Type, not Equal)
  // ============================================================================

  test('Non-dependent elimination should work without K when indices match after substitution', () => {
    const source = `${equalityPreamble}
${natPreamble}

-- Even though we pattern match on Equal x y, we return Nat (non-dependent)
-- After the first refl matches, we know x = y, so the second refl sees Equal x x
sameIndices : {A : Type} -> {x y : A} -> (p q : Equal x y) -> Nat
sameIndices refl refl = Zero
`;

    const result = compileTTFromText(source);
    const testDecl = result.blocks.flatMap(b => (b as any).declarations).find((d: any) => d?.name === 'sameIndices');

    expect(testDecl?.checkSuccess).toBe(true);
  });

  // ============================================================================
  // Heterogeneous equality (if we had it) would also need K
  // ============================================================================

  test('Pattern matching that forces index equality should fail without K', () => {
    const source = `${equalityPreamble}
${natPreamble}

-- This function forces x and y to be equal by pattern matching
-- The RHS refl requires Equal p q, which needs K
forceEq : {A : Type} -> {x y : A} -> (p q : Equal x y) -> Equal p q
forceEq refl refl = refl
`;

    const result = compileTTFromText(source, { assumeK: false });
    const decl = result.blocks.flatMap(b => (b as any).declarations).find((d: any) => d?.name === 'forceEq');

    expect(decl?.checkSuccess).toBe(false);
    expect(decl?.checkErrors?.[0]?.message).toContain('axiom K');
  });

  // ============================================================================
  // Edge case: Pattern matching on refl in function position
  // ============================================================================

  test('Complex pattern with refl should respect K', () => {
    const source = `${equalityPreamble}
${natPreamble}

-- Pattern match that needs K in a more complex context
complexK : {A : Type} -> {x y : A} -> (f : Equal x y -> Nat) -> Equal x y -> Nat
complexK f refl = f refl
`;

    const result = compileTTFromText(source);
    const decl = result.blocks.flatMap(b => (b as any).declarations).find((d: any) => d?.name === 'complexK');

    // This should work - f expects Equal x y, and after matching refl we have x = y
    expect(decl?.checkSuccess).toBe(true);
  });

  // ============================================================================
  // Verify error messages are informative
  // ============================================================================

  test('Deletion rule error should mention axiom K and suggest @assumeK', () => {
    const source = `${equalityPreamble}

uip : {A : Type} -> {x y : A} -> (p q : Equal x y) -> Equal p q
uip refl refl = refl
`;

    const result = compileTTFromText(source, { assumeK: false });
    const uipDecl = result.blocks.flatMap(b => (b as any).declarations).find((d: any) => d?.name === 'uip');

    expect(uipDecl?.checkSuccess).toBe(false);
    const errorMsg = uipDecl?.checkErrors?.[0]?.message || '';

    // Check error message quality
    expect(errorMsg).toContain('axiom K');
    expect(errorMsg).toContain('@assumeK');
  });
});
