/**
 * Test DPair without explicit fn parameter
 * This should work like in Lean/Agda if we implement bidirectional checking
 */
import { describe, test, expect } from 'vitest';
import { compileTTFromText } from './compile';

describe('DPair without explicit fn (bidirectional checking)', () => {
  test('simple case - should infer fn from expected type', () => {
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

plus : Nat -> Nat -> Nat
plus Zero m = m
plus (Succ n) m = Succ (plus n m)

inductive Equal : {A : Type} -> A -> A -> Type where
  refl : {A : Type} -> {a : A} -> Equal a a

record DPair (A : Type) (fn : A -> Type) where
  constructor MkDPair
  fst : A
  snd : fn fst

-- This SHOULD work without explicit {fn := ...}
-- The expected type tells us fn = \\n => Equal Zero (plus Zero n)
test1 : DPair Nat (\\n => Equal Zero (plus Zero n))
test1 = MkDPair Zero refl
`;

    const result = compileTTFromText(source);

    const decl = result.blocks
      .flatMap(b => b.declarations)
      .find(d => d.name === 'test1');

    if (decl && !decl.checkSuccess) {
      console.log('test1 ERRORS:');
      decl.checkErrors.forEach(e => console.log('  -', e.message));
    }

    // This will initially FAIL but should PASS after implementing the fix
    expect(result.success).toBe(true);
    expect(decl?.checkSuccess).toBe(true);
  });
});
