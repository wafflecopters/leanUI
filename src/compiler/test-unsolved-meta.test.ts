import { describe, test, expect } from 'vitest';
import { compileTTFromText } from './compile';

describe('Unsolved meta in let binding', () => {
  test('underscore in let binding should produce error about unsolved meta', () => {
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

plus : Nat -> Nat -> Nat
plus Zero m = m
plus (Succ n) m = Succ (plus n m)

inductive Equal : {A : Type} -> A -> A -> Type where
  refl : {A : Type} -> {a : A} -> Equal a a

inductive Leq : Nat -> Nat -> Type where
  LeqZero : {b : Nat} -> Leq Zero b
  LeqSucc : {a b : Nat} -> Leq a b -> Leq (Succ a) (Succ b)

record DPair (A : Type) (fn : A -> Type) where
  constructor MkDPair
  fst : A
  snd : fn fst

leqImpliesSum : (a b : Nat) -> Leq a b -> DPair Nat (\\n => Equal b (plus a n))
leqImpliesSum Zero b LeqZero = MkDPair b refl
leqImpliesSum (Succ a) (Succ b) (LeqSucc leq) = let p = _ in
  ?FOO
`;

    const result = compileTTFromText(source);

    console.log('Compile success:', result.success);

    const decl = result.blocks
      .flatMap(b => b.declarations)
      .find(d => d.name === 'leqImpliesSum');

    console.log('Declaration found:', !!decl);
    console.log('Check success:', decl?.checkSuccess);

    if (decl && !decl.checkSuccess) {
      console.log('Errors:', decl.checkErrors.map(e => e.message));
    }

    if (decl && decl.checkSuccess) {
      console.log('Pretty value:', decl.prettyValue);

      // Debug: check the actual kernel value structure
      if (decl.kernelValue && decl.kernelValue.tag === 'Match') {
        const clause2 = decl.kernelValue.clauses[1];
        console.log('\nClause 2 RHS:');
        console.log(JSON.stringify(clause2?.rhs, null, 2));
      }
    }

    // The underscore should cause an unsolved meta error
    // BUT: named holes like ?FOO are allowed, and metas for type inference are also allowed
    // Only actual wildcards (_) should be errors
    expect(decl?.checkSuccess).toBe(false);
    expect(decl?.checkErrors.some(e => e.message.includes('unsolved') || e.message.includes('wildcard'))).toBe(true);
  });
});
