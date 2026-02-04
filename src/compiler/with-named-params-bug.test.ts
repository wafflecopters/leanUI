import { describe, test, expect } from 'vitest';
import { compileTTFromText } from './compile';

describe('With-desugaring named parameters bug', () => {
  test('simple function with implicit params and with-clause', () => {
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

foo : {a b : Nat} -> Nat
foo a b with a
  | Zero => b
  | Succ m => b
    `;

    const result = compileTTFromText(source);
    const auxDecl = result.blocks[1].declarations.find(d => d.name?.startsWith('foo-with'));

    expect(auxDecl?.surfaceType?.tag).toBe('MultiBinder');
    if (auxDecl?.surfaceType?.tag === 'MultiBinder') {
      expect(auxDecl.surfaceType.named).toBe(true); // This passes
    }
  });

  test('function with multiple clauses including constructor patterns', () => {
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

bar : {a b : Nat} -> Nat
bar Zero b = b
bar (Succ a) b with a
  | Zero => b
  | Succ m => b
    `;

    const result = compileTTFromText(source);
    const auxDecl = result.blocks[1].declarations.find(d => d.name?.startsWith('bar-with'));

    expect(auxDecl?.surfaceType?.tag).toBe('MultiBinder');
    if (auxDecl?.surfaceType?.tag === 'MultiBinder') {
      expect(auxDecl.surfaceType.named).toBe(true);
    }
  });

  test('EXACT leqCanonical code from user', () => {
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Equal : {A : Type} -> A -> A -> Type where
  refl : {A : Type} -> {a : A} -> Equal a a

inductive Leq : Nat -> Nat -> Type where
  LeqZero : {n : Nat} -> Leq Zero n
  LeqSucc : {n m : Nat} -> Leq n m -> Leq (Succ n) (Succ m)

leqCanonical : {a b : Nat} -> (p q : Leq a b) -> Equal p q
leqCanonical LeqZero LeqZero = refl
leqCanonical (LeqSucc pleq) (LeqSucc qleq) with leqCanonical pleq qleq
  | refl => refl
    `;

    const result = compileTTFromText(source);

    // Find leqCanonical and its auxiliary
    const leqDecl = result.blocks.flatMap(b => b.declarations).find(d => d.name === 'leqCanonical');
    const auxDecl = result.blocks.flatMap(b => b.declarations).find(d => d.name?.startsWith('leqCanonical-with'));

    console.log('leqCanonical surfaceType:', JSON.stringify(leqDecl?.surfaceType, null, 2).substring(0, 300));
    console.log('auxiliary surfaceType:', JSON.stringify(auxDecl?.surfaceType, null, 2).substring(0, 300));

    // THIS IS THE BUG!
    expect(auxDecl?.surfaceType?.tag).toBe('MultiBinder');
    if (auxDecl?.surfaceType?.tag === 'MultiBinder') {
      expect(auxDecl.surfaceType.named).toBe(true);
    }
  });
});
