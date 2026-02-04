import { describe, test, expect } from 'vitest';
import { compileTTFromText } from './compile';

describe('With-desugaring with implicit parameters', () => {
  test('function with implicit params and with-clause', () => {
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
    console.log('Compilation result:', JSON.stringify(result, null, 2));

    // Check that all declarations type-check successfully
    for (const block of result.blocks) {
      for (const decl of block.declarations) {
        if (decl.checkSuccess === false) {
          console.log(`${decl.name} errors:`, decl.checkErrors.map((e: any) => e.message).join('\n'));
        }
        expect(decl.checkSuccess).toBe(true);
      }
    }
  });
});
