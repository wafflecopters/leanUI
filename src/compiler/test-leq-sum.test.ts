/**
 * Test leqImpliesSum with DPair
 */
import { describe, test, expect } from 'vitest';
import { compileTTFromText } from './compile';

describe('leqImpliesSum with DPair', () => {
  test('leqImpliesSum type checks with corrected signature', () => {
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
leqImpliesSum Zero b LeqZero = MkDPair {fn := \\n => Equal b (plus Zero n)} b refl
leqImpliesSum (Succ a) b (LeqSucc s) = ?hole
`;

    console.log('=== COMPILING ===');
    const result = compileTTFromText(source);
    console.log('Compile success:', result.success);

    if (!result.success) {
      console.log('\\n=== ERRORS ===');
      console.log('Num blocks:', result.blocks.length);
      result.blocks.forEach((block, i) => {
        console.log(`Block ${i}: numDecls: ${block.declarations.length}`);
        block.declarations.forEach(decl => {
          console.log(`  Decl: ${decl.name}, checkSuccess: ${decl.checkSuccess}, numErrors: ${decl.checkErrors.length}`);
          if (decl.checkErrors.length > 0) {
            console.log(`    ${decl.name} errors:`);
            decl.checkErrors.forEach(e => console.log('      -', e.message));
          }
        });
      });
    }

    const decl = result.blocks
      .flatMap(b => b.declarations)
      .find(d => d.name === 'leqImpliesSum');

    console.log('\\n=== DECLARATION ===');
    console.log('Found leqImpliesSum:', !!decl);
    console.log('Check success:', decl?.checkSuccess);
    console.log('Pretty type:', decl?.prettyType);
    console.log('Pretty value:', decl?.prettyValue);

    expect(result.success).toBe(true);
    expect(decl?.checkSuccess).toBe(true);
  });
});
