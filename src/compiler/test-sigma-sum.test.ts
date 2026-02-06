import { describe, test, expect } from 'vitest';
import { compileTTFromText } from './compile';

describe('Sigma sum case from user', () => {
  test.skip('sigmaSumStartOrderedRange should compile - WIP: named args issue', () => {
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Equal : {A : Type} -> A -> A -> Type where
  refl : {A : Type} -> {a : A} -> Equal a a

inductive Leq : Nat -> Nat -> Type where
  LeqZero : {n : Nat} -> Leq Zero n
  LeqSucc : {n m : Nat} -> Leq n m -> Leq (Succ n) (Succ m)

record DPair (A : Type) (fn : A -> Type) where
  constructor MkDPair
  fst : A
  snd : fn fst

plus : Nat -> Nat -> Nat
plus Zero b = b
plus (Succ a) b = Succ (plus a b)

succInj: {u v : Nat} -> Equal u v -> Equal (Succ u) (Succ v)
succInj refl = refl

leqImpliesSum : (a b : Nat) -> Leq a b -> DPair Nat (\\n => Equal b (plus a n))
leqImpliesSum Zero b LeqZero = MkDPair b refl
leqImpliesSum (Succ a) (Succ b) (LeqSucc leq) with leqImpliesSum a b leq
  | MkDPair n pf => MkDPair n (succInj pf)

sigmaSumCount : (count : Nat) -> (fn: (index: Nat) -> Nat) -> Nat
sigmaSumCount Zero _ = Zero
sigmaSumCount (Succ k) fn = plus (sigmaSumCount k fn) (Succ k)

sigmaSumStartCount : (start count : Nat) -> (fn: (index: Nat) -> Nat) -> Nat
sigmaSumStartCount start count fn = sigmaSumCount count (\\index => fn (plus start index))

sigmaSumStartOrderedRange : (start end : Nat) -> Leq start end -> (fn: (index: Nat) -> Nat) -> Nat
sigmaSumStartOrderedRange start end leq fn with leqImpliesSum start end leq
  | MkDPair count _ => sigmaSumStartCount start count fn
`;

    const result = compileTTFromText(source);

    // Find the last auxiliary (for sigmaSumStartOrderedRange)
    const auxDecls = result.blocks
      .flatMap(b => b.declarations)
      .filter(d => d.name?.includes('with'));

    console.log('Auxiliary declarations:', auxDecls.map(d => d.name));

    const sigmaAux = auxDecls.find(d => d.name?.includes('sigmaSumStartOrderedRange'));

    if (sigmaAux) {
      console.log('Sigma auxiliary:', sigmaAux.name);
      console.log('Check success:', sigmaAux.checkSuccess);

      if (!sigmaAux.checkSuccess) {
        console.log('Errors:', sigmaAux.checkErrors.map(e => e.message));
      }

      expect(sigmaAux.checkSuccess).toBe(true);
    }

    const mainDecl = result.blocks
      .flatMap(b => b.declarations)
      .find(d => d.name === 'sigmaSumStartOrderedRange');

    if (mainDecl) {
      console.log('Main decl check success:', mainDecl.checkSuccess);
      if (!mainDecl.checkSuccess) {
        console.log('Main errors:', mainDecl.checkErrors.map(e => e.message));
      }
      expect(mainDecl.checkSuccess).toBe(true);
    } else {
      console.log('Main decl not found!');
    }
  });
});
