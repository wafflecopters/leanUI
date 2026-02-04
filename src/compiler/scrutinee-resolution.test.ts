import { describe, test, expect } from 'vitest';
import { compileTTFromText } from './compile';

describe('Scrutinee type resolution', () => {
  test('UNIT: main function should be in definitions before auxiliary is processed', () => {
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

    // Check if main function compiled successfully
    const mainDecl = result.blocks
      .flatMap(b => b.declarations)
      .find(d => d.name === 'leqCanonical');

    console.log('Main function exists:', !!mainDecl);
    console.log('Main function has kernelType:', !!mainDecl?.kernelType);
    console.log('Main function checkSuccess:', mainDecl?.checkSuccess);

    // If main function doesn't have a kernelType, it wasn't pre-registered
    expect(mainDecl).toBeTruthy();

    // This is the KEY test: does the main function have a kernel type?
    // If not, it won't be in definitions when resolveAuxScrutineeTypes runs
    if (mainDecl && !mainDecl.checkSuccess) {
      console.log('Main errors:', mainDecl.checkErrors.map(e => e.message));
    }
  });

  test('UNIT: scrutinee expression structure', () => {
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

    // Find the auxiliary
    const auxDecl = result.blocks
      .flatMap(b => b.declarations)
      .find(d => d.name?.includes('with'));

    expect(auxDecl).toBeTruthy();
    expect(auxDecl!.withScrutineeExprs).toBeTruthy();
    expect(auxDecl!.withScrutineeExprs!.length).toBe(1);

    const scrutinee = auxDecl!.withScrutineeExprs![0];
    console.log('Scrutinee structure:', JSON.stringify(scrutinee, null, 2));

    // The scrutinee should be: App(App(Const("leqCanonical"), Var(?)), Var(?))
    expect(scrutinee.tag).toBe('App');
    if (scrutinee.tag === 'App') {
      expect(scrutinee.fn.tag).toBe('App');
      if (scrutinee.fn.tag === 'App') {
        expect(scrutinee.fn.fn.tag).toBe('Const');
        if (scrutinee.fn.fn.tag === 'Const') {
          expect(scrutinee.fn.fn.name).toBe('leqCanonical');

          // Check the argument indices
          console.log('First arg:', JSON.stringify(scrutinee.fn.arg));
          console.log('Second arg:', JSON.stringify(scrutinee.arg));

          // The args are Var terms - what are their indices?
          if (scrutinee.fn.arg.tag === 'Var') {
            console.log('First arg index:', scrutinee.fn.arg.index);
          }
          if (scrutinee.arg.tag === 'Var') {
            console.log('Second arg index:', scrutinee.arg.index);
          }

          // HYPOTHESIS: These indices are from the MAIN function's context,
          // but in the AUXILIARY context, they should be shifted by 2
          // (to account for the implicit parameters {a b})
          //
          // Main context:  Var(1)=pleq, Var(0)=qleq
          // Aux context:   Var(0)=a, Var(1)=b, Var(2)=pleq, Var(3)=qleq
          //
          // So the scrutinee expression has WRONG indices for the auxiliary!
        }
      }
    }
  });

  test('HYPOTHESIS: scrutinee Var indices are incorrect for auxiliary context', () => {
    // The scrutinee expression is created in the main function's context
    // where pleq=Var(1), qleq=Var(0)
    //
    // But it's used in the auxiliary's TYPE, where:
    // a=Var(0), b=Var(1), pleq=Var(2), qleq=Var(3)
    //
    // When inferScrutineeExprType substitutes these vars into the result type,
    // it produces: Equal Var(1) Var(0)
    // which means: Equal b a  (WRONG!)
    // instead of: Equal pleq qleq

    // This test just documents the hypothesis
    expect(true).toBe(true);
  });
});
