import { describe, test, expect } from 'vitest';
import { compileTTFromText } from './compile';

describe('Isolate leqCanonical bug', () => {
  test('leqCanonical WITHOUT with-clause (should fail - needs recursive proof)', () => {
    // Without a with-clause, we can't prove Equal (LeqSucc pleq) (LeqSucc qleq)
    // because refl requires both sides to be definitionally equal, and
    // pleq ≡ qleq can only be established via the recursive call + pattern refinement
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
leqCanonical (LeqSucc pleq) (LeqSucc qleq) = refl
`;

    const result = compileTTFromText(source);
    const leqDecl = result.blocks.flatMap(b => b.declarations).find(d => d.name === 'leqCanonical');

    // This should fail because we need with-clause + pattern refinement
    expect(leqDecl?.checkSuccess).toBe(false);
  });

  test('Simpler with-clause with recursive call', () => {
    // Test a simpler version that's similar to leqCanonical but less complex
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Equal : {A : Type} -> A -> A -> Type where
  refl : {A : Type} -> {a : A} -> Equal a a

simple : {n : Nat} -> Nat -> Equal n n
simple x with simple x
  | refl => refl
`;

    const result = compileTTFromText(source);
    const auxDecl = result.blocks.flatMap(b => b.declarations).find(d => d.name?.startsWith('simple-with'));

    console.log('\nSimple recursive with-clause:');
    console.log('Check success:', auxDecl?.checkSuccess);
    console.log('Has namedArgMap:', !!auxDecl?.namedArgMap);

    if (auxDecl?.namedArgMap) {
      console.log('namedArgMap:', Array.from(auxDecl.namedArgMap.entries()));
    }

    if (!auxDecl?.checkSuccess) {
      console.log('Errors:', auxDecl?.checkErrors.map(e => e.message));
    }

    // If this fails with the same error, we're getting closer!
  });

  test('Even simpler: with-clause on non-recursive call', () => {
    const source = `
inductive Bool : Type where
  True : Bool
  False : Bool

inductive Maybe : Type -> Type where
  Nothing : {A : Type} -> Maybe A
  Just : {A : Type} -> A -> Maybe A

test : {A : Type} -> Maybe A -> Maybe A
test m with m
  | Nothing => Nothing
  | Just x => Just x
`;

    const result = compileTTFromText(source);
    const auxDecl = result.blocks.flatMap(b => b.declarations).find(d => d.name?.startsWith('test-with'));

    console.log('\nSimple non-recursive with-clause:');
    console.log('Check success:', auxDecl?.checkSuccess);
    console.log('Has namedArgMap:', !!auxDecl?.namedArgMap);

    if (auxDecl?.namedArgMap) {
      console.log('namedArgMap:', Array.from(auxDecl.namedArgMap.entries()));
    }

    if (!auxDecl?.checkSuccess) {
      console.log('Errors:', auxDecl?.checkErrors.map(e => e.message));
    }

    // This should definitely work since it's very simple
  });

  test('Constructor patterns in function position', () => {
    // The difference with leqCanonical is that it has CONSTRUCTOR PATTERNS
    // in the function position: (LeqSucc pleq) (LeqSucc qleq)

    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Equal : {A : Type} -> A -> A -> Type where
  refl : {A : Type} -> {a : A} -> Equal a a

foo : {n m : Nat} -> Nat -> Nat -> Equal n m
foo (Succ x) (Succ y) with foo x y
  | refl => refl
`;

    const result = compileTTFromText(source);
    const auxDecl = result.blocks.flatMap(b => b.declarations).find(d => d.name?.startsWith('foo-with'));

    console.log('\nConstructor patterns in function position:');
    console.log('Check success:', auxDecl?.checkSuccess);
    console.log('Has namedArgMap:', !!auxDecl?.namedArgMap);

    if (auxDecl?.namedArgMap) {
      console.log('namedArgMap:', Array.from(auxDecl.namedArgMap.entries()));
    }

    if (!auxDecl?.checkSuccess) {
      console.log('Errors:', auxDecl?.checkErrors.map(e => e.message));
    }

    // This is very similar to leqCanonical - if this fails, we've found the pattern!
  });
});
