import { describe, test, expect } from 'vitest';
import { compileTTFromText } from './compile';

describe('Compare working vs failing auxiliaries', () => {
  test('DETAILED: filter auxiliary (works) vs leqCanonical auxiliary (fails)', () => {
    const filterSource = `
inductive Bool : Type where
  True : Bool
  False : Bool

inductive List : Type -> Type where
  Nil : {A : Type} -> List A
  Cons : {A : Type} -> A -> List A -> List A

filter : {A : Type} -> (A -> Bool) -> List A -> List A
filter p xs with xs
  | Nil => Nil
  | Cons x rest with p x
    | True => Cons x (filter p rest)
    | False => filter p rest
`;

    const leqSource = `
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

    const filterResult = compileTTFromText(filterSource);
    const leqResult = compileTTFromText(leqSource);

    const filterAux = filterResult.blocks.flatMap(b => b.declarations).find(d => d.name?.startsWith('filter-with-1'));
    const leqAux = leqResult.blocks.flatMap(b => b.declarations).find(d => d.name?.startsWith('leqCanonical-with'));

    console.log('\n========== FILTER AUXILIARY (WORKS) ==========');
    console.log('Check success:', filterAux?.checkSuccess);
    if (filterAux?.surfaceValue?.tag === 'Match') {
      const clause = filterAux.surfaceValue.clauses[0]; // Nil clause
      console.log('Pattern count:', clause.patterns.length);
      console.log('Pattern types:', clause.patterns.map((p: any) => p.tag));
      console.log('namedPatterns:', clause.namedPatterns ? 'exists' : 'undefined');
    }

    console.log('\n========== LEQCANONICAL AUXILIARY (FAILS) ==========');
    console.log('Check success:', leqAux?.checkSuccess);
    if (leqAux?.surfaceValue?.tag === 'Match') {
      const clause = leqAux.surfaceValue.clauses[0];
      console.log('Pattern count:', clause.patterns.length);
      console.log('Pattern types:', clause.patterns.map((p: any) => p.tag));
      console.log('namedPatterns:', clause.namedPatterns ? 'exists' : 'undefined');
    }

    // Key question: What's different between these two cases?
    // - Both have namedArgMaps
    // - Both have constructor patterns (Nil and refl both have implicit args)
    // - Filter works, leqCanonical doesn't

    // One difference: filter's scrutinee is a VARIABLE (xs)
    // leqCanonical's scrutinee is a FUNCTION CALL (leqCanonical pleq qleq)

    console.log('\n========== SCRUTINEE TYPES ==========');
    console.log('filter auxiliary has withScrutineeExprs:', !!filterAux?.withScrutineeExprs);
    console.log('leq auxiliary has withScrutineeExprs:', !!leqAux?.withScrutineeExprs);

    if (filterAux?.withScrutineeExprs && filterAux.withScrutineeExprs.length > 0) {
      console.log('filter scrutinee tag:', filterAux.withScrutineeExprs[0].tag);
    }

    if (leqAux?.withScrutineeExprs && leqAux.withScrutineeExprs.length > 0) {
      console.log('leq scrutinee tag:', leqAux.withScrutineeExprs[0].tag);
    }
  });

  test('HYPOTHESIS: The issue is with function-call scrutinees after my fix', () => {
    // My resolveAuxScrutineeTypes function processes non-variable scrutinees
    // Maybe it's introducing the bug?

    // Let me test a simpler case with a function-call scrutinee
    const simpleSource = `
inductive Bool : Type where
  True : Bool
  False : Bool

not : Bool -> Bool
not True = False
not False = True

test : {x : Bool} -> Bool -> Bool
test y with not y
  | True => True
  | False => False
`;

    const result = compileTTFromText(simpleSource);
    const auxDecl = result.blocks.flatMap(b => b.declarations).find(d => d.name?.startsWith('test-with'));

    console.log('\n========== SIMPLE FUNCTION-CALL SCRUTINEE ==========');
    console.log('Check success:', auxDecl?.checkSuccess);
    console.log('Has withScrutineeExprs:', !!auxDecl?.withScrutineeExprs);
    console.log('Has namedArgMap:', !!auxDecl?.namedArgMap);

    if (auxDecl?.namedArgMap) {
      console.log('namedArgMap:', Array.from(auxDecl.namedArgMap.entries()));
    }

    if (!auxDecl?.checkSuccess && auxDecl?.checkErrors) {
      console.log('Errors:', auxDecl.checkErrors.map(e => e.message));
    }

    // If this also fails with "Too many positional arguments", then my fix is causing the problem!
  });
});
