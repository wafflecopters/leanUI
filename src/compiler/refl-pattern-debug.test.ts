import { describe, test, expect } from 'vitest';
import { compileTTFromText } from './compile';

describe('refl pattern implicit arguments', () => {
  test('UNIT: check what refl pattern becomes during elaboration', () => {
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

    // Check the main function first (without with-clause)
    const mainDecl = result.blocks.flatMap(b => b.declarations).find(d => d.name === 'leqCanonical');

    console.log('\n=== Main function (leqCanonical) ===');
    if (mainDecl?.surfaceValue?.tag === 'Match') {
      const firstClause = mainDecl.surfaceValue.clauses[0];
      console.log('First clause patterns:', firstClause.patterns.length);
      console.log('Pattern tags:', firstClause.patterns.map((p: any) => p.tag));

      // This clause should work fine: leqCanonical LeqZero LeqZero = refl
      // It has 2 patterns (both PCtor), and the RHS is refl
    }

    // Now check the auxiliary
    const auxDecl = result.blocks.flatMap(b => b.declarations).find(d => d.name?.startsWith('leqCanonical-with'));

    console.log('\n=== Auxiliary function ===');
    if (auxDecl?.surfaceValue?.tag === 'Match') {
      const clause = auxDecl.surfaceValue.clauses[0];
      console.log('Patterns:', clause.patterns.length);

      // Check the last pattern (refl)
      const reflPattern = clause.patterns[2];
      console.log('Last pattern (refl):', JSON.stringify(reflPattern, null, 2));

      // If refl is PCtor with args, those args might be counted as separate patterns!
      if (reflPattern.tag === 'PCtor') {
        console.log('Constructor name:', reflPattern.name);
        console.log('Constructor args:', reflPattern.args?.length || 0);

        // HYPOTHESIS: If refl has implicit arguments as pattern args,
        // the elaborator might be counting them as extra positional arguments
      }
    }

    // Let's also check what refl's type signature says
    const equalDecl = result.blocks.flatMap(b => b.declarations).find(d => d.name === 'Equal');
    console.log('\n=== Equal type ===');
    if (equalDecl?.surfaceConstructors) {
      const reflCtor = equalDecl.surfaceConstructors.find(c => c.name === 'refl');
      console.log('refl type:', JSON.stringify(reflCtor?.type, null, 2).substring(0, 300));

      // refl has type: {A : Type} -> {a : A} -> Equal a a
      // So it has 2 implicit parameters before the result type
    }
  });

  test('UNIT: compare working case (filter) with failing case (leqCanonical)', () => {
    // filter works, leqCanonical doesn't - what's the difference?

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

    const filterResult = compileTTFromText(filterSource);
    const filterAux = filterResult.blocks.flatMap(b => b.declarations).find(d => d.name?.startsWith('filter-with-1'));

    console.log('\n=== filter auxiliary (WORKS) ===');
    console.log('Has namedArgMap:', !!filterAux?.namedArgMap);
    if (filterAux?.namedArgMap) {
      console.log('namedArgMap:', Array.from(filterAux.namedArgMap.entries()));
    }
    console.log('Check success:', filterAux?.checkSuccess);

    // Key difference: filter's scrutinee is a VARIABLE (xs), not a function application!
    // My fix only applies to non-variable scrutinees
  });
});
