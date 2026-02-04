import { describe, test, expect } from 'vitest';
import { compileTTFromText } from './compile';

describe('Named patterns causing the bug', () => {
  test('Check what namedPatterns the clause has', () => {
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

    if (auxDecl?.surfaceValue?.tag === 'Match') {
      const clause = auxDecl.surfaceValue.clauses[0];

      console.log('\n=== Clause analysis ===');
      console.log('Patterns count:', clause.patterns.length);
      console.log('Pattern tags:', clause.patterns.map((p: any) => p.tag));

      if (clause.namedPatterns) {
        console.log('\nnamedPatterns EXISTS with', clause.namedPatterns.size, 'entries');
        const entries = Array.from(clause.namedPatterns.entries());
        console.log('Entries:', entries.map(([k, v]) => `${k} -> ${v.tag}`));

        // HYPOTHESIS: clause.namedPatterns has an entry for {n},
        // and this is being treated as an additional pattern on top of the 2 positional ones!
        // Total: 2 positional + 1 named = 3 patterns trying to fill 2 explicit positions
        // Error: "1 extra argument"
      } else {
        console.log('\nnamedPatterns is undefined');
      }
    }

    // Let me also check the MAIN function's clause to see what it has
    const mainDecl = result.blocks.flatMap(b => b.declarations).find(d => d.name === 'simple');
    if (mainDecl?.surfaceValue?.tag === 'Match') {
      const clause = mainDecl.surfaceValue.clauses[0];

      console.log('\n=== Main function clause ===');
      console.log('Patterns count:', clause.patterns.length);

      if (clause.namedPatterns) {
        console.log('Main namedPatterns:', clause.namedPatterns.size, 'entries');
        const entries = Array.from(clause.namedPatterns.entries());
        console.log('Entries:', entries.map(([k, v]) => `${k} -> ${v.tag}`));
      }
    }
  });

  test('Compare working vs failing case namedPatterns', () => {
    const working = `
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

    const failing = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Equal : {A : Type} -> A -> A -> Type where
  refl : {A : Type} -> {a : A} -> Equal a a

simple : {n : Nat} -> Nat -> Equal n n
simple x with simple x
  | refl => refl
`;

    const workingResult = compileTTFromText(working);
    const failingResult = compileTTFromText(failing);

    const workingAux = workingResult.blocks.flatMap(b => b.declarations).find(d => d.name?.startsWith('test-with'));
    const failingAux = failingResult.blocks.flatMap(b => b.declarations).find(d => d.name?.startsWith('simple-with'));

    console.log('\n========== WORKING CASE (test) ==========');
    if (workingAux?.surfaceValue?.tag === 'Match') {
      const clause = workingAux.surfaceValue.clauses[0];
      console.log('Patterns:', clause.patterns.length);
      console.log('namedPatterns:', clause.namedPatterns ? `${clause.namedPatterns.size} entries` : 'undefined');

      if (clause.namedPatterns) {
        console.log('Named pattern entries:', Array.from(clause.namedPatterns.keys()));
      }
    }

    console.log('\n========== FAILING CASE (simple) ==========');
    if (failingAux?.surfaceValue?.tag === 'Match') {
      const clause = failingAux.surfaceValue.clauses[0];
      console.log('Patterns:', clause.patterns.length);
      console.log('namedPatterns:', clause.namedPatterns ? `${clause.namedPatterns.size} entries` : 'undefined');

      if (clause.namedPatterns) {
        console.log('Named pattern entries:', Array.from(clause.namedPatterns.keys()));
      }
    }

    // If the failing case has namedPatterns but the working case doesn't,
    // that's the smoking gun!
  });
});
