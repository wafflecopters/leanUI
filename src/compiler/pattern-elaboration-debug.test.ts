import { describe, test, expect } from 'vitest';
import { compileTTFromText } from './compile';

describe('Pattern elaboration debugging', () => {
  test('UNIT: verify auxiliary clause structure', () => {
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
    const auxDecl = result.blocks.flatMap(b => b.declarations).find(d => d.name?.startsWith('leqCanonical-with'));

    expect(auxDecl).toBeTruthy();

    // Count parameters in the auxiliary type
    function countParams(type: any): { total: number; named: number; explicit: number } {
      let total = 0;
      let named = 0;
      let current = type;

      while (current && (current.tag === 'Binder' || current.tag === 'MultiBinder')) {
        if (current.tag === 'Binder') {
          total++;
          if (current.named) named++;
          current = current.body;
        } else {
          const count = current.names.length;
          total += count;
          if (current.named) named += count;
          current = current.body;
        }
      }

      return { total, named, explicit: total - named };
    }

    const paramCounts = countParams(auxDecl!.surfaceType);
    console.log('Auxiliary parameter counts:', paramCounts);
    console.log('namedArgMap:', auxDecl!.namedArgMap ? Array.from(auxDecl!.namedArgMap.entries()) : 'undefined');

    // Expected: 5 total params ({a b} + (p q) + (_scrut0))
    // Expected: 2 named params ({a b})
    // Expected: 3 explicit params ((p q) + (_scrut0))
    expect(paramCounts.total).toBe(5);
    expect(paramCounts.named).toBe(2);
    expect(paramCounts.explicit).toBe(3);

    // Now check the surfaceValue to see what patterns are in the clause
    if (auxDecl!.surfaceValue?.tag === 'Match') {
      const clause = auxDecl!.surfaceValue.clauses[0];
      console.log('Number of patterns in clause:', clause.patterns.length);
      console.log('Pattern tags:', clause.patterns.map((p: any) => p.tag));
      console.log('Named patterns in clause:', clause.namedPatterns ? 'exists' : 'undefined');

      // The clause should have 3 patterns: pleq, qleq, refl
      expect(clause.patterns.length).toBe(3);
    }
  });

  test('UNIT: check if namedPatterns is causing the issue', () => {
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
    const auxDecl = result.blocks.flatMap(b => b.declarations).find(d => d.name?.startsWith('leqCanonical-with'));

    if (auxDecl!.surfaceValue?.tag === 'Match') {
      const clause = auxDecl!.surfaceValue.clauses[0];

      console.log('\n=== Clause namedPatterns ===');
      if (clause.namedPatterns) {
        console.log('namedPatterns exists with', clause.namedPatterns.length, 'entries');
        console.log('Entries:', clause.namedPatterns.map(np => [np.name, np.pattern.tag]));
      } else {
        console.log('namedPatterns is undefined');
      }

      // HYPOTHESIS: The clause has namedPatterns from the MAIN function (for {a b}),
      // but these are being counted as additional patterns, causing "too many positional arguments"

      // If namedPatterns has entries for {a b}, and the patterns array has [pleq, qleq, refl],
      // then the elaborator might think there are 3 positional + 2 named = 5 arguments total,
      // but the type only has 3 explicit positions!
    }
  });
});
