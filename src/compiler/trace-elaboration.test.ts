import { describe, test, expect } from 'vitest';
import { compileTTFromText } from './compile';

describe('Trace pattern elaboration', () => {
  test('Add logging to understand the reorderPatterns call', () => {
    // The error comes from elab.ts in the reorderPatterns function
    // It says "Too many positional arguments: 1 extra argument"
    // This means: posIdx < positional.length after filling

    // Let's manually trace what should happen:
    // Auxiliary type: {n : Nat} -> Nat -> (Equal n n) -> ...
    //   Position 0: n (named)
    //   Position 1: Nat (not named)
    //   Position 2: Equal n n (not named)
    // totalArity: 3
    // namedArgMap: {n: 0}
    // namedPositions: {0}

    // Clause patterns: [PVar("x"), PCtor("refl")]
    //   These are 2 positional patterns
    // namedPatterns: undefined (no named patterns in the clause)

    // reorderPatterns should:
    // 1. Create result array of size 3
    // 2. Place no named patterns (none provided)
    // 3. Fill positional patterns into non-named positions (1, 2)
    //    - posIdx=0 -> position 1
    //    - posIdx=1 -> position 2
    // 4. Check if posIdx < positional.length
    //    - posIdx should be 2, positional.length is 2
    //    - 2 < 2 is false, so NO error

    // But we're getting an error that there's 1 extra!
    // This means posIdx=1 and positional.length=2
    // OR posIdx=2 and positional.length=3

    // So EITHER:
    // A) Only 1 position got filled (posIdx stopped at 1)
    // B) There are 3 positional patterns instead of 2

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

    // Let me check EXACTLY what the error says
    console.log('Check success:', auxDecl?.checkSuccess);
    console.log('Errors:', auxDecl?.checkErrors.map(e => e.message));

    // The error should be on a specific clause. Let me check which one.
    // If it's on the auxiliary's clause, that's what we're debugging.
  });

  test('Check if the main function is correctly pre-registered', () => {
    // When the auxiliary is being checked, the main function "simple" should be
    // in definitions. Let me verify what info it has.

    // I can't directly access definitions, but I can check the compiled result
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
    const mainDecl = result.blocks.flatMap(b => b.declarations).find(d => d.name === 'simple');

    console.log('\n=== Main function ===');
    console.log('Has namedArgMap:', !!mainDecl?.namedArgMap);
    if (mainDecl?.namedArgMap) {
      console.log('namedArgMap:', Array.from(mainDecl.namedArgMap.entries()));
    }

    // Count params
    function countParams(type: any): number {
      let count = 0;
      let current = type;
      while (current && (current.tag === 'Binder' || current.tag === 'MultiBinder')) {
        if (current.tag === 'Binder') {
          count++;
          current = current.body;
        } else {
          count += current.names.length;
          current = current.body;
        }
      }
      return count;
    }

    const mainParamCount = countParams(mainDecl?.surfaceType);
    console.log('Main function param count:', mainParamCount);
    console.log('Expected: 2 (n + x)');

    // If the main function has been processed as a with-clause function,
    // it might have EXTRA parameters added (the scrutinee)!
    // That would make totalArity wrong!
  });

  test('HYPOTHESIS: Main function gets contaminated with with-clause params', () => {
    // When we have:
    //   simple x with simple x
    //
    // The main function gets desugared and might have scrutinee params added.
    // If the main function's type becomes:
    //   {n : Nat} -> Nat -> (Equal n n) -> ...
    // (with the scrutinee param from the with-clause)
    //
    // Then when the auxiliary tries to look up "simple" in definitions,
    // it gets this contaminated type with 3 params instead of 2!

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
    const mainDecl = result.blocks.flatMap(b => b.declarations).find(d => d.name === 'simple');

    console.log('\n=== Checking for contamination ===');
    console.log('Main surfaceType:', JSON.stringify(mainDecl?.surfaceType, null, 2).substring(0, 400));

    // If we see 3 binders instead of 2, that's the bug!
  });
});
