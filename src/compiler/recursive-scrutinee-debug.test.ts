import { describe, test, expect } from 'vitest';
import { compileTTFromText } from './compile';

describe('Recursive scrutinee debugging', () => {
  test('What does inferScrutineeExprType return for recursive calls?', () => {
    // When we have: simple x with simple x
    // The scrutinee is "simple x", which is a call to the function being defined
    // What type does definitions have for "simple" at this point?

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
    const simpleDecl = result.blocks.flatMap(b => b.declarations).find(d => d.name === 'simple');
    const auxDecl = result.blocks.flatMap(b => b.declarations).find(d => d.name?.startsWith('simple-with'));

    console.log('\n=== Main function (simple) ===');
    console.log('Has kernelType:', !!simpleDecl?.kernelType);
    console.log('Check success:', simpleDecl?.checkSuccess);

    console.log('\n=== Auxiliary function ===');
    console.log('Has kernelType:', !!auxDecl?.kernelType);
    console.log('Check success:', auxDecl?.checkSuccess);
    console.log('namedArgMap:', auxDecl?.namedArgMap ? Array.from(auxDecl.namedArgMap.entries()) : 'undefined');

    // Count params in auxiliary type
    function countParams(type: any): { total: number; named: number } {
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

      return { total, named };
    }

    const params = countParams(auxDecl!.surfaceType);
    console.log('Auxiliary params:', params);
    console.log('Expected: {n} (named) + x (explicit) + _scrut0 (explicit) = 3 total, 1 named');

    // Check the auxiliary clause
    if (auxDecl?.surfaceValue?.tag === 'Match') {
      const clause = auxDecl.surfaceValue.clauses[0];
      console.log('\nClause patterns:', clause.patterns.length);
      console.log('Pattern tags:', clause.patterns.map((p: any) => p.tag));

      // Expected: 2 patterns (x, refl) to fill 2 explicit positions
      // But we're getting "Too many positional arguments: 1 extra"
      // So it thinks there are 3 positional patterns instead of 2!
    }

    console.log('\n=== Auxiliary surface type (first 500 chars) ===');
    console.log(JSON.stringify(auxDecl!.surfaceType, null, 2).substring(0, 500));
  });

  test('Compare non-recursive vs recursive scrutinee types', () => {
    const nonRecursive = `
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

    const recursive = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Equal : {A : Type} -> A -> A -> Type where
  refl : {A : Type} -> {a : A} -> Equal a a

simple : {n : Nat} -> Nat -> Equal n n
simple x with simple x
  | refl => refl
`;

    const nonRecResult = compileTTFromText(nonRecursive);
    const recResult = compileTTFromText(recursive);

    const nonRecAux = nonRecResult.blocks.flatMap(b => b.declarations).find(d => d.name?.startsWith('test-with'));
    const recAux = recResult.blocks.flatMap(b => b.declarations).find(d => d.name?.startsWith('simple-with'));

    console.log('\n========== NON-RECURSIVE (works) ==========');
    console.log('Check success:', nonRecAux?.checkSuccess);
    console.log('withScrutineeExprs[0] tag:', nonRecAux?.withScrutineeExprs?.[0]?.tag);

    console.log('\n========== RECURSIVE (fails) ==========');
    console.log('Check success:', recAux?.checkSuccess);
    console.log('withScrutineeExprs[0] tag:', recAux?.withScrutineeExprs?.[0]?.tag);

    // Both have scrutinee tag 'App', but one works and one doesn't
    // The difference: recursive vs non-recursive

    // When resolveAuxScrutineeTypes processes "simple x":
    // 1. It calls inferScrutineeExprType(App(Const("simple"), Var(0)), definitions)
    // 2. inferScrutineeExprType looks up "simple" in definitions
    // 3. At this point, "simple" IS in definitions (pre-registered)
    // 4. But what type does it have? The MAIN function's type, not the auxiliary's!
    // 5. This might be causing the wrong type to be inferred
  });
});
