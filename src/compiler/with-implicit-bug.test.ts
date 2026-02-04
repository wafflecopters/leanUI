import { describe, test, expect } from 'vitest';
import { compileTTFromText } from './compile';

describe('With-clause implicit parameter bug', () => {
  test.skip('UNIT: auxiliary type should not contain Holes after resolution', () => {
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

    // Find the auxiliary declaration
    let auxDecl: any = null;
    for (const block of result.blocks) {
      if (block.declarations) {
        for (const decl of block.declarations) {
          if (decl.name && decl.name.includes('with')) {
            auxDecl = decl;
            break;
          }
        }
      }
    }

    expect(auxDecl).toBeTruthy();

    // Check if surface type contains Holes
    const typeStr = JSON.stringify(auxDecl.surfaceType);
    const hasHoles = typeStr.includes('"Hole"');

    if (hasHoles) {
      // Find the Hole to see what it is
      const holeMatch = typeStr.match(/"id":"([^"]+)"/);
      console.log('Found Hole with id:', holeMatch ? holeMatch[1] : 'unknown');

      // Check if the auxiliary has scrutinee expressions stored
      console.log('Has withScrutineeExprs:', !!auxDecl.withScrutineeExprs);
      if (auxDecl.withScrutineeExprs) {
        console.log('Scrutinee count:', auxDecl.withScrutineeExprs.length);
        console.log('Scrutinee[0] tag:', auxDecl.withScrutineeExprs[0]?.tag);
      }
    }

    // The surface type should NOT have Holes after resolveAuxScrutineeTypes runs
    expect(hasHoles).toBe(false);
  });

  test.only('leqCanonical should compile successfully', () => {
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

    // Find the auxiliary declaration
    let auxDecl: any = null;
    for (const block of result.blocks) {
      if (block.declarations) {
        for (const decl of block.declarations) {
          if (decl.name && decl.name.includes('with')) {
            auxDecl = decl;
            break;
          }
        }
      }
    }

    expect(auxDecl).toBeTruthy();
    console.log('Auxiliary name:', auxDecl.name);
    console.log('Has kernel type:', !!auxDecl.kernelType);
    console.log('Has namedArgMap:', !!auxDecl.namedArgMap);
    if (auxDecl.namedArgMap) {
      console.log('namedArgMap:', Array.from(auxDecl.namedArgMap.entries()));
    }
    console.log('Check success:', auxDecl.checkSuccess);

    // Check if surface type contains Holes
    const hasHoles = JSON.stringify(auxDecl.surfaceType).includes('"Hole"');
    console.log('Surface type has Holes:', hasHoles);

    if (hasHoles) {
      console.log('Surface type with Holes:', JSON.stringify(auxDecl.surfaceType, null, 2));
    }

    if (!auxDecl.checkSuccess) {
      console.log('Errors:', auxDecl.checkErrors.map((e: any) => e.message));
    }

    // Print the full surface type for debugging
    console.log('\n=== Full auxiliary type ===');
    console.log(JSON.stringify(auxDecl.surfaceType, null, 2));

    // HYPOTHESIS: The auxiliary's type has a Hole which prevents elaboration
    expect(hasHoles).toBe(false);

    // Check the clause structure
    if (auxDecl.surfaceValue && auxDecl.surfaceValue.tag === 'Match') {
      const clause = auxDecl.surfaceValue.clauses[0];
      console.log('\n=== Clause structure ===');
      console.log('Clause patterns count:', clause.patterns.length);
      console.log('Clause patterns:', clause.patterns.map((p: any) => p.tag));
      console.log('namedPatterns:', clause.namedPatterns);
    }

    // Check namedArgMap
    console.log('\n=== namedArgMap ===');
    if (auxDecl.namedArgMap) {
      console.log('namedArgMap:', Array.from(auxDecl.namedArgMap.entries()));
    } else {
      console.log('namedArgMap: undefined');
    }

    // Now check if it compiles successfully
    if (!auxDecl.checkSuccess) {
      console.log('\n=== Compilation errors ===');
      console.log(auxDecl.checkErrors.map((e: any) => e.message).join('\n'));
    }
    expect(auxDecl.checkSuccess).toBe(true);
  });
});
