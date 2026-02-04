import { describe, test, expect } from 'vitest';
import { compileTTFromText } from './compile';

describe('Find where named flag is lost', () => {
  test('Check if main function has named flag', () => {
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

    console.log('\n=== Main function surface type ===');
    console.log(JSON.stringify(simpleDecl!.surfaceType, null, 2).substring(0, 300));

    console.log('\n=== Auxiliary surface type ===');
    console.log(JSON.stringify(auxDecl!.surfaceType, null, 2).substring(0, 300));

    // Check if main function has named flag
    if (simpleDecl!.surfaceType?.tag === 'Binder') {
      console.log('\nMain function first binder has named:', !!(simpleDecl!.surfaceType as any).named);
    }

    // Check if auxiliary has named flag
    if (auxDecl!.surfaceType?.tag === 'Binder') {
      console.log('Auxiliary first binder has named:', !!(auxDecl!.surfaceType as any).named);
    }

    // HYPOTHESIS: The main function has `named: true` but the auxiliary doesn't
    // This means computeAuxiliaryType or spliceScrutineesIntoType is losing it
  });

  test('Check all binders in auxiliary type', () => {
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

    function walkBinders(type: any, depth: number = 0): void {
      if (type.tag === 'Binder') {
        console.log(`Binder at depth ${depth}: name="${type.name}", named=${!!(type as any).named}`);
        walkBinders(type.body, depth + 1);
      } else if (type.tag === 'MultiBinder') {
        console.log(`MultiBinder at depth ${depth}: names=${type.names}, named=${!!(type as any).named}`);
        walkBinders(type.body, depth + type.names.length);
      }
    }

    console.log('\n=== Walking auxiliary binders ===');
    walkBinders(auxDecl!.surfaceType);

    // Expected output:
    // Binder at depth 0: name="n", named=true  <- SHOULD BE TRUE!
    // Binder at depth 1: name="_", named=false
    // Binder at depth 2: name="_scrut0", named=false
  });
});
