import { compileTTFromText } from './src/compiler/compile';

function countParams(type: any): number {
  if (!type) return 0;
  if (type.tag === 'Binder') return 1 + countParams(type.body);
  if (type.tag === 'MultiBinder') return type.names.length + countParams(type.body);
  return 0;
}

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

// Simpler test without with-clause
console.log('\n\n=== Without with-clause ===');
const result2 = compileTTFromText(source);
for (const block of result2.blocks) {
  if (block.declarations) {
    for (const decl of block.declarations) {
      if (decl.name === 'leqCanonical') {
        console.log('leqCanonical check:', decl.checkSuccess ? 'SUCCESS' : 'FAIL');
      }
    }
  }
}

// Now test with with-clause
const source2 = `
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

// Print all declarations
for (const block of result.blocks) {
  if (block.declarations) {
    for (const decl of block.declarations) {
      if (decl.name && decl.name.includes('with')) {
        console.log('\n=== Declaration:', decl.name);
        console.log('Surface Type param count:', countParams(decl.surfaceType));
        console.log('Kernel Type:', decl.kernelType ? 'exists' : 'undefined');
        console.log('elabSuccess:', decl.elabSuccess);
        if (decl.kernelType) {
          console.log('Kernel Type param count:', countParams(decl.kernelType));
        }
        console.log('namedArgMap size:', decl.namedArgMap ? decl.namedArgMap.size : 'undefined');
        if (decl.namedArgMap) {
          console.log('namedArgMap:', Array.from(decl.namedArgMap.entries()));
        }
        if (decl.elabSuccess === false && decl.elabErrors) {
          console.log('ELAB ERRORS:', decl.elabErrors.map((e: any) => e.message).join('\n'));
        }
        if (decl.checkSuccess === false) {
          console.log('CHECK ERRORS:', decl.checkErrors.map(e => e.message).join('\n'));
        }
      }
    }
  }
}
