import { compileSource } from './test-utils';

// Debug vecConcat tests
console.log("=== Debugging vecConcat test ===\n");

const source1 = `inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

plus : Nat -> Nat -> Nat

-- A type family indexed by Nat
F : Nat -> Type

-- This uses 'plus' inside a type expression
test : F (plus Zero Zero)`;

const results1 = compileSource(source1);
for (const r of results1) {
  console.log(`${r.name}: checkSuccess=${r.checkSuccess}`);
  if (!r.checkSuccess) {
    console.log(`  Errors: ${r.checkErrors.map(e => e.message).join(', ')}`);
  }
}

console.log("\n=== Debugging Acc test ===\n");

const source2 = `inductive Acc : (A : Type) -> (A -> A -> Type) -> A -> Type where
  AccIntro : (A : Type) -> (R : A -> A -> Type) -> (x : A) -> ((y : A) -> R y x -> Acc A R y) -> Acc A R x`;

const results2 = compileSource(source2);
for (const r of results2) {
  console.log(`${r.name}: checkSuccess=${r.checkSuccess}`);
  if (!r.checkSuccess) {
    console.log(`  Errors: ${r.checkErrors.map(e => e.message).join(', ')}`);
  }
}
