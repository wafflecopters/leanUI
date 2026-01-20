import { compileSource } from './test-utils';

const source = `inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

plus : Nat -> Nat -> Nat
plus Zero b = b
plus (Succ a) b = Succ (plus a b)

-- A type family indexed by Nat (using inductive to have a proper definition)
inductive F : Nat -> Type where
  MkF : (n : Nat) -> F n

-- This uses 'plus' inside a type expression
-- Type checker must resolve plus, then infer (plus Zero Zero) : Nat,
-- then check F (plus Zero Zero) : Type
test : F (plus Zero Zero)
test = MkF Zero`;

const results = compileSource(source);
for (const r of results) {
  console.log(`${r.name}: checkSuccess=${r.checkSuccess}`);
  if (!r.checkSuccess) {
    console.log(`  Errors: ${r.checkErrors.map(e => e.message).join('\n    ')}`);
  }
}
