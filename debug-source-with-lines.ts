const source = `inductive Nat : Type where
  Zero : Na
  Succ : Nat -> Nat

plus : Nat -> Nat -> Na`;

const lines = source.split('\n');
lines.forEach((line, i) => {
  console.log(`Line ${i + 1}: "${line}"`);
});
