import { groupByIndentation } from './src/parser/indentation-grouper';

const source = `inductive Nat : Type where
  Zero : Na
  Succ : Nat -> Nat

plus : Nat -> Nat -> Na`;

const blocks = groupByIndentation(source);

blocks.forEach((block, i) => {
  console.log(`\nBlock ${i}:`);
  console.log(`  Start line: ${block.startLine}`);
  console.log(`  Is inductive: ${block.isInductive}`);
  console.log(`  Lines:`);
  block.lines.forEach((line, j) => {
    console.log(`    ${j + 1}: "${line}"`);
  });
});
