import { parseBlocks } from './src/parser/block-parser';
import { checkSourceBlocks } from './src/parser/block-checker';
import { elaborateToKernel, resolveNames } from './src/types/name-resolution';

const source = `inductive Nat : Type where
  | Zero : Nat
  | Succ : Nat -> Nat

plus : Nat -> Nat -> Nat
plus Zero b = b
plus (Succ a) b = Succ (plus a b)`;

const blocks = parseBlocks(source);
// @ts-ignore
const termBlock = blocks[1];

console.log("Parsed block term value:");
console.log(JSON.stringify(termBlock.value, null, 2));
