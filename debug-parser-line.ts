import { Parser } from './src/parser/tt-parser';

const blockSource = `inductive Nat : Type where
  Zero : Na
  Succ : Nat -> Nat`;

const parser = new Parser();
const declsWithSource = parser.parseDeclarationsWithSource(blockSource, []);

console.log('Parsed declarations with source maps:');
declsWithSource.forEach((dws, i) => {
  console.log(`\nDeclaration ${i}: ${dws.decl.name}`);
  console.log('  Source map entries:');
  for (const [key, range] of dws.sourceMap.entries()) {
    console.log(`    "${key}": line ${range.start.line}, col ${range.start.col} -> line ${range.end.line}, col ${range.end.col}`);
  }
});
