import { Parser } from './src/parser/tt-parser';
import { groupByIndentation } from './src/parser/indentation-grouper';

const source = `-- Natural Numbers
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

plus : Nat -> Nat -> Na
plus Zero b = b
plus (Succ a) b = Succ (plus a b)`;

const blocks = groupByIndentation(source);
const plusBlock = blocks[1]; // The 'plus' block

const blockSource = plusBlock.lines.join('\n');

console.log('\n=== PLUS BLOCK SOURCE MAP DEBUG ===\n');
console.log(`Block text:\n${blockSource}\n`);
console.log(`Block starts at line: ${plusBlock.startLine}\n`);

const parser = new Parser();
const declsWithSource = parser.parseDeclarationsWithSource(blockSource, []);

console.log(`Number of declarations parsed: ${declsWithSource.length}\n`);

declsWithSource.forEach((dws, i) => {
  console.log(`Declaration ${i}: ${dws.decl.name}`);
  console.log(`  Has type: ${!!dws.decl.type}`);
  console.log(`  Has value: ${!!dws.decl.value}`);
  console.log(`  Value tag: ${dws.decl.value?.tag}`);

  console.log(`  SourceMap entries (${dws.sourceMap.size} total):`);
  const entries = Array.from(dws.sourceMap.entries()).sort((a, b) => {
    // Sort by line then column
    if (a[1].start.line !== b[1].start.line) {
      return a[1].start.line - b[1].start.line;
    }
    return a[1].start.col - b[1].start.col;
  });

  for (const [path, range] of entries) {
    console.log(`    "${path}": line ${range.start.line}, col ${range.start.col} -> line ${range.end.line}, col ${range.end.col}`);
  }
  console.log();
});
