import { Parser } from './src/parser/tt-parser';

const source = `inductive Nat : Type where
  Zero : Nat
  Succ : Na -> Nat`;

const parser = new Parser(source);
const declsWithSource = parser.parseDeclarationsWithSource(source, []);

console.log('\n=== CONSTRUCTOR SOURCE POSITIONS ===\n');

declsWithSource.forEach((dws, i) => {
  console.log(`Declaration ${i}: ${dws.decl.name}`);
  console.log(`  SourceMap entries:`);

  for (const [path, range] of dws.sourceMap.entries()) {
    console.log(`    "${path}": line ${range.start.line}, col ${range.start.col} -> line ${range.end.line}, col ${range.end.col}`);
  }

  if (dws.decl.constructors) {
    console.log(`  Constructors:`);
    dws.decl.constructors.forEach((ctor, idx) => {
      console.log(`    [${idx}] ${ctor.name}: ${JSON.stringify(ctor.type)}`);
    });
  }
});
