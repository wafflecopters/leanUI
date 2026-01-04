import { checkSourceBlocks } from './src/parser/block-checker';

const source = `-- Natural Numbers
inductive Nat : Type where
  Zero : Nat
  Succ : Na -> Nat`;

const results = checkSourceBlocks(source);

console.log('\n=== NAME RESOLUTION ERROR PATHS ===\n');

results.forEach((result, i) => {
  console.log(`Block ${i}: ${result.name || '(unnamed)'}`);
  console.log(`  Name Resolution: ${result.nameResolutionSuccess ? 'OK' : 'FAIL'}`);

  if (!result.nameResolutionSuccess) {
    console.log(`  Errors:`);
    result.nameResolutionErrors.forEach((err, j) => {
      console.log(`    Error ${j}:`);
      console.log(`      Message: ${err.error.message}`);
      console.log(`      Symbol: ${err.error.symbolName}`);
      console.log(`      Path: ${JSON.stringify(err.error.path)}`);
      console.log(`      Serialized: "${err.error.path.join('.')}"`);
      if (err.location) {
        console.log(`      Location: line ${err.location.start.line}, col ${err.location.start.col} -> line ${err.location.end.line}, col ${err.location.end.col}`);
      } else {
        console.log(`      Location: NULL`);
      }
    });
  }
});
