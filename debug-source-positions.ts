import { checkSourceBlocks } from './src/parser/block-checker';

const source = `inductive Nat : Type where
  Zero : Na
  Succ : Nat -> Nat

plus : Nat -> Nat -> Na`;

const results = checkSourceBlocks(source);

console.log('\n=== DEBUGGING SOURCE POSITIONS ===\n');

results.forEach((result, i) => {
  console.log(`Block ${i}: ${result.name || '(unnamed)'}`);
  console.log(`  Name Resolution: ${result.nameResolutionSuccess ? 'OK' : 'FAIL'}`);

  if (!result.nameResolutionSuccess) {
    console.log(`  Errors:`);
    result.nameResolutionErrors.forEach((err, j) => {
      console.log(`    Error ${j}: ${err.error.message}`);
      console.log(`      Symbol: ${err.error.symbolName}`);
      console.log(`      Path: ${JSON.stringify(err.error.path)}`);
      if (err.location) {
        console.log(`      Location: line ${err.location.start.line}, col ${err.location.start.col} -> line ${err.location.end.line}, col ${err.location.end.col}`);
      } else {
        console.log(`      Location: NULL`);
      }
    });
  }
});
