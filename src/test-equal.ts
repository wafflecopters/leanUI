import { checkSourceBlocks, summarizeCheckResults } from './parser/block-checker';

// Equal/Eq definition
const equalDef = `
inductive Equal : (A: Type) -> A -> A -> Type where
  refl : (A : Type) -> (x : A) -> Equal A x x
`;

console.log('Testing Equal:');
console.log(equalDef);
console.log('---');

const results = checkSourceBlocks(equalDef);
const summary = summarizeCheckResults(results);

console.log('Summary:', summary);

for (const result of results) {
  if (!result.parseSuccess) {
    console.log(`Block ${result.blockIndex}: Parse errors:`, result.parseErrors.map(e => e.message));
  } else if (!result.nameResolutionSuccess) {
    console.log(`Block ${result.blockIndex}: Name resolution errors:`, result.nameResolutionErrors.map(e => e.error.message));
  } else if (!result.checkSuccess) {
    console.log(`Block ${result.blockIndex}: Check errors:`, result.checkErrors.map(e => e.error.message));
  } else {
    console.log(`Block ${result.blockIndex}: SUCCESS`);
  }
}
