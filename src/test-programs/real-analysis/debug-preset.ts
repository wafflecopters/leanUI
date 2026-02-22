import { compileTTFromText } from '../../compiler/compile';
import { REAL_ANALYSIS_CODE } from '../../presets/real-analysis';

const result = compileTTFromText(REAL_ANALYSIS_CODE);
let hasErrors = false;
for (const block of result.blocks) {
  if (!block.parseSuccess) {
    console.log(`PARSE ERROR in block ${block.blockIndex}:`);
    for (const e of block.parseErrors) {
      console.log(`  ${e.message}`);
    }
    hasErrors = true;
  }
  if (!block.nameResolutionSuccess) {
    console.log(`NAME ERROR in block ${block.blockIndex}:`);
    for (const e of block.nameResolutionErrors) {
      console.log(`  ${e.message}`);
    }
    hasErrors = true;
  }
  for (const decl of block.declarations) {
    if (!decl.checkSuccess && decl.checkErrors.length > 0) {
      console.log(`CHECK ERROR in ${decl.name}:`);
      for (const e of decl.checkErrors) {
        console.log(`  ${e.message}`);
      }
      hasErrors = true;
    }
  }
}
if (!hasErrors) {
  console.log('All OK! No errors in preset.');
}
console.log(`Total blocks: ${result.blocks.length}, success: ${result.success}`);
