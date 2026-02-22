import { compileTTFromText } from '../compiler/compile';
import { REAL_ANALYSIS_CODE } from '../presets/real-analysis';

// Compile the full preset and check for errors
const result = compileTTFromText(REAL_ANALYSIS_CODE);

let allOk = true;
for (const block of result.blocks) {
  for (const decl of block.declarations) {
    if (!decl.checkSuccess) {
      allOk = false;
      console.log(`CHECK ERROR: ${decl.name}`);
      for (const e of decl.checkErrors) {
        console.log(`  ${e.message}`);
        if ((e as any).cause) console.log(`    cause: ${(e as any).cause.message}`);
      }
    }
  }
}
console.log(`Total: ${allOk ? 'ALL OK' : 'ERRORS'} (${result.blocks.length} blocks)`);
