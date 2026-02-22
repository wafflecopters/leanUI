import { compileTTFromText } from '../compiler/compile';
import { REAL_ANALYSIS_CODE } from '../presets/real-analysis';

const result = compileTTFromText(REAL_ANALYSIS_CODE);

// Find continuousFromDeriv
let found = false;
for (const block of result.blocks) {
  for (const decl of block.declarations) {
    if (decl.name && decl.name.includes('continuous')) {
      console.log(`${decl.name}: block=${block.blockIndex} check=${decl.checkSuccess}`);
      found = true;
    }
  }
}
if (!found) console.log('continuousFromDeriv NOT FOUND in any block');

// Show blocks around the issue
for (const block of result.blocks) {
  if (block.blockIndex >= 145 && block.blockIndex <= 149) {
    const names = block.declarations.map(d => d.name).filter(Boolean).join(', ');
    console.log(`Block ${block.blockIndex}: [${names}] parse=${block.parseSuccess} nameRes=${block.nameResolutionSuccess}`);
    if (!block.parseSuccess) {
      for (const e of block.parseErrors) console.log(`  PARSE: ${e.message}`);
    }
  }
}
