/**
 * Debug script: render all theorems from the real-analysis preset.
 * Run with: npx tsx src/compiler/_debug-proofs.ts
 */
import { compileTTFromText } from './compile';
import { convertToLatex, makeDefaultNotations } from './latex-converter';
import { REAL_ANALYSIS_CODE } from '../presets/real-analysis';

const result = compileTTFromText(REAL_ANALYSIS_CODE);
const notations = makeDefaultNotations();
const doc = convertToLatex(result, notations);

for (const section of doc.sections) {
  if (section.category === 'theorem') {
    console.log(`\n${'='.repeat(60)}`);
    console.log(`  ${section.name} (${section.checkSuccess ? 'OK' : 'ERR'})`);
    console.log('='.repeat(60));
    for (const block of section.blocks) {
      console.log(`[${block.kind}] ${block.latex}`);
    }
    if (section.errors.length > 0) {
      for (const err of section.errors) {
        console.log(`  ERROR: ${err}`);
      }
    }
  }
}
// Also show any non-theorem errors
for (const section of doc.sections) {
  if (section.errors.length > 0 && section.category !== 'theorem') {
    console.log(`\n!!! ${section.name} (${section.category}): ${section.errors.join('; ')}`);
  }
}
