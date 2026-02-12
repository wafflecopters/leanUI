import { describe, test, expect } from 'vitest';
import { compileTTFromText } from './compile';
import { convertToLatex } from './latex-converter';

describe('limitAdd rendering', () => {
  test('no leaked de Bruijn indices in limitAdd proof', async () => {
    // Regression test: inlined lambdas inside MkPair inside MkDPair inside eitherElim
    // previously lost their lambda wrappers in the kernel term, causing #N indices to leak.
    // The fix was in LAM-INFER (checker.ts) to preserve the lambda in elaboratedTerm.
    const { REAL_ANALYSIS_CODE } = await import('../presets/real-analysis');
    const result = compileTTFromText(REAL_ANALYSIS_CODE);

    // Verify limitAdd and pickDelta type-check
    for (const block of result.blocks) {
      for (const decl of block.declarations) {
        if (decl.name === 'limitAdd' || decl.name === 'pickDelta') {
          expect(decl.checkSuccess).toBe(true);
        }
      }
    }

    const latexResult = convertToLatex(result);

    // Check pickDelta rendering (contains the eitherElim case bodies)
    const pickDeltaEntry = latexResult.sections.find(e => e.name === 'pickDelta');
    if (pickDeltaEntry) {
      const allLatex = pickDeltaEntry.blocks.map(b => b.latex).join('\n');
      expect(allLatex).not.toMatch(/\\#\d+/);
    }
  });
});
