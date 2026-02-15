import { describe, test, expect } from 'vitest';
import { compileTTFromText } from './compile';
import { convertToLatex } from './latex-converter';

describe('limitAdd rendering', () => {
  test('no leaked de Bruijn indices in limitAdd proof', async () => {
    // Regression test: inlined lambdas inside MkPair inside MkDPair inside eitherElim
    // previously lost their lambda wrappers in the kernel term, causing #N indices to leak.
    // The fix was in LAM-INFER (checker.ts) to preserve the lambda in elaboratedTerm.
    // pickDelta is now inlined into limitAdd, so we only check limitAdd.
    const { REAL_ANALYSIS_CODE } = await import('../presets/real-analysis');
    const result = compileTTFromText(REAL_ANALYSIS_CODE);

    // Verify limitAdd type-checks
    for (const block of result.blocks) {
      for (const decl of block.declarations) {
        if (decl.name === 'limitAdd') {
          expect(decl.checkSuccess).toBe(true);
        }
      }
    }

    const latexResult = convertToLatex(result);

    // Check limitAdd rendering (contains the eitherElim case bodies)
    const limitAddEntry = latexResult.sections.find(e => e.name === 'limitAdd');
    if (limitAddEntry) {
      const allLatex = limitAddEntry.blocks.map(b => b.latex).join('\n');
      expect(allLatex).not.toMatch(/\\#\d+/);
    }
  });
});
