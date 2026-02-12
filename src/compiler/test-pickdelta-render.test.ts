import { describe, test, expect } from 'vitest';
import { compileTTFromText } from './compile';
import { convertToLatex } from './latex-converter';

describe('limitAdd rendering', () => {
  test('no leaked de Bruijn indices in limitAdd case bodies', async () => {
    // Regression test: inlined lambdas inside MkPair inside MkDPair inside eitherElim
    // previously lost their lambda wrappers in the kernel term, causing #N indices to leak.
    // The fix was in LAM-INFER (checker.ts) to preserve the lambda in elaboratedTerm.
    const { REAL_ANALYSIS_CODE } = await import('../presets/real-analysis');
    const result = compileTTFromText(REAL_ANALYSIS_CODE);
    const latexResult = convertToLatex(result);

    const limitAddEntry = latexResult.sections.find(e => e.name === 'limitAdd');
    expect(limitAddEntry).toBeDefined();

    const allLatex = limitAddEntry!.blocks.map(b => b.latex).join('\n');

    // No leaked de Bruijn indices
    expect(allLatex).not.toMatch(/\\#\d+/);
  });
});
