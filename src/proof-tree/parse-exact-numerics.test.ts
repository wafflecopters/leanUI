import { describe, test, expect } from 'vitest';
import { parseExactExpr } from './goal-computation';
import { compileTTFromText } from '../compiler/compile';
import { REAL_ANALYSIS_CODE } from '../presets/real-analysis';

describe('parseExactExpr — numeric literals', () => {
  let definitions: any;
  test('setup', { timeout: 30000 }, () => {
    const r = compileTTFromText(REAL_ANALYSIS_CODE);
    definitions = (r as any).kernelEnv?.definitions ?? (r as any).definitions;
    expect(definitions).toBeTruthy();
  });

  test('positive integer → NatLit', () => {
    const term: any = parseExactExpr('5', [], definitions);
    expect(term?.tag).toBe('NatLit');
    expect(term?.value).toBe(5n);
  });

  test('positive decimal → RatLit (gcd-reduced)', () => {
    const term: any = parseExactExpr('1.5', [], definitions);
    expect(term?.tag).toBe('RatLit');
    expect(term?.num).toBe(3n);
    expect(term?.den).toBe(2n);
  });

  test('negative integer → rneg(_R, NatLit N)', () => {
    const term: any = parseExactExpr('-1', [], definitions);
    expect(term?.tag).toBe('App');
    // Inner positive value:
    expect(term?.arg?.tag).toBe('NatLit');
    expect(term?.arg?.value).toBe(1n);
    // Head spine: rneg with one implicit hole inserted
    expect(term?.fn?.tag).toBe('App');
    expect(term?.fn?.fn?.tag).toBe('Const');
    expect(term?.fn?.fn?.name).toBe('rneg');
    expect(term?.fn?.arg?.tag).toBe('Hole');
  });

  test('negative decimal → rneg(_R, RatLit N/D)', () => {
    const term: any = parseExactExpr('-1.5', [], definitions);
    expect(term?.tag).toBe('App');
    expect(term?.arg?.tag).toBe('RatLit');
    expect(term?.arg?.num).toBe(3n);
    expect(term?.arg?.den).toBe(2n);
    expect(term?.fn?.fn?.name).toBe('rneg');
  });
});
