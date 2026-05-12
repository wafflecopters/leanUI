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

  test('negative integer → signed RatLit{-N, 1}', () => {
    const term: any = parseExactExpr('-1', [], definitions);
    expect(term?.tag).toBe('RatLit');
    expect(term?.num).toBe(-1n);
    expect(term?.den).toBe(1n);
  });

  test('negative multi-digit integer → signed RatLit{-N, 1}', () => {
    const term: any = parseExactExpr('-42', [], definitions);
    expect(term?.tag).toBe('RatLit');
    expect(term?.num).toBe(-42n);
    expect(term?.den).toBe(1n);
  });

  test('negative decimal → signed RatLit{-N, D} (gcd-reduced)', () => {
    const term: any = parseExactExpr('-1.5', [], definitions);
    expect(term?.tag).toBe('RatLit');
    expect(term?.num).toBe(-3n);
    expect(term?.den).toBe(2n);
  });
});
