/**
 * Verify NatLit + @ofNat work end-to-end in the real-analysis preset.
 *
 * After Phase 3b, users can write `1 : Carrier R` and the elaborator
 * inserts `realOfNat R 1` automatically.
 */

import { describe, test, expect, beforeAll } from 'vitest';
import { compileTTFromText, type CompileResult } from '../compiler/compile';
import { REAL_ANALYSIS_CODE } from './real-analysis';

const COMPILE_TIMEOUT = 30000;

describe('NatLit + @ofNat in real-analysis preset', () => {
  let baseline: CompileResult;
  beforeAll(() => {
    baseline = compileTTFromText(REAL_ANALYSIS_CODE);
  }, COMPILE_TIMEOUT);

  test('preset compiles successfully', () => {
    expect(baseline.success).toBe(true);
    expect(baseline.totalCheckErrors).toBe(0);
  });

  test('Nat is registered as @impl=nat', () => {
    const reg = baseline.definitions?.natImplByCtor;
    expect(reg).toBeDefined();
    expect(reg!.get('Zero')).toMatchObject({ inductiveName: 'Nat', zeroCtor: 'Zero', succCtor: 'Succ' });
    expect(reg!.get('Succ')).toMatchObject({ inductiveName: 'Nat', zeroCtor: 'Zero', succCtor: 'Succ' });
  });

  test('realOfNat is registered as @ofNat for Carrier', () => {
    const reg = baseline.definitions?.ofNatByTargetHead;
    expect(reg).toBeDefined();
    expect(reg!.get('Carrier')).toBe('realOfNat');
  });

  // Augmented compiles for the literal-coercion tests below
  let withOne: CompileResult, withZero: CompileResult, withFive: CompileResult, withArith: CompileResult;
  beforeAll(() => {
    withOne = compileTTFromText(REAL_ANALYSIS_CODE + `

oneInRealCarrier : (R : Real) -> Carrier R
oneInRealCarrier R = 1
`);
    withZero = compileTTFromText(REAL_ANALYSIS_CODE + `

zeroInRealCarrier : (R : Real) -> Carrier R
zeroInRealCarrier R = 0
`);
    withFive = compileTTFromText(REAL_ANALYSIS_CODE + `

fiveInRealCarrier : (R : Real) -> Carrier R
fiveInRealCarrier R = 5
`);
    withArith = compileTTFromText(REAL_ANALYSIS_CODE + `

twoPlusThree : (R : Real) -> Carrier R
twoPlusThree R = radd 2 3
`);
  }, COMPILE_TIMEOUT);

  test('user code: `1 : Carrier R` typechecks via auto-coercion', () => {
    expect(withOne.success).toBe(true);
    expect(withOne.totalCheckErrors).toBe(0);
  });

  test('user code: `0 : Carrier R` typechecks via auto-coercion', () => {
    expect(withZero.success).toBe(true);
    expect(withZero.totalCheckErrors).toBe(0);
  });

  test('user code: `5 : Carrier R` typechecks via auto-coercion', () => {
    expect(withFive.success).toBe(true);
    expect(withFive.totalCheckErrors).toBe(0);
  });

  test('user code: arithmetic with literals works', () => {
    expect(withArith.success).toBe(true);
    expect(withArith.totalCheckErrors).toBe(0);
  });
});
