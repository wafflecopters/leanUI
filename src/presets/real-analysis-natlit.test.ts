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

  // Proof that the abstraction composes: with the literal coercion AND a field
  // axiom (addZeroLeft), we can prove a "computational" fact on abstract Reals.
  // This is the simplest non-trivial use of the @ofNat machinery in proofs.
  let withProof: CompileResult;
  beforeAll(() => {
    withProof = compileTTFromText(REAL_ANALYSIS_CODE + `

-- The simplest "computational" fact on abstract Reals:
--   0 + 1 = 1 (using the addZeroLeft field axiom)
-- The {A := Carrier R} annotation tells Equal which type its sides
-- should be in; without it the standalone literal \`1\` defaults to
-- \`Nat\` and unification fails. Future bidirectional elaboration
-- could propagate the type from the first arg to the second.
zero_plus_one : (R : Real) -> Equal {A := Carrier R} (radd 0 1) 1
zero_plus_one R = addZeroLeft 1
`);
  }, COMPILE_TIMEOUT);

  test('proof: 0 + 1 = 1 on abstract Real (literal coercion + field axiom)', () => {
    expect(withProof.success).toBe(true);
    expect(withProof.totalCheckErrors).toBe(0);
  });

  // ----- The bridge: addRealOfNat lemma -----
  // These tests verify the homomorphism `realOfNat R (plus n m) = realOfNat R n + realOfNat R m`
  // and its consequence: `170 + 34 = 204` is provable on abstract Real, not just Nat.

  let withBridge170: CompileResult,
      withBridge1plus1: CompileResult,
      withBridgeAutoCoerce: CompileResult,
      withBridgeNested: CompileResult,
      withBridgeUsedInProof: CompileResult,
      withWrongAnswer: CompileResult;

  beforeAll(() => {
    // The flagship proof: 170 + 34 = 204 on abstract Carrier R.
    withBridge170 = compileTTFromText(REAL_ANALYSIS_CODE + `

bridge_170_34 : (R : Real) -> Equal (radd (realOfNat R 170) (realOfNat R 34)) (realOfNat R 204)
bridge_170_34 R = addRealOfNat R 170 34
`);

    // Smaller, used as a check that small literals work.
    withBridge1plus1 = compileTTFromText(REAL_ANALYSIS_CODE + `

bridge_1_1 : (R : Real) -> Equal (radd (realOfNat R 1) (realOfNat R 1)) (realOfNat R 2)
bridge_1_1 R = addRealOfNat R 1 1
`);

    // Auto-coercion + the bridge: literals on the LHS of radd, abstract on RHS.
    // This is the closest thing to user-friendly: `radd 170 34 = 204` on Carrier R.
    withBridgeAutoCoerce = compileTTFromText(REAL_ANALYSIS_CODE + `

bridge_auto : (R : Real) -> Equal {A := Carrier R} (radd 170 34) (realOfNat R 204)
bridge_auto R = addRealOfNat R 170 34
`);

    // Nested: chain three additions. Tests that the lemma composes via trans.
    // (1 + 2) + 3 = 6 via two applications of addRealOfNat plus trans/cong.
    withBridgeNested = compileTTFromText(REAL_ANALYSIS_CODE + `

bridge_nested : (R : Real) -> Equal (radd (radd (realOfNat R 1) (realOfNat R 2)) (realOfNat R 3)) (realOfNat R 6)
bridge_nested R = trans (cong (\\z => radd z (realOfNat R 3)) (addRealOfNat R 1 2)) (addRealOfNat R 3 3)
`);

    // The lemma used to bridge two different decompositions of the same number.
    // Prove: 100 + 100 = 50 + 150 on abstract Real, by routing both through
    // realOfNat R 200. This is the canonical "two ways to compute the same
    // value" use case and the foundation for norm_num-style normalization.
    withBridgeUsedInProof = compileTTFromText(REAL_ANALYSIS_CODE + `

bridge_step : (R : Real) -> Equal {A := Carrier R} (radd 100 100) (radd 50 150)
bridge_step R = trans (addRealOfNat R 100 100) (sym (addRealOfNat R 50 150))
`);

    // Negative test: 170 + 34 = 205 must FAIL.
    // This proves the lemma isn't a vacuous trick — wrong answers are rejected.
    withWrongAnswer = compileTTFromText(REAL_ANALYSIS_CODE + `

bridge_wrong : (R : Real) -> Equal (radd (realOfNat R 170) (realOfNat R 34)) (realOfNat R 205)
bridge_wrong R = addRealOfNat R 170 34
`);
  }, COMPILE_TIMEOUT);

  test('bridge: 170 + 34 = 204 on abstract Real via addRealOfNat', () => {
    expect(withBridge170.success).toBe(true);
    expect(withBridge170.totalCheckErrors).toBe(0);
  });

  test('bridge: 1 + 1 = 2 on abstract Real', () => {
    expect(withBridge1plus1.success).toBe(true);
    expect(withBridge1plus1.totalCheckErrors).toBe(0);
  });

  test('bridge: auto-coerced literals — radd 170 34 = 204 on Carrier R', () => {
    expect(withBridgeAutoCoerce.success).toBe(true);
    expect(withBridgeAutoCoerce.totalCheckErrors).toBe(0);
  });

  test('bridge: chained — (1+2)+3 = 6 via composing addRealOfNat', () => {
    expect(withBridgeNested.success).toBe(true);
    expect(withBridgeNested.totalCheckErrors).toBe(0);
  });

  test('bridge: lemma usable inside a larger proof step', () => {
    expect(withBridgeUsedInProof.success).toBe(true);
    expect(withBridgeUsedInProof.totalCheckErrors).toBe(0);
  });

  test('bridge: WRONG answer 170 + 34 = 205 is REJECTED', () => {
    // The whole point of the proof is to verify, not just produce a term.
    // If addRealOfNat happily proved a false equation, our lemma would be wrong.
    expect(withWrongAnswer.success).toBe(false);
    expect(withWrongAnswer.totalCheckErrors).toBeGreaterThan(0);
  });

  // ----- Multiplication bridge: mulRealOfNat -----
  // Same shape as addRealOfNat. NOTE: kept to small N (≤ 4) because the
  // current kernel defeq has a perf cliff around N*M ≈ 25 (tracked separately).

  let withMul3x2: CompileResult,
      withMul0xN: CompileResult,
      withMul1xN: CompileResult,
      withMul2x4: CompileResult,
      withMulAutoCoerce: CompileResult,
      withMulWrong: CompileResult;

  beforeAll(() => {
    withMul3x2 = compileTTFromText(REAL_ANALYSIS_CODE + `

mul_3_2 : (R : Real) -> Equal (rmul (realOfNat R 3) (realOfNat R 2)) (realOfNat R 6)
mul_3_2 R = mulRealOfNat R 3 2
`);

    withMul0xN = compileTTFromText(REAL_ANALYSIS_CODE + `

mul_0_n : (R : Real) -> Equal (rmul (realOfNat R 0) (realOfNat R 99)) (realOfNat R 0)
mul_0_n R = mulRealOfNat R 0 99
`);

    withMul1xN = compileTTFromText(REAL_ANALYSIS_CODE + `

mul_1_n : (R : Real) -> Equal (rmul (realOfNat R 1) (realOfNat R 4)) (realOfNat R 4)
mul_1_n R = mulRealOfNat R 1 4
`);

    withMul2x4 = compileTTFromText(REAL_ANALYSIS_CODE + `

mul_2_4 : (R : Real) -> Equal (rmul (realOfNat R 2) (realOfNat R 4)) (realOfNat R 8)
mul_2_4 R = mulRealOfNat R 2 4
`);

    // Auto-coerced literals + mul: rmul 3 2 = 6 on Carrier R.
    withMulAutoCoerce = compileTTFromText(REAL_ANALYSIS_CODE + `

mul_auto : (R : Real) -> Equal {A := Carrier R} (rmul 3 2) (realOfNat R 6)
mul_auto R = mulRealOfNat R 3 2
`);

    // Negative test: 3*2 = 7 must FAIL.
    withMulWrong = compileTTFromText(REAL_ANALYSIS_CODE + `

mul_wrong : (R : Real) -> Equal (rmul (realOfNat R 3) (realOfNat R 2)) (realOfNat R 7)
mul_wrong R = mulRealOfNat R 3 2
`);
  }, COMPILE_TIMEOUT);

  test('bridge mul: 3 * 2 = 6 on abstract Real via mulRealOfNat', () => {
    expect(withMul3x2.success).toBe(true);
    expect(withMul3x2.totalCheckErrors).toBe(0);
  });

  test('bridge mul: 0 * 99 = 0 (large RHS, instant via Zero case)', () => {
    expect(withMul0xN.success).toBe(true);
    expect(withMul0xN.totalCheckErrors).toBe(0);
  });

  test('bridge mul: 1 * 4 = 4 on abstract Real', () => {
    expect(withMul1xN.success).toBe(true);
    expect(withMul1xN.totalCheckErrors).toBe(0);
  });

  test('bridge mul: 2 * 4 = 8 on abstract Real', () => {
    expect(withMul2x4.success).toBe(true);
    expect(withMul2x4.totalCheckErrors).toBe(0);
  });

  test('bridge mul: auto-coerced — rmul 3 2 = 6 on Carrier R', () => {
    expect(withMulAutoCoerce.success).toBe(true);
    expect(withMulAutoCoerce.totalCheckErrors).toBe(0);
  });

  test('bridge mul: WRONG answer 3 * 2 = 7 is REJECTED', () => {
    expect(withMulWrong.success).toBe(false);
    expect(withMulWrong.totalCheckErrors).toBeGreaterThan(0);
  });
});
