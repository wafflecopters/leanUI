/**
 * Int (Lean-style signed integers) tests.
 *
 * Verifies the two-constructor representation correctly handles:
 * - Pure positive / pure negative arithmetic
 * - Mixed-sign cases (boundary between IntOfNat and IntNegSucc)
 * - The zero edge case (0 + -3 = -3, 0 * -3 = 0, 3 + -3 = 0)
 */
import { describe, test, expect, beforeAll } from 'vitest';
import { compileTTFromText, type CompileResult } from '../compiler/compile';
import { REAL_ANALYSIS_CODE } from './real-analysis';

const COMPILE_TIMEOUT = 120000;

describe('Int arithmetic (Lean-style two-ctor)', () => {
  let withTests: CompileResult;
  beforeAll(() => {
    withTests = compileTTFromText(REAL_ANALYSIS_CODE + `

-- Addition
test_add_pos    : Equal {A := Int} (intAdd (IntOfNat 3) (IntOfNat 5)) (IntOfNat 8)
test_add_pos    = refl
test_add_neg    : Equal {A := Int} (intAdd (IntNegSucc 2) (IntNegSucc 4)) (IntNegSucc 7)
test_add_neg    = refl
test_add_mix_1  : Equal {A := Int} (intAdd (IntOfNat 3) (IntNegSucc 4)) (IntNegSucc 1)
test_add_mix_1  = refl
test_add_mix_2  : Equal {A := Int} (intAdd (IntOfNat 5) (IntNegSucc 2)) (IntOfNat 2)
test_add_mix_2  = refl
test_add_cancel : Equal {A := Int} (intAdd (IntOfNat 3) (IntNegSucc 2)) (IntOfNat 0)
test_add_cancel = refl

-- Subtraction
test_sub_pos    : Equal {A := Int} (intSub (IntOfNat 7) (IntOfNat 3)) (IntOfNat 4)
test_sub_pos    = refl
test_sub_to_neg : Equal {A := Int} (intSub (IntOfNat 3) (IntOfNat 7)) (IntNegSucc 3)
test_sub_to_neg = refl
test_sub_negs   : Equal {A := Int} (intSub (IntNegSucc 4) (IntNegSucc 2)) (IntNegSucc 1)
test_sub_negs   = refl

-- Multiplication
test_mul_pos    : Equal {A := Int} (intMul (IntOfNat 3) (IntOfNat 4)) (IntOfNat 12)
test_mul_pos    = refl
test_mul_neg    : Equal {A := Int} (intMul (IntNegSucc 2) (IntNegSucc 3)) (IntOfNat 12)
test_mul_neg    = refl
test_mul_mix    : Equal {A := Int} (intMul (IntOfNat 3) (IntNegSucc 4)) (IntNegSucc 14)
test_mul_mix    = refl
test_mul_zero_l : Equal {A := Int} (intMul (IntOfNat 0) (IntNegSucc 4)) (IntOfNat 0)
test_mul_zero_l = refl
test_mul_zero_r : Equal {A := Int} (intMul (IntNegSucc 4) (IntOfNat 0)) (IntOfNat 0)
test_mul_zero_r = refl

-- Negation
test_neg_pos    : Equal {A := Int} (intNeg (IntOfNat 5)) (IntNegSucc 4)
test_neg_pos    = refl
test_neg_neg    : Equal {A := Int} (intNeg (IntNegSucc 4)) (IntOfNat 5)
test_neg_neg    = refl
test_neg_zero   : Equal {A := Int} (intNeg (IntOfNat 0)) (IntOfNat 0)
test_neg_zero   = refl
`);
  }, COMPILE_TIMEOUT);

  test('preset compiles with all Int tests', () => {
    expect(withTests.success).toBe(true);
    expect(withTests.totalCheckErrors).toBe(0);
  });

  test('Int has the two expected constructors', () => {
    const intDef = withTests.definitions?.inductiveTypes.get('Int');
    expect(intDef).toBeDefined();
    expect(intDef!.constructors.map(c => c.name).sort()).toEqual(['IntNegSucc', 'IntOfNat']);
  });

  // Spot-check each named test compiled successfully
  const expectedTests = [
    'test_add_pos', 'test_add_neg', 'test_add_mix_1', 'test_add_mix_2', 'test_add_cancel',
    'test_sub_pos', 'test_sub_to_neg', 'test_sub_negs',
    'test_mul_pos', 'test_mul_neg', 'test_mul_mix', 'test_mul_zero_l', 'test_mul_zero_r',
    'test_neg_pos', 'test_neg_neg', 'test_neg_zero',
  ];
  for (const name of expectedTests) {
    test(`${name} proves by refl`, () => {
      const decl = withTests.blocks
        .flatMap(b => b.declarations ?? [])
        .find(d => d.name === name);
      expect(decl?.checkSuccess).toBe(true);
    });
  }
});
