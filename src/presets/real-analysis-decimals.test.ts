/**
 * Phase 6 milestone: prove decimal-arithmetic identities on abstract Real.
 *
 * The chain:
 *   - Decimal literals (e.g. `185.6`) parse to canonical RatLit (kernel
 *     primitive, gcd-reduced).
 *   - In `Carrier R` position, @ofRat coerces them to `realOfRat R (MkRat n d)`.
 *   - Rat arithmetic (ratPlus/ratMult/ratSub) computes via BigInt fast-path
 *     thanks to @ratAdd/@ratMul/@ratSub primitives.
 *   - The homomorphism lemmas (postulated for now) bridge Rat arithmetic
 *     to abstract Real arithmetic.
 *
 * The user's headline milestone — `185.6 - 85.7 = 99.9` on `Carrier R` — is
 * a one-liner: `subRealOfRat R 185.6 85.7`. The lemma's stated type:
 *   Equal (rsub (realOfRat R a) (realOfRat R b)) (realOfRat R (ratSub a b))
 * The kernel reduces `ratSub 185.6 85.7` to RatLit{999, 10} = 99.9 via
 * the primitive, so the type lines up with the goal `realOfRat R 99.9`.
 */
import { describe, test, expect, beforeAll } from 'vitest';
import { compileTTFromText, type CompileResult } from '../compiler/compile';
import { REAL_ANALYSIS_CODE } from './real-analysis';

const COMPILE_TIMEOUT = 30000;

describe('Phase 6 milestone: decimal arithmetic on abstract Real', () => {
  let withMilestones: CompileResult;
  beforeAll(() => {
    // After the realOfRat-d=1 fix and @ofRat-priority routing, integer
    // and decimal literals coexist in the same expression: \`radd 1.5 2\`
    // produces compatible kernel terms on both sides of the homomorphism
    // lemma. Each test below mixes integer + decimal literals freely.
    withMilestones = compileTTFromText(REAL_ANALYSIS_CODE + `

-- 1.5 + 0.5 = 2.0 (integer-valued result)
proof_add : (R : Real) -> Equal {A := Carrier R} (radd 1.5 0.5) 2.0
proof_add R = addRealOfRat R 1.5 0.5

-- 185.6 - 85.7 = 99.9   (THE HEADLINE)
proof_sub : (R : Real) -> Equal {A := Carrier R} (rsub 185.6 85.7) 99.9
proof_sub R = subRealOfRat R 185.6 85.7

-- 1.5 * 4 = 6.0 (mixed integer + decimal operand, integer-valued result)
proof_mul : (R : Real) -> Equal {A := Carrier R} (rmul 1.5 4) 6.0
proof_mul R = mulRealOfRat R 1.5 4

-- 0.99 + 0.01 = 1.0 (decimal rounding to integer)
proof_round : (R : Real) -> Equal {A := Carrier R} (radd 0.99 0.01) 1.0
proof_round R = addRealOfRat R 0.99 0.01

-- 100 - 0.1 = 99.9 (mixed integer-on-LHS + decimal-on-RHS)
proof_cross : (R : Real) -> Equal {A := Carrier R} (rsub 100 0.1) 99.9
proof_cross R = subRealOfRat R 100 0.1
`);
  }, COMPILE_TIMEOUT);

  test('preset compiles with all milestone proofs', () => {
    expect(withMilestones.success).toBe(true);
    expect(withMilestones.totalCheckErrors).toBe(0);
  });

  test('rat homomorphism lemmas are present in the preset output', () => {
    const declarationNames = new Set(
      withMilestones.blocks.flatMap(b => b.declarations ?? []).map(d => d.name)
    );
    expect(declarationNames.has('addRealOfRat')).toBe(true);
    expect(declarationNames.has('mulRealOfRat')).toBe(true);
    expect(declarationNames.has('subRealOfRat')).toBe(true);
  });

  test('1.5 + 0.5 = 2.0 on abstract Real (integer-valued result)', () => {
    const decl = withMilestones.blocks
      .flatMap(b => b.declarations ?? [])
      .find(d => d.name === 'proof_add');
    expect(decl?.checkSuccess).toBe(true);
  });

  test('THE MILESTONE: 185.6 - 85.7 = 99.9 on abstract Real', () => {
    const decl = withMilestones.blocks
      .flatMap(b => b.declarations ?? [])
      .find(d => d.name === 'proof_sub');
    expect(decl?.checkSuccess).toBe(true);
  });

  test('1.5 * 4 = 6.0 on abstract Real (mixed integer + decimal)', () => {
    const decl = withMilestones.blocks
      .flatMap(b => b.declarations ?? [])
      .find(d => d.name === 'proof_mul');
    expect(decl?.checkSuccess).toBe(true);
  });

  test('0.99 + 0.01 = 1.0 on abstract Real (decimal rounding to integer)', () => {
    const decl = withMilestones.blocks
      .flatMap(b => b.declarations ?? [])
      .find(d => d.name === 'proof_round');
    expect(decl?.checkSuccess).toBe(true);
  });

  test('100 - 0.1 = 99.9 on abstract Real (mixed integer LHS + decimal)', () => {
    const decl = withMilestones.blocks
      .flatMap(b => b.declarations ?? [])
      .find(d => d.name === 'proof_cross');
    expect(decl?.checkSuccess).toBe(true);
  });
});
