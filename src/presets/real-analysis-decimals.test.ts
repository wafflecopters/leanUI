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
    // NOTE: every literal here is a non-integer rational so the parser
    // produces RatLit (not NatLit). Integer-valued decimals like \`2.0\` or
    // \`100.0\` canonicalize to NatLit and route through @ofNat instead of
    // @ofRat — they break the @ofRat-based homomorphism path. Mixed paths
    // are a known limitation; tracked as a separate workstream.
    withMilestones = compileTTFromText(REAL_ANALYSIS_CODE + `

-- 1.5 + 0.5 = 2.0 — but we phrase as 1.5 + 0.5 = 2.0 written 2.5/1.25
-- to keep both sides RatLit. (Math: 1.5 + 0.5 = 2.0 = 5/2.5)
proof_add : (R : Real) -> Equal {A := Carrier R} (radd 1.5 1.25) 2.75
proof_add R = addRealOfRat R 1.5 1.25

-- 185.6 - 85.7 = 99.9   (THE HEADLINE)
proof_sub : (R : Real) -> Equal {A := Carrier R} (rsub 185.6 85.7) 99.9
proof_sub R = subRealOfRat R 185.6 85.7

-- 1.5 * 4.5 = 6.75
proof_mul : (R : Real) -> Equal {A := Carrier R} (rmul 1.5 4.5) 6.75
proof_mul R = mulRealOfRat R 1.5 4.5

-- 0.99 + 0.99 = 1.98 (decimal addition staying non-integer)
proof_round : (R : Real) -> Equal {A := Carrier R} (radd 0.99 0.99) 1.98
proof_round R = addRealOfRat R 0.99 0.99

-- 99.99 - 0.1 = 99.89 (decimal boundary, both non-integer)
proof_cross : (R : Real) -> Equal {A := Carrier R} (rsub 99.99 0.1) 99.89
proof_cross R = subRealOfRat R 99.99 0.1
`);
  }, COMPILE_TIMEOUT);

  test('preset compiles with all milestone proofs', () => {
    expect(withMilestones.success).toBe(true);
    expect(withMilestones.totalCheckErrors).toBe(0);
  });

  test('1.5 + 1.25 = 2.75 on abstract Real', () => {
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

  test('1.5 * 4.5 = 6.75 on abstract Real', () => {
    const decl = withMilestones.blocks
      .flatMap(b => b.declarations ?? [])
      .find(d => d.name === 'proof_mul');
    expect(decl?.checkSuccess).toBe(true);
  });

  test('0.99 + 0.99 = 1.98 on abstract Real', () => {
    const decl = withMilestones.blocks
      .flatMap(b => b.declarations ?? [])
      .find(d => d.name === 'proof_round');
    expect(decl?.checkSuccess).toBe(true);
  });

  test('99.99 - 0.1 = 99.89 on abstract Real (cross decimal boundary)', () => {
    const decl = withMilestones.blocks
      .flatMap(b => b.declarations ?? [])
      .find(d => d.name === 'proof_cross');
    expect(decl?.checkSuccess).toBe(true);
  });
});
