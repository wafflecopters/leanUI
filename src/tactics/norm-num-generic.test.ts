/**
 * Proof-of-genericity: a minimal SECOND preset with entirely different names
 * (\`madd\` / \`mmul\` / \`mzero\` / \`mone\` / \`mtwo\` instead of \`r*\`)
 * gets the full norm_num pipeline — registry population, inferIsRat
 * evaluation, isCarrierArithHead recognition, AND the renderer's display
 * lookup — purely by tagging its functions with the same generic
 * \`@carrier*\` annotations. ZERO kernel/pipeline changes needed.
 *
 * If this test passes alongside the existing real-analysis tests, the
 * "generic" claim is honest: the infrastructure is data-driven, not
 * hardcoded to any specific preset.
 */

import { describe, test, expect } from 'vitest';
import { compileTTFromText } from '../compiler/compile';
import { inferIsRat, isCarrierArithHead, ratValueLabel } from './norm-num';
import { buildReverseRegistry } from '../math-editor/tt-to-math';
import type { TTKTerm } from '../compiler/kernel';

// A minimal preset built on top of Nat. The "Magnitude" type is a tagged
// Nat — totally different naming convention from real-analysis. Tagged
// with @carrierAdd / @carrierMul / @carrierValue so the generic
// norm_num infra picks it up.
const MAGNITUDE_PRESET = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

plus : Nat -> Nat -> Nat
plus Zero m = m
plus (Succ n) m = Succ (plus n m)

mult : Nat -> Nat -> Nat
mult Zero m = Zero
mult (Succ n) m = plus m (mult n m)

inductive Magnitude : Type where
  MkMag : Nat -> Magnitude

@syntax @carrierValue 0
mzero : Magnitude
mzero = MkMag Zero

@syntax @carrierValue 1
mone : Magnitude
mone = MkMag (Succ Zero)

@syntax @carrierValue 2
mtwo : Magnitude
mtwo = MkMag (Succ (Succ Zero))

@syntax @carrierAdd
madd : Magnitude -> Magnitude -> Magnitude
madd (MkMag a) (MkMag b) = MkMag (plus a b)

@syntax @carrierMul
mmul : Magnitude -> Magnitude -> Magnitude
mmul (MkMag a) (MkMag b) = MkMag (mult a b)
`;

describe('norm_num generic: Magnitude preset (NOT real-analysis)', () => {
  const r = compileTTFromText(MAGNITUDE_PRESET);
  const definitions = r.definitions!;

  test('preset compiles cleanly', () => {
    // No checkErrors on the magnitude definitions themselves.
    const magnitudeDecls = ['mzero', 'mone', 'mtwo', 'madd', 'mmul'];
    for (const name of magnitudeDecls) {
      const decl = r.blocks.flatMap(b => b.declarations).find(d => d.name === name);
      expect(decl, `decl ${name} should exist`).toBeDefined();
      expect(decl?.checkErrors ?? [], `decl ${name} should have no check errors`).toHaveLength(0);
    }
  });

  test('@carrierXxx annotations populate the registry — generic, no real-analysis names', () => {
    // Op registry: madd → add, mmul → mul (these are MAGNITUDE names, not r-prefixed)
    expect(definitions.carrierOpByFn?.get('madd')).toBe('add');
    expect(definitions.carrierOpByFn?.get('mmul')).toBe('mul');
    // Value registry: mzero/mone/mtwo → 0/1/2
    expect(definitions.carrierValues?.get('mzero')).toEqual({ num: 0n, den: 1n });
    expect(definitions.carrierValues?.get('mone')).toEqual({ num: 1n, den: 1n });
    expect(definitions.carrierValues?.get('mtwo')).toEqual({ num: 2n, den: 1n });
  });

  test('inferIsRat works on the Magnitude preset using its own names', () => {
    const mzero: TTKTerm = { tag: 'Const', name: 'mzero' };
    // mzero takes no args, but inferIsRat expects an App for leaf classification.
    // The renderer's actual subterms will be Const-of-zero-args. Adapt the
    // test by directly using the Const term. inferIsRat returns null for
    // bare Consts, so we need to wrap in App. But mzero in this preset is
    // a Const, not a function. Construct it as the kernel does:
    // \`mzero\` → \`App(MkMag, Zero)\` after δ-reduction, but for the registry
    // path we just check the Const head. The current inferIsRat requires
    // args.length === 1 for carrierValue lookup — adapt the test to use
    // a wrapped form.

    // Build: \`madd mtwo mone\` — should evaluate to 3.
    // madd takes 2 explicit args (no implicit R since Magnitude has no
    // parameter), so the term is App(App(Const("madd"), mtwo), mone).
    const mone: TTKTerm = { tag: 'Const', name: 'mone' };
    const mtwo: TTKTerm = { tag: 'Const', name: 'mtwo' };
    const madd_2_1: TTKTerm = {
      tag: 'App',
      fn: { tag: 'App', fn: { tag: 'Const', name: 'madd' }, arg: mtwo },
      arg: mone,
    };
    // inferIsRat needs the leaf carrierValue terms to be Apps (it requires
    // args.length >= 1 for carrierValue lookup since it expects spine).
    // Magnitude leaves are bare Consts — null args. To make inferIsRat
    // recognize them, the spine extraction needs to handle bare Const.
    // Check current behavior:
    const result = inferIsRat(madd_2_1, definitions);
    // Expected: 2 + 1 = 3. Current inferIsRat may fail because it requires
    // args.length === 1 for carrierValue lookup.
    expect(result).toEqual({ num: 3n, den: 1n });
  });

  test('isCarrierArithHead recognizes Magnitude ops generically', () => {
    expect(isCarrierArithHead('madd', definitions)).toBe(true);
    expect(isCarrierArithHead('mmul', definitions)).toBe(true);
    // Magnitude doesn't define sub/neg/inv/div — registry should NOT have them
    expect(isCarrierArithHead('msub', definitions)).toBe(false);
    expect(isCarrierArithHead('mneg', definitions)).toBe(false);
    // Real-analysis names shouldn't accidentally bleed in
    expect(isCarrierArithHead('radd', definitions)).toBe(false);
    // Non-arith heads
    expect(isCarrierArithHead('mzero', definitions)).toBe(false);
    expect(isCarrierArithHead('plus', definitions)).toBe(false);
  });

  test('renderer carrierValueDisplay map is built from registry', () => {
    const rev = buildReverseRegistry({ symbolMap: new Map(), entries: [] }, definitions);
    // Magnitude literals show up with their values
    expect(rev.carrierValueDisplay?.get('mzero')).toBe('0');
    expect(rev.carrierValueDisplay?.get('mone')).toBe('1');
    expect(rev.carrierValueDisplay?.get('mtwo')).toBe('2');
    // Real-analysis names shouldn't be in THIS preset's rev
    expect(rev.carrierValueDisplay?.get('rzero')).toBeUndefined();
  });

  test('ratValueLabel works the same way regardless of preset', () => {
    expect(ratValueLabel({ num: 3n, den: 1n })).toBe('3');
    expect(ratValueLabel({ num: 1n, den: 2n })).toBe('1/2');
  });
});
