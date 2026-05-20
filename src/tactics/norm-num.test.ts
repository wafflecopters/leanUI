import { describe, test, expect } from 'vitest';
import { compileTTFromText } from '../compiler/compile';
import { REAL_ANALYSIS_CODE } from '../presets/real-analysis';
import { inferIsRat, ratValueLabel, isCarrierArithHead } from './norm-num';
import type { TTKTerm } from '../compiler/kernel';

describe('inferIsRat — generic registry-driven', () => {
  // Compile the real-analysis preset ONCE to populate carrierOpByFn /
  // carrierValues / ofRatByTargetHead etc. from its @carrier* annotations.
  // This test asserts norm_num works WITHOUT any hardcoded names — purely
  // via the registry the preset populates.
  let definitions: ReturnType<typeof compileTTFromText>['definitions'];
  let R: TTKTerm;
  let rzero: TTKTerm, rone: TTKTerm, rtwo: TTKTerm, rhalf: TTKTerm;
  const radd = (a: TTKTerm, b: TTKTerm): TTKTerm => ({
    tag: 'App',
    fn: { tag: 'App', fn: { tag: 'App', fn: { tag: 'Const', name: 'radd' }, arg: R }, arg: a },
    arg: b,
  });
  const rsub = (a: TTKTerm, b: TTKTerm): TTKTerm => ({
    tag: 'App',
    fn: { tag: 'App', fn: { tag: 'App', fn: { tag: 'Const', name: 'rsub' }, arg: R }, arg: a },
    arg: b,
  });
  const rmul = (a: TTKTerm, b: TTKTerm): TTKTerm => ({
    tag: 'App',
    fn: { tag: 'App', fn: { tag: 'App', fn: { tag: 'Const', name: 'rmul' }, arg: R }, arg: a },
    arg: b,
  });
  const rneg = (a: TTKTerm): TTKTerm => ({
    tag: 'App',
    fn: { tag: 'App', fn: { tag: 'Const', name: 'rneg' }, arg: R },
    arg: a,
  });
  const rinv = (a: TTKTerm): TTKTerm => ({
    tag: 'App',
    fn: { tag: 'App', fn: { tag: 'Const', name: 'rinv' }, arg: R },
    arg: a,
  });
  const rdiv = (a: TTKTerm, b: TTKTerm): TTKTerm => ({
    tag: 'App',
    fn: { tag: 'App', fn: { tag: 'App', fn: { tag: 'Const', name: 'rdiv' }, arg: R }, arg: a },
    arg: b,
  });
  const realOfRatLit = (num: number, den: number): TTKTerm => ({
    tag: 'App',
    fn: { tag: 'App', fn: { tag: 'Const', name: 'realOfRat' }, arg: R },
    arg: { tag: 'RatLit', num: BigInt(num), den: BigInt(den) },
  });

  // Set up before all tests
  const r = compileTTFromText(REAL_ANALYSIS_CODE);
  definitions = r.definitions!;
  R = { tag: 'Var', index: 0 } as any; // stand-in for a Real in scope
  rzero = { tag: 'App', fn: { tag: 'Const', name: 'rzero' }, arg: R };
  rone = { tag: 'App', fn: { tag: 'Const', name: 'rone' }, arg: R };
  rtwo = { tag: 'App', fn: { tag: 'Const', name: 'rtwo' }, arg: R };
  rhalf = { tag: 'App', fn: { tag: 'Const', name: 'rhalf' }, arg: R };

  test('preset compiles and populates carrier registries', () => {
    expect(definitions.carrierOpByFn).toBeDefined();
    // Five core arithmetic ops should be registered from the @carrierXxx tags
    expect(definitions.carrierOpByFn!.get('radd')).toBe('add');
    expect(definitions.carrierOpByFn!.get('rsub')).toBe('sub');
    expect(definitions.carrierOpByFn!.get('rmul')).toBe('mul');
    expect(definitions.carrierOpByFn!.get('rneg')).toBe('neg');
    expect(definitions.carrierOpByFn!.get('rinv')).toBe('inv');
    expect(definitions.carrierOpByFn!.get('rdiv')).toBe('div');
    // Literals
    expect(definitions.carrierValues!.get('rzero')).toEqual({ num: 0n, den: 1n });
    expect(definitions.carrierValues!.get('rone')).toEqual({ num: 1n, den: 1n });
    expect(definitions.carrierValues!.get('rtwo')).toEqual({ num: 2n, den: 1n });
    expect(definitions.carrierValues!.get('rhalf')).toEqual({ num: 1n, den: 2n });
    // Bridges: the alias-→-realOfRat bridges norm_num uses to normalize
    // alias-form literals before applying arithmetic homomorphism lemmas.
    expect(definitions.carrierBridges).toBeDefined();
    expect(definitions.carrierBridges!.has('rzeroAsRealOfRat')).toBe(true);
    expect(definitions.carrierBridges!.has('roneAsRealOfRat')).toBe(true);
    expect(definitions.carrierBridges!.has('rtwoAsRealOfRat')).toBe(true);
  });

  test('rzero R → 0  (via @carrierValue 0)', () => {
    expect(inferIsRat(rzero, definitions)).toEqual({ num: 0n, den: 1n });
  });

  test('rtwo R → 2  (via @carrierValue 2)', () => {
    expect(inferIsRat(rtwo, definitions)).toEqual({ num: 2n, den: 1n });
  });

  test('rhalf R → 1/2  (via @carrierValue 1/2)', () => {
    expect(inferIsRat(rhalf, definitions)).toEqual({ num: 1n, den: 2n });
  });

  test('realOfRat R (RatLit -1 1) → -1  (via @ofRat coercion registry)', () => {
    expect(inferIsRat(realOfRatLit(-1, 1), definitions)).toEqual({ num: -1n, den: 1n });
  });

  test('radd rtwo (realOfRat -1) → 1  (the user image-#47 case)', () => {
    expect(inferIsRat(radd(rtwo, realOfRatLit(-1, 1)), definitions)).toEqual({ num: 1n, den: 1n });
  });

  test('rsub rtwo rone → 1', () => {
    expect(inferIsRat(rsub(rtwo, rone), definitions)).toEqual({ num: 1n, den: 1n });
  });

  test('rmul rtwo rtwo → 4', () => {
    expect(inferIsRat(rmul(rtwo, rtwo), definitions)).toEqual({ num: 4n, den: 1n });
  });

  test('rneg rone → -1', () => {
    expect(inferIsRat(rneg(rone), definitions)).toEqual({ num: -1n, den: 1n });
  });

  test('rinv rtwo → 1/2', () => {
    expect(inferIsRat(rinv(rtwo), definitions)).toEqual({ num: 1n, den: 2n });
  });

  test('rinv rzero → null (1/0 undefined)', () => {
    expect(inferIsRat(rinv(rzero), definitions)).toBeNull();
  });

  test('rdiv rone rtwo → 1/2', () => {
    expect(inferIsRat(rdiv(rone, rtwo), definitions)).toEqual({ num: 1n, den: 2n });
  });

  test('nested: radd (rmul rtwo rtwo) (rneg rone) → 3', () => {
    expect(inferIsRat(radd(rmul(rtwo, rtwo), rneg(rone)), definitions)).toEqual({ num: 3n, den: 1n });
  });

  // REGRESSION (image #50): in deeply-nested proof contexts (limits via
  // ltLeTrans / addLeRightCancel chains), δ-reduction sometimes unfolds the
  // `radd` / `rzero` / `rone` aliases to their underlying record-projection
  // forms (`CompleteOrderedField.add (field R) a b`, etc.). The Compute
  // suggestion was missing because the registry was keyed only under the
  // alias names. Now the @carrier* registration propagates leaf aliases to
  // their underlying head, so projection-form goals classify identically.
  test('projection-form aliasing: CompleteOrderedField.add classifies as carrier add', () => {
    expect(isCarrierArithHead('CompleteOrderedField.add', definitions)).toBe(true);
    expect(isCarrierArithHead('CompleteOrderedField.mul', definitions)).toBe(true);
    expect(isCarrierArithHead('CompleteOrderedField.neg', definitions)).toBe(true);
  });

  test('projection-form aliasing: CompleteOrderedField.zero/one classify as carrier values', () => {
    expect(definitions.carrierValues!.get('CompleteOrderedField.zero')).toEqual({ num: 0n, den: 1n });
    expect(definitions.carrierValues!.get('CompleteOrderedField.one')).toEqual({ num: 1n, den: 1n });
  });

  test('projection-form aliasing: rtwo / rhalf NOT propagated (derived, not leaf aliases)', () => {
    // rtwo R = radd (rone R) (rone R)   — 2 top-level apps → not a leaf alias
    // rhalf R = rinv (rtwo R)            — rinv has implicit R → 2 apps → not a leaf
    // Propagating these as carrierValues would mis-tag radd / rinv as
    // literals, since unfoldLeafAliasHead correctly walks past the first
    // App to find the underlying head.
    expect(definitions.carrierValues!.get('radd')).toBeUndefined();
    expect(definitions.carrierValues!.get('rinv')).toBeUndefined();
  });

  test('projection-form arithmetic: inferIsRat on unfolded radd (= 2 + (-1)) → 1', () => {
    // Construct the kernel form the user actually sees in image #50 after
    // δ-reduction has unfolded `radd`: CompleteOrderedField.add applied to
    // (field R) plus two operands. Both operands left as their alias forms
    // for simplicity (the test for the unfolded literal forms is below).
    const cofAdd = (a: TTKTerm, b: TTKTerm): TTKTerm => ({
      tag: 'App',
      fn: { tag: 'App', fn: { tag: 'App',
        fn: { tag: 'Const', name: 'CompleteOrderedField.add' },
        arg: { tag: 'App', fn: { tag: 'Const', name: 'field' }, arg: R } },
        arg: a }, arg: b });
    expect(inferIsRat(cofAdd(rtwo, rneg(rone)), definitions))
      .toEqual({ num: 1n, den: 1n });
  });

  test('returns null for free variable', () => {
    expect(inferIsRat({ tag: 'Var', index: 5 }, definitions)).toBeNull();
  });

  test('returns null for unknown head', () => {
    const t: TTKTerm = { tag: 'App', fn: { tag: 'Const', name: 'foo' }, arg: R };
    expect(inferIsRat(t, definitions)).toBeNull();
  });

  test('returns null when arithmetic op has a non-closed arg', () => {
    const t = radd(rone, { tag: 'Var', index: 7 });
    expect(inferIsRat(t, definitions)).toBeNull();
  });

  test('isCarrierArithHead reads from registry, not hardcoded list', () => {
    expect(isCarrierArithHead('radd', definitions)).toBe(true);
    expect(isCarrierArithHead('rsub', definitions)).toBe(true);
    expect(isCarrierArithHead('rmul', definitions)).toBe(true);
    expect(isCarrierArithHead('rneg', definitions)).toBe(true);
    expect(isCarrierArithHead('rinv', definitions)).toBe(true);
    expect(isCarrierArithHead('rdiv', definitions)).toBe(true);
    // Non-arith heads return false
    expect(isCarrierArithHead('rle', definitions)).toBe(false);
    expect(isCarrierArithHead('rzero', definitions)).toBe(false);
    expect(isCarrierArithHead('foo', definitions)).toBe(false);
    expect(isCarrierArithHead(undefined, definitions)).toBe(false);
  });

  test('ratValueLabel formats integers without slash', () => {
    expect(ratValueLabel({ num: 5n, den: 1n })).toBe('5');
    expect(ratValueLabel({ num: -3n, den: 1n })).toBe('-3');
    expect(ratValueLabel({ num: 1n, den: 2n })).toBe('1/2');
  });
});
