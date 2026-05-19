/**
 * Test that the Generic Literals Demo preset proves the @carrier* system
 * is genuinely generic across multiple algebras AND that each algebra can
 * close a concrete arithmetic theorem by refl.
 *
 * Asserts:
 *   - The preset compiles cleanly (no checkErrors).
 *   - All four algebras (Nat / Int / Real / Complex) populate
 *     `carrierOpByFn` and `carrierValues` in DefinitionsMap.
 *   - `inferIsRat` evaluates closed arithmetic in EACH algebra
 *     correctly, using ONLY the registry — no preset-specific code.
 *   - `isCarrierArithHead` recognizes the right heads in each algebra.
 *   - The four `1 + 4 = 5` theorems each typecheck (= refl reduction
 *     goes through end-to-end in each algebra).
 */
import { describe, test, expect } from 'vitest';
import { compileTTFromText } from '../compiler/compile';
import { LITERALS_DEMO_CODE } from './literals-demo';
import { inferIsRat, isCarrierArithHead } from '../tactics/norm-num';
import { buildReverseRegistry } from '../math-editor/tt-to-math';
import type { TTKTerm } from '../compiler/kernel';

describe('Generic Literals Demo preset', () => {
  const r = compileTTFromText(LITERALS_DEMO_CODE);
  const definitions = r.definitions!;
  const allDecls = r.blocks.flatMap(b => b.declarations);
  const findDecl = (name: string) => allDecls.find(d => d.name === name);

  test('preset compiles with no check errors', () => {
    const declsWithErrors = allDecls.filter(d =>
      d.checkErrors && d.checkErrors.length > 0
    );
    if (declsWithErrors.length > 0) {
      const summary = declsWithErrors.map(d => {
        const errs = (d.checkErrors ?? []).map(e =>
          typeof e === 'string' ? e : (e as any).message ?? JSON.stringify(e)
        ).join('; ');
        return `${d.name}: ${errs}`;
      }).join('\n');
      throw new Error(`Check errors in preset:\n${summary}`);
    }
    expect(declsWithErrors).toHaveLength(0);
  });

  test('registry populated across all four algebras', () => {
    // ALGEBRA 1: Nat (plus / mult tagged with both @natAdd and @carrierAdd)
    expect(definitions.carrierOpByFn?.get('plus')).toBe('add');
    expect(definitions.carrierOpByFn?.get('mult')).toBe('mul');
    expect(definitions.carrierValues?.get('nat_0')).toEqual({ num: 0n, den: 1n });
    expect(definitions.carrierValues?.get('nat_1')).toEqual({ num: 1n, den: 1n });
    expect(definitions.carrierValues?.get('nat_4')).toEqual({ num: 4n, den: 1n });
    expect(definitions.carrierValues?.get('nat_5')).toEqual({ num: 5n, den: 1n });

    // ALGEBRA 2: Int
    expect(definitions.carrierOpByFn?.get('intAdd')).toBe('add');
    expect(definitions.carrierOpByFn?.get('intNegFn')).toBe('neg');
    expect(definitions.carrierValues?.get('int_0')).toEqual({ num: 0n, den: 1n });
    expect(definitions.carrierValues?.get('int_1')).toEqual({ num: 1n, den: 1n });
    expect(definitions.carrierValues?.get('int_4')).toEqual({ num: 4n, den: 1n });
    expect(definitions.carrierValues?.get('int_5')).toEqual({ num: 5n, den: 1n });
    expect(definitions.carrierValues?.get('int_neg1')).toEqual({ num: -1n, den: 1n });

    // ALGEBRA 3: Real
    expect(definitions.carrierOpByFn?.get('realAdd')).toBe('add');
    expect(definitions.carrierOpByFn?.get('realNeg')).toBe('neg');
    expect(definitions.carrierValues?.get('real_0')).toEqual({ num: 0n, den: 1n });
    expect(definitions.carrierValues?.get('real_1')).toEqual({ num: 1n, den: 1n });
    expect(definitions.carrierValues?.get('real_4')).toEqual({ num: 4n, den: 1n });
    expect(definitions.carrierValues?.get('real_5')).toEqual({ num: 5n, den: 1n });

    // ALGEBRA 4: Complex
    expect(definitions.carrierOpByFn?.get('complexAdd')).toBe('add');
    expect(definitions.carrierValues?.get('complex_0')).toEqual({ num: 0n, den: 1n });
    expect(definitions.carrierValues?.get('complex_1')).toEqual({ num: 1n, den: 1n });
    expect(definitions.carrierValues?.get('complex_4')).toEqual({ num: 4n, den: 1n });
    expect(definitions.carrierValues?.get('complex_5')).toEqual({ num: 5n, den: 1n });
  });

  test('inferIsRat evaluates 1+4=5 in each algebra via the registry', () => {
    const mkAdd = (head: string, a: TTKTerm, b: TTKTerm): TTKTerm => ({
      tag: 'App',
      fn: { tag: 'App', fn: { tag: 'Const', name: head }, arg: a },
      arg: b,
    });
    const c = (name: string): TTKTerm => ({ tag: 'Const', name });

    // Nat:  plus nat_1 nat_4 → 5
    expect(inferIsRat(mkAdd('plus', c('nat_1'), c('nat_4')), definitions))
      .toEqual({ num: 5n, den: 1n });

    // Int:  intAdd int_1 int_4 → 5
    expect(inferIsRat(mkAdd('intAdd', c('int_1'), c('int_4')), definitions))
      .toEqual({ num: 5n, den: 1n });

    // Real: realAdd real_1 real_4 → 5
    expect(inferIsRat(mkAdd('realAdd', c('real_1'), c('real_4')), definitions))
      .toEqual({ num: 5n, den: 1n });

    // Complex: complexAdd complex_1 complex_4 → 5
    expect(inferIsRat(mkAdd('complexAdd', c('complex_1'), c('complex_4')), definitions))
      .toEqual({ num: 5n, den: 1n });
  });

  test('isCarrierArithHead distinguishes the four algebras cleanly', () => {
    expect(isCarrierArithHead('plus', definitions)).toBe(true);
    expect(isCarrierArithHead('mult', definitions)).toBe(true);
    expect(isCarrierArithHead('intAdd', definitions)).toBe(true);
    expect(isCarrierArithHead('intNegFn', definitions)).toBe(true);
    expect(isCarrierArithHead('realAdd', definitions)).toBe(true);
    expect(isCarrierArithHead('realNeg', definitions)).toBe(true);
    expect(isCarrierArithHead('complexAdd', definitions)).toBe(true);

    // Constructors aren't arithmetic heads
    expect(isCarrierArithHead('MkReal', definitions)).toBe(false);
    expect(isCarrierArithHead('MkComplex', definitions)).toBe(false);
    // Literal-named functions aren't arithmetic heads (they're values, not ops)
    expect(isCarrierArithHead('nat_1', definitions)).toBe(false);
    expect(isCarrierArithHead('complex_5', definitions)).toBe(false);
    // Real-analysis names aren't in THIS preset
    expect(isCarrierArithHead('radd', definitions)).toBe(false);
  });

  test('renderer carrierValueDisplay map contains all four algebras', () => {
    const rev = buildReverseRegistry({ symbolMap: new Map(), entries: [] }, definitions);
    // Nat
    expect(rev.carrierValueDisplay?.get('nat_0')).toBe('0');
    expect(rev.carrierValueDisplay?.get('nat_5')).toBe('5');
    // Int
    expect(rev.carrierValueDisplay?.get('int_neg1')).toBe('-1');
    expect(rev.carrierValueDisplay?.get('int_4')).toBe('4');
    // Real
    expect(rev.carrierValueDisplay?.get('real_1')).toBe('1');
    expect(rev.carrierValueDisplay?.get('real_5')).toBe('5');
    // Complex
    expect(rev.carrierValueDisplay?.get('complex_0')).toBe('0');
    expect(rev.carrierValueDisplay?.get('complex_4')).toBe('4');
    // Unary op display picked up the @carrierNeg tags
    expect(rev.carrierUnaryOpDisplay?.get('intNegFn')).toBe('-');
    expect(rev.carrierUnaryOpDisplay?.get('realNeg')).toBe('-');
  });

  test('the four "1 + 4 = 5" proofs each typecheck (refl reduction works end-to-end)', () => {
    for (const name of [
      'natOnePlusFour',
      'intOnePlusFour',
      'realOnePlusFour',
      'complexOnePlusFour',
    ]) {
      const decl = findDecl(name);
      expect(decl, `${name} should exist`).toBeDefined();
      const errs = decl?.checkErrors ?? [];
      if (errs.length > 0) {
        const msg = errs.map(e =>
          typeof e === 'string' ? e : (e as any).message ?? JSON.stringify(e)
        ).join('; ');
        throw new Error(`${name} failed to typecheck: ${msg}`);
      }
      expect(errs).toHaveLength(0);
    }
  });
});
