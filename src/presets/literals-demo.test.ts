/**
 * Test that the Generic Literals Demo preset proves the @carrier* system
 * is genuinely generic across multiple presets/algebras.
 *
 * Asserts:
 *   - The preset compiles cleanly (no checkErrors).
 *   - All three algebras (Magnitude / Score / Fraction) populate
 *     `carrierOpByFn` and `carrierValues` in DefinitionsMap.
 *   - `inferIsRat` evaluates closed arithmetic in EACH algebra
 *     correctly, using ONLY the registry — no preset-specific code.
 *   - `isCarrierArithHead` recognizes the right heads in each algebra
 *     and rejects others.
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

  test('preset compiles with no check errors', () => {
    const declsWithErrors = r.blocks.flatMap(b => b.declarations).filter(d =>
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

  test('registry populated with all three algebras', () => {
    // ALGEBRA 1: Magnitude
    expect(definitions.carrierOpByFn?.get('madd')).toBe('add');
    expect(definitions.carrierOpByFn?.get('mmul')).toBe('mul');
    expect(definitions.carrierValues?.get('mzero')).toEqual({ num: 0n, den: 1n });
    expect(definitions.carrierValues?.get('mone')).toEqual({ num: 1n, den: 1n });
    expect(definitions.carrierValues?.get('mtwo')).toEqual({ num: 2n, den: 1n });
    expect(definitions.carrierValues?.get('mthree')).toEqual({ num: 3n, den: 1n });

    // ALGEBRA 2: Score
    expect(definitions.carrierOpByFn?.get('sadd')).toBe('add');
    expect(definitions.carrierOpByFn?.get('sneg')).toBe('neg');
    expect(definitions.carrierValues?.get('szero')).toEqual({ num: 0n, den: 1n });
    expect(definitions.carrierValues?.get('sone')).toEqual({ num: 1n, den: 1n });
    expect(definitions.carrierValues?.get('sneg_one')).toEqual({ num: -1n, den: 1n });

    // ALGEBRA 3: Fraction
    expect(definitions.carrierOpByFn?.get('fadd')).toBe('add');
    expect(definitions.carrierOpByFn?.get('fmul')).toBe('mul');
    expect(definitions.carrierValues?.get('fzero')).toEqual({ num: 0n, den: 1n });
    expect(definitions.carrierValues?.get('fone')).toEqual({ num: 1n, den: 1n });
    expect(definitions.carrierValues?.get('fhalf')).toEqual({ num: 1n, den: 2n });
    expect(definitions.carrierValues?.get('ftwoThirds')).toEqual({ num: 2n, den: 3n });
  });

  test('inferIsRat evaluates closed Magnitude arithmetic', () => {
    // madd mtwo mone → 3
    const mone: TTKTerm = { tag: 'Const', name: 'mone' };
    const mtwo: TTKTerm = { tag: 'Const', name: 'mtwo' };
    const mthree: TTKTerm = { tag: 'Const', name: 'mthree' };
    const madd = (a: TTKTerm, b: TTKTerm): TTKTerm => ({
      tag: 'App',
      fn: { tag: 'App', fn: { tag: 'Const', name: 'madd' }, arg: a },
      arg: b,
    });
    const mmul = (a: TTKTerm, b: TTKTerm): TTKTerm => ({
      tag: 'App',
      fn: { tag: 'App', fn: { tag: 'Const', name: 'mmul' }, arg: a },
      arg: b,
    });
    expect(inferIsRat(madd(mtwo, mone), definitions)).toEqual({ num: 3n, den: 1n });
    expect(inferIsRat(mmul(mtwo, mthree), definitions)).toEqual({ num: 6n, den: 1n });
    expect(inferIsRat(madd(madd(mone, mtwo), mthree), definitions)).toEqual({ num: 6n, den: 1n });
  });

  test('inferIsRat evaluates closed Score arithmetic', () => {
    const szero: TTKTerm = { tag: 'Const', name: 'szero' };
    const sone: TTKTerm = { tag: 'Const', name: 'sone' };
    const sneg_one: TTKTerm = { tag: 'Const', name: 'sneg_one' };
    const stwo: TTKTerm = { tag: 'Const', name: 'stwo' };
    const sadd = (a: TTKTerm, b: TTKTerm): TTKTerm => ({
      tag: 'App',
      fn: { tag: 'App', fn: { tag: 'Const', name: 'sadd' }, arg: a },
      arg: b,
    });
    const sneg = (a: TTKTerm): TTKTerm => ({
      tag: 'App', fn: { tag: 'Const', name: 'sneg' }, arg: a,
    });
    expect(inferIsRat(sadd(stwo, sneg_one), definitions)).toEqual({ num: 1n, den: 1n });
    expect(inferIsRat(sadd(sone, sneg_one), definitions)).toEqual({ num: 0n, den: 1n });
    expect(inferIsRat(sneg(sone), definitions)).toEqual({ num: -1n, den: 1n });
    void szero; // not used in assertions but keeps the example for reference
  });

  test('inferIsRat evaluates closed Fraction arithmetic', () => {
    const fhalf: TTKTerm = { tag: 'Const', name: 'fhalf' };
    const ftwoThirds: TTKTerm = { tag: 'Const', name: 'ftwoThirds' };
    const fone: TTKTerm = { tag: 'Const', name: 'fone' };
    const fadd = (a: TTKTerm, b: TTKTerm): TTKTerm => ({
      tag: 'App',
      fn: { tag: 'App', fn: { tag: 'Const', name: 'fadd' }, arg: a },
      arg: b,
    });
    const fmul = (a: TTKTerm, b: TTKTerm): TTKTerm => ({
      tag: 'App',
      fn: { tag: 'App', fn: { tag: 'Const', name: 'fmul' }, arg: a },
      arg: b,
    });
    // 1/2 + 1/2 = 1
    expect(inferIsRat(fadd(fhalf, fhalf), definitions)).toEqual({ num: 1n, den: 1n });
    // 1/2 + 2/3 = 7/6
    expect(inferIsRat(fadd(fhalf, ftwoThirds), definitions)).toEqual({ num: 7n, den: 6n });
    // (1/2) * (2/3) = 1/3
    expect(inferIsRat(fmul(fhalf, ftwoThirds), definitions)).toEqual({ num: 1n, den: 3n });
    void fone;
  });

  test('isCarrierArithHead distinguishes the three algebras cleanly', () => {
    // Magnitude ops
    expect(isCarrierArithHead('madd', definitions)).toBe(true);
    expect(isCarrierArithHead('mmul', definitions)).toBe(true);
    // Score ops
    expect(isCarrierArithHead('sadd', definitions)).toBe(true);
    expect(isCarrierArithHead('sneg', definitions)).toBe(true);
    // Fraction ops
    expect(isCarrierArithHead('fadd', definitions)).toBe(true);
    expect(isCarrierArithHead('fmul', definitions)).toBe(true);
    // Cross-algebra heads aren't accidentally registered
    expect(isCarrierArithHead('msub', definitions)).toBe(false); // Magnitude has no sub
    expect(isCarrierArithHead('smul', definitions)).toBe(false); // Score has no mul in this preset
    expect(isCarrierArithHead('fneg', definitions)).toBe(false); // Fraction has no neg
    // Real-analysis names absent
    expect(isCarrierArithHead('radd', definitions)).toBe(false);
  });

  test('renderer carrierValueDisplay map contains all three algebras', () => {
    const rev = buildReverseRegistry({ symbolMap: new Map(), entries: [] }, definitions);
    // Magnitude
    expect(rev.carrierValueDisplay?.get('mzero')).toBe('0');
    expect(rev.carrierValueDisplay?.get('mthree')).toBe('3');
    // Score
    expect(rev.carrierValueDisplay?.get('sneg_one')).toBe('-1');
    // Fraction
    expect(rev.carrierValueDisplay?.get('fhalf')).toBe('1/2');
    expect(rev.carrierValueDisplay?.get('ftwoThirds')).toBe('2/3');
    // Carrier prefix ops
    expect(rev.carrierUnaryOpDisplay?.get('sneg')).toBe('-');
  });
});
