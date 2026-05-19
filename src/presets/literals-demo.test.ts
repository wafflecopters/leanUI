/**
 * Test that the Generic Literals Demo preset proves the @carrier* / @ofNat
 * literal-coercion system is genuinely generic. Four algebras share the
 * SAME surface form `1 + 4 = 5` but elaborate to four distinct kernel
 * shapes — each one definitionally reducing to refl.
 */
import { describe, test, expect } from 'vitest';
import { compileTTFromText } from '../compiler/compile';
import { LITERALS_DEMO_CODE } from './literals-demo';
import { inferIsRat, isCarrierArithHead } from '../tactics/norm-num';
import { renderSubtermLatex } from '../proof-tree/goal-computation';
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

  test('registry populated: kernel impls, carrier ops, @ofNat coercions', () => {
    // Kernel impls — Nat and Int are @impl-tagged so literals coerce
    // natively without a wrapper.
    expect([...(definitions.natImplByCtor?.values() ?? [])].map(i => i.inductiveName))
      .toContain('Nat');
    expect([...(definitions.intImplByCtor?.values() ?? [])].map(i => i.inductiveName))
      .toContain('Int');

    // Carrier arithmetic ops registered per-algebra
    expect(definitions.carrierOpByFn?.get('plus')).toBe('add');
    expect(definitions.carrierOpByFn?.get('mult')).toBe('mul');
    expect(definitions.carrierOpByFn?.get('intAdd')).toBe('add');
    expect(definitions.carrierOpByFn?.get('intNegFn')).toBe('neg');
    expect(definitions.carrierOpByFn?.get('realAdd')).toBe('add');
    expect(definitions.carrierOpByFn?.get('realNeg')).toBe('neg');
    expect(definitions.carrierOpByFn?.get('complexAdd')).toBe('add');

    // @ofNat coercions wire bare numerals to the user-defined algebras
    expect(definitions.ofNatByTargetHead?.get('Real')).toBe('realOfNat');
    expect(definitions.ofNatByTargetHead?.get('Complex')).toBe('complexOfNat');
  });

  test('the four "1 + 4 = 5" proofs all close by refl', () => {
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

  test('inferIsRat evaluates closed arithmetic in each algebra via the registry', () => {
    // Surface "1 + 4" in each algebra elaborates differently — we
    // reconstruct each algebra's specific kernel shape and confirm the
    // norm_num walker arrives at 5 via the right path.
    const natLit = (n: bigint): TTKTerm => ({ tag: 'NatLit', value: n });
    const app = (head: string, ...as: TTKTerm[]): TTKTerm =>
      as.reduce<TTKTerm>(
        (fn, a) => ({ tag: 'App', fn, arg: a }),
        { tag: 'Const', name: head },
      );

    // Nat: bare NatLits + @carrierAdd-tagged plus
    expect(inferIsRat(app('plus', natLit(1n), natLit(4n)), definitions))
      .toEqual({ num: 5n, den: 1n });

    // Int: IntOfNat-wrapped NatLits (the @impl=int expansion form)
    const intLit = (n: bigint): TTKTerm => app('IntOfNat', natLit(n));
    // intAdd is @carrierAdd but its args are constructors, not @ofNat-coerced.
    // Test the @ofNat-style path with realOfNat directly:
    expect(inferIsRat(app('intAdd', intLit(1n), intLit(4n)), definitions))
      .toBeNull(); // IntOfNat isn't itself a @carrierValue/@ofNat — null is correct

    // Real: @ofNat coercion (realOfNat is registered)
    expect(inferIsRat(app('realAdd', app('realOfNat', natLit(1n)), app('realOfNat', natLit(4n))), definitions))
      .toEqual({ num: 5n, den: 1n });

    // Complex: @ofNat coercion (complexOfNat is registered)
    expect(inferIsRat(app('complexAdd', app('complexOfNat', natLit(1n)), app('complexOfNat', natLit(4n))), definitions))
      .toEqual({ num: 5n, den: 1n });
  });

  test('renderer collapses @ofNat-coerced literals to bare numerals', () => {
    const rev = buildReverseRegistry({ symbolMap: new Map(), entries: [] }, definitions);
    const natLit = (n: bigint): TTKTerm => ({ tag: 'NatLit', value: n });
    const app = (head: string, ...as: TTKTerm[]): TTKTerm =>
      as.reduce<TTKTerm>(
        (fn, a) => ({ tag: 'App', fn, arg: a }),
        { tag: 'Const', name: head },
      );

    // `realOfNat 5` should render as just "5", not "realOfNat(5)" or similar.
    const realFive = app('realOfNat', natLit(5n));
    const realOut = renderSubtermLatex(realFive, [], definitions, rev);
    expect(realOut).toBe('5');

    // `complexOfNat 5` should also render as "5".
    const complexFive = app('complexOfNat', natLit(5n));
    const complexOut = renderSubtermLatex(complexFive, [], definitions, rev);
    expect(complexOut).toBe('5');

    // And the full surface form: `complexAdd (complexOfNat 1) (complexOfNat 4)`
    // should display the @ofNat-coerced args as bare numerals, not the
    // verbose `complexOfNat(1)` form.
    const complexAdd14 = app('complexAdd',
      app('complexOfNat', natLit(1n)),
      app('complexOfNat', natLit(4n)));
    const addOut = renderSubtermLatex(complexAdd14, [], definitions, rev);
    expect(addOut).not.toContain('complexOfNat');
    expect(addOut).toContain('1');
    expect(addOut).toContain('4');
  });

  test('isCarrierArithHead recognizes ops across all four algebras', () => {
    expect(isCarrierArithHead('plus', definitions)).toBe(true);
    expect(isCarrierArithHead('mult', definitions)).toBe(true);
    expect(isCarrierArithHead('intAdd', definitions)).toBe(true);
    expect(isCarrierArithHead('intNegFn', definitions)).toBe(true);
    expect(isCarrierArithHead('realAdd', definitions)).toBe(true);
    expect(isCarrierArithHead('realNeg', definitions)).toBe(true);
    expect(isCarrierArithHead('complexAdd', definitions)).toBe(true);

    // Constructors and coercions are not arithmetic heads
    expect(isCarrierArithHead('MkReal', definitions)).toBe(false);
    expect(isCarrierArithHead('MkComplex', definitions)).toBe(false);
    expect(isCarrierArithHead('realOfNat', definitions)).toBe(false);
    expect(isCarrierArithHead('complexOfNat', definitions)).toBe(false);
    // Real-analysis names aren't in THIS preset
    expect(isCarrierArithHead('radd', definitions)).toBe(false);
  });
});
