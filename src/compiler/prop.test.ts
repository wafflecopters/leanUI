import { describe, test, expect } from 'vitest';
import {
  TTKTerm,
  mkProp,
  mkType,
  mkSort,
  mkULit,
  mkLSucc,
  mkLMax,
  mkLIMax,
  mkLOmega,
  mkMeta,
  mkVar,
  mkApp,
  mkConst,
  isProp,
  isPropLevel,
  prettyPrint,
} from './kernel';

/**
 * Step 1 invariants: Prop = Sort(ULit(0)), distinct from Type 0 = Sort(USucc(ULit(0))).
 *
 * These tests pin down the foundational shape and lookup behaviour. Every
 * subsequent step (impredicativity, cumulativity, proof irrelevance,
 * large-elim ban) depends on `isProp` correctly classifying sorts.
 */
describe('Prop foundations: isProp / isPropLevel / mkProp', () => {
  describe('isProp', () => {
    test('mkProp is recognized as Prop', () => {
      expect(isProp(mkProp())).toBe(true);
    });

    test('Sort(ULit(0)) is Prop', () => {
      expect(isProp(mkSort(mkULit(0)))).toBe(true);
    });

    test('mkType(0) is NOT Prop (it is Type 0 = Sort 1)', () => {
      expect(isProp(mkType(0))).toBe(false);
    });

    test('Sort(USucc(ULit(0))) is NOT Prop', () => {
      expect(isProp(mkSort(mkLSucc(mkULit(0))))).toBe(false);
    });

    test('Sort(ULit(1)) is NOT Prop', () => {
      expect(isProp(mkSort(mkULit(1)))).toBe(false);
    });

    test('Sort(ULit(7)) is NOT Prop', () => {
      expect(isProp(mkSort(mkULit(7)))).toBe(false);
    });

    test('non-Sort terms are not Prop', () => {
      expect(isProp(mkVar(0))).toBe(false);
      expect(isProp(mkConst('Nat'))).toBe(false);
      expect(isProp(mkApp(mkConst('f'), mkVar(0)))).toBe(false);
    });

    test('Sort with unresolved meta level is not Prop', () => {
      // Conservative: we don't know what the meta resolves to
      expect(isProp(mkSort(mkMeta('?m0')))).toBe(false);
    });

    test('Sort with level variable is not Prop', () => {
      // Universe polymorphic: depends on the level
      expect(isProp(mkSort(mkVar(0)))).toBe(false);
    });
  });

  describe('isPropLevel: simplification', () => {
    test('ULit(0) is Prop level', () => {
      expect(isPropLevel(mkULit(0))).toBe(true);
    });

    test('ULit(1) is not Prop level', () => {
      expect(isPropLevel(mkULit(1))).toBe(false);
    });

    test('USucc(ULit(0)) = 1 is not Prop level', () => {
      expect(isPropLevel(mkLSucc(mkULit(0)))).toBe(false);
    });

    test('UMax(0,0) simplifies to 0 → Prop level', () => {
      expect(isPropLevel(mkLMax(mkULit(0), mkULit(0)))).toBe(true);
    });

    test('UMax(0,1) simplifies to 1 → not Prop level', () => {
      expect(isPropLevel(mkLMax(mkULit(0), mkULit(1)))).toBe(false);
    });

    test('UIMax(anything, 0) = 0 → Prop level (impredicativity rule)', () => {
      // imax(l, 0) is always 0, regardless of l
      expect(isPropLevel(mkLIMax(mkULit(5), mkULit(0)))).toBe(true);
      expect(isPropLevel(mkLIMax(mkLOmega(), mkULit(0)))).toBe(true);
      // Even with an unresolved meta on the left, imax(_, 0) = 0
      expect(isPropLevel(mkLIMax(mkMeta('?m0'), mkULit(0)))).toBe(true);
    });

    test('UIMax(0, 5) simplifies to 5 → not Prop level', () => {
      expect(isPropLevel(mkLIMax(mkULit(0), mkULit(5)))).toBe(false);
    });

    test('UOmega is not Prop level', () => {
      expect(isPropLevel(mkLOmega())).toBe(false);
    });

    test('meta is not Prop level (unresolved)', () => {
      expect(isPropLevel(mkMeta('?m0'))).toBe(false);
    });
  });
});

describe('Prop foundations: pretty-printing', () => {
  test('mkProp prints as "Prop"', () => {
    expect(prettyPrint(mkProp())).toBe('Prop');
  });

  test('mkType(0) prints as "Type"', () => {
    expect(prettyPrint(mkType(0))).toBe('Type');
  });

  test('mkType(1) prints as "Type 1"', () => {
    expect(prettyPrint(mkType(1))).toBe('Type 1');
  });

  test('Sort(ULit(0)) prints as "Prop" (not "Sort 0")', () => {
    expect(prettyPrint(mkSort(mkULit(0)))).toBe('Prop');
  });
});

describe('Prop foundations: AST distinctness', () => {
  test('mkProp and mkType(0) are structurally distinct', () => {
    const prop = mkProp();
    const type0 = mkType(0);
    expect(prop).not.toEqual(type0);
  });

  test('mkProp is Sort(ULit(0))', () => {
    const prop = mkProp();
    expect(prop.tag).toBe('Sort');
    if (prop.tag !== 'Sort') throw new Error('unreachable');
    expect(prop.level.tag).toBe('ULit');
    if (prop.level.tag !== 'ULit') throw new Error('unreachable');
    expect(prop.level.n).toBe(0);
  });

  test('mkType(0) is Sort(USucc(ULit(0)))', () => {
    const type0 = mkType(0);
    expect(type0.tag).toBe('Sort');
    if (type0.tag !== 'Sort') throw new Error('unreachable');
    expect(type0.level.tag).toBe('App');
    if (type0.level.tag !== 'App') throw new Error('unreachable');
    expect(type0.level.fn).toEqual(mkConst('USucc'));
    expect(type0.level.arg).toEqual(mkULit(0));
  });
});
