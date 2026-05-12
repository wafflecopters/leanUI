import { describe, expect, test } from 'vitest';
import { validateAnnotatedAbsurdClauses } from './compile-term-absurdity';
import { compileTTFromText } from './compile';
import { mkConst, mkPi } from './kernel';
import { createTCEnv } from './term';

describe('compile-term-absurdity', () => {
  test('rejects #absurd on an inhabited case', () => {
    const definitions = compileTTFromText(`
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat
`).definitions;

    const result = validateAnnotatedAbsurdClauses(
      {
        name: 'badAbsurd',
        kind: 'term',
        surfaceValue: {
          tag: 'Match',
          scrutinee: { tag: 'Const', name: 'x' },
          clauses: [{
            patterns: [{ tag: 'PCtor', name: 'Zero', args: [] }],
            rhs: { tag: 'AbsurdMarker' },
          }],
        } as any,
      },
      createTCEnv({ definitions, options: { mode: 'check' } }).withValue({ name: 'badAbsurd', type: mkPi(mkConst('Nat'), mkConst('Nat'), 'x'), value: { tag: 'Hole', id: '_v' } as any }),
      mkPi(mkConst('Nat'), mkConst('Nat'), 'x'),
    );

    expect(result.success).toBe(false);
    if (result.success) {
      throw new Error('expected inhabited #absurd to fail');
    }
    expect(result.errors[0].message).toContain('#absurd used but case is not absurd');
  });

  test('accepts #absurd when the argument type has no constructors', () => {
    const definitions = compileTTFromText(`
inductive Void : Type where
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat
`).definitions;

    const result = validateAnnotatedAbsurdClauses(
      {
        name: 'voidElim',
        kind: 'term',
        surfaceValue: {
          tag: 'Match',
          scrutinee: { tag: 'Const', name: 'x' },
          clauses: [{
            patterns: [{ tag: 'PWild', name: '_' }],
            rhs: { tag: 'AbsurdMarker' },
          }],
        } as any,
      },
      createTCEnv({ definitions, options: { mode: 'check' } }).withValue({ name: 'voidElim', type: mkPi(mkConst('Void'), mkConst('Nat'), 'x'), value: { tag: 'Hole', id: '_v' } as any }),
      mkPi(mkConst('Void'), mkConst('Nat'), 'x'),
    );

    expect(result.success).toBe(true);
    if (!result.success) {
      throw new Error('expected void #absurd to succeed');
    }
    expect(result.annotatedAbsurdClauses).toEqual([0]);
  });
});
