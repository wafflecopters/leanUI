import { describe, expect, test } from 'vitest';
import { compileTTFromText } from './compile';
import { elabToKernelWithMap } from './elab';
import { createNamedArgInfoLookup, createDefinitionsMap } from './term';
import { computeEffectiveTotalArity, prepareMatchSurfaceClauses } from './compile-term-match-preparation';

describe('compile-term-match-preparation', () => {
  test('prepareMatchSurfaceClauses filters absurd branches while preserving original indices', () => {
    const surfaceValue = {
      tag: 'Match',
      scrutinee: { tag: 'Var', name: 'xs' },
      clauses: [
        {
          patterns: [{ tag: 'PVar', name: 'x' }],
          rhs: { tag: 'Var', name: 'x' },
        },
        {
          patterns: [{ tag: 'PWild', name: '_' }],
          rhs: { tag: 'AbsurdMarker' },
        },
        {
          patterns: [{ tag: 'PVar', name: 'y' }],
          rhs: { tag: 'Var', name: 'y' },
        },
      ],
    } as any;

    expect(prepareMatchSurfaceClauses(surfaceValue)).toEqual({
      surfaceClauses: [
        surfaceValue.clauses[0],
        surfaceValue.clauses[2],
      ],
      surfaceClauseIndices: [0, 2],
    });
  });

  test('prepareMatchSurfaceClauses returns empty data for non-match values', () => {
    expect(prepareMatchSurfaceClauses(undefined)).toEqual({
      surfaceClauses: [],
      surfaceClauseIndices: [],
    });

    expect(prepareMatchSurfaceClauses({ tag: 'Var', name: 'x' } as any)).toEqual({
      surfaceClauses: [],
      surfaceClauseIndices: [],
    });
  });

  test('computeEffectiveTotalArity unfolds reducible aliases before counting Pi binders', () => {
    const definitions = compileTTFromText(`
inductive Void : Type where

Not : Type -> Type
Not A = A -> Void

inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat
`).definitions;

    const zonkedKernelType = elabToKernelWithMap(
      {
        tag: 'App',
        fn: { tag: 'Const', name: 'Not' },
        arg: { tag: 'Const', name: 'Nat' },
      } as any,
      new Map(),
      [{ kind: 'field', name: 'type' }],
      [{ kind: 'field', name: 'type' }],
      undefined,
      createNamedArgInfoLookup(definitions),
    );

    expect(computeEffectiveTotalArity(zonkedKernelType, 0, definitions)).toBe(1);
    expect(computeEffectiveTotalArity(zonkedKernelType, undefined, definitions)).toBeUndefined();
  });

  test('computeEffectiveTotalArity leaves plain binder counts unchanged', () => {
    const type = {
      tag: 'Binder',
      name: 'x',
      binderKind: { tag: 'BPi' },
      domain: { tag: 'Const', name: 'Nat' },
      body: {
        tag: 'Binder',
        name: 'y',
        binderKind: { tag: 'BPi' },
        domain: { tag: 'Const', name: 'Nat' },
        body: { tag: 'Const', name: 'Nat' },
      },
    } as any;

    expect(computeEffectiveTotalArity(type, 2, createDefinitionsMap())).toBe(2);
  });
});
