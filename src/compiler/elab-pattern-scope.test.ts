import { describe, expect, test } from 'vitest';

import { collectSyntheticPatternVariableNames, fixRhsForVariablePatterns } from './elab';
import { createDefinitionsMap } from './term';
import type { TPattern, TTerm } from './surface';

describe('surface clause RHS scope repair', () => {
  test('collects synthetic reordered pattern binders even when their names look parser-bindable', () => {
    const patterns: TPattern[] = [
      { tag: 'PVar', name: 'A', named: true },
      { tag: 'PVar', name: 'B', named: true },
      { tag: 'PVar', name: 'x' },
    ];

    const forced = collectSyntheticPatternVariableNames(patterns, [null, null, 0]);

    expect([...forced]).toEqual(['A', 'B']);
  });

  test('repairs RHS references to reordered synthetic implicit binders', () => {
    const patterns: TPattern[] = [
      { tag: 'PVar', name: 'A', named: true },
      { tag: 'PVar', name: 'B', named: true },
      { tag: 'PVar', name: 'x' },
    ];
    const rhs: TTerm = {
      tag: 'App',
      fn: {
        tag: 'App',
        fn: { tag: 'Const', name: 'Either' },
        arg: { tag: 'Const', name: 'A' },
      },
      arg: { tag: 'Const', name: 'B' },
    };

    const forced = collectSyntheticPatternVariableNames(patterns, [null, null, 0]);
    const repaired = fixRhsForVariablePatterns(
      patterns,
      rhs,
      createDefinitionsMap(),
      forced,
    );

    expect(repaired).toEqual({
      tag: 'App',
      fn: {
        tag: 'App',
        fn: { tag: 'Const', name: 'Either' },
        arg: { tag: 'Var', index: 2 },
      },
      arg: { tag: 'Var', index: 1 },
    });
  });

  test('does not force explicit clause-level named patterns that the parser already bound', () => {
    const patterns: TPattern[] = [
      { tag: 'PVar', name: 'T', named: true },
      { tag: 'PVar', name: 'x' },
    ];

    const forced = collectSyntheticPatternVariableNames(
      patterns,
      [null, 0],
      new Set(['T']),
    );

    expect([...forced]).toEqual([]);
  });
});
