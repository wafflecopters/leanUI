import { describe, expect, test } from 'vitest';
import { findUnsolvedWildcards } from './compile-term-value';

describe('compile-term-value', () => {
  test('findUnsolvedWildcards reports nested wildcard holes and metas with stable paths', () => {
    const term = {
      tag: 'Annot',
      term: {
        tag: 'Match',
        scrutinee: { tag: 'Hole', id: '_' },
        clauses: [{
          patterns: [],
          rhs: {
            tag: 'Binder',
            name: 'x',
            binderKind: {
              tag: 'BLet',
              defVal: { tag: 'Meta', id: '_' },
            },
            domain: { tag: 'Const', name: 'Nat' },
            body: { tag: 'Hole', id: '_' },
          },
        }],
      },
      type: { tag: 'Meta', id: 'namedHole' },
    } as any;

    expect(findUnsolvedWildcards(term)).toEqual([
      ['term', 'scrutinee', 'Hole._'],
      ['term', 'clauses', '0', 'rhs', 'body', 'Hole._'],
      ['term', 'clauses', '0', 'rhs', 'binderKind', 'defVal', 'Meta._'],
    ]);
  });

  test('findUnsolvedWildcards ignores named holes and solved-looking subterms', () => {
    const term = {
      tag: 'App',
      fn: { tag: 'Hole', id: 'goal' },
      arg: {
        tag: 'Binder',
        name: 'x',
        binderKind: { tag: 'BPi' },
        domain: { tag: 'Const', name: 'Nat' },
        body: { tag: 'Meta', id: 'm0' },
      },
    } as any;

    expect(findUnsolvedWildcards(term)).toEqual([]);
  });

  test('findUnsolvedWildcards descends through application spines in order', () => {
    const term = {
      tag: 'App',
      fn: {
        tag: 'App',
        fn: { tag: 'Meta', id: '_' },
        arg: { tag: 'Const', name: 'Zero' },
      },
      arg: { tag: 'Hole', id: '_' },
    } as any;

    expect(findUnsolvedWildcards(term)).toEqual([
      ['fn', 'fn', 'Meta._'],
      ['arg', 'Hole._'],
    ]);
  });
});
