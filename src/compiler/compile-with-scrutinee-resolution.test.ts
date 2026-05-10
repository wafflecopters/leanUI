import { describe, expect, test } from 'vitest';
import {
  countScrutineesBeforeHoles,
  substituteHoles,
} from './compile-with-scrutinee-resolution';

describe('compile-with-scrutinee-resolution', () => {
  test('countScrutineesBeforeHoles stops at the first hole-typed scrutinee binder', () => {
    const type = {
      tag: 'Binder',
      name: 'n',
      binderKind: { tag: 'BPiTT' },
      domain: { tag: 'Const', name: 'Nat' },
      body: {
        tag: 'Binder',
        name: '_scrut0',
        binderKind: { tag: 'BPiTT' },
        domain: { tag: 'Const', name: 'Nat' },
        body: {
          tag: 'Binder',
          name: '_scrut1',
          binderKind: { tag: 'BPiTT' },
          domain: { tag: 'Hole', id: '_scrut1_type', type: { tag: 'Sort', level: { tag: 'ULit', n: 0 } } },
          body: { tag: 'Const', name: 'Bool' },
        },
      },
    } as any;

    expect(countScrutineesBeforeHoles(type)).toBe(1);
  });

  test('countScrutineesBeforeHoles counts multi-binder scrutinees before a hole domain', () => {
    const type = {
      tag: 'MultiBinder',
      names: ['_scrut0', '_scrut1'],
      binderKind: { tag: 'BPiTT' },
      domain: { tag: 'Const', name: 'Nat' },
      body: {
        tag: 'MultiBinder',
        names: ['_scrut2', '_scrut3'],
        binderKind: { tag: 'BPiTT' },
        domain: { tag: 'Hole', id: '_scrut2_type', type: { tag: 'Sort', level: { tag: 'ULit', n: 0 } } },
        body: { tag: 'Const', name: 'Bool' },
      },
    } as any;

    expect(countScrutineesBeforeHoles(type)).toBe(2);
  });

  test('substituteHoles rewrites nested let and match structures', () => {
    const term = {
      tag: 'Match',
      scrutinee: { tag: 'Hole', id: '_scrut0_type', type: { tag: 'Sort', level: { tag: 'ULit', n: 0 } } },
      clauses: [{
        patterns: [],
        rhs: {
          tag: 'Binder',
          name: 'x',
          binderKind: {
            tag: 'BLetTT',
            defVal: { tag: 'Hole', id: '_scrut0_type', type: { tag: 'Sort', level: { tag: 'ULit', n: 0 } } },
          },
          domain: { tag: 'Hole', id: '_scrut0_type', type: { tag: 'Sort', level: { tag: 'ULit', n: 0 } } },
          body: { tag: 'Hole', id: '_scrut0_type', type: { tag: 'Sort', level: { tag: 'ULit', n: 0 } } },
        },
      }],
    } as any;

    const replacement = { tag: 'Const', name: 'Nat' } as any;
    const rewritten = substituteHoles(term, new Map([['_scrut0_type', replacement]])) as any;

    expect(rewritten.scrutinee).toEqual(replacement);
    expect(rewritten.clauses[0].rhs.domain).toEqual(replacement);
    expect(rewritten.clauses[0].rhs.body).toEqual(replacement);
    expect(rewritten.clauses[0].rhs.binderKind.defVal).toEqual(replacement);
  });

  test('substituteHoles leaves tactic blocks and absurd markers untouched', () => {
    const tacticBlock = { tag: 'TacticBlock', tactics: [] } as any;
    const absurd = { tag: 'AbsurdMarker' } as any;

    expect(substituteHoles(tacticBlock, new Map())).toBe(tacticBlock);
    expect(substituteHoles(absurd, new Map())).toBe(absurd);
  });
});
