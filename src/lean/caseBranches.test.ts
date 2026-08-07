import { describe, expect, test } from 'vitest';
import { caseBranchCount, scrutineeHead } from './caseBranches';
import type { LeanDeclaration } from './types';

const decl = (name: string, conclCtors?: number): LeanDeclaration => ({
  name,
  kind: 'theorem',
  prettyType: '',
  line: 1,
  col: 0,
  ...(conclCtors === undefined ? {} : { conclCtors }),
});

const DECLS = [decl('leTotal', 2), decl('divTwoPos', 0), decl('mkPair', 1)];
const HYPS = [
  { name: 'hF', ctors: 1 },   // a one-constructor structure (DPair)
  { name: 'hOr', ctors: 2 },  // an Either
  { name: 'ε' },              // a real: not an inductive, no count
];

describe('scrutineeHead', () => {
  test('bare name', () => expect(scrutineeHead('hF')).toBe('hF'));
  test('application', () => expect(scrutineeHead('leTotal deltaF deltaG')).toBe('leTotal'));
  test('parenthesised', () => expect(scrutineeHead('(leTotal a b)')).toBe('leTotal'));
  test('dotted projection', () => expect(scrutineeHead('fProof.snd x')).toBe('fProof.snd'));
  test('greek identifiers survive', () => expect(scrutineeHead('ε')).toBe('ε'));
  test('no head', () => expect(scrutineeHead('   ')).toBeNull());
});

describe('caseBranchCount', () => {
  test('splitting on a lemma application uses its CONCLUSION — leTotal gives two', () => {
    expect(caseBranchCount(DECLS, HYPS, 'leTotal deltaF deltaG')).toBe(2);
  });

  test('a one-constructor hypothesis gives ONE branch, not Nat’s two', () => {
    expect(caseBranchCount(DECLS, HYPS, 'hF')).toBe(1);
  });

  test('a two-constructor hypothesis gives two', () => {
    expect(caseBranchCount(DECLS, HYPS, 'hOr')).toBe(2);
  });

  test('a hypothesis shadows a same-named lemma', () => {
    expect(caseBranchCount(DECLS, [{ name: 'leTotal', ctors: 1 }], 'leTotal a b')).toBe(1);
  });

  test('unknown scrutinee says so rather than guessing', () => {
    expect(caseBranchCount(DECLS, HYPS, 'whoKnows x')).toBeNull();
  });

  test('a non-inductive scrutinee says so — splitting a real is not a 2-way split', () => {
    expect(caseBranchCount(DECLS, HYPS, 'ε')).toBeNull();
    expect(caseBranchCount(DECLS, HYPS, 'divTwoPos ε h')).toBeNull();
  });

  test('facts absent (older extractor) degrades to null, never to a guess', () => {
    expect(caseBranchCount([decl('leTotal')], [{ name: 'hF' }], 'leTotal a b')).toBeNull();
  });
});
