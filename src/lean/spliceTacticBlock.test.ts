import { describe, expect, test } from 'vitest';
import { spliceTacticBlock } from './spliceTacticBlock';
import { extractTacticBlock } from './extractTacticBlock';
import type { LeanDeclaration } from './types';

const decl = (line: number): LeanDeclaration => ({ name: 't', kind: 'theorem', prettyType: '', line, col: 0 });

describe('spliceTacticBlock', () => {
  test('replaces a multi-line block, preserving the header', () => {
    const src = ['theorem t : n = n := by', '  sorry'].join('\n');
    const out = spliceTacticBlock(src, decl(1), undefined, '  exact rfl');
    expect(out).toBe(['theorem t : n = n := by', '  exact rfl'].join('\n'));
  });

  test('keeps following declarations intact', () => {
    const src = ['theorem a : True := by', '  sorry', 'theorem b : True := by', '  trivial'].join('\n');
    const out = spliceTacticBlock(src, decl(1), 3, '  trivial');
    expect(out).toBe(['theorem a : True := by', '  trivial', 'theorem b : True := by', '  trivial'].join('\n'));
  });

  test('replaces an inline by-proof with a fresh block', () => {
    const src = 'theorem t : n = n := by rfl';
    const out = spliceTacticBlock(src, decl(1), undefined, '  exact rfl');
    expect(out).toBe('theorem t : n = n := by\n  exact rfl');
  });

  test('no by block → source unchanged', () => {
    const src = 'def x : Nat := 42';
    expect(spliceTacticBlock(src, decl(1), undefined, '  whatever')).toBe(src);
  });

  test('round-trips with extractTacticBlock', () => {
    const src = ['theorem t : a = b := by', '  rw [foo]', '  exact bar'].join('\n');
    const block = extractTacticBlock(src, decl(1), undefined)!;
    // splice the same block back → unchanged
    expect(spliceTacticBlock(src, decl(1), undefined, block)).toBe(src);
  });
});
