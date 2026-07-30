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

  test('term body := <term> is converted to := by <block>', () => {
    // A def/theorem written `:= sorry` (or any term) gets a proof tree spliced
    // back as a `by` block, so building a proof on a term body works.
    const src = 'theorem t : a = b := sorry';
    expect(spliceTacticBlock(src, decl(1), undefined, '  exact h')).toBe('theorem t : a = b := by\n  exact h');
  });

  test('no := at all → source unchanged', () => {
    const src = 'inductive Foo where | bar';
    expect(spliceTacticBlock(src, decl(1), undefined, '  whatever')).toBe(src);
  });

  test('round-trips with extractTacticBlock', () => {
    const src = ['theorem t : a = b := by', '  rw [foo]', '  exact bar'].join('\n');
    const block = extractTacticBlock(src, decl(1), undefined)!;
    // splice the same block back → unchanged
    expect(spliceTacticBlock(src, decl(1), undefined, block)).toBe(src);
  });

  // REGRESSION: the window runs to the NEXT declaration's line, so a comment
  // introducing that declaration sits inside it. Splicing the whole window
  // deleted the comment on the first structural edit — silent data loss in the
  // user's file.
  test('a comment introducing the next declaration survives write-back', () => {
    const src = [
      'theorem a : True := by',
      '  sorry',
      '',
      '-- what the next one is for',
      '-- (second line)',
      'theorem b : True := by',
      '  trivial',
    ].join('\n');
    const out = spliceTacticBlock(src, decl(1), 6, '  trivial');
    expect(out).toBe([
      'theorem a : True := by',
      '  trivial',
      '',
      '-- what the next one is for',
      '-- (second line)',
      'theorem b : True := by',
      '  trivial',
    ].join('\n'));
  });

  test('extract and splice agree on where the body ends', () => {
    const src = [
      'theorem a : True := by',
      '  constructor',
      '  sorry',
      '',
      '-- next up',
      'theorem b : True := by',
      '  trivial',
    ].join('\n');
    // Extract must not read the comment in as if it were a tactic...
    expect(extractTacticBlock(src, decl(1), 6)).toBe('  constructor\n  sorry');
    // ...and splicing the extracted block back must be a no-op.
    expect(spliceTacticBlock(src, decl(1), 6, extractTacticBlock(src, decl(1), 6)!)).toBe(src);
  });
});
