import { describe, expect, test } from 'vitest';
import { assembleProofDecl } from './assembleProofDecl';
import { mkIntros, mkExact, mkHole, resetProofIds } from '../proof-tree/proof-tree';

describe('assembleProofDecl', () => {
  test('wraps proof in theorem … := by and offsets node ranges past the header', () => {
    resetProofIds();
    const tree = mkIntros(['n'], mkExact('rfl'));
    const { source, lean } = assembleProofDecl({ name: 't', typeSource: '∀ (n : Nat), n = n', proof: tree });
    const lines = source.split('\n');
    expect(lines[0]).toBe('theorem t : ∀ (n : Nat), n = n := by');
    expect(lines[1]).toBe('  intro n');
    expect(lines[2]).toBe('  exact rfl');
    // header is line 1, first tactic on line 2
    expect(lean.nodeRanges.get(tree.id)!.startLine).toBe(2);
  });

  test('preamble shifts the proof block down', () => {
    resetProofIds();
    const tree = mkHole();
    const { source, lean } = assembleProofDecl({
      name: 'g',
      typeSource: 'True',
      proof: tree,
      preamble: ['import Mathlib', ''],
    });
    const lines = source.split('\n');
    expect(lines[0]).toBe('import Mathlib');
    expect(lines[2]).toBe('theorem g : True := by');
    expect(lines[3]).toBe('  sorry');
    // preamble (2 lines) + header (1) → first tactic at line 4
    expect(lean.nodeRanges.get(tree.id)!.startLine).toBe(4);
  });

  test('sanitizes unsafe chars but keeps a valid-leading name', () => {
    resetProofIds();
    const { source } = assembleProofDecl({ name: 'my name!', typeSource: 'True', proof: mkHole() });
    expect(source.split('\n')[0]).toBe('theorem my_name_ : True := by');
  });

  test('a name starting with a digit falls back to the default', () => {
    resetProofIds();
    const { source } = assembleProofDecl({ name: '1bad', typeSource: 'True', proof: mkHole() });
    expect(source.split('\n')[0]).toBe('theorem _leanui_goal : True := by');
  });

  test('falls back to default name when missing', () => {
    resetProofIds();
    const { source } = assembleProofDecl({ typeSource: 'True', proof: mkHole() });
    expect(source.split('\n')[0]).toBe('theorem _leanui_goal : True := by');
  });
});
