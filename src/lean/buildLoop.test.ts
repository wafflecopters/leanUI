import { describe, expect, test } from 'vitest';
import { leanTacticsToTree } from './leanTacticsToTree';
import { assembleProofDecl } from './assembleProofDecl';
import { mapLeanGoalsToNodes } from './leanGoalMapping';
import { proofTreeToLean } from './proofTreeToLean';
import { resetProofIds } from '../proof-tree/proof-tree';
import type { LeanGoal } from './types';

/**
 * Build-loop integration (offline): seed a proof tree from Lean source, print it
 * back, assemble a decl, then map a simulated Lean analysis back onto nodes —
 * the exact pipeline `useLeanProofGoals` runs, minus the network. Locks the
 * source↔tree↔goals round-trip so refactors can't silently break it.
 */
describe('build loop: source → tree → decl → goals', () => {
  test('hole proof assembles with a sorry the mapper can resolve', () => {
    resetProofIds();
    const tree = leanTacticsToTree('  sorry');
    const { source, lean } = assembleProofDecl({ name: 't', typeSource: 'n = n', proof: tree });
    expect(source).toContain('theorem t : n = n := by');
    expect(source).toContain('sorry');
    // Simulate Lean: no open goals reported at the sorry → hole marked solved.
    const goalMap = mapLeanGoalsToNodes({
      nodeRanges: lean.nodeRanges,
      holeNodeIds: lean.holeNodeIds,
      goals: [],
      messages: [],
    });
    expect([...goalMap.values()][0].validation).toEqual({ status: 'solved' });
  });

  test('induction proof: each node gets its Lean goal by range', () => {
    resetProofIds();
    const block = ['  induction n with', '  | zero =>', '    sorry', '  | succ k ih =>', '    sorry'].join('\n');
    const tree = leanTacticsToTree(block);
    const { lean } = assembleProofDecl({ name: 't', typeSource: '∀ (n : Nat), P n', proof: tree });

    // Fabricate Lean goals at the recorded node ranges.
    const ranges = [...lean.nodeRanges.values()];
    const goals: LeanGoal[] = ranges.map((r, i) => ({
      startLine: r.startLine,
      startCol: r.startCol,
      endLine: r.endLine,
      endCol: r.endCol,
      goals: [{ hyps: [], targetTagged: { t: 'text', s: `goal${i}` }, plain: `goal${i}` }],
    }));
    const goalMap = mapLeanGoalsToNodes({
      nodeRanges: lean.nodeRanges,
      holeNodeIds: lean.holeNodeIds,
      goals,
      messages: [],
    });
    // Every node with a range got a goal.
    expect(goalMap.size).toBe(lean.nodeRanges.size);
  });

  test('editing the tree reprints deterministically (stable build loop)', () => {
    resetProofIds();
    const tree = leanTacticsToTree('  intro n\n  exact rfl');
    const printedA = proofTreeToLean(tree).source;
    // Re-parse + reprint must be identical (no drift across edit cycles).
    resetProofIds();
    const printedB = proofTreeToLean(leanTacticsToTree(printedA)).source;
    expect(printedB).toBe(printedA);
  });
});
