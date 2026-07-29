import { describe, expect, test } from 'vitest';
import { orderApplyBranches } from './orderApplyBranches';
import { mkApply, mkExact, mkHole, mkIntros, type ProofNode, type ProofNodeId } from '../proof-tree/proof-tree';
import type { NodeGoalInfo } from '../proof-tree/goal-computation';

/** Goal map + text map from `[nodeId, caseTag, target]` triples. */
function goals(entries: Array<[ProofNodeId, string | undefined, string]>) {
  const goalMap = new Map<ProofNodeId, NodeGoalInfo>();
  const goalTexts = new Map<ProofNodeId, string>();
  for (const [id, tag, target] of entries) {
    goalMap.set(id, { goalLatex: target, hypotheses: [], ...(tag ? { caseLabelLatex: tag } : {}) });
    goalTexts.set(id, target);
  }
  return { goalMap, goalTexts };
}

const run = (root: ProofNode, g: ReturnType<typeof goals>, cursorId = 0) =>
  orderApplyBranches({ root, ...g, cursorId });

describe('orderApplyBranches', () => {
  // `apply ltLeTrans` on `0 < 2`: Lean orders the obligations before the
  // midpoint they depend on. A person picks the midpoint first.
  test('the branch the others depend on is moved to the front', () => {
    const [hab, hbc, b] = [mkHole(), mkHole(), mkHole()];
    const root = mkApply('ltLeTrans', [hab, hbc, b]);
    const g = goals([
      [hab.id, 'hb.hab', '0 ≤ ?hb.b'],
      [hbc.id, 'hb.hbc', '?hb.b ≤ 2'],
      [b.id, 'hb.b', 'ℝ'],
    ]);
    const out = run(root, g);
    expect(out.changed).toBe(true);
    const apply = out.root as unknown as { children: ProofNode[]; childTags?: string[] };
    expect(apply.children.map((c) => c.id)).toEqual([b.id, hab.id, hbc.id]);
    // The tags are recorded so the printed proof selects goals BY NAME.
    expect(apply.childTags).toEqual(['hb.b', 'hb.hab', 'hb.hbc']);
  });

  test('the cursor follows to the branch that is now first', () => {
    const [hab, hbc, b] = [mkHole(), mkHole(), mkHole()];
    const root = mkApply('ltLeTrans', [hab, hbc, b]);
    const g = goals([
      [hab.id, 'hab', '0 ≤ ?b'],
      [hbc.id, 'hbc', '?b ≤ 2'],
      [b.id, 'b', 'ℝ'],
    ]);
    // The cursor landed on the first branch, as it does right after `apply`.
    expect(run(root, g, hab.id).cursorId).toBe(b.id);
  });

  test('the cursor stays put when that branch already has work in it', () => {
    const [hab, hbc, b] = [mkExact('h'), mkHole(), mkHole()];
    const root = mkApply('ltLeTrans', [hab, hbc, b]);
    const g = goals([
      [hab.id, 'hab', '0 ≤ ?b'],
      [hbc.id, 'hbc', '?b ≤ 2'],
      [b.id, 'b', 'ℝ'],
    ]);
    // Moving someone off a step they've been writing would be rude.
    expect(run(root, g, hab.id).cursorId).toBe(hab.id);
  });

  // Once the witness is supplied the cursor must be free to move on. Dragging
  // it back to a finished branch on every refresh makes the proof unworkable.
  test('the cursor is NOT pulled back once the witness is filled', () => {
    const [hab, hbc, b] = [mkHole(), mkHole(), mkExact('1')];
    const root = mkApply('ltLeTrans', [hab, hbc, b]);
    const g = goals([
      [hab.id, 'hab', '0 ≤ 1'],
      [hbc.id, 'hbc', '1 ≤ 2'],
      [b.id, 'b', 'ℝ'],
    ]);
    // The user has moved on to the first obligation; leave them there.
    expect(run(root, g, hab.id).cursorId).toBe(hab.id);
  });

  test('running it again changes nothing (idempotent)', () => {
    const [hab, hbc, b] = [mkHole(), mkHole(), mkHole()];
    const root = mkApply('ltLeTrans', [hab, hbc, b]);
    const g = goals([
      [hab.id, 'hab', '0 ≤ ?b'],
      [hbc.id, 'hbc', '?b ≤ 2'],
      [b.id, 'b', 'ℝ'],
    ]);
    const once = run(root, g);
    const twice = run(once.root, g);
    expect(twice.changed).toBe(false);
    expect(twice.root).toBe(once.root);
  });

  // `apply divPos` leaves `0 < ε` and `0 < 2` — two ordinary obligations with
  // nothing to choose. Reordering them would be meddling.
  test('branches with nothing to choose are left in Lean’s order', () => {
    const [ha, hb] = [mkHole(), mkHole()];
    const root = mkApply('divPos', [ha, hb]);
    const g = goals([
      [ha.id, 'ha', '0 < ε'],
      [hb.id, 'hb', '0 < 2'],
    ]);
    const out = run(root, g);
    expect(out.changed).toBe(false);
    expect((out.root as unknown as { children: ProofNode[] }).children.map((c) => c.id)).toEqual([ha.id, hb.id]);
  });

  test('an untagged branch means we cannot tell — leave it alone', () => {
    const [hab, b] = [mkHole(), mkHole()];
    const root = mkApply('ltLeTrans', [hab, b]);
    const g = goals([
      [hab.id, undefined, '0 ≤ ?b'],
      [b.id, 'b', 'ℝ'],
    ]);
    expect(run(root, g).changed).toBe(false);
  });

  test('a single-branch apply is never touched', () => {
    const only = mkHole();
    const root = mkApply('divTwoPos', [only]);
    expect(run(root, goals([[only.id, 'hlt', '0 < ε']])).changed).toBe(false);
  });

  test('branches nested deeper in the proof are reordered too', () => {
    const [hab, hbc, b] = [mkHole(), mkHole(), mkHole()];
    const root = mkIntros(['ε'], mkApply('ltLeTrans', [hab, hbc, b]));
    const g = goals([
      [hab.id, 'hab', '0 ≤ ?b'],
      [hbc.id, 'hbc', '?b ≤ 2'],
      [b.id, 'b', 'ℝ'],
    ]);
    const out = run(root, g);
    expect(out.changed).toBe(true);
    const apply = (out.root as unknown as { child: { children: ProofNode[] } }).child;
    expect(apply.children[0].id).toBe(b.id);
  });

  test('stale tags are refreshed when Lean renames the goals', () => {
    const [hab, hbc, b] = [mkHole(), mkHole(), mkHole()];
    // Recorded under an older enclosing structure…
    const root = mkApply('ltLeTrans', [b, hab, hbc], false, ['old.b', 'old.hab', 'old.hbc']);
    const g = goals([
      [b.id, 'hb.b', 'ℝ'],
      [hab.id, 'hb.hab', '0 ≤ ?hb.b'],
      [hbc.id, 'hb.hbc', '?hb.b ≤ 2'],
    ]);
    const out = run(root, g);
    expect(out.changed).toBe(true);
    expect((out.root as unknown as { childTags?: string[] }).childTags).toEqual(['hb.b', 'hb.hab', 'hb.hbc']);
  });
});
