/**
 * Every tree walker must see through EVERY node kind.
 *
 * Adding `DestructureNode`, five separate walkers silently skipped it: three
 * had a `default:` branch or returned void (so TypeScript's exhaustiveness
 * check said nothing), and the symptoms ranged from a truncated outline that
 * reported "✓ complete" over an unproved goal, to a Tactics tab rendering
 * nothing below the new node. This suite is the net for the NEXT node kind:
 * one tree that chains every kind above a single marker hole, and every
 * walker must reach that hole.
 */
import { describe, expect, test } from 'vitest';
import {
  findNode,
  linearize,
  mkCase,
  mkDestructure,
  mkExact,
  mkHave,
  mkHole,
  mkInduction,
  mkIntros,
  mkRewrite,
  mkSimp,
  replaceNode,
  type ProofNode,
} from './proof-tree';
import { findFirstHole } from './tactic-to-tree';
import { generateProofProse } from './proof-prose';
import { proofOutline } from '../controller/outline';
import { collectBranchTags } from '../lean/leanGoalMapping';
import { enrichInductionCaseNames } from '../lean/enrichInductionCases';
import { proofTreeToLean } from '../lean/proofTreeToLean';

/** One tree containing every chaining node kind, ending in a lone hole. */
function everyKindTree(): { root: ProofNode; leaf: ProofNode } {
  const leaf = mkHole();
  let node: ProofNode = leaf;
  node = mkSimp([], [], node);
  node = mkRewrite('lemmaR', node);
  node = mkDestructure('h', ['a', 'b'], node);
  node = mkHave('hv', 'expr', node);
  node = mkInduction('n', [mkCase('c', node)], true);
  node = mkIntros(['x'], node);
  return { root: node, leaf };
}

describe('every walker sees through every node kind', () => {
  test('findNode reaches the leaf', () => {
    const { root, leaf } = everyKindTree();
    expect(findNode(root, leaf.id)?.id).toBe(leaf.id);
  });

  test('findFirstHole reaches the leaf', () => {
    const { root, leaf } = everyKindTree();
    expect(findFirstHole(root)?.id).toBe(leaf.id);
  });

  test('replaceNode reaches the leaf', () => {
    const { root, leaf } = everyKindTree();
    const swapped = replaceNode(root, leaf.id, mkExact('done'));
    expect(findFirstHole(swapped)).toBeNull();
  });

  test('linearize lists the leaf', () => {
    const { root, leaf } = everyKindTree();
    expect(linearize(root).some((e) => e.id === leaf.id)).toBe(true);
  });

  test('the outline contains the leaf — this is what `complete` counts', () => {
    const { root, leaf } = everyKindTree();
    const ids: number[] = [];
    const walk = (n: { id: number; children: unknown[] }): void => {
      ids.push(n.id);
      for (const c of n.children as Array<typeof n>) walk(c);
    };
    walk(proofOutline(root, leaf.id, new Map(), new Map()) as never);
    expect(ids).toContain(leaf.id);
  });

  test('the prose includes a row for the leaf', () => {
    const { root, leaf } = everyKindTree();
    const items = generateProofProse(root, leaf.id, new Map());
    expect(items.some((i) => i.nodeId === leaf.id)).toBe(true);
  });

  test('the printer emits a sorry for the leaf', () => {
    const { root, leaf } = everyKindTree();
    const printed = proofTreeToLean(root);
    expect(printed.holeNodeIds.has(leaf.id)).toBe(true);
  });

  test('collectBranchTags and enrichment traverse without dropping the subtree', () => {
    const { root } = everyKindTree();
    expect(() => collectBranchTags(root)).not.toThrow();
    const { root: enriched } = enrichInductionCaseNames(root, new Map());
    expect(findFirstHole(enriched)).not.toBeNull();
  });
});
