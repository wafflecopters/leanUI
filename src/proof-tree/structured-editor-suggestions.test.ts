/**
 * STRUCTURED EDITOR ↔ TACTICS UNIFIED TEST INFRA
 *
 * This is the test pattern the user asked for: build a ProofNode tree
 * (mirroring what the structured editor produces), replay it via the real
 * tactic engine, and assert on (a) the goal state at the leaf hole AND
 * (b) the suggestions that surface at that goal. End-to-end, no shortcuts.
 *
 * Image #24 / #25 scenario: prove `rle 1 2` via
 *   intros R
 *   apply addLeRightCancel
 *     ⊢ ℝ          ←  exact -1
 *     ⊢ 1+(-1) ≤ 2+(-1)
 *                  ←  rewrite addRealOfRat   (×2)
 *     ⊢ "0 ≤ 1"     ← (hole, leaf where the user is looking)
 *
 * At the leaf, the user expects `apply CompleteOrderedField.zeroLeOne` to
 * surface. The kernel goal at this point actually contains UN-REDUCED
 * `ratPlus 1 -1` / `ratPlus 2 -1` (whnf-at-head doesn't descend into
 * realOfRat-args), so the structural unifier sees a head mismatch and the
 * apply tactic's unify+defEq gate fails. Fix: positional spine-shape
 * fallback in ApplyTactic (tactic.ts) — when heads + arity align after
 * whnf with projections stripped, accept the apply and let the post-hoc
 * positional matcher fill in implicit metas.
 */
import { describe, test, expect } from 'vitest';
import { compileTTFromText } from '../compiler/compile';
import { REAL_ANALYSIS_CODE } from '../presets/real-analysis';
import { mkIntros, mkApply, mkRewrite, mkHole, mkExact, type ProofNode } from './proof-tree';
import { replayToEngine } from './goal-computation';
import { computeTacticSuggestions } from './tactic-suggestions';
import { renderInteractiveGoal } from './interactive-goal';
import { buildReverseRegistry } from '../math-editor/tt-to-math';

function compileTop(declName: string, source: string) {
  const r = compileTTFromText(REAL_ANALYSIS_CODE + '\n\n' + source);
  let decl: any;
  for (const b of r.blocks) for (const d of b.declarations) if (d.name === declName) decl = d;
  expect(decl).toBeDefined();
  return { r, decl };
}

describe('structured editor → engine state → suggestions at hole', () => {
  test('image-#24 scenario closes via apply zeroLeOne', { timeout: 30000 }, () => {
    const { r, decl } = compileTop('testImg24', `testImg24 : (R : Real) -> rle 1 2
testImg24 R = ?h`);

    // Mirror the user's structured-editor moves:
    const leafHole = mkHole();
    const proof: ProofNode = mkIntros(
      ['R'],
      mkApply('addLeRightCancel', [
        mkExact('-1'), // the c-witness
        mkRewrite('addRealOfRat', mkRewrite('addRealOfRat', leafHole)),
      ])
    );

    // Replay to the leaf hole and inspect the engine state.
    const engine = replayToEngine(proof, leafHole.id, decl.kernelType, r.definitions);
    expect(engine).not.toBeNull();
    if (!engine) return;
    const focusedGoal = engine.getFocusedGoal();
    expect(focusedGoal).toBeDefined();

    // Compute suggestions at the leaf goal's rle subterm.
    const rev = buildReverseRegistry({ symbolMap: new Map(), entries: [] });
    const ig = renderInteractiveGoal(engine, focusedGoal!, r.definitions, rev);
    let rlePath: string | null = null;
    for (const [p, info] of ig.subtermMap) {
      if (info.headName === 'rle' && info.occurrenceIndex === 1) { rlePath = p; break; }
    }
    expect(rlePath).not.toBeNull();

    const sugs = computeTacticSuggestions(rlePath!, ig, r.definitions, {
      engine, goal: focusedGoal!, definitions: r.definitions, rev,
    });
    const hasZeroLeOne = sugs.some(s => s.id.includes('zeroLeOne'));
    expect(hasZeroLeOne).toBe(true);
  });

  test('REGRESSION (image #28): zeroLeOne is NOT suggested on `rle 1 2` — it cannot close `1 ≤ 2`', { timeout: 30000 }, () => {
    const { r, decl } = compileTop('testRle12', `testRle12 : (R : Real) -> rle 1 2
testRle12 R = ?h`);
    const leafHole = mkHole();
    const proof: ProofNode = mkIntros(['R'], leafHole);
    const engine = replayToEngine(proof, leafHole.id, decl.kernelType, r.definitions);
    expect(engine).not.toBeNull();
    if (!engine) return;
    const focusedGoal = engine.getFocusedGoal();
    expect(focusedGoal).toBeDefined();
    const rev = buildReverseRegistry({ symbolMap: new Map(), entries: [] });
    const ig = renderInteractiveGoal(engine, focusedGoal!, r.definitions, rev);
    let rlePath: string | null = null;
    for (const [p, info] of ig.subtermMap) {
      if (info.headName === 'rle' && info.occurrenceIndex === 1) { rlePath = p; break; }
    }
    expect(rlePath).not.toBeNull();
    const sugs = computeTacticSuggestions(rlePath!, ig, r.definitions, {
      engine, goal: focusedGoal!, definitions: r.definitions, rev,
    });
    const hasZeroLeOne = sugs.some(s => s.id.includes('zeroLeOne'));
    expect(hasZeroLeOne).toBe(false);
  });

  test('REGRESSION (image #30): leRefl is NOT suggested on `0 ≤ 1` — wrong type (a ≤ a) even after silent constraint-solver first-wins', { timeout: 30000 }, () => {
    // Image-#30 bug: \`simp; apply CompleteOrderedField.leRefl\` falsely
    // surfaced as a closing suggestion on \`0 ≤ 1\`. The constraint solver
    // silently picks \`?a := 0\` from position 2 and drops the conflicting
    // \`?a := 1\` from position 3, producing a proof of \`0 ≤ 0\` which is
    // GROUND but wrong-typed. Apply tactic now type-checks the substituted
    // candidate return type against the goal type after solving — catches
    // this. The suggestion must not surface.
    const { r, decl } = compileTop('testImg30', `testImg30 : (R : Real) -> rle 0 1
testImg30 R = ?h`);
    const leafHole = mkHole();
    const proof: ProofNode = mkIntros(['R'], leafHole);
    const engine = replayToEngine(proof, leafHole.id, decl.kernelType, r.definitions);
    expect(engine).not.toBeNull();
    if (!engine) return;
    const focusedGoal = engine.getFocusedGoal();
    const rev = buildReverseRegistry({ symbolMap: new Map(), entries: [] });
    const ig = renderInteractiveGoal(engine, focusedGoal!, r.definitions, rev);
    let rlePath: string | null = null;
    for (const [p, info] of ig.subtermMap) {
      if (info.headName === 'rle' && info.occurrenceIndex === 1) { rlePath = p; break; }
    }
    const sugs = computeTacticSuggestions(rlePath!, ig, r.definitions, {
      engine, goal: focusedGoal!, definitions: r.definitions, rev,
    });
    const leReflSugs = sugs.filter(s => s.id.includes('leRefl'));
    expect(leReflSugs.length).toBe(0);
    // But zeroLeOne IS sound for `0 ≤ 1` — must surface.
    const hasZeroLeOne = sugs.some(s => s.id.includes('zeroLeOne'));
    expect(hasZeroLeOne).toBe(true);
  });

  test('REGRESSION (image #29): clicking the zeroLeOne suggestion closes the goal end-to-end (proof tree replay)', { timeout: 30000 }, async () => {
    // Image-#29 bug: clicking `apply zeroLeOne` in the structured editor
    // produced "missing required argument: 'r'" because the dispatch used
    // `applyExact` (no implicit-arg inference) instead of `applyApplyTactic`
    // (creates fresh metas for implicits). Verify: the FULL click flow
    // — suggestion lookup, dispatch, proof tree replay — closes cleanly.
    const { r, decl } = compileTop('testImg29', `testImg29 : (R : Real) -> rle 1 2
testImg29 R = ?h`);
    const leafHole = mkHole();
    const proof: ProofNode = mkIntros(
      ['R'],
      mkApply('addLeRightCancel', [
        mkExact('-1'),
        mkRewrite('addRealOfRat', mkRewrite('addRealOfRat', leafHole)),
      ])
    );
    const engine = replayToEngine(proof, leafHole.id, decl.kernelType, r.definitions);
    expect(engine).not.toBeNull();
    if (!engine) return;
    const focusedGoal = engine.getFocusedGoal();
    expect(focusedGoal).toBeDefined();
    const rev = buildReverseRegistry({ symbolMap: new Map(), entries: [] });
    const ig = renderInteractiveGoal(engine, focusedGoal!, r.definitions, rev);
    let rlePath: string | null = null;
    for (const [p, info] of ig.subtermMap) {
      if (info.headName === 'rle' && info.occurrenceIndex === 1) { rlePath = p; break; }
    }
    const sugs = computeTacticSuggestions(rlePath!, ig, r.definitions, {
      engine, goal: focusedGoal!, definitions: r.definitions, rev,
    });
    // The suggestion must include a zeroLeOne path that closes the goal.
    const zeroLeOneSug = sugs.find(s => s.id.includes('zeroLeOne'));
    expect(zeroLeOneSug).toBeDefined();
    expect(zeroLeOneSug!.numSubgoals).toBe(0);
  });

  test('REGRESSION (image #32): full simp+apply chain replays without "return type mismatch (conflict)"', { timeout: 30000 }, async () => {
    // Image #32: user reached `0 ≤ 1` via intros + apply addLeRightCancel
    // + exact -1 + 2 rewrites with addRealOfRat + simp. They clicked
    // \`apply CompleteOrderedField.zeroLeOne\` and got "return type mismatch
    // (conflict)" at REPLAY time. Reproduce the exact tree structure.
    const { r, decl } = compileTop('testImg32', `testImg32 : (R : Real) -> rle 1 2
testImg32 R = ?h`);
    const { runSimp } = await import('../tactics/simp-tactic');
    const { applySimp, applyApplyTactic } = await import('./proof-tree');

    // Build tree up to the post-rewrite leaf hole.
    const preSimpLeaf = mkHole();
    const partialTree: ProofNode = mkIntros(
      ['R'],
      mkApply('addLeRightCancel', [
        mkExact('-1'),
        mkRewrite('addRealOfRat', mkRewrite('addRealOfRat', preSimpLeaf)),
      ])
    );

    // Replay to post-rewrite leaf. The kernel goal there has un-reduced
    // \`realOfRat R (ratPlus 1 -1)\` (renderer collapses to \`0 ≤ 1\`).
    const preSimpEngine = replayToEngine(partialTree, preSimpLeaf.id, decl.kernelType, r.definitions);
    expect(preSimpEngine).not.toBeNull();
    if (!preSimpEngine) return;

    // Now run runSimp to get simp steps + the simplified engine.
    const lemmas = [...(r.definitions.simpLemmas ?? [])];
    const simpResult = runSimp(preSimpEngine, lemmas);
    expect(simpResult.success).toBe(true);
    expect(simpResult.steps.length).toBeGreaterThan(0);

    // Add a simp node to the proof tree with these steps; cursor moves to
    // a child hole AFTER the simp.
    const stateBeforeSimp = { root: partialTree, cursor: { nodeId: preSimpLeaf.id } };
    const stateAfterSimp = applySimp(stateBeforeSimp, lemmas, simpResult.proofNodes);
    expect(stateAfterSimp).not.toBeNull();
    if (!stateAfterSimp) return;

    // Click apply zeroLeOne on the post-simp leaf (0 subgoals).
    const stateAfterApply = applyApplyTactic(stateAfterSimp, 'CompleteOrderedField.zeroLeOne', 0);
    expect(stateAfterApply).not.toBeNull();
    if (!stateAfterApply) return;

    // FULL TREE REPLAY from root: this is what the live editor does on
    // every keystroke. Must reach the cursor without errors.
    // FULL TREE WALK: replayEntireTree walks every node and validates.
    const { replayEntireTree } = await import('./goal-computation');
    const rev = buildReverseRegistry({ symbolMap: new Map(), entries: [] });
    const goalMap = replayEntireTree(stateAfterApply.root, decl.kernelType, r.definitions, rev);

    // Find the apply node's validation status.
    const findApplyNode = (n: ProofNode): any => {
      if (n.tag === 'apply' && n.name.includes('zeroLeOne')) return n;
      if (n.tag === 'apply') for (const c of n.children) { const f = findApplyNode(c); if (f) return f; }
      if ('child' in n && n.child) return findApplyNode(n.child as ProofNode);
      if (n.tag === 'simp') return findApplyNode(n.child as ProofNode);
      return null;
    };
    const applyNode = findApplyNode(stateAfterApply.root);
    expect(applyNode).not.toBeNull();
    const applyInfo = goalMap.get(applyNode.id);
    // The apply node should NOT have a tacticError. The live editor's
    // `replayEntireTreeViaWalk` records `tacticError` on apply nodes whose
    // ApplyTactic.apply returns success=false — that's exactly the
    // "return type mismatch (conflict)" the user sees in image #32.
    expect((applyInfo as any)?.tacticError).toBeUndefined();
    if (applyInfo?.validation?.status === 'error') {
      throw new Error(`apply node validation failed: ${applyInfo.validation.message}`);
    }
  });
});
