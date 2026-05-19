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
import { beforeEach, describe, test, expect } from 'vitest';
import { compileTTFromText } from '../compiler/compile';
import { REAL_ANALYSIS_CODE } from '../presets/real-analysis';
import { applyTacticCommandsAtCursor, buildApplyTacticCommands } from './tactic-command-bridge';
import { applySimp, mkIntros, mkApply, mkRewrite, mkHole, mkExact, resetProofIds, type ProofNode } from './proof-tree';
import { replayEntireTree, replayToEngine } from './goal-computation';
import { computeTacticSuggestions } from './tactic-suggestions';
import { renderInteractiveGoal } from './interactive-goal';
import { buildReverseRegistry } from '../math-editor/tt-to-math';
import { runSimp } from '../tactics/simp-tactic';

function compileTop(declName: string, source: string) {
  const r = compileTTFromText(REAL_ANALYSIS_CODE + '\n\n' + source);
  let decl: any;
  for (const b of r.blocks) for (const d of b.declarations) if (d.name === declName) decl = d;
  expect(decl).toBeDefined();
  return { r, decl };
}

beforeEach(() => {
  resetProofIds();
});

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

  test('REGRESSION (image #35): clicking a collapsed literal (`2`) does NOT surface simp rewrites of its parent', { timeout: 60000 }, () => {
    // Image #35: user clicked just `2` (which renders from
    // \`realOfRat R MkRat2\` via @ofRat-fold), but saw \`Simp addRealOfRat
    // → 1\` — a rewrite of the PARENT \`2 + (-1)\`. Clicking a literal
    // shouldn't surface rewrites that operate on a wider subterm.
    const { r, decl } = compileTop('testFocus2', `testFocus2 : (R : Real) -> rle 1 2
testFocus2 R = ?h`);
    const leaf = mkHole();
    const tree: ProofNode = mkIntros(['R'], mkApply('addLeRightCancel', [
      mkExact('-1'),
      mkRewrite('addRealOfRat', leaf),
    ]));
    const engine = replayToEngine(tree, leaf.id, decl.kernelType, r.definitions);
    expect(engine).not.toBeNull();
    if (!engine) return;
    const focusedGoal = engine.getFocusedGoal()!;
    const rev = buildReverseRegistry({ symbolMap: new Map(), entries: [] });
    const ig = renderInteractiveGoal(engine, focusedGoal, r.definitions, rev);
    // Find a subterm path whose rendered term is a literal (head undefined,
    // term tag NatLit/RatLit/Hole or term that the renderer treats as
    // collapsed literal).
    let literalPath: string | null = null;
    for (const [path, info] of ig.subtermMap) {
      if (info.headName === undefined && info.term.tag !== 'Var') { literalPath = path; break; }
    }
    expect(literalPath).not.toBeNull();
    const sugs = computeTacticSuggestions(literalPath!, ig, r.definitions, {
      engine, goal: focusedGoal, definitions: r.definitions, rev,
    });
    // No \`simp-*\` suggestion should fire on a literal click.
    const simpSugs = sugs.filter(s => s.id.startsWith('simp-'));
    expect(simpSugs.length).toBe(0);
  });

  test('REGRESSION (image #34): apply leTrans subgoal previews resolve field-implicit to bound R (no `field(□)`)', { timeout: 90000 }, () => {
    // Image #34: subgoal previews for \`apply CompleteOrderedField.leTrans\`
    // on \`rle 0 1\` showed \`CompleteOrderedField.le (field (□), 0, a)\`
    // — the \`□\` was an unsolved elaborator Hole (the implicit \`{R}\` of
    // \`rle 0 1\`) that wasn't pinned to the bound \`R\` after intros R.
    // Fix: IntroTactic now pins compatible Holes to context vars when
    // there's a unique type match. Subgoal previews must NOT contain \`□\`.
    const { r, decl } = compileTop('testFieldBox', `testFieldBox : (R : Real) -> rle 0 1
testFieldBox R = ?h`);
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
    const leTransSug = sugs.find(s => s.id.includes('leTrans'));
    expect(leTransSug).toBeDefined();
    // No subgoal preview LaTeX should contain a placeholder for unsolved
    // metas — that's the `□` symbol (rendered as `\square` or similar) or
    // the kernel meta-marker `??`.
    const previews = leTransSug!.subgoalPreviews ?? [];
    for (const p of previews) {
      expect(p).not.toContain('\\square');
      expect(p).not.toMatch(/□|\?\?/);
    }
  });

  test('REGRESSION (image #32): full simp+apply chain replays without "return type mismatch (conflict)"', { timeout: 30000 }, () => {
    // Image #32: user reached `0 ≤ 1` via intros + apply addLeRightCancel
    // + exact -1 + 2 rewrites with addRealOfRat + simp. They clicked
    // \`apply CompleteOrderedField.zeroLeOne\` and got "return type mismatch
    // (conflict)" at REPLAY time. Reproduce the exact tree structure.
    const { r, decl } = compileTop('testImg32', `testImg32 : (R : Real) -> rle 1 2
testImg32 R = ?h`);
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
    const stateAfterApply = applyTacticCommandsAtCursor(
      stateAfterSimp,
      buildApplyTacticCommands('CompleteOrderedField.zeroLeOne', 0),
    );
    expect(stateAfterApply).not.toBeNull();
    if (!stateAfterApply) return;

    // FULL TREE REPLAY from root: this is what the live editor does on
    // every keystroke. Must reach the cursor without errors.
    // FULL TREE WALK: replayEntireTree walks every node and validates.
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
    // REGRESSION (image #39): a 0-subgoal apply (e.g. `apply zeroLeOne` on
    // `0 ≤ 1`) closes the goal. The walker must mark the apply node's
    // validation as 'solved' so the editor shows the green "Goal solved"
    // indicator in the side panel when the cursor lands on the apply line.
    expect(applyInfo?.validation?.status).toBe('solved');
  });

  // REGRESSION (image #36): user typed `exact -1` in a `Carrier R` position.
  // Previously parsed as `App(Const("sub"), NatLit(1))` because the prefix
  // parselet used the same `constName` as infix `-`. Result: "Type definition
  // not found: sub". Fix: parser now emits a signed RatLit for `-<digit>`
  // (no whitespace), which routes through the elaborator's @ofInt path.
  test('REGRESSION (image #36): exact -1 in Carrier R position elaborates without "sub not found"', { timeout: 30000 }, () => {
    const { r, decl } = compileTop('testImg36', `testImg36 : (R : Real) -> Carrier R
testImg36 R = ?h`);

    const proof: ProofNode = mkIntros(['R'], mkExact('-1'));
    const leafHole = mkHole();
    // Use the goal-computation walk to surface any tactic errors at the exact node.
    const rev = buildReverseRegistry({ symbolMap: new Map(), entries: [] });
    return (async () => {
      const { replayEntireTree } = await import('./goal-computation');
      const goalMap = replayEntireTree(proof, decl.kernelType, r.definitions, rev);
      // Find the exact node and verify it produced no tactic error.
      const findExact = (n: ProofNode): any => {
        if (n.tag === 'exact') return n;
        if ('child' in n && n.child) return findExact(n.child as ProofNode);
        return null;
      };
      const exactNode = findExact(proof);
      expect(exactNode).not.toBeNull();
      const exactInfo = goalMap.get(exactNode.id);
      // The old broken behavior surfaced an error mentioning "sub" — that should
      // not happen anymore. The exact's elaboration should succeed; the kernel
      // value should resolve to a real number via realOfInt / rneg-of-rone.
      const err = (exactInfo as any)?.tacticError;
      if (err) {
        expect(err.toLowerCase()).not.toContain('sub');
        expect(err.toLowerCase()).not.toContain('type definition not found');
      }
      // Re-suppress unused leafHole warning (kept for symmetry with other tests).
      void leafHole;
    })();
  });

  // REGRESSION (image #40): clicking the alias-headed `2 + (-1)` subterm in
  // `1 + (-1) ≤ 2 + (-1)` must surface lemmas keyed under the projection head
  // (e.g. `CompleteOrderedField.addComm`), not just `addRealOfRat`. The
  // candidate gets collected via the head-expansion logic in
  // collectRewriteCandidates; the rewrite tactic now also bridges
  // alias↔projection in the occurrence-targeted substituteImpl path. Before
  // the fix, targetHead='radd' and lhsHead='CompleteOrderedField.add' didn't
  // match in the gate at rewrite-tactic.ts step 4e, dropping addComm before
  // tryRewrite ever ran.
  test('REGRESSION (image #40): clicking radd-headed subterm surfaces CompleteOrderedField.addComm', { timeout: 30000 }, async () => {
    const { r, decl } = compileTop('testImg40', `testImg40 : (R : Real) -> rle 1 2
testImg40 R = ?h`);
    const leafHole = mkHole();
    const proof: ProofNode = mkIntros(
      ['R'],
      mkApply('addLeRightCancel', [
        mkExact('-1'),
        mkRewrite('addRealOfRat', leafHole),
      ])
    );
    const engine = replayToEngine(proof, leafHole.id, decl.kernelType, r.definitions);
    expect(engine).not.toBeNull();
    if (!engine) return;
    const focusedGoal = engine.getFocusedGoal();
    expect(focusedGoal).toBeDefined();
    if (!focusedGoal) return;
    const rev = buildReverseRegistry({ symbolMap: new Map(), entries: [] });
    const ig = renderInteractiveGoal(engine, focusedGoal, r.definitions, rev);
    // Find first radd-headed subterm path (occurrence 1).
    let raddPath: string | null = null;
    for (const [p, info] of ig.subtermMap) {
      if (info.headName === 'radd' && info.occurrenceIndex === 1) { raddPath = p; break; }
    }
    expect(raddPath).not.toBeNull();
    if (!raddPath) return;
    const { computeRewriteSuggestionsIncremental } = await import('./tactic-suggestions');
    const collected: any[] = [];
    let done = false;
    computeRewriteSuggestionsIncremental(raddPath, ig, {
      engine, goal: focusedGoal, definitions: r.definitions, rev,
    } as any, (progress) => {
      for (const s of progress.suggestions) {
        if (!collected.find(x => x.id === s.id)) collected.push(s);
      }
      done = progress.done;
    });
    // Drain the setTimeout-batched pipeline.
    for (let i = 0; i < 30 && !done; i++) await new Promise(r => setTimeout(r, 50));
    const names = collected.map(s => s.rewriteName);
    expect(names).toContain('CompleteOrderedField.addComm');
  });

  // The "intro-shape" reverse rewrites — lemmas whose RHS is a bare Meta —
  // were previously dropped twice: (a) collectRewriteCandidates required a
  // matching RHS head, but bare-Meta RHS has no head, so the candidate
  // never made it past head filtering; (b) tryRewrite dropped any rewrite
  // whose result LaTeX was strictly longer than the input, which is exactly
  // the shape "introduce shape" rewrites produce. Now both gates are relaxed.
  test('REGRESSION (image #42): clicking radd-headed subterm surfaces intro-shape reverse rewrites (e.g. addZeroLeft←)', { timeout: 30000 }, async () => {
    const { r, decl } = compileTop('testImg42', `testImg42 : (R : Real) -> rle 1 2
testImg42 R = ?h`);
    const leafHole = mkHole();
    const proof: ProofNode = mkIntros(
      ['R'],
      mkApply('addLeRightCancel', [
        mkExact('-1'),
        mkRewrite('addRealOfRat', leafHole),
      ])
    );
    const engine = replayToEngine(proof, leafHole.id, decl.kernelType, r.definitions);
    expect(engine).not.toBeNull();
    if (!engine) return;
    const focusedGoal = engine.getFocusedGoal();
    if (!focusedGoal) return;
    const rev = buildReverseRegistry({ symbolMap: new Map(), entries: [] });
    const ig = renderInteractiveGoal(engine, focusedGoal, r.definitions, rev);
    let raddPath: string | null = null;
    for (const [p, info] of ig.subtermMap) {
      if (info.headName === 'radd' && info.occurrenceIndex === 1) { raddPath = p; break; }
    }
    if (!raddPath) return;
    const { computeRewriteSuggestionsIncremental } = await import('./tactic-suggestions');
    const collected: any[] = [];
    let done = false;
    computeRewriteSuggestionsIncremental(raddPath, ig, {
      engine, goal: focusedGoal, definitions: r.definitions, rev,
    } as any, (progress) => {
      for (const s of progress.suggestions) {
        if (!collected.find(x => x.id === s.id)) collected.push(s);
      }
      done = progress.done;
    });
    for (let i = 0; i < 60 && !done; i++) await new Promise(r => setTimeout(r, 50));
    const reverseNames = collected.filter(s => s.reverse).map(s => s.rewriteName);
    // Spot-check one canonical intro-shape reverse: addZeroLeft (RHS=Meta, LHS head=radd via δ-bridge).
    // The actual surface lemma may be named `addZeroLeft` (preset top-level)
    // or `CompleteOrderedField.addZeroRight` etc.; both have the right shape.
    const hasIntroShape = reverseNames.some(n =>
      n.toLowerCase().includes('zerole') ||
      n.toLowerCase().includes('zeroright') ||
      n.toLowerCase().includes('addzero')
    );
    expect(hasIntroShape).toBe(true);
  });

  // REGRESSION (image #42 follow-up): after rewriting one of two `radd`-headed
  // subterms with `addComm`, the rewritten subterm's kernel head changes to
  // the projection form (`CompleteOrderedField.add`), while the un-rewritten
  // sibling keeps the alias head (`radd`). The UI's fold pipeline shows both
  // as `+` (radd in surface) and the surface annotator counts them together.
  // But substituteImpl was counting by KERNEL head only — so a click on the
  // projection-headed occurrence (occurrence 2 here) couldn't be reached: the
  // counter never advanced to 2 for radd-targeted lemmas. Fix: substituteImpl
  // now counts via the expanded head set, so both alias and projection forms
  // of the same surface head count together. Also: isMatch tries unfolding
  // BOTH sides (term and `from`), so `addRealOfRat` (LHS is alias) matches a
  // projection-headed goal subterm.
  test('REGRESSION (image #42b): after addComm on RHS, clicking the rewritten subterm surfaces both addComm AND addRealOfRat', { timeout: 30000 }, async () => {
    const { r, decl } = compileTop('testImg42b', `testImg42b : (R : Real) -> rle 1 2
testImg42b R = ?h`);
    const leafHole = mkHole();
    const proof: ProofNode = mkIntros(
      ['R'],
      mkApply('addLeRightCancel', [
        mkExact('-1'),
        {
          tag: 'rewrite',
          id: -1 as any,  // resetProofIds via beforeEach reassigns
          name: 'CompleteOrderedField.addComm',
          reverse: false,
          occurrences: [2],
          targetHead: 'radd',
          child: leafHole,
        } as any,
      ])
    );
    const engine = replayToEngine(proof, leafHole.id, decl.kernelType, r.definitions);
    expect(engine).not.toBeNull();
    if (!engine) return;
    const focusedGoal = engine.getFocusedGoal();
    if (!focusedGoal) return;
    const rev = buildReverseRegistry({ symbolMap: new Map(), entries: [] });
    const ig = renderInteractiveGoal(engine, focusedGoal, r.definitions, rev);
    let occ2Path: string | null = null;
    for (const [p, info] of ig.subtermMap) {
      if (info.headName === 'radd' && info.occurrenceIndex === 2) { occ2Path = p; break; }
    }
    expect(occ2Path).not.toBeNull();
    if (!occ2Path) return;
    const { computeRewriteSuggestionsIncremental } = await import('./tactic-suggestions');
    const collected: any[] = [];
    let done = false;
    computeRewriteSuggestionsIncremental(occ2Path, ig, {
      engine, goal: focusedGoal, definitions: r.definitions, rev,
    } as any, (progress) => {
      for (const s of progress.suggestions) {
        if (!collected.find(x => x.id === s.id)) collected.push(s);
      }
      done = progress.done;
    });
    for (let i = 0; i < 60 && !done; i++) await new Promise(r => setTimeout(r, 50));
    const names = collected.map(s => s.rewriteName);
    expect(names).toContain('CompleteOrderedField.addComm');
    // The key assertion: addRealOfRat must surface on the projection-headed
    // occurrence, because the kernel goal still contains the same realOfRat
    // structure — just wrapped under the projection head after the rewrite.
    expect(names).toContain('addRealOfRat');
  });

  // REGRESSION (image #44): inside a `have h : T` proof subtree, apply-def
  // suggestions used to disappear entirely — only "Unfold X" surfaced.
  // Root cause: `isCleanApply` was zonking the WHOLE engine term and checking
  // for dangling metas. In a have block, the engine still holds the outer
  // theorem's goal (intentionally unsolved while we work on the have's body),
  // which surfaces as a "dangling meta" and rejects every apply candidate.
  // Fix: check only the SPECIFIC applied goal's solution, not the whole
  // engine.
  test('REGRESSION (image #44): apply suggestions surface inside have proof subtree', { timeout: 30000 }, async () => {
    const { r, decl } = compileTop('testImg44', `testImg44 : (R : Real) -> (ε : Carrier R) -> rlt (rzero R) ε -> rlt (rzero R) (rdiv ε (rtwo R))
testImg44 R ε hε = ?outer`);
    // Set up: intros, then have h : 0 < ε/2, cursor in the have's proof
    const { mkHave } = await import('./proof-tree');
    const haveProofHole = mkHole();
    const outerHole = mkHole();
    const haveNode = mkHave('h', '?', outerHole, '(rlt (rzero R) (rdiv ε (rtwo R)))', haveProofHole);
    const proof: ProofNode = mkIntros(['R', 'ε', 'hε'], haveNode);
    const engine = replayToEngine(proof, haveProofHole.id, decl.kernelType, r.definitions);
    expect(engine).not.toBeNull();
    if (!engine) return;
    const focusedGoal = engine.getFocusedGoal();
    expect(focusedGoal).toBeDefined();
    if (!focusedGoal) return;
    const rev = buildReverseRegistry({ symbolMap: new Map(), entries: [] });
    const ig = renderInteractiveGoal(engine, focusedGoal, r.definitions, rev);
    let rltPath: string | null = null;
    for (const [p, info] of ig.subtermMap) {
      if (info.headName === 'rlt' && info.occurrenceIndex === 1) { rltPath = p; break; }
    }
    expect(rltPath).not.toBeNull();
    if (!rltPath) return;
    const sugs = computeTacticSuggestions(rltPath, ig, r.definitions, {
      engine, goal: focusedGoal, definitions: r.definitions, rev,
    });
    const labels = sugs.map(s => s.label);
    // Expect at minimum: Unfold rlt PLUS at least one apply suggestion.
    // The exact best apply lemma can vary with surrounding search heuristics,
    // but the regression we care about is that apply-def suggestions surface
    // at all inside the `have` proof subtree.
    expect(labels).toContain('Unfold rlt');
    const hasApplySuggestion = sugs.some(s => (s.id as string)?.startsWith('apply-def-'));
    expect(hasApplySuggestion).toBe(true);
  });

  // REGRESSION (image #45): clicking a `radd`-headed subterm inside a `have`
  // proof subtree must surface `rw addRealOfRat` (and other rewrites whose
  // LHS pattern matches via the alias). Root cause: the have-block path in
  // `replayProofTree` set up the proof's goal type via
  // `parseExactExpr → elaborateType` but did NOT pin elaborator-leftover
  // Holes for implicit args (e.g. `rle`'s `{R}`, `radd`'s `{R}`) to bound
  // context vars. IntrosTactic does this pinning (since image #34), but the
  // have-block setup skipped it — so the goal carried unresolved
  // `Hole(_implicit_R)` placeholders that broke pattern matching in the
  // rewrite tactic. Fix: also run `pinHolesToCtxVars` on the have block's
  // elaborated type.
  test('REGRESSION (image #45): rw addRealOfRat surfaces for radd inside have proof', { timeout: 30000 }, async () => {
    const { r, decl } = compileTop('testImg45', `testImg45 : (R : Real) -> rle 1 2
testImg45 R = ?outer`);
    const { mkHave } = await import('./proof-tree');
    const haveProof = mkHole();
    const outer = mkHole();
    // Have type: `0 ≤ 2 + (-1)` — uses natural surface syntax so implicit
    // `{R}` args show up as Holes from parseExactExpr; pinHolesToCtxVars
    // must resolve them before pattern matching.
    const haveNode = mkHave('h', '?', outer,
      '(rle (rzero R) (radd (realOfRat R 2) (realOfRat R -1)))',
      haveProof);
    const proof: ProofNode = mkIntros(['R'], haveNode);
    const engine = replayToEngine(proof, haveProof.id, decl.kernelType, r.definitions);
    expect(engine).not.toBeNull();
    if (!engine) return;
    const focusedGoal = engine.getFocusedGoal();
    if (!focusedGoal) return;
    const rev = buildReverseRegistry({ symbolMap: new Map(), entries: [] });
    const ig = renderInteractiveGoal(engine, focusedGoal, r.definitions, rev);
    let raddPath: string | null = null;
    for (const [p, info] of ig.subtermMap) {
      if (info.headName === 'radd' && info.occurrenceIndex === 1) { raddPath = p; break; }
    }
    expect(raddPath).not.toBeNull();
    if (!raddPath) return;
    const { computeRewriteSuggestionsIncremental } = await import('./tactic-suggestions');
    const collected: any[] = [];
    let done = false;
    computeRewriteSuggestionsIncremental(raddPath, ig, {
      engine, goal: focusedGoal, definitions: r.definitions, rev,
    } as any, (progress) => {
      for (const s of progress.suggestions) {
        if (!collected.find(x => x.id === s.id)) collected.push(s);
      }
      done = progress.done;
    });
    for (let i = 0; i < 120 && !done; i++) await new Promise(r => setTimeout(r, 50));
    const names = collected.map(s => s.rewriteName);
    expect(names).toContain('addRealOfRat');
    expect(names).toContain('CompleteOrderedField.addComm');
  });
});
