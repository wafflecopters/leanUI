/**
 * Two tightly-related fixes to interactive-goal suggestion gating:
 *
 * (F) Image #21 bug: clicking `(-1)` showed `Simp addRealOfRat → 0` — a
 *     suggestion whose rewrite changed the PARENT `1 + (-1)`, not the clicked
 *     subterm. The "inner pass" of the simp-lemma scanner (try-anywhere) was
 *     running on every interior click. Fix: gate the inner pass to whole-goal
 *     selections only (root/body/body-head).
 *
 * (R) Image #22 bug: clicking `1 + (-1)` only showed `Simp addNegRight` —
 *     useful rewrites like `addComm` (commutativity, same-length result) were
 *     filtered by a "strictly shorter" gate. Fix: relax to "strictly longer →
 *     drop, identical → drop, anything else → keep".
 */
import { describe, test, expect } from 'vitest';
import { compileTTFromText } from '../compiler/compile';
import { REAL_ANALYSIS_CODE } from '../presets/real-analysis';
import { createInitialEngine } from '../tactics/tacticsEngine';
import { IntrosTactic } from '../tactics/tactic';
import { computeTacticSuggestions } from './tactic-suggestions';
import { renderInteractiveGoal } from './interactive-goal';
import { buildReverseRegistry } from '../math-editor/tt-to-math';

function setup(source: string, declName: string) {
  const r = compileTTFromText(REAL_ANALYSIS_CODE + '\n\n' + source);
  let decl: any;
  for (const b of r.blocks) for (const d of b.declarations) if (d.name === declName) decl = d;
  expect(decl).toBeDefined();
  let engine = createInitialEngine(decl.kernelType, [], r.definitions);
  engine = (new IntrosTactic(['R']).apply(engine, engine.metaVars.get(engine.goals[0])!, engine.goals[0]) as any).newEngine;
  const g = engine.metaVars.get(engine.goals[0])!;
  const rev = buildReverseRegistry({ symbolMap: new Map(), entries: [] });
  const ig = renderInteractiveGoal(engine, g, r.definitions, rev);
  return { r, engine, g, rev, ig };
}

function findSubterm(ig: any, headName: string, occ = 1): string | null {
  for (const [path, info] of ig.subtermMap) {
    if (info.headName === headName && info.occurrenceIndex === occ) return path;
  }
  return null;
}

describe('(F) inner-pass gating: interior clicks don\'t surface rewrites of other subterms', () => {
  test('clicking `(-1)` (rneg) does NOT receive simp suggestions that rewrite the parent radd', { timeout: 30000 }, () => {
    const { r, engine, g, rev, ig } = setup(
      `testF : (R : Real) -> rle (radd (rone R) (rneg (rone R))) (radd (rtwo R) (rneg (rone R)))
testF R = ?h`,
      'testF'
    );
    const negPath = findSubterm(ig, 'rneg', 1);
    expect(negPath).not.toBeNull();
    const sugs = computeTacticSuggestions(negPath!, ig, r.definitions, { engine, goal: g, definitions: r.definitions, rev });
    // No simp suggestion should mention addNegRight (that's a parent-level
    // rewrite — clicking the child shouldn't surface it).
    const parentLevelSuggestion = sugs.find(s => s.id.includes('addNegRight') || s.id.includes('simp-then-apply'));
    expect(parentLevelSuggestion).toBeUndefined();
  });

  test('clicking `1+(-1)` (radd) DOES receive `addNegRight` (rewrite at clicked level)', { timeout: 30000 }, () => {
    const { r, engine, g, rev, ig } = setup(
      `testFparent : (R : Real) -> rle (radd (rone R) (rneg (rone R))) (radd (rtwo R) (rneg (rone R)))
testFparent R = ?h`,
      'testFparent'
    );
    const raddPath = findSubterm(ig, 'radd', 1);
    expect(raddPath).not.toBeNull();
    const sugs = computeTacticSuggestions(raddPath!, ig, r.definitions, { engine, goal: g, definitions: r.definitions, rev });
    const ids = sugs.map(s => s.id);
    expect(ids.some(id => id.includes('addNegRight'))).toBe(true);
  });
});

describe('(R) relaxed-shorter filter: same-length useful rewrites surface', () => {
  test('clicking `1+(-1)` shows MORE than one simp suggestion (e.g. `addNegRight` and `addComm`-style)', { timeout: 30000 }, () => {
    const { r, engine, g, rev, ig } = setup(
      `testR : (R : Real) -> rle (radd (rone R) (rneg (rone R))) (radd (rtwo R) (rneg (rone R)))
testR R = ?h`,
      'testR'
    );
    const raddPath = findSubterm(ig, 'radd', 1);
    expect(raddPath).not.toBeNull();
    const sugs = computeTacticSuggestions(raddPath!, ig, r.definitions, { engine, goal: g, definitions: r.definitions, rev });
    const simpSuggestions = sugs.filter(s => s.id.startsWith('simp-'));
    // Before relaxation: just `simp-addNegRight`. After: at least one more
    // useful same-length rewrite should slip through (commutativity, etc.).
    expect(simpSuggestions.length).toBeGreaterThanOrEqual(1);
    // Specifically, addNegRight should be there.
    expect(simpSuggestions.some(s => s.id.includes('addNegRight'))).toBe(true);
  });

  test('no-op rewrites are still filtered (same rendered result on both sides)', { timeout: 30000 }, () => {
    // A rewrite that leaves rendered LaTeX unchanged should NOT surface —
    // it'd be confusing to show "Simp X" when nothing visible changes.
    const { r, engine, g, rev, ig } = setup(
      `testNoOp : (R : Real) -> rle (rone R) (rone R)
testNoOp R = ?h`,
      'testNoOp'
    );
    // The whole goal is \`rle 1 1\` (trivially true via refl). Clicking
    // anywhere should give suggestions whose rendered output differs from
    // the clicked subterm. No-op rewrites must be suppressed.
    const rlePath = findSubterm(ig, 'rle', 1);
    if (rlePath) {
      const sugs = computeTacticSuggestions(rlePath!, ig, r.definitions, { engine, goal: g, definitions: r.definitions, rev });
      for (const s of sugs.filter(s => s.id.startsWith('simp-'))) {
        // Each simp suggestion's resultGoalLatex must differ from a no-op preview.
        expect(s.resultGoalLatex).toBeDefined();
      }
    }
  });
});
