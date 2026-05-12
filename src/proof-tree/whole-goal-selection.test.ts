/**
 * Regression: the "is this a whole-goal selection?" gate that scopes
 * apply / exact-hyp suggestions needs to handle the click-on-body-root
 * case too — not just the synthetic goal-root / goal-body wrapper ids.
 *
 * When the goal is `rlt (rzero R) (rdiv e 2)` and the user clicks the
 * rendered `0 < ε/2` expression, the click registers on the goal-tN
 * subterm whose head is `rlt`, not on the goal-body wrapper. The gate
 * has to detect "selected subterm's head matches goal-body's head AND
 * is the first occurrence AND has no binder-index" — that's the
 * structural definition of "selected = the goal as a unit".
 */
import { describe, test, expect } from 'vitest';
import { compileTTFromText } from '../compiler/compile';
import { REAL_ANALYSIS_CODE } from '../presets/real-analysis';
import { computeTacticSuggestions } from './tactic-suggestions';
import { renderInteractiveGoal } from './interactive-goal';
import { buildReverseRegistry } from '../math-editor/tt-to-math';
import { createInitialEngine } from '../tactics/tacticsEngine';
import { IntrosTactic } from '../tactics/tactic';

describe('whole-goal selection unlocks apply/exact-hyp suggestions', () => {
  test('clicking the rlt body subterm offers apply-lemma suggestions', { timeout: 30000 }, () => {
    const r = compileTTFromText(REAL_ANALYSIS_CODE + `
testGoal : (R : Real) -> (e : Carrier R) -> rlt (rzero R) (rdiv e 2)
testGoal R e = ?h
`);
    const decl = r.blocks.flatMap(b => b.declarations).find(d => d.name === 'testGoal')!;
    let engine = createInitialEngine(decl.kernelType!, [], r.definitions);
    const intros = new IntrosTactic(['R', 'e']);
    const ir = intros.apply(engine, engine.metaVars.get(engine.goals[0])!, engine.goals[0]);
    expect(ir.success).toBe(true);
    if (!ir.success) return;
    engine = ir.newEngine;

    const gid = engine.goals[0];
    const goal = engine.metaVars.get(gid)!;
    const rev = buildReverseRegistry({ symbolMap: new Map(), entries: [] });
    const ig = renderInteractiveGoal(engine, goal, r.definitions, rev);

    let rltPath: string | null = null;
    for (const [path, info] of ig.subtermMap) {
      if (info.headName === 'rlt' && info.occurrenceIndex === 1) { rltPath = path; break; }
    }
    expect(rltPath).not.toBeNull();
    if (!rltPath) return;

    const kernelGoal = { engine, goal, definitions: r.definitions, rev };
    const suggestions = computeTacticSuggestions(rltPath, ig, r.definitions, kernelGoal);
    const applyIds = suggestions.map(s => s.id).filter(id => id.startsWith('apply-def-'));
    // At least one apply-lemma suggestion should fire (e.g., leLtTrans).
    expect(applyIds.length).toBeGreaterThan(0);
  });

  test('clicking an interior subterm does NOT offer apply-lemma suggestions', { timeout: 30000 }, () => {
    // Same goal, but click an interior subterm (rdiv ε 2 — the RHS of rlt).
    const r = compileTTFromText(REAL_ANALYSIS_CODE + `
testGoal : (R : Real) -> (e : Carrier R) -> rlt (rzero R) (rdiv e 2)
testGoal R e = ?h
`);
    const decl = r.blocks.flatMap(b => b.declarations).find(d => d.name === 'testGoal')!;
    let engine = createInitialEngine(decl.kernelType!, [], r.definitions);
    const intros = new IntrosTactic(['R', 'e']);
    const ir = intros.apply(engine, engine.metaVars.get(engine.goals[0])!, engine.goals[0]);
    expect(ir.success).toBe(true);
    if (!ir.success) return;
    engine = ir.newEngine;

    const gid = engine.goals[0];
    const goal = engine.metaVars.get(gid)!;
    const rev = buildReverseRegistry({ symbolMap: new Map(), entries: [] });
    const ig = renderInteractiveGoal(engine, goal, r.definitions, rev);

    let rdivPath: string | null = null;
    for (const [path, info] of ig.subtermMap) {
      if (info.headName === 'rdiv') { rdivPath = path; break; }
    }
    expect(rdivPath).not.toBeNull();
    if (!rdivPath) return;

    const kernelGoal = { engine, goal, definitions: r.definitions, rev };
    const suggestions = computeTacticSuggestions(rdivPath, ig, r.definitions, kernelGoal);
    const applyIds = suggestions.map(s => s.id).filter(id => id.startsWith('apply-def-'));
    // Interior subterm: apply-on-goal suggestions are noise here.
    expect(applyIds.length).toBe(0);
  });
});
