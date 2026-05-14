/**
 * Regression: apply-suggestion path used to skip every \`Name.member\`
 * definition (line: \`if (defName.includes('.')) continue;\`). That kept
 * record-field projections like \`Pair.fst\` out of the apply strip — but
 * also tossed out field-structure axioms like
 * \`CompleteOrderedField.zeroLeOne\`, which the user expects to surface
 * when the goal is \`0 ≤ 1\` on \`Carrier R\`.
 *
 * Fix: stop the blanket skip; keep the return-type-head filter; and
 * additionally accept matches where the candidate's return head equals
 * the goal's δ-expanded head (so \`rle\` goals match
 * \`CompleteOrderedField.le\` axioms after one layer of aliasing).
 */
import { describe, test, expect } from 'vitest';
import { compileTTFromText } from '../compiler/compile';
import { REAL_ANALYSIS_CODE } from '../presets/real-analysis';
import { createInitialEngine } from '../tactics/tacticsEngine';
import { IntrosTactic } from '../tactics/tactic';
import { computeTacticSuggestions } from './tactic-suggestions';
import { renderInteractiveGoal } from './interactive-goal';
import { buildReverseRegistry } from '../math-editor/tt-to-math';

describe('apply suggestions surface field-structure axioms', () => {
  test('0 ≤ 1 on Carrier R offers CompleteOrderedField.zeroLeOne', { timeout: 30000 }, () => {
    const r = compileTTFromText(REAL_ANALYSIS_CODE + `
testZeroLeOne : (R : Real) -> rle (rzero R) (rone R)
testZeroLeOne R = ?h
`);
    const decl = r.blocks.flatMap(b => b.declarations).find(d => d.name === 'testZeroLeOne')!;
    let engine = createInitialEngine(decl.kernelType!, [], r.definitions);
    engine = (new IntrosTactic(['R']).apply(engine, engine.metaVars.get(engine.goals[0])!, engine.goals[0]) as any).newEngine;
    const goal = engine.metaVars.get(engine.goals[0])!;
    const rev = buildReverseRegistry({ symbolMap: new Map(), entries: [] });
    const ig = renderInteractiveGoal(engine, goal, r.definitions, rev);
    let rlePath: string | null = null;
    for (const [p, info] of ig.subtermMap) {
      if (info.headName === 'rle' && info.occurrenceIndex === 1) { rlePath = p; break; }
    }
    expect(rlePath).not.toBeNull();

    const kernelGoal = { engine, goal, definitions: r.definitions, rev };
    const sugs = computeTacticSuggestions(rlePath!, ig, r.definitions, kernelGoal);
    const ids = sugs.map(s => s.id);
    expect(ids).toContain('apply-def-CompleteOrderedField.zeroLeOne');
  });
});
