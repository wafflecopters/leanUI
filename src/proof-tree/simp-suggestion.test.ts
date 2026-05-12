/**
 * Tests for @simp-tagged lemmas surfacing as one-click suggestions on
 * subterm selection. The high-leverage cases for the milestone:
 *
 *   - addRealOfRat tagged @simp ⇒ `radd (realOfRat R p) (realOfRat R q)`
 *     reduces to `realOfRat R (ratPlus p q)` (which the kernel collapses
 *     via @ratAdd to a single literal).
 *
 *   - mulRealOfRat and subRealOfRat: same shape, same reduction path.
 */
import { describe, test, expect } from 'vitest';
import { compileTTFromText } from '../compiler/compile';
import { REAL_ANALYSIS_CODE } from '../presets/real-analysis';
import { computeTacticSuggestions } from './tactic-suggestions';
import { renderInteractiveGoal } from './interactive-goal';
import { buildReverseRegistry } from '../math-editor/tt-to-math';
import { createInitialEngine } from '../tactics/tacticsEngine';
import { IntrosTactic } from '../tactics/tactic';

describe('@simp suggestion surfacing', () => {
  test('addRealOfRat is registered in @simp set after compiling preset', { timeout: 30000 }, () => {
    const r = compileTTFromText(REAL_ANALYSIS_CODE);
    const simpLemmas = r.definitions.simpLemmas;
    expect(simpLemmas).toBeDefined();
    expect(simpLemmas?.has('addRealOfRat')).toBe(true);
    expect(simpLemmas?.has('mulRealOfRat')).toBe(true);
    expect(simpLemmas?.has('subRealOfRat')).toBe(true);
  });

  test('clicking radd-of-literals offers a Simp addRealOfRat suggestion', { timeout: 30000 }, () => {
    // Goal type: \`(R : Real) -> Equal {A := Carrier R} (radd 1.5 0.5) 2.0\`.
    // After intros R, the body becomes a literal-arithmetic equality
    // perfect for one-click @simp.
    const source = `
proof_add : (R : Real) -> Equal {A := Carrier R} (radd 1.5 0.5) 2.0
proof_add R = ?hole
`;
    const r = compileTTFromText(REAL_ANALYSIS_CODE + source);
    const decl = r.blocks.flatMap(b => b.declarations).find(d => d.name === 'proof_add');
    expect(decl?.kernelType).toBeDefined();

    let engine = createInitialEngine(decl!.kernelType!, [], r.definitions);
    const intros = new IntrosTactic(['R']);
    const introsResult = intros.apply(engine, engine.metaVars.get(engine.goals[0])!, engine.goals[0]);
    expect(introsResult.success).toBe(true);
    if (!introsResult.success) return;
    engine = introsResult.newEngine;

    const goalId = engine.goals[0];
    const goal = engine.metaVars.get(goalId)!;
    const rev = buildReverseRegistry({ symbolMap: new Map(), entries: [] });
    const interactiveGoal = renderInteractiveGoal(engine, goal, r.definitions, rev);

    // Find a path that targets the radd LHS of the Equal. The
    // subtermMap has entries keyed by goal-tN ids; we search for the one
    // whose head is radd.
    let raddPath: string | null = null;
    for (const [path, info] of interactiveGoal.subtermMap) {
      if (info.headName === 'radd') { raddPath = path; break; }
    }
    expect(raddPath).not.toBeNull();
    if (!raddPath) return;

    const kernelGoal = { engine, goal, definitions: r.definitions, rev };
    const suggestions = computeTacticSuggestions(raddPath, interactiveGoal, r.definitions, kernelGoal);
    const ids = suggestions.map(s => s.id);
    expect(ids.some(id => id.startsWith('simp-addRealOfRat'))).toBe(true);

    // The result preview should show "2" — addRealOfRat rewrites
    // \`radd 1.5 0.5\` to \`realOfRat R (ratPlus 1.5 0.5)\`, kernel @ratAdd
    // computes ratPlus → 2/1, NatLit collapses, @ofRat fold renders "2".
    const simp = suggestions.find(s => s.id.startsWith('simp-addRealOfRat'));
    expect(simp?.resultGoalLatex).toBe('2');
  });
});
