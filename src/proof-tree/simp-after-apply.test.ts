/**
 * Regression: @simp suggestions must zonk the goal type before
 * pattern-matching.
 *
 * After \`apply addLeRightCancel\` (or any apply that introduces
 * metavariable arguments solved on sibling subgoals via \`exact\`),
 * the focused goal's type still references the raw tactic metas —
 * \`(rle ?_meta_R (radd ?_meta_R ?_meta_a ?_meta_c) (radd ?_meta_R ?_meta_b ?_meta_c))\`.
 * The user SEES the substituted form (\`1 + (-1) ≤ 2 + (-1)\`)
 * because renderInteractiveGoal zonks for display, but
 * computeTacticSuggestions used to feed the raw type into
 * RewriteTactic — which rejects every simp lemma because the
 * pattern's \`realOfRat ?a ?b\` structure can't match a bare meta.
 *
 * Fix: zonk the goal type before passing to the rewrite tactic so
 * pattern matching sees what the user sees.
 */
import { describe, test, expect } from 'vitest';
import { compileTTFromText } from '../compiler/compile';
import { REAL_ANALYSIS_CODE } from '../presets/real-analysis';
import { createInitialEngine } from '../tactics/tacticsEngine';
import { IntrosTactic, ApplyTactic, ExactTactic } from '../tactics/tactic';
import { computeTacticSuggestions } from './tactic-suggestions';
import { renderInteractiveGoal } from './interactive-goal';
import { buildReverseRegistry } from '../math-editor/tt-to-math';
import { parseExactExpr as parseExpr } from './goal-computation';

describe('@simp suggestions survive open metas from apply', () => {
  test('after apply addLeRightCancel + exact witnesses, simp fires on the radd subgoal', { timeout: 30000 }, () => {
    const r = compileTTFromText(REAL_ANALYSIS_CODE);
    const demo = r.blocks.flatMap(b => b.declarations).find(d => d.name === 'demoTestLiterals')!;

    let engine = createInitialEngine(demo.kernelType!, [], r.definitions);
    engine = (new IntrosTactic(['R']).apply(engine, engine.metaVars.get(engine.goals[0])!, engine.goals[0]) as any).newEngine;
    engine = (new ApplyTactic({ tag: 'Const', name: 'addLeRightCancel' }).apply(engine, engine.metaVars.get(engine.goals[0])!, engine.goals[0]) as any).newEngine;

    // Provide witnesses for the three Carrier-R subgoals via exact.
    let carrierIdx = 0;
    for (const gid of [...engine.goals]) {
      const g = engine.metaVars.get(gid);
      if (!g) continue;
      let head: any = g.type;
      while (head.tag === 'App') head = head.fn;
      if (head.tag !== 'Const' || head.name !== 'Carrier') continue;
      const expr = ['1', '2', '-1'][carrierIdx++];
      const witness = parseExpr(expr, g.ctx, r.definitions);
      expect(witness).not.toBeNull();
      const er = new ExactTactic(witness as any).apply(engine, g, gid);
      expect(er.success).toBe(true);
      if (er.success) engine = er.newEngine;
    }

    // Focus the rle goal.
    let rleId: string | null = null;
    for (const gid of engine.goals) {
      let h: any = engine.metaVars.get(gid)!.type;
      while (h.tag === 'App') h = h.fn;
      if (h.tag === 'Const' && h.name === 'rle') { rleId = gid; break; }
    }
    expect(rleId).not.toBeNull();
    engine = engine.withUpdates({ focusIndex: engine.goals.indexOf(rleId!) });
    const rleGoal = engine.metaVars.get(rleId!)!;

    const rev = buildReverseRegistry({ symbolMap: new Map(), entries: [] });
    const ig = renderInteractiveGoal(engine, rleGoal, r.definitions, rev);

    // Find the radd subterm path (occurrence 1 = LHS of rle).
    let raddPath: string | null = null;
    for (const [p, info] of ig.subtermMap) {
      if (info.headName === 'radd' && info.occurrenceIndex === 1) { raddPath = p; break; }
    }
    expect(raddPath).not.toBeNull();

    const kernelGoal = { engine, goal: rleGoal, definitions: r.definitions, rev };
    const suggestions = computeTacticSuggestions(raddPath!, ig, r.definitions, kernelGoal);
    const ids = suggestions.map(s => s.id);

    // The point: at LEAST one simp suggestion appears. Without the zonk fix,
    // every simp lemma's RewriteTactic.apply returned "no occurrences found"
    // because the goal type held raw \`?tactic_meta_N\` placeholders where
    // the pattern wanted Const-headed apps.
    expect(ids.some(id => id.startsWith('simp-'))).toBe(true);
  });
});
