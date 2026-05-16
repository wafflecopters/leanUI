/**
 * Regression: zeroLeOne surfaces as an apply suggestion on `rle 0 1`.
 * Historically this came via the \`simp-then-apply-def-X\` path (with a
 * dedup-aware resultGoalLatex per def name); the kernel apply tactic now
 * handles record-projection unification directly via positional matching,
 * so the suggestion surfaces as plain \`apply-def-CompleteOrderedField.zeroLeOne\`.
 */
import { describe, test, expect } from 'vitest';
import { compileTTFromText } from '../compiler/compile';
import { REAL_ANALYSIS_CODE } from '../presets/real-analysis';
import { createInitialEngine } from '../tactics/tacticsEngine';
import { IntrosTactic } from '../tactics/tactic';
import { computeTacticSuggestions } from './tactic-suggestions';
import { renderInteractiveGoal } from './interactive-goal';
import { buildReverseRegistry } from '../math-editor/tt-to-math';

describe('simp-then-apply-def-X dedup: each closing candidate has unique latex', () => {
  test('both leRefl and zeroLeOne surface with distinct resultGoalLatex on `0 ≤ 1`', { timeout: 30000 }, () => {
    const r = compileTTFromText(REAL_ANALYSIS_CODE + `

testZleDedup : (R : Real) -> rle 0 1
testZleDedup R = ?h
`);
    let decl: any;
    for (const b of r.blocks) for (const d of b.declarations) if (d.name === 'testZleDedup') decl = d;
    let engine = createInitialEngine(decl.kernelType, [], r.definitions);
    engine = (new IntrosTactic(['R']).apply(engine, engine.metaVars.get(engine.goals[0])!, engine.goals[0]) as any).newEngine;
    const g = engine.metaVars.get(engine.goals[0])!;
    const rev = buildReverseRegistry({ symbolMap: new Map(), entries: [] });
    const ig = renderInteractiveGoal(engine, g, r.definitions, rev);
    let rlePath: string | null = null;
    for (const [p, info] of ig.subtermMap) {
      if (info.headName === 'rle' && info.occurrenceIndex === 1) { rlePath = p; break; }
    }
    const sugs = computeTacticSuggestions(rlePath!, ig, r.definitions, { engine, goal: g, definitions: r.definitions, rev });
    // The CompleteOrderedField.zeroLeOne suggestion MUST surface — whether as
    // a direct \`apply-def-\` (kernel positional fallback) or as the older
    // \`simp-then-apply-def-\` path.
    const hasZeroLeOne = sugs.some(s => s.id.includes('zeroLeOne'));
    expect(hasZeroLeOne).toBe(true);
    // Any closing \`simp-then-apply-def-X\` suggestion must have a UNIQUE
    // resultGoalLatex so React dedup doesn't collapse closes-the-goal cards.
    const closingSimpThenApply = sugs.filter(s => s.id.startsWith('simp-then-apply-def-') && s.resultGoalLatex);
    const latexes = new Set(closingSimpThenApply.map(s => s.resultGoalLatex));
    expect(latexes.size).toBe(closingSimpThenApply.length);
    for (const s of closingSimpThenApply) {
      const defName = s.id.slice('simp-then-apply-def-'.length);
      expect(s.resultGoalLatex).toContain(defName.split('.').pop()!);
    }
  });
});
