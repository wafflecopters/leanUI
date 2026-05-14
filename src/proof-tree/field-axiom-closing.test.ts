/**
 * Tests that the field axioms \`zeroLeOne\` / \`zeroLtOne\` (and their
 * CompleteOrderedField counterparts) can SURFACE as apply-suggestions
 * AND ACTUALLY APPLY on goals of shape \`rle 0 1\` / \`rlt 0 1\`,
 * regardless of which kernel literal form the 0 and 1 took.
 *
 * Three kernel forms for \`0\` and \`1\` at \`Carrier R\` show up
 * depending on how the user got there:
 *   (A) Direct literal in source: \`realOfRat R (MkRat (IntOfNat n) 1 (IsSucc 0))\`
 *       — the constructor form, produced by parser elaboration + @ofRat
 *       routing via natLitAsRatExpr.
 *   (B) After @ratAdd / @ratMul fast-path: \`realOfRat R (NatLit n)\` —
 *       canonicalized form. mkRatLit collapses integer-valued Rats with
 *       \`num >= 0, den = 1\` to NatLit, so any reduction that goes
 *       through ratPlus / ratMult / ratSub lands here.
 *   (C) Bare alias forms: \`rzero R\` / \`rone R\` — the user wrote
 *       them explicitly or a simp chain canonicalized to them.
 *
 * The lemma return types are in form (C). For the user's flow to work
 * one-click, either:
 *   - the apply unifier handles (A)/(B) → (C) via WHNF, or
 *   - simp bridges (A)/(B) → (C) and apply runs on the simplified goal.
 */
import { describe, test, expect } from 'vitest';
import { compileTTFromText } from '../compiler/compile';
import { REAL_ANALYSIS_CODE } from '../presets/real-analysis';
import { createInitialEngine } from '../tactics/tacticsEngine';
import { IntrosTactic, ApplyTactic } from '../tactics/tactic';
import { RewriteTactic } from '../tactics/rewrite-tactic';
import { runSimp } from '../tactics/simp-tactic';
import { computeTacticSuggestions } from './tactic-suggestions';
import { renderInteractiveGoal } from './interactive-goal';
import { buildReverseRegistry } from '../math-editor/tt-to-math';
import type { TTKTerm } from '../compiler/kernel';

const C = (n: string): TTKTerm => ({ tag: 'Const', name: n });
const A = (fn: TTKTerm, a: TTKTerm): TTKTerm => ({ tag: 'App', fn, arg: a });
const VAR = (i: number): TTKTerm => ({ tag: 'Var', index: i });
const NLIT = (v: bigint): TTKTerm => ({ tag: 'NatLit', value: v });
const MKRAT = (n: bigint): TTKTerm =>
  A(A(A(C('MkRat'), A(C('IntOfNat'), NLIT(n))), NLIT(1n)), A(C('IsSucc'), NLIT(0n)));
const rofR = (R: TTKTerm, x: TTKTerm) => A(A(C('realOfRat'), R), x);
const PI = (name: string, dom: TTKTerm, body: TTKTerm): TTKTerm => ({
  tag: 'Binder' as const, binderKind: { tag: 'BPi' as const }, name, domain: dom, body,
});

function setup() {
  const r = compileTTFromText(REAL_ANALYSIS_CODE);
  return r;
}

function buildGoal(headName: 'rle' | 'rlt', lhs: TTKTerm, rhs: TTKTerm): TTKTerm {
  const R = VAR(0);
  return PI('R', C('Real'), A(A(A(C(headName), R), lhs), rhs));
}

function intros(engine: any) {
  return (new IntrosTactic(['R']).apply(engine, engine.metaVars.get(engine.goals[0])!, engine.goals[0]) as any).newEngine;
}

describe('field axiom application: 0 ≤ 1 / 0 < 1', () => {
  const r = setup();

  describe('Form A: MkRat-form literals (direct source elaboration)', () => {
    test('apply zeroLeOne on rle (realOfRat R MkRat0) (realOfRat R MkRat1)', () => {
      const R = VAR(0);
      const goal = buildGoal('rle', rofR(R, MKRAT(0n)), rofR(R, MKRAT(1n)));
      let engine = createInitialEngine(goal, [], r.definitions);
      engine = intros(engine);
      const g = engine.metaVars.get(engine.goals[0])!;
      const result = new ApplyTactic({ tag: 'Const', name: 'CompleteOrderedField.zeroLeOne' }).apply(engine, g, engine.goals[0]);
      // EXPECTED to work — but currently fails. Skip until apply unifier learns WHNF.
      expect(result.success).toBe(true);
    });

    test('apply zeroLtOne on rlt (realOfRat R MkRat0) (realOfRat R MkRat1)', () => {
      const R = VAR(0);
      const goal = buildGoal('rlt', rofR(R, MKRAT(0n)), rofR(R, MKRAT(1n)));
      let engine = createInitialEngine(goal, [], r.definitions);
      engine = intros(engine);
      const g = engine.metaVars.get(engine.goals[0])!;
      const result = new ApplyTactic({ tag: 'Const', name: 'zeroLtOne' }).apply(engine, g, engine.goals[0]);
      expect(result.success).toBe(true);
    });

    test('simp canonicalizes MkRat-form 0 → rzero, 1 → rone', () => {
      const R = VAR(0);
      const goal = buildGoal('rle', rofR(R, MKRAT(0n)), rofR(R, MKRAT(1n)));
      let engine = createInitialEngine(goal, [], r.definitions);
      engine = intros(engine);
      const lemmas = [...(r.definitions.simpLemmas ?? [])];
      const simpRes = runSimp(engine, lemmas);
      expect(simpRes.success).toBe(true);
      expect(simpRes.steps.length).toBeGreaterThanOrEqual(2); // realOfRatZero + realOfRatOne
    });

    test('suggestions include zeroLeOne when click body-head of MkRat-form rle', () => {
      const R = VAR(0);
      const goal = buildGoal('rle', rofR(R, MKRAT(0n)), rofR(R, MKRAT(1n)));
      let engine = createInitialEngine(goal, [], r.definitions);
      engine = intros(engine);
      const g = engine.metaVars.get(engine.goals[0])!;
      const rev = buildReverseRegistry({ symbolMap: new Map(), entries: [] });
      const ig = renderInteractiveGoal(engine, g, r.definitions, rev);
      let rlePath: string | null = null;
      for (const [p, info] of ig.subtermMap) {
        if (info.headName === 'rle' && info.occurrenceIndex === 1) { rlePath = p; break; }
      }
      expect(rlePath).not.toBeNull();
      const sugs = computeTacticSuggestions(rlePath!, ig, r.definitions, { engine, goal: g, definitions: r.definitions, rev });
      const ids = sugs.map(s => s.id);
      // After the fix, the field-axiom suggestion should appear AND succeed.
      const hasFieldAxiom = ids.some(id => id === 'apply-def-CompleteOrderedField.zeroLeOne');
      expect(hasFieldAxiom).toBe(true);
    });
  });

  describe('Form B: NatLit-form literals (after @ratAdd fast-path)', () => {
    test('apply zeroLeOne on rle (realOfRat R NatLit0) (realOfRat R NatLit1)', () => {
      const R = VAR(0);
      const goal = buildGoal('rle', rofR(R, NLIT(0n)), rofR(R, NLIT(1n)));
      let engine = createInitialEngine(goal, [], r.definitions);
      engine = intros(engine);
      const g = engine.metaVars.get(engine.goals[0])!;
      const result = new ApplyTactic({ tag: 'Const', name: 'CompleteOrderedField.zeroLeOne' }).apply(engine, g, engine.goals[0]);
      expect(result.success).toBe(true);
    });

    test('simp closes/canonicalizes NatLit-form rle', () => {
      const R = VAR(0);
      const goal = buildGoal('rle', rofR(R, NLIT(0n)), rofR(R, NLIT(1n)));
      let engine = createInitialEngine(goal, [], r.definitions);
      engine = intros(engine);
      const lemmas = [...(r.definitions.simpLemmas ?? [])];
      const simpRes = runSimp(engine, lemmas);
      expect(simpRes.success).toBe(true);
      // We need at least the realOfRatZero / realOfRatOne bridges to fire
      // even when their LHS is keyed on MkRat-form and the goal is NatLit-form.
      expect(simpRes.steps.length).toBeGreaterThanOrEqual(2);
    });
  });

  describe('Form C: bare aliases (rzero R / rone R)', () => {
    test('apply zeroLeOne on rle (rzero R) (rone R) — control', () => {
      const R = VAR(0);
      const goal = buildGoal('rle', A(C('rzero'), R), A(C('rone'), R));
      let engine = createInitialEngine(goal, [], r.definitions);
      engine = intros(engine);
      const g = engine.metaVars.get(engine.goals[0])!;
      const result = new ApplyTactic({ tag: 'Const', name: 'CompleteOrderedField.zeroLeOne' }).apply(engine, g, engine.goals[0]);
      expect(result.success).toBe(true);
    });

    test('apply zeroLtOne on rlt (rzero R) (rone R) — control', () => {
      const R = VAR(0);
      const goal = buildGoal('rlt', A(C('rzero'), R), A(C('rone'), R));
      let engine = createInitialEngine(goal, [], r.definitions);
      engine = intros(engine);
      const g = engine.metaVars.get(engine.goals[0])!;
      const result = new ApplyTactic({ tag: 'Const', name: 'zeroLtOne' }).apply(engine, g, engine.goals[0]);
      expect(result.success).toBe(true);
    });
  });
});
