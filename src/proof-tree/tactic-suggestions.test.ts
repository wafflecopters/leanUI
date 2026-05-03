import { describe, test, expect, beforeAll } from 'vitest';
import { TTKTerm } from '../compiler/kernel';
import { createDefinitionsMap, addDefinition, MetaVar } from '../compiler/term';
import { mkConstTT } from '../compiler/surface';
import { collectRewriteCandidates, computeTacticSuggestions, KernelGoalInfo } from './tactic-suggestions';
import { compileTTFromText } from '../compiler/compile';
import { createInitialEngine } from '../tactics/tacticsEngine';
import { IntrosTactic, ApplyTactic, ExactTactic } from '../tactics/tactic';
import { InteractiveGoal } from './interactive-goal';
import { parseExactExpr, elaborateType } from './goal-computation';
import { renderInteractiveGoal } from './interactive-goal';
import { buildReverseRegistry } from '../math-editor/tt-to-math';
import { createDefaultRegistry } from '../math-editor/syntax-registry';

// ============================================================================
// Helpers
// ============================================================================

/** Make an Equal type: Equal A lhs rhs */
function mkEqual(lhs: TTKTerm, rhs: TTKTerm, typeA: TTKTerm = { tag: 'Const', name: 'Nat' }): TTKTerm {
  return {
    tag: 'App',
    fn: {
      tag: 'App',
      fn: { tag: 'App', fn: { tag: 'Const', name: 'Equal' }, arg: typeA },
      arg: lhs,
    },
    arg: rhs,
  };
}

/** Make a Pi type: (name : domain) -> body */
function mkPi(name: string, domain: TTKTerm, body: TTKTerm): TTKTerm {
  return { tag: 'Binder', binderKind: { tag: 'BPi' as const }, name, domain, body };
}

const nat: TTKTerm = { tag: 'Const', name: 'Nat' };
const zero: TTKTerm = { tag: 'Const', name: 'Zero' };

function mkApp(fn: TTKTerm, arg: TTKTerm): TTKTerm {
  return { tag: 'App', fn, arg };
}

function mkConst(name: string): TTKTerm {
  return { tag: 'Const', name };
}

function mkVar(index: number): TTKTerm {
  return { tag: 'Var', index };
}

// ============================================================================
// Tests for self-referential filtering
// ============================================================================

describe('collectRewriteCandidates', () => {
  test('includes equality definitions as rewrite candidates', () => {
    // Define: plusComm : (n m : Nat) -> Equal (add n m) (add m n)
    let defs = createDefinitionsMap();
    defs = addDefinition(defs, 'plusComm',
      mkPi('n', nat, mkPi('m', nat,
        mkEqual(mkApp(mkApp(mkConst('add'), mkVar(1)), mkVar(0)),
                mkApp(mkApp(mkConst('add'), mkVar(0)), mkVar(1))))),
    );

    const goal: MetaVar = {
      ctx: [],
      type: mkEqual(mkApp(mkApp(mkConst('add'), mkConst('a')), mkConst('b')),
                     mkApp(mkApp(mkConst('add'), mkConst('b')), mkConst('a'))),
    };

    const candidates = collectRewriteCandidates(goal, defs, { selectedHead: 'add' });
    const names = candidates.map(c => c.name);
    expect(names).toContain('plusComm');
  });

  test('filters out self-referential definition when currentDeclName is set', () => {
    // Define: triangleSum : (n : Nat) -> Equal (mul 2 (sum n)) (mul (add n 1) n)
    let defs = createDefinitionsMap();
    const triangleType = mkPi('n', nat,
      mkEqual(
        mkApp(mkApp(mkConst('mul'), mkConst('two')), mkApp(mkConst('sum'), mkVar(0))),
        mkApp(mkApp(mkConst('mul'), mkApp(mkApp(mkConst('add'), mkVar(0)), mkConst('one'))), mkVar(0)),
      ),
    );
    defs = addDefinition(defs, 'triangleSum', triangleType);

    // Also add a different equality
    defs = addDefinition(defs, 'mulComm',
      mkPi('a', nat, mkPi('b', nat,
        mkEqual(mkApp(mkApp(mkConst('mul'), mkVar(1)), mkVar(0)),
                mkApp(mkApp(mkConst('mul'), mkVar(0)), mkVar(1))))),
    );

    const goal: MetaVar = {
      ctx: [],
      type: mkEqual(mkApp(mkApp(mkConst('mul'), mkConst('two')), mkApp(mkConst('sum'), zero)),
                     mkApp(mkApp(mkConst('mul'), mkConst('one')), zero)),
    };

    // Without currentDeclName: triangleSum IS included
    const candidatesWithout = collectRewriteCandidates(goal, defs, { selectedHead: 'mul' });
    const namesWithout = candidatesWithout.map(c => c.name);
    expect(namesWithout).toContain('triangleSum');
    expect(namesWithout).toContain('mulComm');

    // With currentDeclName: triangleSum is FILTERED OUT
    const candidatesWith = collectRewriteCandidates(goal, defs, { selectedHead: 'mul' }, 'triangleSum');
    const namesWith = candidatesWith.map(c => c.name);
    expect(namesWith).not.toContain('triangleSum');
    expect(namesWith).toContain('mulComm');
  });

  test('hypothesis-based rewrites are not affected by currentDeclName', () => {
    let defs = createDefinitionsMap();

    // IH in context: Equal (mul 2 (sum n')) (mul (add n' 1) n')
    const ihType = mkEqual(
      mkApp(mkApp(mkConst('mul'), mkConst('two')), mkApp(mkConst('sum'), mkVar(0))),
      mkApp(mkApp(mkConst('mul'), mkApp(mkApp(mkConst('add'), mkVar(0)), mkConst('one'))), mkVar(0)),
    );

    const goal: MetaVar = {
      ctx: [
        { name: 'n\'', type: nat },
        { name: 'IH', type: ihType },
      ],
      type: mkEqual(mkApp(mkApp(mkConst('mul'), mkConst('two')), mkApp(mkConst('sum'), mkVar(1))),
                     mkApp(mkApp(mkConst('mul'), mkConst('one')), mkVar(1))),
    };

    // IH (a hypothesis, not a definition) should still appear even with currentDeclName
    const candidates = collectRewriteCandidates(goal, defs, { selectedHead: 'mul' }, 'triangleSum');
    const names = candidates.map(c => c.name);
    expect(names).toContain('IH');
  });

  test('self-referential candidate allowed in induction case with structural decrease', () => {
    // In the Succ case of induction on n:
    // Context: [n' : Nat, IH : ...]
    // Goal has sum(n') — the smaller argument
    // triangleSum should be allowed because caseTag is set and argument is a Var

    let defs = createDefinitionsMap();
    const triangleType = mkPi('n', nat,
      mkEqual(
        mkApp(mkApp(mkConst('mul'), mkConst('two')), mkApp(mkConst('sum'), mkVar(0))),
        mkApp(mkApp(mkConst('mul'), mkApp(mkApp(mkConst('add'), mkVar(0)), mkConst('one'))), mkVar(0)),
      ),
    );
    defs = addDefinition(defs, 'triangleSum', triangleType);

    const goal: MetaVar = {
      ctx: [
        { name: 'n\'', type: nat },
        { name: 'IH', type: mkEqual(mkConst('lhs'), mkConst('rhs')) },
      ],
      type: mkEqual(
        mkApp(mkApp(mkConst('mul'), mkConst('two')), mkApp(mkConst('sum'), mkVar(1))),
        mkConst('rhs'),
      ),
      caseTag: 'Succ',  // We're inside an induction case
    };

    // Self-reference should be tagged for structural check (not blanket-filtered)
    const candidates = collectRewriteCandidates(goal, defs, { selectedHead: 'mul' }, 'triangleSum');
    const selfRefs = candidates.filter(c => c.name === 'triangleSum');
    // Self-references in induction cases are included but tagged
    expect(selfRefs.length).toBeGreaterThan(0);
    expect(selfRefs[0].isSelfReference).toBe(true);
  });

  test('self-referential candidate rejected outside induction case', () => {
    let defs = createDefinitionsMap();
    const triangleType = mkPi('n', nat,
      mkEqual(
        mkApp(mkApp(mkConst('mul'), mkConst('two')), mkApp(mkConst('sum'), mkVar(0))),
        mkApp(mkApp(mkConst('mul'), mkApp(mkApp(mkConst('add'), mkVar(0)), mkConst('one'))), mkVar(0)),
      ),
    );
    defs = addDefinition(defs, 'triangleSum', triangleType);

    const goal: MetaVar = {
      ctx: [],
      type: mkEqual(
        mkApp(mkApp(mkConst('mul'), mkConst('two')), mkApp(mkConst('sum'), zero)),
        mkConst('rhs'),
      ),
      // No caseTag — not inside induction
    };

    const candidates = collectRewriteCandidates(goal, defs, { selectedHead: 'mul' }, 'triangleSum');
    const names = candidates.map(c => c.name);
    expect(names).not.toContain('triangleSum');
  });
});

// ============================================================================
// Hypothesis suggestions (exact / apply)
// ============================================================================

describe('computeTacticSuggestions — hypothesis exact/apply on goal-body', () => {
  /** Minimal InteractiveGoal for testing (not used for rendering, just structure). */
  function minimalGoal(): InteractiveGoal {
    return {
      latex: '',
      binders: [],
      subtermMap: new Map(),
      contextVarTypes: new Map(),
    };
  }

  test('suggests exact on hypothesis whose type matches goal', () => {
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

goal : Nat -> Nat -> Nat
goal x y = ?hole
`;
    const result = compileTTFromText(source);
    const goalDecl = result.blocks.flatMap(b => b.declarations).find(d => d.name === 'goal')!;
    const defs = result.definitions;

    let engine = createInitialEngine(goalDecl.kernelType!, [], defs);
    const intros = new IntrosTactic(['x', 'y']);
    const introsResult = intros.apply(engine, engine.metaVars.get(engine.goals[0])!, engine.goals[0]);
    expect(introsResult.success).toBe(true);
    if (!introsResult.success) return;
    engine = introsResult.newEngine;

    const goalId = engine.goals[0];
    const goal = engine.metaVars.get(goalId)!;

    const kernelGoal: KernelGoalInfo = { engine, goal, definitions: defs };
    const suggestions = computeTacticSuggestions('goal-body', minimalGoal(), defs, kernelGoal);
    const ids = suggestions.map(s => s.id);
    // Both x and y have type Nat, which matches the goal type Nat
    expect(ids).toContain('exact-hyp-x');
    expect(ids).toContain('exact-hyp-y');
  });

  test('suggests apply on hypothesis whose return type matches goal', () => {
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

goal : (f : Nat -> Nat) -> Nat -> Nat
goal f x = ?hole
`;
    const result = compileTTFromText(source);
    const goalDecl = result.blocks.flatMap(b => b.declarations).find(d => d.name === 'goal')!;
    const defs = result.definitions;

    let engine = createInitialEngine(goalDecl.kernelType!, [], defs);
    const intros = new IntrosTactic(['f', 'x']);
    const introsResult = intros.apply(engine, engine.metaVars.get(engine.goals[0])!, engine.goals[0]);
    expect(introsResult.success).toBe(true);
    if (!introsResult.success) return;
    engine = introsResult.newEngine;

    const goalId = engine.goals[0];
    const goal = engine.metaVars.get(goalId)!;

    const kernelGoal: KernelGoalInfo = { engine, goal, definitions: defs };
    const suggestions = computeTacticSuggestions('goal-body', minimalGoal(), defs, kernelGoal);
    const ids = suggestions.map(s => s.id);
    // x : Nat matches goal Nat → exact
    expect(ids).toContain('exact-hyp-x');
    // f : Nat → Nat, return type matches goal → apply (not exact, since it needs an argument)
    expect(ids).toContain('apply-hyp-f');
    // f should NOT have an exact suggestion (it's a function, not the goal type)
    expect(ids).not.toContain('exact-hyp-f');
  });

  test('does not suggest exact/apply on non-matching hypotheses', () => {
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Bool : Type where
  True : Bool
  False : Bool

goal : Bool -> Nat
goal b = ?hole
`;
    const result = compileTTFromText(source);
    const goalDecl = result.blocks.flatMap(b => b.declarations).find(d => d.name === 'goal')!;
    const defs = result.definitions;

    let engine = createInitialEngine(goalDecl.kernelType!, [], defs);
    const intros = new IntrosTactic(['b']);
    const introsResult = intros.apply(engine, engine.metaVars.get(engine.goals[0])!, engine.goals[0]);
    expect(introsResult.success).toBe(true);
    if (!introsResult.success) return;
    engine = introsResult.newEngine;

    const goalId = engine.goals[0];
    const goal = engine.metaVars.get(goalId)!;

    const kernelGoal: KernelGoalInfo = { engine, goal, definitions: defs };
    const suggestions = computeTacticSuggestions('goal-body', minimalGoal(), defs, kernelGoal);
    const ids = suggestions.map(s => s.id);
    // b : Bool doesn't match goal Nat
    expect(ids).not.toContain('exact-hyp-b');
    expect(ids).not.toContain('apply-hyp-b');
  });

  test('suggestions shown on subterm selection (goal-tN), not just goal-body', () => {
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

goal : Nat -> Nat
goal x = ?hole
`;
    const result = compileTTFromText(source);
    const goalDecl = result.blocks.flatMap(b => b.declarations).find(d => d.name === 'goal')!;
    const defs = result.definitions;

    let engine = createInitialEngine(goalDecl.kernelType!, [], defs);
    const intros = new IntrosTactic(['x']);
    const introsResult = intros.apply(engine, engine.metaVars.get(engine.goals[0])!, engine.goals[0]);
    expect(introsResult.success).toBe(true);
    if (!introsResult.success) return;
    engine = introsResult.newEngine;

    const goalId = engine.goals[0];
    const goal = engine.metaVars.get(goalId)!;

    const kernelGoal: KernelGoalInfo = { engine, goal, definitions: defs };
    // Selecting a specific subterm should also show hypothesis suggestions
    const suggestions = computeTacticSuggestions('goal-t0', minimalGoal(), defs, kernelGoal);
    const ids = suggestions.map(s => s.id);
    expect(ids).toContain('exact-hyp-x');
  });

  test('no hypothesis suggestions on binder selection', () => {
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

goal : Nat -> Nat
goal x = ?hole
`;
    const result = compileTTFromText(source);
    const goalDecl = result.blocks.flatMap(b => b.declarations).find(d => d.name === 'goal')!;
    const defs = result.definitions;

    const engine = createInitialEngine(goalDecl.kernelType!, [], defs);
    const goalId = engine.goals[0];
    const goal = engine.metaVars.get(goalId)!;

    const kernelGoal: KernelGoalInfo = { engine, goal, definitions: defs };
    // Selecting a binder (goal-0) should NOT show hypothesis suggestions
    const ig = minimalGoal();
    // Need binders for the binder path to be recognized
    const igWithBinders: InteractiveGoal = {
      ...ig,
      binders: [{ index: 0, name: 'x', domain: mkConstTT('Nat'), domainLatex: 'Nat', isImplicit: false }],
    };
    const suggestions = computeTacticSuggestions('goal-0', igWithBinders, defs, kernelGoal);
    const ids = suggestions.map(s => s.id);
    // Binder selection gives intro suggestions, not hypothesis suggestions
    expect(ids).not.toContain('exact-hyp-x');
  });
});

// ============================================================================
// Definition search suggestions with subgoal previews
// ============================================================================

describe('definition search suggestions', () => {
  // Use the real-analysis preset for realistic testing
  // eslint-disable-next-line @typescript-eslint/no-var-requires
  let defs: import('../compiler/term').DefinitionsMap;
  beforeAll(async () => {
    const { REAL_ANALYSIS_CODE } = await import('../presets/real-analysis');
    const compiled = compileTTFromText(REAL_ANALYSIS_CODE);
    defs = compiled.definitions!;
  });

  test('divTwoPos appears as suggestion for goal 0 < ε/2', () => {
    // Context: R : Real, ε : Carrier R, hε : rlt (rzero R) ε
    const ctx = [
      { name: 'R', type: { tag: 'Const' as const, name: 'Real' } },
      { name: 'ε', type: { tag: 'App' as const, fn: { tag: 'Const' as const, name: 'Carrier' }, arg: { tag: 'Var' as const, index: 0 } } },
    ];
    // Parse the hε type
    const hεType = parseExactExpr('rlt (rzero R) ε', ctx, defs);
    expect(hεType).not.toBeNull();
    const fullCtx = [...ctx, { name: 'hε', type: hεType! }];

    // Goal: rlt (rzero R) (rdiv ε (rtwo R))
    const goalType = parseExactExpr('rlt (rzero R) (rdiv ε (rtwo R))', fullCtx, defs);
    expect(goalType).not.toBeNull();
    // Elaborate to resolve Holes
    const elaborated = elaborateType(goalType!, fullCtx, defs);

    const engine = createInitialEngine(elaborated, fullCtx, defs);
    const goal = engine.getFocusedGoal()!;
    const goalId = engine.getFocusedGoalId()!;

    // Build KernelGoalInfo
    const registry = createDefaultRegistry();
    const rev = buildReverseRegistry(registry);
    const kernelGoal: KernelGoalInfo = { engine, goal, definitions: defs, rev };

    const ig = renderInteractiveGoal(engine, goal, defs, rev);
    expect(ig).not.toBeNull();

    // Click on the root subterm to get suggestions
    const suggestions = computeTacticSuggestions('goal-root', ig!, defs, kernelGoal);
    const ids = suggestions.map(s => s.id);

    // divTwoPos should appear
    expect(ids).toContain('apply-def-divTwoPos');

    // It should have 1 subgoal preview (0 < ε)
    const divTwoSugg = suggestions.find(s => s.id === 'apply-def-divTwoPos');
    expect(divTwoSugg?.subgoalPreviews).toBeDefined();
    expect(divTwoSugg!.subgoalPreviews!.length).toBe(1);
  });

  test('subgoal previews use fresh names instead of □', () => {
    const ctx = [
      { name: 'R', type: { tag: 'Const' as const, name: 'Real' } },
      { name: 'ε', type: { tag: 'App' as const, fn: { tag: 'Const' as const, name: 'Carrier' }, arg: { tag: 'Var' as const, index: 0 } } },
    ];
    const goalType = parseExactExpr('rlt (rzero R) (rdiv ε (rtwo R))', ctx, defs);
    const elaborated = elaborateType(goalType!, ctx, defs);

    const engine = createInitialEngine(elaborated, ctx, defs);
    const goal = engine.getFocusedGoal()!;
    const registry = createDefaultRegistry();
    const rev = buildReverseRegistry(registry);
    const kernelGoal: KernelGoalInfo = { engine, goal, definitions: defs, rev };
    const ig = renderInteractiveGoal(engine, goal, defs, rev);

    const suggestions = computeTacticSuggestions('goal-root', ig!, defs, kernelGoal);
    const leLtSugg = suggestions.find(s => s.id === 'apply-def-leLtTrans');

    if (leLtSugg?.subgoalPreviews) {
      // Subgoal previews should NOT contain □ (the hole character)
      for (const preview of leLtSugg.subgoalPreviews) {
        expect(preview).not.toContain('\\square');
      }
    }
  });

  test('zeroLtOne does NOT match goal 0 < ε/2', () => {
    const ctx = [
      { name: 'R', type: { tag: 'Const' as const, name: 'Real' } },
      { name: 'ε', type: { tag: 'App' as const, fn: { tag: 'Const' as const, name: 'Carrier' }, arg: { tag: 'Var' as const, index: 0 } } },
    ];
    const goalType = parseExactExpr('rlt (rzero R) (rdiv ε (rtwo R))', ctx, defs);
    const elaborated = elaborateType(goalType!, ctx, defs);

    const engine = createInitialEngine(elaborated, ctx, defs);
    const goal = engine.getFocusedGoal()!;
    const registry = createDefaultRegistry();
    const rev = buildReverseRegistry(registry);
    const kernelGoal: KernelGoalInfo = { engine, goal, definitions: defs, rev };
    const ig = renderInteractiveGoal(engine, goal, defs, rev);

    const suggestions = computeTacticSuggestions('goal-root', ig!, defs, kernelGoal);
    const ids = suggestions.map(s => s.id);

    // zeroLtOne proves 0 < 1, not 0 < ε/2 — should NOT appear
    expect(ids).not.toContain('apply-def-zeroLtOne');
  });

  test('elaborateType resolves Holes in parsed rlt expression', () => {
    const ctx = [
      { name: 'R', type: { tag: 'Const' as const, name: 'Real' } },
      { name: 'ε', type: { tag: 'App' as const, fn: { tag: 'Const' as const, name: 'Carrier' }, arg: { tag: 'Var' as const, index: 0 } } },
    ];
    // Parse rlt (rzero R) (rdiv ε (rtwo R)) — inserts Holes for implicit args
    const parsed = parseExactExpr('rlt (rzero R) (rdiv ε (rtwo R))', ctx, defs);
    expect(parsed).not.toBeNull();

    // Elaborate to resolve Holes
    const elaborated = elaborateType(parsed!, ctx, defs);
    expect(elaborated).not.toBe(parsed); // should NOT be the same object

    // No Holes should remain
    const json = JSON.stringify(elaborated);
    expect(json).not.toContain('"Hole"');

    // Head should be rlt
    let h: any = elaborated;
    while (h.tag === 'App') h = h.fn;
    expect(h.tag).toBe('Const');
    expect(h.name).toBe('rlt');
  });

  test('exact hε works on goal 0 < ε via elaborated typeExpr', async () => {
    const { shiftTerm } = await import('../compiler/subst');
    const ctx = [
      { name: 'R', type: { tag: 'Const' as const, name: 'Real' } },
      { name: 'ε', type: { tag: 'App' as const, fn: { tag: 'Const' as const, name: 'Carrier' }, arg: { tag: 'Var' as const, index: 0 } } },
    ];
    // Parse and elaborate the goal type: rlt (rzero R) ε
    const parsed = parseExactExpr('rlt (rzero R) ε', ctx, defs);
    expect(parsed).not.toBeNull();
    const goalType = elaborateType(parsed!, ctx, defs);

    // Verify Holes are resolved
    expect(JSON.stringify(goalType)).not.toContain('"Hole"');

    // hε has the SAME type; shift goal type by 1 since we're adding hε to context
    const shiftedGoalType = shiftTerm(goalType, 1, 0);
    const fullCtx = [...ctx, { name: 'hε', type: goalType }];
    const engine = createInitialEngine(shiftedGoalType, fullCtx, defs);
    const goal = engine.getFocusedGoal()!;
    const gId = engine.getFocusedGoalId()!;

    // exact hε (Var index 0 = hε)
    const hεVar: import('../compiler/kernel').TTKTerm = { tag: 'Var', index: 0 };
    const result = new ExactTactic(hεVar).apply(engine, goal, gId);
    expect(result.success).toBe(true);
  });

  test('exact hε NOT offered for goal 0<2 after epsOverMPos (E2E)', async () => {
    const { ConstructorTactic } = await import('../tactics/constructor-tactic');
    const rev = buildReverseRegistry(createDefaultRegistry());

    // Simulate limitsAdd proof: intros → constructor → intros ε hε → apply epsOverMPos
    const limType = defs.terms.get('limitAdd')?.type;
    expect(limType).toBeDefined();

    let engine = createInitialEngine(limType!, [], defs);
    let goal = engine.getFocusedGoal()!;
    let gId = engine.getFocusedGoalId()!;

    // Intros
    let r = new IntrosTactic(['R', 'f', 'g', 'x0', 'L', 'M', 'limF', 'limG']).apply(engine, goal, gId);
    if (!r.success) throw new Error('intros failed');
    engine = r.newEngine; goal = engine.getFocusedGoal()!; gId = engine.getFocusedGoalId()!;

    // Constructor
    r = new ConstructorTactic().apply(engine, goal, gId);
    if (!r.success) throw new Error('constructor failed');
    engine = r.newEngine; goal = engine.getFocusedGoal()!; gId = engine.getFocusedGoalId()!;

    // Intros ε, hε
    r = new IntrosTactic(['ε', 'hε']).apply(engine, goal, gId);
    if (!r.success) throw new Error('intros 2 failed');
    engine = r.newEngine; goal = engine.getFocusedGoal()!; gId = engine.getFocusedGoalId()!;

    // Create hoisted have subgoal: 0 < ε/2
    const parsed = parseExactExpr('rlt (rzero R) (rdiv ε (rtwo R))', goal.ctx, defs)!;
    const goalType = elaborateType(parsed, goal.ctx, defs);
    const subId = 'have_proof';
    const subMeta = { ctx: goal.ctx, type: goalType, solution: undefined as undefined };
    const subVars = new Map(engine.metaVars);
    subVars.set(subId, subMeta);
    const subEngine = engine.withUpdates({ metaVars: subVars, goals: [subId] });

    // Apply epsOverMPos
    r = new ApplyTactic({ tag: 'Const', name: 'epsOverMPos' }).apply(subEngine, subMeta, subId);
    if (!r.success) throw new Error('epsOverMPos failed');
    const epsEngine = r.newEngine;

    // Find the 0 < 2 goal — the second unsolved goal from epsOverMPos
    const unsolvedGoals = epsEngine.goals.filter(g => {
      const m = epsEngine.metaVars.get(g);
      return m && m.solution === undefined;
    });
    expect(unsolvedGoals.length).toBeGreaterThanOrEqual(2);
    const goal2Id = unsolvedGoals[1]; // second subgoal = 0 < M = 0 < 2
    const goal2 = epsEngine.metaVars.get(goal2Id!)!;

    // Compute suggestions for goal 0 < 2
    const ig = renderInteractiveGoal(epsEngine, goal2, defs, rev);
    expect(ig).not.toBeNull();

    // Find rlt subterm path
    const rltPath = [...ig!.subtermMap.entries()].find(([, v]) => v.headName === 'rlt')?.[0];
    expect(rltPath).toBeDefined();

    const kernelGoal: KernelGoalInfo = {
      engine: epsEngine.withUpdates({ goals: [goal2Id!] }),
      goal: goal2,
      definitions: defs,
      rev,
    };
    const suggestions = computeTacticSuggestions(rltPath!, ig!, defs, kernelGoal);

    // exact hε should NOT appear (hε proves 0 < ε, not 0 < 2)
    const exactHε = suggestions.find(s => s.id === 'exact-hyp-hε');
    expect(exactHε).toBeUndefined();

    // apply hε should NOT appear either
    const applyHε = suggestions.find(s => s.id === 'apply-hyp-hε');
    expect(applyHε).toBeUndefined();
  });

  test('parseExactExpr resolves 1→rone(R), 2→rtwo(R), 0→rzero(R)', () => {
    const ctx = [
      { name: 'R', type: { tag: 'Const' as const, name: 'Real' } },
    ];

    const p1 = parseExactExpr('1', ctx, defs);
    expect(p1).not.toBeNull();
    // Should be rone(Var(0)) = rone applied to R
    expect(p1!.tag).toBe('App');
    expect((p1 as any).fn.tag).toBe('Const');
    expect((p1 as any).fn.name).toBe('rone');
    expect((p1 as any).arg.tag).toBe('Var');
    expect((p1 as any).arg.index).toBe(0);

    const p2 = parseExactExpr('2', ctx, defs);
    expect(p2).not.toBeNull();
    expect((p2 as any).fn.tag).toBe('Const');
    expect((p2 as any).fn.name).toBe('rtwo');

    const p0 = parseExactExpr('0', ctx, defs);
    expect(p0).not.toBeNull();
    expect((p0 as any).fn.tag).toBe('Const');
    expect((p0 as any).fn.name).toBe('rzero');
  });

  test('exact 1 closes goal Carrier R', () => {
    const ctx = [
      { name: 'R', type: { tag: 'Const' as const, name: 'Real' } },
    ];
    // Goal: Carrier R
    const goalType: import('../compiler/kernel').TTKTerm = {
      tag: 'App', fn: { tag: 'Const', name: 'Carrier' }, arg: { tag: 'Var', index: 0 }
    };

    const engine = createInitialEngine(goalType, ctx, defs);
    const goal = engine.getFocusedGoal()!;
    const gId = engine.getFocusedGoalId()!;

    // Parse "1" and apply as exact
    const term = parseExactExpr('1', ctx, defs)!;
    const result = new ExactTactic(term).apply(engine, goal, gId);
    expect(result.success).toBe(true);
  });

  test('sibling goals show resolved metas after exact on first child', async () => {
    // After apply leLtTransLe (creates 3 subgoals: a:ℝ, 0≤a, a≤2),
    // solving goal 1 with "exact 1" should make siblings show 0≤1 and 1≤2
    const { mkExact, mkHole, mkApply, mkIntros } = await import('./proof-tree');
    const { replayEntireTree } = await import('./goal-computation');
    const rev = buildReverseRegistry(createDefaultRegistry());

    // Goal type: (R : Real) → rle(R, rzero(R), rtwo(R))
    // Need a Pi binder so intros can introduce R
    const R: import('../compiler/kernel').TTKTerm = { tag: 'Var', index: 0 };
    const rleGoal: import('../compiler/kernel').TTKTerm = {
      tag: 'App', fn: { tag: 'App', fn: { tag: 'App', fn: { tag: 'Const', name: 'rle' }, arg: R },
        arg: { tag: 'App', fn: { tag: 'Const', name: 'rzero' }, arg: R } },
      arg: { tag: 'App', fn: { tag: 'Const', name: 'rtwo' }, arg: R }
    };
    const goalType: import('../compiler/kernel').TTKTerm = {
      tag: 'Binder', binderKind: { tag: 'BPi' }, name: 'R',
      domain: { tag: 'Const', name: 'Real' },
      body: rleGoal,
    };

    // Build tree: intros [R] → apply leLtTransLe → [exact "1", hole, hole]
    const child1 = mkExact('1');
    const child2 = mkHole();
    const child3 = mkHole();
    const applyNode = mkApply('leLtTransLe', [child1, child2, child3]);
    const root = mkIntros(['R'], applyNode);

    const goalMap = replayEntireTree(root, goalType, defs, rev);

    const info2 = goalMap.get(child2.id);
    const info3 = goalMap.get(child3.id);

    expect(info2).toBeDefined();
    expect(info3).toBeDefined();

    // Goal 2 should NOT contain □ (metas should be resolved to 1)
    if (info2?.goalLatex) {
      expect(info2.goalLatex).not.toContain('\\square');
      expect(info2.goalLatex).toContain('1');
    }
    // Goal 3 should NOT contain □
    if (info3?.goalLatex) {
      expect(info3.goalLatex).not.toContain('\\square');
      expect(info3.goalLatex).toContain('1');
    }
  });

  test('exact zeroLtOne auto-applies R and closes goal 0<1', () => {
    const ctx = [
      { name: 'R', type: { tag: 'Const' as const, name: 'Real' } },
    ];
    const R: import('../compiler/kernel').TTKTerm = { tag: 'Var', index: 0 };
    const goalType: import('../compiler/kernel').TTKTerm = {
      tag: 'App', fn: { tag: 'App', fn: { tag: 'App', fn: { tag: 'Const', name: 'rlt' }, arg: R },
        arg: { tag: 'App', fn: { tag: 'Const', name: 'rzero' }, arg: R } },
      arg: { tag: 'App', fn: { tag: 'Const', name: 'rone' }, arg: R }
    };

    const engine = createInitialEngine(goalType, ctx, defs);
    const goal = engine.getFocusedGoal()!;
    const gId = engine.getFocusedGoalId()!;

    // Parse "zeroLtOne" — should auto-apply R
    const term = parseExactExpr('zeroLtOne', ctx, defs)!;
    expect(term).not.toBeNull();
    // Should be App(Const("zeroLtOne"), Var(0)) — with R applied
    expect(term.tag).toBe('App');

    const result = new ExactTactic(term).apply(engine, goal, gId);
    expect(result.success).toBe(true);
  });

  test('computeTermSlots produces correct Var indices for rlt slot type', async () => {
    const { computeTermSlots, kernelTermToSource } = await import('./term-builder');
    const { createInitialEngine } = await import('../tactics/tacticsEngine');
    const { shiftTerm } = await import('../compiler/subst');

    // Simulate: ctx = [R, f, x0, L, M, limF, ε, hε]
    // (simplified from the full limitsAdd context)
    const RType: import('../compiler/kernel').TTKTerm = { tag: 'Const', name: 'Real' };
    const CarrierR = (rIdx: number): import('../compiler/kernel').TTKTerm =>
      ({ tag: 'App', fn: { tag: 'Const', name: 'Carrier' }, arg: { tag: 'Var', index: rIdx } });
    const FnType = (rIdx: number): import('../compiler/kernel').TTKTerm =>
      ({ tag: 'Binder', binderKind: { tag: 'BPi' }, name: '_', domain: CarrierR(rIdx), body: CarrierR(rIdx + 1) });

    const ctx: import('../compiler/kernel').TTKContext = [
      { name: 'R', type: RType },
      { name: 'f', type: FnType(0) },
      { name: 'x0', type: CarrierR(1) },
      { name: 'L', type: CarrierR(2) },
      { name: 'M', type: CarrierR(3) },
    ];
    // limF : Limit(R, f, x0, L) — Var indices relative to ctx[0..4]
    // R=Var(4), f=Var(3), x0=Var(2), L=Var(1)
    const limFType: import('../compiler/kernel').TTKTerm = {
      tag: 'App', fn: { tag: 'App', fn: { tag: 'App', fn: {
        tag: 'App', fn: { tag: 'Const', name: 'Limit' },
        arg: { tag: 'Var', index: 4 } },
        arg: { tag: 'Var', index: 3 } },
        arg: { tag: 'Var', index: 2 } },
      arg: { tag: 'Var', index: 1 }
    };
    const fullCtx = [...ctx, { name: 'limF', type: limFType }];

    // Goal: some dummy type
    const goalType: import('../compiler/kernel').TTKTerm = { tag: 'Const', name: 'Type' };
    const goalMeta = { ctx: fullCtx, type: goalType, solution: undefined as any };

    // Prefill: limF at first explicit position (position 4, since 4 implicits)
    // limF is at ctx index 5, debruijn = 5 (from end of 6-entry ctx)
    const prefilled = new Map<number, import('../compiler/kernel').TTKTerm>();
    prefilled.set(4, { tag: 'Var', index: 0 }); // limF

    const engine = createInitialEngine(goalType, fullCtx, defs);
    const rev = buildReverseRegistry(createDefaultRegistry());

    const builder = computeTermSlots('Limit.eps_delta', prefilled, engine, goalMeta, defs, rev);
    expect(builder).not.toBeNull();

    // Find the rlt-typed slot (the last explicit slot, the hε arg)
    const rltSlot = builder!.slots.find(s => {
      let h = s.type;
      while (h.tag === 'App') h = h.fn;
      return h.tag === 'Const' && h.name === 'rlt';
    });
    expect(rltSlot).toBeDefined();

    // The rlt slot's type should reference R (the Real), not L or M
    // Convert to source and check it mentions R, not L
    const source = kernelTermToSource(rltSlot!.type, fullCtx, defs);
    expect(source).toContain('rzero');
    // Should NOT contain 'L' or 'M' as the Real parameter
    expect(source).not.toMatch(/\bL\b/);
    expect(source).not.toMatch(/\bM\b/);
    expect(source).not.toMatch(/\bf\b/);
  });

  test('unfold rlt preview renders rtwo as 2, not 1+1', () => {
    const ctx = [
      { name: 'R', type: { tag: 'Const' as const, name: 'Real' } },
      { name: 'ε', type: { tag: 'App' as const, fn: { tag: 'Const' as const, name: 'Carrier' }, arg: { tag: 'Var' as const, index: 0 } } },
    ];
    // Goal: rlt(R, rzero(R), rdiv(R, ε, rtwo(R))) — 0 < ε/2  (no Holes, manual construction)
    const goalType: import('../compiler/kernel').TTKTerm = {
      tag: 'App', fn: {
        tag: 'App', fn: {
          tag: 'App', fn: { tag: 'Const', name: 'rlt' },
          arg: { tag: 'Var', index: 1 }
        },
        arg: { tag: 'App', fn: { tag: 'App', fn: { tag: 'Const', name: 'rzero' }, arg: { tag: 'Var', index: 1 } }, arg: { tag: 'Var', index: 1 } }
      },
      arg: {
        tag: 'App', fn: {
          tag: 'App', fn: { tag: 'App', fn: { tag: 'Const', name: 'rdiv' }, arg: { tag: 'Var', index: 1 } },
          arg: { tag: 'Var', index: 0 }
        },
        arg: { tag: 'App', fn: { tag: 'App', fn: { tag: 'Const', name: 'rtwo' }, arg: { tag: 'Var', index: 1 } }, arg: { tag: 'Var', index: 1 } }
      }
    };

    const engine = createInitialEngine(goalType, ctx, defs);
    const goal = engine.getFocusedGoal()!;
    const gId = engine.getFocusedGoalId()!;

    const registry = createDefaultRegistry();
    const rev = buildReverseRegistry(registry);
    const kernelGoal: KernelGoalInfo = { engine, goal, definitions: defs, rev };
    const ig = renderInteractiveGoal(engine, goal, defs, rev);

    // Find the subterm path for rlt (outermost App head)
    const rltPath = [...ig!.subtermMap.entries()].find(([, v]) => v.headName === 'rlt')?.[0] ?? 'goal-t3';
    const suggestions = computeTacticSuggestions(rltPath, ig!, defs, kernelGoal);
    const unfoldSugg = suggestions.find(s => s.id === 'unfold-rlt');

    expect(unfoldSugg).toBeDefined();
    expect(unfoldSugg!.resultGoalLatex).toBeDefined();
    // The preview should contain "2" (from rtwo), not "1+1" or "{R⇒1+1}"
    expect(unfoldSugg!.resultGoalLatex).toContain('2');
    expect(unfoldSugg!.resultGoalLatex).not.toContain('1+1');
    expect(unfoldSugg!.resultGoalLatex).not.toContain('\\Rightarrow');
  });

  test('parseExactExpr resolves "1" to rone(R) when R in context', () => {
    const ctx = [{ name: 'R', type: { tag: 'Const' as const, name: 'Real' } }];
    const parsed = parseExactExpr('1', ctx, defs);
    expect(parsed).not.toBeNull();
    // Should be App(Const("rone"), Var(0)) — rone applied to R
    expect(parsed!.tag).toBe('App');
    const app = parsed as Extract<import('../compiler/kernel').TTKTerm, { tag: 'App' }>;
    expect(app.fn.tag).toBe('Const');
    expect((app.fn as any).name).toBe('rone');
    expect(app.arg.tag).toBe('Var');
    expect((app.arg as any).index).toBe(0);
  });

  test('parseExactExpr resolves "0" to rzero(R) and "2" to rtwo(R)', () => {
    const ctx = [{ name: 'R', type: { tag: 'Const' as const, name: 'Real' } }];
    const p0 = parseExactExpr('0', ctx, defs);
    const p2 = parseExactExpr('2', ctx, defs);
    expect((p0 as any)?.fn?.name).toBe('rzero');
    expect((p2 as any)?.fn?.name).toBe('rtwo');
  });

  test('exact 1 succeeds for goal Carrier R (E2E)', () => {
    const ctx = [{ name: 'R', type: { tag: 'Const' as const, name: 'Real' } }];
    // Goal: Carrier R
    const goalType: import('../compiler/kernel').TTKTerm = {
      tag: 'App', fn: { tag: 'Const', name: 'Carrier' }, arg: { tag: 'Var', index: 0 }
    };
    const engine = createInitialEngine(goalType, ctx, defs);
    const goal = engine.getFocusedGoal()!;
    const gId = engine.getFocusedGoalId()!;

    // Parse "1" — should resolve to rone(R)
    const term = parseExactExpr('1', ctx, defs);
    expect(term).not.toBeNull();

    // ExactTactic with the resolved term should succeed
    const r = new ExactTactic(term!).apply(engine, goal, gId);
    expect(r.success).toBe(true);
  });
});
