import { describe, test, expect, beforeAll } from 'vitest';
import { TTKTerm } from '../compiler/kernel';
import { createDefinitionsMap, addDefinition, MetaVar } from '../compiler/term';
import { mkConstTT } from '../compiler/surface';
import { collectRewriteCandidates, computeTacticSuggestions, KernelGoalInfo } from './tactic-suggestions';
import { compileTTFromText } from '../compiler/compile';
import { createInitialEngine } from '../tactics/tacticsEngine';
import { IntrosTactic, ApplyTactic } from '../tactics/tactic';
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
});
