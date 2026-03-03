import { describe, test, expect, beforeEach } from 'vitest';
import { mkPiTT, mkConstTT, mkAppTT, mkVarTT } from '../compiler/surface';
import { mkVar, mkConst, mkApp, mkPi, mkLambda, mkSort, mkULit } from '../compiler/kernel';
import { TTKTerm } from '../compiler/kernel';
import { createDefinitionsMap, addDefinition, addInductiveDefinition, DefinitionsMap } from '../compiler/term';
import { compileTTFromText } from '../compiler/compile';
import { SyntaxRegistry } from '../math-editor/syntax-registry';
import { resetIds } from '../math-editor/types';
import {
  resetProofIds,
  mkHole as mkTreeHole, mkIntros, mkInduction, mkCase, mkExact, mkUnfold,
  applyUnfold,
} from './proof-tree';
import {
  computeTypedContext,
  InductiveMap, InductiveInfo,
  extractTypeHead, peelConstructorParams, generateCaseInfos,
  kernelTypeToSurface,
  replaceVar,
  computeCaseGoalDirect,
} from './goal-computation';
import { TTerm } from '../compiler/surface';

beforeEach(() => {
  resetProofIds();
  resetIds();
});

const emptyRegistry: SyntaxRegistry = { symbolMap: new Map(), entries: [] };

// Helper: build surface types
const Nat = mkConstTT('Nat');
const NatToNat = mkPiTT(Nat, Nat, '_');

function mkTestType() {
  // (i : Nat) -> (f : Nat -> Nat) -> (n : Nat) -> Nat
  return mkPiTT(Nat, mkPiTT(NatToNat, mkPiTT(Nat, Nat, 'n'), 'f'), 'i');
}

// Nat inductive info for tests
const natInfo: InductiveInfo = {
  name: 'Nat',
  constructors: [
    { name: 'Zero', type: Nat },  // Zero : Nat
    { name: 'Succ', type: mkPiTT(Nat, Nat, 'n') },  // Succ : Nat -> Nat
  ],
};

const natInductiveMap: InductiveMap = new Map([['Nat', natInfo]]);

// ============================================================================
// Surface-only computeTypedContext tests (backwards compat — no kernel type)
// ============================================================================

describe('computeTypedContext (surface-only fallback)', () => {
  test('cursor on root hole shows full type as goal', () => {
    const hole = mkTreeHole();
    const type = mkTestType();
    const ctx = computeTypedContext(hole, hole.id, type, emptyRegistry);
    expect(ctx).not.toBeNull();
    expect(ctx!.hypotheses).toEqual([]);
    expect(ctx!.goal).toContain('Nat');
  });

  test('intros peel Pi binders — shows types for each name', () => {
    const child = mkTreeHole();
    const intros = mkIntros(['i', 'f', 'n'], child);
    const type = mkTestType();

    const ctx = computeTypedContext(intros, child.id, type, emptyRegistry);
    expect(ctx).not.toBeNull();
    expect(ctx!.hypotheses).toHaveLength(3);

    expect(ctx!.hypotheses[0].name).toBe('i');
    expect(ctx!.hypotheses[0].type).toBe('Nat');

    expect(ctx!.hypotheses[1].name).toBe('f');
    expect(ctx!.hypotheses[1].type).toContain('Nat');
    expect(ctx!.hypotheses[1].type).toContain('\\to');

    expect(ctx!.hypotheses[2].name).toBe('n');
    expect(ctx!.hypotheses[2].type).toBe('Nat');

    expect(ctx!.goal).toBe('Nat');
  });

  test('cursor on intros node itself has empty context', () => {
    const child = mkTreeHole();
    const intros = mkIntros(['n'], child);
    const type = mkPiTT(Nat, Nat, 'n');

    const ctx = computeTypedContext(intros, intros.id, type, emptyRegistry);
    expect(ctx!.hypotheses).toEqual([]);
  });

  test('intros with more names than Pi binders shows ? for extra', () => {
    const child = mkTreeHole();
    const intros = mkIntros(['n', 'm', 'extra'], child);
    const type = mkPiTT(Nat, Nat, 'n');

    const ctx = computeTypedContext(intros, child.id, type, emptyRegistry);
    expect(ctx!.hypotheses).toHaveLength(3);
    expect(ctx!.hypotheses[0].type).toBe('Nat');
    expect(ctx!.hypotheses[1].type).toBe('?');
    expect(ctx!.hypotheses[2].type).toBe('?');
  });

  test('returns null when cursor not found', () => {
    const hole = mkTreeHole();
    const type = Nat;
    expect(computeTypedContext(hole, 9999, type, emptyRegistry)).toBeNull();
  });

  test('cursor on case header shows case info and goal', () => {
    const c1 = mkCase('n = 0', mkTreeHole());
    const c2 = mkCase("n = k'", mkTreeHole());
    const ind = mkInduction('n', [c1, c2]);
    const intros = mkIntros(['n'], ind);
    const type = mkPiTT(Nat, Nat, 'n');

    const ctx = computeTypedContext(intros, c1.id, type, emptyRegistry);
    expect(ctx!.caseLabel).toBe('n = 0');
    expect(ctx!.inductionVar).toBe('n');
    expect(ctx!.hypotheses).toHaveLength(1);
    expect(ctx!.hypotheses[0].name).toBe('n');
    expect(ctx!.goal).toBe('Nat');
  });

  test('cursor in case body shows case info + goal', () => {
    const body1 = mkTreeHole();
    const body2 = mkTreeHole();
    const c1 = mkCase('n = 0', body1);
    const c2 = mkCase("n = k'", body2);
    const ind = mkInduction('n', [c1, c2]);
    const intros = mkIntros(['n'], ind);
    const type = mkPiTT(Nat, Nat, 'n');

    const ctx = computeTypedContext(intros, body2.id, type, emptyRegistry);
    expect(ctx!.caseLabel).toBe("n = k'");
    expect(ctx!.inductionVar).toBe('n');
    expect(ctx!.goal).toBe('Nat');
  });

  test('exact node shows expression as goal', () => {
    const exact = mkExact('refl');
    const type = Nat;
    const ctx = computeTypedContext(exact, exact.id, type, emptyRegistry);
    expect(ctx!.goal).toBe('refl');
  });

  test('full workflow: intros → induction → exact', () => {
    const exact = mkExact('refl');
    const hole = mkTreeHole();
    const c1 = mkCase('n = 0', exact);
    const c2 = mkCase("n = k'", hole);
    const ind = mkInduction('n', [c1, c2]);
    const intros = mkIntros(['i', 'f', 'n'], ind);
    const type = mkTestType();

    const ctx1 = computeTypedContext(intros, exact.id, type, emptyRegistry);
    expect(ctx1!.hypotheses).toHaveLength(3);
    expect(ctx1!.caseLabel).toBe('n = 0');
    expect(ctx1!.goal).toBe('refl');

    const ctx2 = computeTypedContext(intros, hole.id, type, emptyRegistry);
    expect(ctx2!.hypotheses).toHaveLength(3);
    expect(ctx2!.caseLabel).toBe("n = k'");
    expect(ctx2!.goal).toBe('Nat');
  });

  test('renders correct variable names in context', () => {
    const equalNM = mkAppTT(mkAppTT(mkConstTT('Equal'), mkVarTT(1)), mkVarTT(0));
    const type = mkPiTT(Nat, mkPiTT(Nat, mkPiTT(equalNM, Nat, 'h'), 'm'), 'n');

    const child = mkTreeHole();
    const intros = mkIntros(['n', 'm', 'h'], child);

    const ctx = computeTypedContext(intros, child.id, type, emptyRegistry);
    expect(ctx!.hypotheses[0].type).toBe('Nat');
    expect(ctx!.hypotheses[1].type).toBe('Nat');
    expect(ctx!.hypotheses[2].type).toContain('Equal');
    expect(ctx!.hypotheses[2].type).toContain('n');
    expect(ctx!.hypotheses[2].type).toContain('m');
  });

  test('syntax registry renders types with visual symbols', () => {
    const registry: SyntaxRegistry = {
      symbolMap: new Map([['\\mathbb{N}', { source: 'Nat', needsR: false }]]),
      entries: [],
    };

    const child = mkTreeHole();
    const intros = mkIntros(['n'], child);
    const type = mkPiTT(Nat, Nat, 'n');

    const ctx = computeTypedContext(intros, child.id, type, registry);
    expect(ctx!.hypotheses[0].type).toContain('\\mathbb{N}');
    expect(ctx!.goal).toContain('\\mathbb{N}');
  });
});

// ============================================================================
// Helper function tests
// ============================================================================

describe('extractTypeHead', () => {
  test('extracts head from Const', () => {
    expect(extractTypeHead(mkConstTT('Nat'))).toBe('Nat');
  });

  test('extracts head from App(Const, ...)', () => {
    expect(extractTypeHead(mkAppTT(mkConstTT('List'), mkConstTT('Nat')))).toBe('List');
  });

  test('returns null for Var', () => {
    expect(extractTypeHead(mkVarTT(0))).toBeNull();
  });
});

describe('peelConstructorParams', () => {
  test('zero-param constructor (Zero : Nat)', () => {
    const params = peelConstructorParams(Nat);
    expect(params).toEqual([]);
  });

  test('one-param constructor (Succ : Nat -> Nat)', () => {
    const succType = mkPiTT(Nat, Nat, 'n');
    const params = peelConstructorParams(succType);
    expect(params).toHaveLength(1);
    expect(params[0].name).toBe('n');
  });

  test('multi-param constructor (Cons : A -> List A -> List A)', () => {
    const ListA = mkAppTT(mkConstTT('List'), mkVarTT(0));
    const consType = mkPiTT(mkVarTT(0), mkPiTT(ListA, ListA, 'xs'), 'x');
    const params = peelConstructorParams(consType);
    expect(params).toHaveLength(2);
    expect(params[0].name).toBe('x');
    expect(params[1].name).toBe('xs');
  });
});

describe('generateCaseInfos', () => {
  test('generates case infos for Nat', () => {
    const cases = generateCaseInfos('n', natInfo);
    expect(cases).toHaveLength(2);

    expect(cases[0].label).toBe('n = Zero');
    expect(cases[0].constructorName).toBe('Zero');
    expect(cases[0].paramNames).toEqual([]);

    expect(cases[1].label).toBe('n = Succ n');
    expect(cases[1].constructorName).toBe('Succ');
    expect(cases[1].paramNames).toEqual(['n']);
  });
});

// ============================================================================
// kernelTypeToSurface tests
// ============================================================================

describe('kernelTypeToSurface', () => {
  test('converts Var', () => {
    const result = kernelTypeToSurface(mkVar(3));
    expect(result).toEqual(mkVarTT(3));
  });

  test('converts Const', () => {
    const result = kernelTypeToSurface(mkConst('Nat'));
    expect(result).toEqual(mkConstTT('Nat'));
  });

  test('converts simple App', () => {
    const kernel = mkApp(mkConst('Succ'), mkVar(0));
    const result = kernelTypeToSurface(kernel);
    expect(result.tag).toBe('App');
    if (result.tag === 'App') {
      expect(result.fn).toEqual(mkConstTT('Succ'));
      expect(result.arg).toEqual(mkVarTT(0));
    }
  });

  test('converts Pi', () => {
    const kernel = mkPi(mkConst('Nat'), mkConst('Nat'), 'n');
    const result = kernelTypeToSurface(kernel);
    expect(result.tag).toBe('Binder');
  });

  test('converts ULit', () => {
    const kernel: TTKTerm = { tag: 'ULit', n: 1 };
    const result = kernelTypeToSurface(kernel);
    expect(result.tag).toBe('ULit');
  });

  test('omits implicit args when definitions provided', () => {
    const namedArgMap = new Map([['A', 0]]);
    let defs = createDefinitionsMap();
    defs = addDefinition(defs, 'plus',
      mkPi(mkSort(mkULit(0)), mkPi(mkConst('Nat'), mkPi(mkConst('Nat'), mkConst('Nat')))),
      undefined, namedArgMap,
    );

    const kernel = mkApp(mkApp(mkApp(mkConst('plus'), mkSort(mkULit(0))), mkVar(1)), mkVar(0));
    const result = kernelTypeToSurface(kernel, defs);

    expect(result.tag).toBe('App');
    if (result.tag === 'App') {
      expect(result.arg).toEqual(mkVarTT(0));
      if (result.fn.tag === 'App') {
        expect(result.fn.arg).toEqual(mkVarTT(1));
        expect(result.fn.fn).toEqual(mkConstTT('plus'));
      }
    }
  });

  test('converts Sort', () => {
    const kernel = mkSort(mkULit(0));
    const result = kernelTypeToSurface(kernel);
    expect(result.tag).toBe('Sort');
  });
});

// ============================================================================
// Unfold proof tree operation tests
// ============================================================================

describe('applyUnfold (proof tree)', () => {
  test('applyUnfold creates unfold node with child hole', () => {
    const hole = mkTreeHole();
    const state = { root: hole, cursor: { nodeId: hole.id } };

    const result = applyUnfold(state, 'plus');
    expect(result).not.toBeNull();
    expect(result!.root.tag).toBe('unfold');
    if (result!.root.tag === 'unfold') {
      expect(result!.root.name).toBe('plus');
      expect(result!.root.child.tag).toBe('hole');
      expect(result!.cursor.nodeId).toBe(result!.root.child.id);
    }
  });

  test('applyUnfold on non-hole returns null', () => {
    const exact = mkExact('refl');
    const state = { root: exact, cursor: { nodeId: exact.id } };

    const result = applyUnfold(state, 'plus');
    expect(result).toBeNull();
  });
});

// ============================================================================
// computeTypedContext with TacticEngine (kernel types + definitions)
// ============================================================================

describe('computeTypedContext with TacticEngine', () => {
  function makeNatDefs(): DefinitionsMap {
    let defs = createDefinitionsMap();
    defs = addInductiveDefinition(defs, 'Nat', mkSort(mkULit(0)), [
      { name: 'Zero', type: mkConst('Nat') },
      { name: 'Succ', type: mkPi(mkConst('Nat'), mkConst('Nat'), 'n') },
    ], []);
    return defs;
  }

  test('intros peels Pi binders using real IntrosTactic', () => {
    const defs = makeNatDefs();
    const kernelType = mkPi(mkConst('Nat'), mkPi(mkConst('Nat'), mkConst('Nat'), 'm'), 'n');
    const surfaceType = mkPiTT(Nat, mkPiTT(Nat, Nat, 'm'), 'n');

    const child = mkTreeHole();
    const intros = mkIntros(['n', 'm'], child);

    const ctx = computeTypedContext(
      intros, child.id, surfaceType, emptyRegistry,
      undefined, kernelType, defs,
    );
    expect(ctx).not.toBeNull();
    expect(ctx!.hypotheses).toHaveLength(2);
    expect(ctx!.hypotheses[0].name).toBe('n');
    expect(ctx!.hypotheses[0].type).toBe('Nat');
    expect(ctx!.hypotheses[1].name).toBe('m');
    expect(ctx!.hypotheses[1].type).toBe('Nat');
    expect(ctx!.goal).toBe('Nat');
  });

  test('unfold after intros works (was broken with manual Pi peeling)', () => {
    let defs = makeNatDefs();

    // myNat = Nat (trivial alias)
    defs = addDefinition(defs, 'myNat', mkSort(mkULit(0)), mkConst('Nat'));

    // Type: (n : Nat) -> myNat
    const kernelType = mkPi(mkConst('Nat'), mkConst('myNat'), 'n');
    const surfaceType = mkPiTT(Nat, mkConstTT('myNat'), 'n');

    const childHole = mkTreeHole();
    const unfold = mkUnfold('myNat', childHole);
    const intros = mkIntros(['n'], unfold);

    const ctx = computeTypedContext(
      intros, childHole.id, surfaceType, emptyRegistry,
      undefined, kernelType, defs,
    );
    expect(ctx).not.toBeNull();
    expect(ctx!.hypotheses).toHaveLength(1);
    expect(ctx!.hypotheses[0].name).toBe('n');
    // After unfold, myNat should become Nat
    expect(ctx!.goal).toBe('Nat');
  });

  test('unfold with pattern matching (iota reduction)', () => {
    let defs = makeNatDefs();

    // plus : Nat -> Nat -> Nat
    // plus Zero m = m
    // plus (Succ n) m = Succ (plus n m)
    const plusBody: TTKTerm = {
      tag: 'Match',
      scrutinee: mkVar(1),
      clauses: [
        {
          patterns: [{ tag: 'PCtor', name: 'Zero', args: [] }],
          rhs: mkVar(0),
        },
        {
          patterns: [{ tag: 'PCtor', name: 'Succ', args: [{ tag: 'PVar', name: 'k' }] }],
          rhs: mkApp(mkConst('Succ'), mkApp(mkApp(mkConst('plus'), mkVar(0)), mkVar(1))),
        },
      ],
    };
    const plusVal = mkLambda(mkConst('Nat'),
      mkLambda(mkConst('Nat'), plusBody, 'm'),
      'n',
    );
    defs = addDefinition(defs, 'plus',
      mkPi(mkConst('Nat'), mkPi(mkConst('Nat'), mkConst('Nat'), 'm'), 'n'),
      plusVal,
    );

    // Goal: Equal (plus Zero m) m  (where m is Var(0) in context)
    // After unfold plus, plus(Zero, m) should reduce to m via iota
    const kernelGoal = mkApp(
      mkApp(mkConst('Equal'), mkApp(mkApp(mkConst('plus'), mkConst('Zero')), mkVar(0))),
      mkVar(0),
    );
    const surfaceGoal = mkAppTT(
      mkAppTT(mkConstTT('Equal'), mkAppTT(mkAppTT(mkConstTT('plus'), mkConstTT('Zero')), mkVarTT(0))),
      mkVarTT(0),
    );

    const childHole = mkTreeHole();
    const unfold = mkUnfold('plus', childHole);

    const ctx = computeTypedContext(
      unfold, childHole.id, surfaceGoal, emptyRegistry,
      undefined, kernelGoal, defs,
    );
    expect(ctx).not.toBeNull();
    // After unfolding, goal should not contain 'plus' (reduced away)
    expect(ctx!.goal).toContain('Equal');
    expect(ctx!.goal).not.toContain('plus');
  });

  test('unfold on cursor node itself shows pre-unfold goal', () => {
    let defs = makeNatDefs();
    defs = addDefinition(defs, 'myNat', mkSort(mkULit(0)), mkConst('Nat'));

    const childHole = mkTreeHole();
    const unfold = mkUnfold('myNat', childHole);

    const ctx = computeTypedContext(
      unfold, unfold.id, mkConstTT('myNat'), emptyRegistry,
      undefined, mkConst('myNat'), defs,
    );
    expect(ctx).not.toBeNull();
    expect(ctx!.goal).toBe('myNat');
  });

  test('unfold without definitions falls through unchanged', () => {
    const childHole = mkTreeHole();
    const unfold = mkUnfold('plus', childHole);
    const type = mkConstTT('Nat');

    // No kernel type — surface-only fallback
    const ctx = computeTypedContext(unfold, childHole.id, type, emptyRegistry);
    expect(ctx).not.toBeNull();
    expect(ctx!.goal).toBe('Nat');
  });

  test('multiple unfolds in sequence', () => {
    let defs = createDefinitionsMap();
    defs = addDefinition(defs, 'b', mkSort(mkULit(0)), mkConst('Nat'));
    defs = addDefinition(defs, 'a', mkSort(mkULit(0)), mkConst('b'));

    const childHole = mkTreeHole();
    const unfold2 = mkUnfold('b', childHole);
    const unfold1 = mkUnfold('a', unfold2);

    const ctx = computeTypedContext(
      unfold1, childHole.id, mkConstTT('a'), emptyRegistry,
      undefined, mkConst('a'), defs,
    );
    expect(ctx).not.toBeNull();
    expect(ctx!.goal).toBe('Nat');
  });

  test('induction with real tactic creates case-specific goals', () => {
    let defs = makeNatDefs();
    // Equal inductive type (simplified)
    defs = addInductiveDefinition(defs, 'Equal',
      mkPi(mkSort(mkULit(0)), mkPi(mkVar(0), mkPi(mkVar(1), mkSort(mkULit(0)), 'b'), 'a'), 'A'),
      [{ name: 'refl', type: mkApp(mkApp(mkApp(mkConst('Equal'), mkVar(2)), mkVar(0)), mkVar(0)) }],
      [],
    );

    // Goal: (n : Nat) -> Equal Nat (plus n Zero) n
    // Kernel: Pi(Nat, Equal(Nat, plus(Var(0), Zero), Var(0)))
    const goalBody = mkApp(mkApp(mkApp(mkConst('Equal'), mkConst('Nat')),
      mkApp(mkApp(mkConst('plus'), mkVar(0)), mkConst('Zero'))),
      mkVar(0));
    const kernelType = mkPi(mkConst('Nat'), goalBody, 'n');
    const surfaceType = mkPiTT(Nat, mkConstTT('_'), 'n'); // surface doesn't matter when kernel is provided

    const body1 = mkTreeHole();
    const body2 = mkTreeHole();
    const c1 = mkCase('n = Zero', body1, 'Zero', []);
    const c2 = mkCase('n = Succ k', body2, 'Succ', ['k']);
    const ind = mkInduction('n', [c1, c2]);
    const intros = mkIntros(['n'], ind);

    const ctx1 = computeTypedContext(
      intros, body1.id, surfaceType, emptyRegistry,
      natInductiveMap, kernelType, defs,
    );
    // The Zero case goal should be specific to n=Zero
    expect(ctx1).not.toBeNull();
    expect(ctx1!.caseLabel).toBe('n = Zero');
    expect(ctx1!.inductionVar).toBe('n');
    // Should have hypotheses from intro (n) — but in the Zero branch,
    // the tactic engine extends context differently
    expect(ctx1!.goal).toContain('Equal');

    const ctx2 = computeTypedContext(
      intros, body2.id, surfaceType, emptyRegistry,
      natInductiveMap, kernelType, defs,
    );
    expect(ctx2).not.toBeNull();
    expect(ctx2!.caseLabel).toBe('n = Succ k');
    expect(ctx2!.goal).toContain('Equal');
  });
});

// ============================================================================
// replaceVar unit tests
// ============================================================================

describe('replaceVar', () => {
  test('replaces matching Var', () => {
    const result = replaceVar(mkVar(1), 1, mkConst('Zero'));
    expect(result).toEqual(mkConst('Zero'));
  });

  test('does NOT replace non-matching Var', () => {
    const result = replaceVar(mkVar(0), 1, mkConst('Zero'));
    expect(result).toEqual(mkVar(0));
  });

  test('does NOT decrement other Var indices (unlike standard subst)', () => {
    // Var(2) should stay Var(2) when replacing Var(1)
    const result = replaceVar(mkVar(2), 1, mkConst('Zero'));
    expect(result).toEqual(mkVar(2));
  });

  test('replaces inside App', () => {
    // App(f, Var(1)) with Var(1) → Zero => App(f, Zero)
    const term = mkApp(mkConst('f'), mkVar(1));
    const result = replaceVar(term, 1, mkConst('Zero'));
    expect(result).toEqual(mkApp(mkConst('f'), mkConst('Zero')));
  });

  test('shifts target index under Binder', () => {
    // Pi(Nat, Var(2)) — under binder, original Var(1) is now Var(2)
    const term = mkPi(mkConst('Nat'), mkVar(2), 'x');
    const result = replaceVar(term, 1, mkConst('Zero'));
    expect(result.tag).toBe('Binder');
    if (result.tag === 'Binder') {
      expect(result.body).toEqual(mkConst('Zero'));
    }
  });

  test('does NOT replace bound variable that happens to match shifted index', () => {
    // Pi(Nat, Var(0)) — Var(0) in body is bound by the Pi, not our target
    // If target is 1, under binder target becomes 2, Var(0) stays untouched
    const term = mkPi(mkConst('Nat'), mkVar(0), 'x');
    const result = replaceVar(term, 1, mkConst('Zero'));
    expect(result).toEqual(term); // Unchanged — Var(0) doesn't match target 2
  });

  test('shifts replacement under Binder', () => {
    // Pi(Nat, Var(2)) replacing Var(1) with Var(0)
    // Under binder: target→2, replacement Var(0)→Var(1)
    const term = mkPi(mkConst('Nat'), mkVar(2), 'x');
    const result = replaceVar(term, 1, mkVar(0));
    expect(result.tag).toBe('Binder');
    if (result.tag === 'Binder') {
      // Replacement Var(0) shifted to Var(1) under binder
      expect(result.body).toEqual(mkVar(1));
    }
  });

  test('preserves Const and other leaf terms', () => {
    expect(replaceVar(mkConst('Nat'), 0, mkConst('Zero'))).toEqual(mkConst('Nat'));
    const sort = mkSort(mkULit(0));
    expect(replaceVar(sort, 0, mkConst('Zero'))).toEqual(sort);
  });
});

// ============================================================================
// computeCaseGoalDirect unit tests
// ============================================================================

describe('computeCaseGoalDirect', () => {
  function makeNatDefs(): DefinitionsMap {
    let defs = createDefinitionsMap();
    defs = addInductiveDefinition(defs, 'Nat', mkSort(mkULit(0)), [
      { name: 'Zero', type: mkConst('Nat') },
      { name: 'Succ', type: mkPi(mkConst('Nat'), mkConst('Nat'), 'n') },
    ], []);
    return defs;
  }

  test('Zero case with scrutinee at index 0 — simplest case', () => {
    const defs = makeNatDefs();

    // Context: [n : Nat], goal: Equal(Nat, n, n) where n = Var(0)
    const goal = {
      ctx: [{ name: 'n', type: mkConst('Nat') as TTKTerm }],
      type: mkApp(mkApp(mkApp(mkConst('Equal'), mkConst('Nat')), mkVar(0)), mkVar(0)),
      solution: undefined,
    };

    const zeroCtor = { name: 'Zero', type: mkConst('Nat') as TTKTerm };
    const result = computeCaseGoalDirect(goal, 0, zeroCtor, 'Nat', defs);

    // Goal should be Equal(Nat, Zero, Zero) — n replaced by Zero
    expect(result.type).toEqual(
      mkApp(mkApp(mkApp(mkConst('Equal'), mkConst('Nat')), mkConst('Zero')), mkConst('Zero'))
    );
    // Context should still have n : Nat (no new entries for Zero)
    expect(result.ctx).toHaveLength(1);
    expect(result.caseTag).toBe('Zero');
  });

  test('Zero case with scrutinee at index 1 — THE BUG CASE', () => {
    const defs = makeNatDefs();

    // Context: [i : Nat, n : Nat, f : Nat → Nat]
    // In TTKContext order: [{i}, {n}, {f}]
    // De Bruijn: f=Var(0), n=Var(1), i=Var(2)
    // Goal: Equal(Nat, App(f, n), App(f, i))
    //     = Equal(Nat, App(Var(0), Var(1)), App(Var(0), Var(2)))
    const goal = {
      ctx: [
        { name: 'i', type: mkConst('Nat') as TTKTerm },
        { name: 'n', type: mkConst('Nat') as TTKTerm },
        { name: 'f', type: mkPi(mkConst('Nat'), mkConst('Nat')) as TTKTerm },
      ],
      type: mkApp(
        mkApp(mkApp(mkConst('Equal'), mkConst('Nat')),
          mkApp(mkVar(0), mkVar(1))),  // f(n)
        mkApp(mkVar(0), mkVar(2)),     // f(i)
      ),
      solution: undefined,
    };

    // Scrutinee is n at index 1
    const zeroCtor = { name: 'Zero', type: mkConst('Nat') as TTKTerm };
    const result = computeCaseGoalDirect(goal, 1, zeroCtor, 'Nat', defs);

    // Goal should be Equal(Nat, f(Zero), f(i)) — n replaced by Zero, f and i untouched
    expect(result.type).toEqual(
      mkApp(
        mkApp(mkApp(mkConst('Equal'), mkConst('Nat')),
          mkApp(mkVar(0), mkConst('Zero'))),  // f(Zero)
        mkApp(mkVar(0), mkVar(2)),             // f(i)
      )
    );
    // Context unchanged (Zero has no params)
    expect(result.ctx).toHaveLength(3);
  });

  test('Succ case with scrutinee at index 1 — adds param and IH', () => {
    const defs = makeNatDefs();

    // Context: [i : Nat, n : Nat, f : Nat → Nat]
    // Goal: Equal(Nat, App(f, n), i) = Equal(Nat, App(Var(0), Var(1)), Var(2))
    const goal = {
      ctx: [
        { name: 'i', type: mkConst('Nat') as TTKTerm },
        { name: 'n', type: mkConst('Nat') as TTKTerm },
        { name: 'f', type: mkPi(mkConst('Nat'), mkConst('Nat')) as TTKTerm },
      ],
      type: mkApp(
        mkApp(mkApp(mkConst('Equal'), mkConst('Nat')),
          mkApp(mkVar(0), mkVar(1))),  // f(n)
        mkVar(2),                       // i
      ),
      solution: undefined,
    };

    const succCtor = { name: 'Succ', type: mkPi(mkConst('Nat'), mkConst('Nat'), 'n') as TTKTerm };
    const result = computeCaseGoalDirect(goal, 1, succCtor, 'Nat', defs);

    // Context should add n' (Succ param) and IH
    // Original: [i, n, f]  + [n', IH] = 5 entries
    expect(result.ctx).toHaveLength(5);
    expect(result.ctx[3].name).toBe('n');  // Succ's param name from ctor type
    expect(result.ctx[4].name).toBe('IH');

    // Goal should be Equal(Nat, f(Succ(n')), i)
    // After extending context by 2 (n', IH):
    //   f was Var(0) → Var(2), n was Var(1) → replaced by Succ(Var(1)),
    //   i was Var(2) → Var(4)
    // Succ(n'): n' is at index 1 (shifted by ihOffset=1), so Succ(Var(1))
    // But wait — constructor app has params.length=1, ihOffset=1
    // ctorApp = App(Const("Succ"), Var((1-1-0)+1)) = App(Const("Succ"), Var(1))
    // So goal = Equal(Nat, App(Var(2), App(Const("Succ"), Var(1))), Var(4))
    expect(result.type).toEqual(
      mkApp(
        mkApp(mkApp(mkConst('Equal'), mkConst('Nat')),
          mkApp(mkVar(2), mkApp(mkConst('Succ'), mkVar(1)))),  // f(Succ(n'))
        mkVar(4),                                                 // i
      )
    );

    // IH type should be: Equal(Nat, f(n'), i) — the goal with n replaced by n'
    // n' is at the right index from IH's perspective
    expect(result.ctx[4].type).toEqual(
      mkApp(
        mkApp(mkApp(mkConst('Equal'), mkConst('Nat')),
          mkApp(mkVar(2), mkVar(1))),  // f(n')
        mkVar(4),                       // i
      )
    );

    expect(result.caseTag).toBe('Succ');
  });

  test('Zero case with scrutinee at index 2 — deeply nested', () => {
    const defs = makeNatDefs();

    // Context: [n : Nat, a : Nat, b : Nat]
    // De Bruijn: b=Var(0), a=Var(1), n=Var(2)
    // Goal: Equal(Nat, n, a)
    const goal = {
      ctx: [
        { name: 'n', type: mkConst('Nat') as TTKTerm },
        { name: 'a', type: mkConst('Nat') as TTKTerm },
        { name: 'b', type: mkConst('Nat') as TTKTerm },
      ],
      type: mkApp(mkApp(mkApp(mkConst('Equal'), mkConst('Nat')), mkVar(2)), mkVar(1)),
      solution: undefined,
    };

    const zeroCtor = { name: 'Zero', type: mkConst('Nat') as TTKTerm };
    const result = computeCaseGoalDirect(goal, 2, zeroCtor, 'Nat', defs);

    // n (Var(2)) → Zero, a (Var(1)) and b (Var(0)) untouched
    expect(result.type).toEqual(
      mkApp(mkApp(mkApp(mkConst('Equal'), mkConst('Nat')), mkConst('Zero')), mkVar(1))
    );
  });
});

// ============================================================================
// Full pipeline: intros → induction with scrutinee NOT at index 0
// ============================================================================

describe('induction goal computation with scrutinee at various indices', () => {
  function makeNatDefs(): DefinitionsMap {
    let defs = createDefinitionsMap();
    defs = addInductiveDefinition(defs, 'Nat', mkSort(mkULit(0)), [
      { name: 'Zero', type: mkConst('Nat') },
      { name: 'Succ', type: mkPi(mkConst('Nat'), mkConst('Nat'), 'n') },
    ], []);
    return defs;
  }

  test('intros [i, n, f] then induction on n — Zero case substitutes correctly', () => {
    const defs = makeNatDefs();

    // Type: (i : Nat) → (n : Nat) → (f : Nat → Nat) → Equal Nat (f n) (f i)
    // Kernel: Pi(Nat, Pi(Nat, Pi(Pi(Nat,Nat), Equal(Nat, App(Var(0), Var(1)), App(Var(0), Var(2))))))
    const goalBody = mkApp(
      mkApp(mkApp(mkConst('Equal'), mkConst('Nat')),
        mkApp(mkVar(0), mkVar(1))),  // f(n)
      mkApp(mkVar(0), mkVar(2)),     // f(i)
    );
    const kernelType = mkPi(mkConst('Nat'),
      mkPi(mkConst('Nat'),
        mkPi(mkPi(mkConst('Nat'), mkConst('Nat')),
          goalBody, 'f'),
        'n'),
      'i');
    const surfaceType = mkPiTT(Nat, mkPiTT(Nat, mkPiTT(NatToNat, Nat, 'f'), 'n'), 'i');

    const zeroBody = mkTreeHole();
    const succBody = mkTreeHole();
    const c1 = mkCase('n = 0', zeroBody, 'Zero', []);
    const c2 = mkCase('n = Succ k', succBody, 'Succ', ['k']);
    const ind = mkInduction('n', [c1, c2]);
    const intros = mkIntros(['i', 'n', 'f'], ind);

    // Test Zero case
    const ctx1 = computeTypedContext(
      intros, zeroBody.id, surfaceType, emptyRegistry,
      natInductiveMap, kernelType, defs,
    );
    expect(ctx1).not.toBeNull();
    expect(ctx1!.caseLabel).toBe('n = 0');

    // The goal should contain Zero — n was replaced by Zero
    // It should NOT still contain a bare variable reference where n was
    expect(ctx1!.goal).toContain('Equal');
    // Check that 0 (rendered from Zero) appears in the goal
    expect(ctx1!.goal).toMatch(/0|Zero/);
    // Verify no rendering artifacts (boxes, etc.)
    expect(ctx1!.goal).not.toContain('\\mapsto');
    expect(ctx1!.goal).not.toContain('□');

    // Hypotheses should include i, n, f (from intros)
    expect(ctx1!.hypotheses.length).toBeGreaterThanOrEqual(3);
    expect(ctx1!.hypotheses[0].name).toBe('i');
    expect(ctx1!.hypotheses[1].name).toBe('n');
    expect(ctx1!.hypotheses[2].name).toBe('f');
  });

  test('intros [i, n, f] then induction on n — Succ case has IH and constructor', () => {
    const defs = makeNatDefs();

    const goalBody = mkApp(
      mkApp(mkApp(mkConst('Equal'), mkConst('Nat')),
        mkApp(mkVar(0), mkVar(1))),
      mkApp(mkVar(0), mkVar(2)),
    );
    const kernelType = mkPi(mkConst('Nat'),
      mkPi(mkConst('Nat'),
        mkPi(mkPi(mkConst('Nat'), mkConst('Nat')),
          goalBody, 'f'),
        'n'),
      'i');
    const surfaceType = mkPiTT(Nat, mkPiTT(Nat, mkPiTT(NatToNat, Nat, 'f'), 'n'), 'i');

    const zeroBody = mkTreeHole();
    const succBody = mkTreeHole();
    const c1 = mkCase('n = 0', zeroBody, 'Zero', []);
    const c2 = mkCase('n = Succ k', succBody, 'Succ', ['k']);
    const ind = mkInduction('n', [c1, c2]);
    const intros = mkIntros(['i', 'n', 'f'], ind);

    const ctx2 = computeTypedContext(
      intros, succBody.id, surfaceType, emptyRegistry,
      natInductiveMap, kernelType, defs,
    );
    expect(ctx2).not.toBeNull();
    expect(ctx2!.caseLabel).toBe('n = Succ k');
    expect(ctx2!.goal).toContain('Equal');
    expect(ctx2!.goal).toContain('Succ');
    // No rendering artifacts
    expect(ctx2!.goal).not.toContain('\\mapsto');
    expect(ctx2!.goal).not.toContain('□');

    // Should have i, n, f from intros + n (Succ param) + IH
    expect(ctx2!.hypotheses.length).toBeGreaterThanOrEqual(5);
    const ihHyp = ctx2!.hypotheses.find(h => h.name === 'IH');
    expect(ihHyp).toBeDefined();
    expect(ihHyp!.type).toContain('Equal');
  });

  test('intros [n] then induction on n — scrutinee at index 0 works too', () => {
    const defs = makeNatDefs();

    // Type: (n : Nat) → Equal Nat n n
    const goalBody = mkApp(mkApp(mkApp(mkConst('Equal'), mkConst('Nat')), mkVar(0)), mkVar(0));
    const kernelType = mkPi(mkConst('Nat'), goalBody, 'n');
    const surfaceType = mkPiTT(Nat, Nat, 'n');

    const zeroBody = mkTreeHole();
    const succBody = mkTreeHole();
    const c1 = mkCase('n = 0', zeroBody, 'Zero', []);
    const c2 = mkCase('n = Succ k', succBody, 'Succ', ['k']);
    const ind = mkInduction('n', [c1, c2]);
    const intros = mkIntros(['n'], ind);

    const ctx1 = computeTypedContext(
      intros, zeroBody.id, surfaceType, emptyRegistry,
      natInductiveMap, kernelType, defs,
    );
    expect(ctx1).not.toBeNull();
    // Zero case goal should have Zero substituted for n
    expect(ctx1!.goal).toContain('Equal');
    expect(ctx1!.goal).toMatch(/0|Zero/);

    // Succ case
    const ctx2 = computeTypedContext(
      intros, succBody.id, surfaceType, emptyRegistry,
      natInductiveMap, kernelType, defs,
    );
    expect(ctx2).not.toBeNull();
    expect(ctx2!.goal).toContain('Equal');
    expect(ctx2!.goal).toContain('Succ');
    // Should have IH in hypotheses
    const ihHyp = ctx2!.hypotheses.find(h => h.name === 'IH');
    expect(ihHyp).toBeDefined();
  });
});

// ============================================================================
// Real preset: summationSplit — the actual bug scenario
// ============================================================================

describe('summationSplit preset: intros [i, n, f] then induction on n', () => {
  // Compile the actual nat-math preset to get real kernel types and definitions
  function compilePreset() {
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Equal : {A : Type} -> A -> A -> Type where
  refl : {A : Type} -> {a : A} -> Equal a a

plus : Nat -> Nat -> Nat
plus Zero m = m
plus (Succ n) m = Succ (plus n m)

minus : Nat -> Nat -> Nat
minus a Zero = a
minus Zero _ = Zero
minus (Succ a) (Succ b) = minus a b

sumStartCount : (start count : Nat) -> (Nat -> Nat) -> Nat
sumStartCount start Zero f = Zero
sumStartCount start (Succ k) f = plus (sumStartCount start k f) (f (plus start (Succ k)))

sum : (start end : Nat) -> (Nat -> Nat) -> Nat
sum start end f = sumStartCount start (Succ (minus end start)) f

summationSplit : (i n : Nat) -> (f : Nat -> Nat) -> Equal (sum i (Succ n) (\\k => (f (k)))) (plus (sum i n (\\k => (f (k)))) (f (plus i (Succ n))))
summationSplit = ?TODO
`;
    return compileTTFromText(source);
  }

  test('compiles successfully', () => {
    const result = compilePreset();
    // summationSplit is a postulate (?TODO), so the block should parse and name-resolve fine
    expect(result.blocks.length).toBeGreaterThan(0);
    // Find the summationSplit declaration
    const sumSplitDecl = result.blocks.flatMap(b => b.declarations).find(d => d.name === 'summationSplit');
    expect(sumSplitDecl).toBeDefined();
    expect(sumSplitDecl!.kernelType).toBeDefined();
  });

  test('Zero case goal does not contain lambdas or boxes', () => {
    const result = compilePreset();
    const sumSplitDecl = result.blocks.flatMap(b => b.declarations).find(d => d.name === 'summationSplit');
    const kernelType = sumSplitDecl!.kernelType!;
    const definitions = result.definitions;

    // Build proof tree: intros [i, n, f] then induction on n
    const zeroBody = mkTreeHole();
    const succBody = mkTreeHole();
    const c1 = mkCase('n = 0', zeroBody, 'Zero', []);
    const c2 = mkCase('n = Succ k', succBody, 'Succ', ['k']);
    const ind = mkInduction('n', [c1, c2]);
    const intros = mkIntros(['i', 'n', 'f'], ind);

    const surfaceType = mkConstTT('_'); // doesn't matter when kernel type is provided

    const ctx = computeTypedContext(
      intros, zeroBody.id, surfaceType, emptyRegistry,
      undefined, kernelType, definitions,
    );
    expect(ctx).not.toBeNull();

    // Goal should still reference sum, plus, Equal — not their unfolded definitions
    expect(ctx!.goal).toContain('Equal');
    expect(ctx!.goal).toContain('sum');
    expect(ctx!.goal).toContain('plus');

    // Goal should NOT contain internal helpers that appear after over-normalization
    expect(ctx!.goal).not.toContain('sumStartCount');
    expect(ctx!.goal).not.toContain('minus');
    // No grey boxes (unknown/unsupported terms)
    expect(ctx!.goal).not.toContain('\\square');

    // Should contain Zero (rendered from Const("Zero"))
    expect(ctx!.goal).toContain('Zero');
  });

  test('Succ case goal contains Succ substitution and IH', () => {
    const result = compilePreset();
    const sumSplitDecl = result.blocks.flatMap(b => b.declarations).find(d => d.name === 'summationSplit');
    const kernelType = sumSplitDecl!.kernelType!;
    const definitions = result.definitions;

    const zeroBody = mkTreeHole();
    const succBody = mkTreeHole();
    const c1 = mkCase('n = 0', zeroBody, 'Zero', []);
    const c2 = mkCase('n = Succ k', succBody, 'Succ', ['k']);
    const ind = mkInduction('n', [c1, c2]);
    const intros = mkIntros(['i', 'n', 'f'], ind);

    const surfaceType = mkConstTT('_');

    const ctx = computeTypedContext(
      intros, succBody.id, surfaceType, emptyRegistry,
      undefined, kernelType, definitions,
    );
    expect(ctx).not.toBeNull();

    // No over-normalization artifacts
    expect(ctx!.goal).not.toContain('sumStartCount');
    expect(ctx!.goal).not.toContain('\\square');

    // Should contain Succ (the constructor substituted for n) and proper names
    expect(ctx!.goal).toContain('Succ');
    expect(ctx!.goal).toContain('Equal');
    expect(ctx!.goal).toContain('sum');

    // Should have IH hypothesis
    const ihHyp = ctx!.hypotheses.find(h => h.name === 'IH');
    expect(ihHyp).toBeDefined();
  });

  test('intros → induction → unfold: does not over-reduce', () => {
    const result = compilePreset();
    const sumSplitDecl = result.blocks.flatMap(b => b.declarations).find(d => d.name === 'summationSplit');
    const kernelType = sumSplitDecl!.kernelType!;
    const definitions = result.definitions;

    // Build proof tree: intros [i, n, f] → induction n → Zero case → unfold sum
    const unfoldChild = mkTreeHole();
    const unfoldNode = mkUnfold('sum', unfoldChild);
    const succBody = mkTreeHole();
    const c1 = mkCase('n = 0', unfoldNode, 'Zero', []);
    const c2 = mkCase('n = Succ k', succBody, 'Succ', ['k']);
    const ind = mkInduction('n', [c1, c2]);
    const intros = mkIntros(['i', 'n', 'f'], ind);

    const surfaceType = mkConstTT('_');

    const ctx = computeTypedContext(
      intros, unfoldChild.id, surfaceType, emptyRegistry,
      undefined, kernelType, definitions,
    );
    expect(ctx).not.toBeNull();

    // After unfold sum, sum should be replaced but NOT over-reduced
    // Should NOT have grey boxes (internal helpers rendered as unknown)
    expect(ctx!.goal).not.toContain('\\square');
    // sum was unfolded — it should be replaced by its body (sumStartCount)
    // but sumStartCount itself should NOT be further unfolded
    expect(ctx!.goal).not.toContain('sum(');  // sum should be gone (unfolded)
    // But no additional lambdas from definition unfolding
    expect(ctx!.goal).toContain('Equal');
  });

  test('intros → induction → unfold sum → unfold minus: no grey boxes', () => {
    const result = compilePreset();
    const sumSplitDecl = result.blocks.flatMap(b => b.declarations).find(d => d.name === 'summationSplit');
    const kernelType = sumSplitDecl!.kernelType!;
    const definitions = result.definitions;

    // Build proof tree: intros [i, n, f] → induction n → Zero case → unfold sum → unfold minus
    const minusChild = mkTreeHole();
    const unfoldMinus = mkUnfold('minus', minusChild);
    const unfoldSum = mkUnfold('sum', unfoldMinus);
    const succBody = mkTreeHole();
    const c1 = mkCase('n = 0', unfoldSum, 'Zero', []);
    const c2 = mkCase('n = Succ k', succBody, 'Succ', ['k']);
    const ind = mkInduction('n', [c1, c2]);
    const intros = mkIntros(['i', 'n', 'f'], ind);

    const surfaceType = mkConstTT('_');

    const ctx = computeTypedContext(
      intros, minusChild.id, surfaceType, emptyRegistry,
      undefined, kernelType, definitions,
    );
    expect(ctx).not.toBeNull();
    expect(ctx!.goal).not.toContain('\\square');
    expect(ctx!.goal).toContain('Equal');
  });
});
