import { describe, test, expect, beforeEach } from 'vitest';
import { mkPiTT, mkConstTT, mkAppTT, mkVarTT } from '../compiler/surface';
import { SyntaxRegistry } from '../math-editor/syntax-registry';
import { resetIds } from '../math-editor/types';
import {
  resetProofIds,
  mkHole as mkTreeHole, mkIntros, mkInduction, mkCase, mkExact,
} from './proof-tree';
import {
  computeTypedContext,
  InductiveMap, InductiveInfo,
  extractTypeHead, peelConstructorParams, generateCaseInfos,
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

describe('computeTypedContext', () => {
  test('cursor on root hole shows full type as goal', () => {
    const hole = mkTreeHole();
    const type = mkTestType();
    const ctx = computeTypedContext(hole, hole.id, type, emptyRegistry);
    expect(ctx).not.toBeNull();
    expect(ctx!.hypotheses).toEqual([]);
    // Goal should contain Nat rendered via structured math pipeline
    expect(ctx!.goal).toContain('Nat');
  });

  test('intros peel Pi binders — shows types for each name', () => {
    const child = mkTreeHole();
    const intros = mkIntros(['i', 'f', 'n'], child);
    const type = mkTestType();

    const ctx = computeTypedContext(intros, child.id, type, emptyRegistry);
    expect(ctx).not.toBeNull();
    expect(ctx!.hypotheses).toHaveLength(3);

    // i : Nat
    expect(ctx!.hypotheses[0].name).toBe('i');
    expect(ctx!.hypotheses[0].type).toBe('Nat');

    // f : Nat -> Nat (arrow rendered by structured math pipeline)
    expect(ctx!.hypotheses[1].name).toBe('f');
    expect(ctx!.hypotheses[1].type).toContain('Nat');
    expect(ctx!.hypotheses[1].type).toContain('\\to');

    // n : Nat
    expect(ctx!.hypotheses[2].name).toBe('n');
    expect(ctx!.hypotheses[2].type).toBe('Nat');

    // Goal should be remaining type (Nat)
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
    // Type only has one Pi binder
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

    // Check exact in first case
    const ctx1 = computeTypedContext(intros, exact.id, type, emptyRegistry);
    expect(ctx1!.hypotheses).toHaveLength(3);
    expect(ctx1!.caseLabel).toBe('n = 0');
    expect(ctx1!.goal).toBe('refl');

    // Check hole in second case
    const ctx2 = computeTypedContext(intros, hole.id, type, emptyRegistry);
    expect(ctx2!.hypotheses).toHaveLength(3);
    expect(ctx2!.caseLabel).toBe("n = k'");
    expect(ctx2!.goal).toBe('Nat');
  });

  test('renders correct variable names in context', () => {
    // (n : Nat) -> (m : Nat) -> Equal n m -> Nat
    const equalNM = mkAppTT(mkAppTT(mkConstTT('Equal'), mkVarTT(1)), mkVarTT(0));
    const type = mkPiTT(Nat, mkPiTT(Nat, mkPiTT(equalNM, Nat, 'h'), 'm'), 'n');

    const child = mkTreeHole();
    const intros = mkIntros(['n', 'm', 'h'], child);

    const ctx = computeTypedContext(intros, child.id, type, emptyRegistry);
    expect(ctx!.hypotheses[0].type).toBe('Nat');
    expect(ctx!.hypotheses[1].type).toBe('Nat');
    // h's type should reference n and m by name
    expect(ctx!.hypotheses[2].type).toContain('Equal');
    expect(ctx!.hypotheses[2].type).toContain('n');
    expect(ctx!.hypotheses[2].type).toContain('m');
  });

  test('syntax registry renders types with visual symbols', () => {
    // Registry that maps "Nat" → "ℕ"
    const registry: SyntaxRegistry = {
      symbolMap: new Map([['\\mathbb{N}', { source: 'Nat', needsR: false }]]),
      entries: [],
    };

    const child = mkTreeHole();
    const intros = mkIntros(['n'], child);
    const type = mkPiTT(Nat, Nat, 'n');

    const ctx = computeTypedContext(intros, child.id, type, registry);
    // With the registry, Nat should render as ℕ
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
// Case-specific goal substitution tests
// ============================================================================

describe('case-specific goal substitution', () => {
  test('Zero case substitutes scrutinee with Zero in dependent goal', () => {
    // Type: (n : Nat) -> Equal (plus n Zero) n
    // Goal after intros n: Equal (plus n Zero) n
    // In case n = Zero: goal should become Equal (plus Zero Zero) Zero
    const plusNZero = mkAppTT(mkAppTT(mkConstTT('plus'), mkVarTT(0)), mkConstTT('Zero'));
    const goalType = mkAppTT(mkAppTT(mkConstTT('Equal'), plusNZero), mkVarTT(0));
    const fullType = mkPiTT(Nat, goalType, 'n');

    const body1 = mkTreeHole();
    const body2 = mkTreeHole();
    const c1 = mkCase('n = Zero', body1, 'Zero', []);
    const c2 = mkCase('n = Succ k', body2, 'Succ', ['k']);
    const ind = mkInduction('n', [c1, c2]);
    const intros = mkIntros(['n'], ind);

    const ctx = computeTypedContext(intros, body1.id, fullType, emptyRegistry, natInductiveMap);
    expect(ctx).not.toBeNull();
    // Goal should contain Zero substituted for n
    expect(ctx!.goal).toContain('Zero');
    expect(ctx!.goal).toContain('plus');
    // Should NOT contain bare 'n' as a variable reference (it's been substituted)
    expect(ctx!.hypotheses).toHaveLength(1); // just the intro'd n
  });

  test('Succ case adds k hypothesis and ih with correct type', () => {
    // Type: (n : Nat) -> Equal (plus n Zero) n
    const plusNZero = mkAppTT(mkAppTT(mkConstTT('plus'), mkVarTT(0)), mkConstTT('Zero'));
    const goalType = mkAppTT(mkAppTT(mkConstTT('Equal'), plusNZero), mkVarTT(0));
    const fullType = mkPiTT(Nat, goalType, 'n');

    const body1 = mkTreeHole();
    const body2 = mkTreeHole();
    const c1 = mkCase('n = Zero', body1, 'Zero', []);
    const c2 = mkCase('n = Succ k', body2, 'Succ', ['k']);
    const ind = mkInduction('n', [c1, c2]);
    const intros = mkIntros(['n'], ind);

    const ctx = computeTypedContext(intros, body2.id, fullType, emptyRegistry, natInductiveMap);
    expect(ctx).not.toBeNull();
    // Should have: n (intro'd), k (constructor param), ih (induction hypothesis)
    expect(ctx!.hypotheses.length).toBeGreaterThanOrEqual(3);
    expect(ctx!.hypotheses[0].name).toBe('n');

    // k should be Nat
    const kHyp = ctx!.hypotheses.find(h => h.name === 'k');
    expect(kHyp).toBeDefined();
    expect(kHyp!.type).toContain('Nat');

    // ih should exist
    const ihHyp = ctx!.hypotheses.find(h => h.name === 'ih');
    expect(ihHyp).toBeDefined();
    // ih type should reference plus and Equal (it's the induction hypothesis)
    expect(ihHyp!.type).toContain('Equal');
    expect(ihHyp!.type).toContain('plus');
  });

  test('non-dependent goal works for both cases (scrutinee not in goal)', () => {
    // Type: (n : Nat) -> Nat  (n doesn't appear in result type)
    const fullType = mkPiTT(Nat, Nat, 'n');

    const body1 = mkTreeHole();
    const body2 = mkTreeHole();
    const c1 = mkCase('n = Zero', body1, 'Zero', []);
    const c2 = mkCase('n = Succ k', body2, 'Succ', ['k']);
    const ind = mkInduction('n', [c1, c2]);
    const intros = mkIntros(['n'], ind);

    const ctx1 = computeTypedContext(intros, body1.id, fullType, emptyRegistry, natInductiveMap);
    expect(ctx1!.goal).toBe('Nat');

    const ctx2 = computeTypedContext(intros, body2.id, fullType, emptyRegistry, natInductiveMap);
    expect(ctx2!.goal).toBe('Nat');
  });

  test('without inductiveMap, falls back to same goal for all cases', () => {
    const plusNZero = mkAppTT(mkAppTT(mkConstTT('plus'), mkVarTT(0)), mkConstTT('Zero'));
    const goalType = mkAppTT(mkAppTT(mkConstTT('Equal'), plusNZero), mkVarTT(0));
    const fullType = mkPiTT(Nat, goalType, 'n');

    const body1 = mkTreeHole();
    const body2 = mkTreeHole();
    const c1 = mkCase('n = Zero', body1, 'Zero', []);
    const c2 = mkCase('n = Succ k', body2, 'Succ', ['k']);
    const ind = mkInduction('n', [c1, c2]);
    const intros = mkIntros(['n'], ind);

    // Without inductiveMap — should fall back to unsubstituted goal
    const ctx1 = computeTypedContext(intros, body1.id, fullType, emptyRegistry);
    const ctx2 = computeTypedContext(intros, body2.id, fullType, emptyRegistry);
    // Both should have the same goal (no substitution)
    expect(ctx1!.goal).toBe(ctx2!.goal);
  });

  test('cases without constructor metadata fall back to same goal', () => {
    const plusNZero = mkAppTT(mkAppTT(mkConstTT('plus'), mkVarTT(0)), mkConstTT('Zero'));
    const goalType = mkAppTT(mkAppTT(mkConstTT('Equal'), plusNZero), mkVarTT(0));
    const fullType = mkPiTT(Nat, goalType, 'n');

    const body1 = mkTreeHole();
    // Case WITHOUT constructor metadata (old-style)
    const c1 = mkCase('n = 0', body1);
    const ind = mkInduction('n', [c1]);
    const intros = mkIntros(['n'], ind);

    const ctx = computeTypedContext(intros, body1.id, fullType, emptyRegistry, natInductiveMap);
    expect(ctx).not.toBeNull();
    // Should still work, just with unsubstituted goal
    expect(ctx!.goal).toContain('plus');
  });
});
