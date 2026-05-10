import { describe, test, expect } from 'vitest';
import { inferType, checkType, buildOfNatCoercionHoleId } from './checker';
import { TTKTerm, mkVar, mkConst, mkType, mkPi, mkLambda, mkApp, mkULevel, mkLSucc, mkLMax, mkMeta } from './kernel';
import { TCEnv, DefinitionsMap } from './term';
import { unifyTerms, UnifyResult } from './unify';

// Helper to create a minimal TCEnv for testing
function createTestEnv(term: TTKTerm, context: { name: string; type: TTKTerm }[] = []): TCEnv<TTKTerm> {
  const definitions: DefinitionsMap = {
    terms: new Map(),
    inductiveTypes: new Map(),
    inductiveNameOfConstructor: new Map(),
  };

  // Add Nat type for testing
  definitions.terms.set('Nat', { name: 'Nat', type: mkType() });
  definitions.terms.set('Zero', { name: 'Zero', type: mkConst('Nat') });
  definitions.terms.set('Succ', { name: 'Succ', type: mkPi(mkConst('Nat'), mkConst('Nat'), '_') });

  // Add a simple identity function for testing
  // id : (A : Type) -> A -> A
  const idType = mkPi(mkType(), mkPi(mkVar(0), mkVar(1), 'x'), 'A');
  definitions.terms.set('id', { name: 'id', type: idType });

  const ttkContext = context.map(c => ({ name: c.name, type: c.type }));

  return new TCEnv(
    ttkContext,
    definitions,
    new Map(), // metaVars
    [], // constraints
    [], // indexPath
    [], // valueStack
    term,
    new Map(), // levelMetas
    { mode: 'check' }
  );
}

describe('inferType', () => {
  test('Var returns its type from context', () => {
    const term: TTKTerm = mkVar(0);
    const env = createTestEnv(term, [{ name: 'x', type: mkConst('Nat') }]);

    const result = inferType(env);

    // The returned value should be the TYPE (Nat), not the term
    expect(result.value).toEqual(mkConst('Nat'));
  });

  test('Const returns its type from definitions', () => {
    const term: TTKTerm = mkConst('Zero');
    const env = createTestEnv(term);

    const result = inferType(env);

    expect(result.value).toEqual(mkConst('Nat'));
  });

  test('App returns the result type', () => {
    // Succ Zero : Nat
    const term: TTKTerm = mkApp(mkConst('Succ'), mkConst('Zero'));
    const env = createTestEnv(term);

    const result = inferType(env);

    expect(result.value).toEqual(mkConst('Nat'));
  });

  test('Hole in infer mode creates a Meta', () => {
    const term: TTKTerm = { tag: 'Hole', id: '_' };
    const env = createTestEnv(term);

    const result = inferType(env);

    // The returned value should be a Meta (for the TYPE, since we're inferring)
    // Actually, createMetaForHole returns the meta term, so result.value should be a Meta
    expect(result.value.tag).toBe('Meta');
  });
});

describe('checkType', () => {
  test('Var checking against correct type succeeds', () => {
    const term: TTKTerm = mkVar(0);
    const env = createTestEnv(term, [{ name: 'x', type: mkConst('Nat') }]);

    const result = checkType(env, mkConst('Nat'));

    // checkType should return the original term for CONV case
    expect(result.value).toEqual(mkVar(0));
  });

  test('Hole checking creates a Meta and returns it', () => {
    const term: TTKTerm = { tag: 'Hole', id: '_' };
    const env = createTestEnv(term);

    const result = checkType(env, mkConst('Nat'));

    // For Holes, checkType should return a Meta
    expect(result.value.tag).toBe('Meta');

    // The meta should be registered in metaVars
    expect(result.metaVars.size).toBe(1);
  });

  test('App with Hole argument returns elaborated App with Meta', () => {
    // Succ _ where _ should become ?m0
    const hole: TTKTerm = { tag: 'Hole', id: '_' };
    const term: TTKTerm = mkApp(mkConst('Succ'), hole);
    const env = createTestEnv(term);

    const result = checkType(env, mkConst('Nat'));

    // The result should be an App with Meta as the argument
    expect(result.value.tag).toBe('App');
    if (result.value.tag === 'App') {
      expect(result.value.fn).toEqual(mkConst('Succ'));
      expect(result.value.arg.tag).toBe('Meta'); // Elaborated!
    }

    // The meta should be registered in metaVars
    expect(result.metaVars.size).toBe(1);
  });

  test('Lambda checking returns elaborated Lambda with Meta body', () => {
    // \(x : Nat) => _ where _ should become ?m0
    const hole: TTKTerm = { tag: 'Hole', id: '_' };
    const term: TTKTerm = mkLambda(mkConst('Nat'), hole, 'x');
    const expectedType = mkPi(mkConst('Nat'), mkConst('Nat'), 'x');
    const env = createTestEnv(term);

    const result = checkType(env, expectedType);

    // The result should be a Lambda with Meta as the body
    expect(result.value.tag).toBe('Binder');
    if (result.value.tag === 'Binder') {
      expect(result.value.binderKind.tag).toBe('BLam');
      expect(result.value.body.tag).toBe('Meta'); // Elaborated!
    }

    // The meta should be registered in metaVars
    expect(result.metaVars.size).toBe(1);
  });

  test('Nested App with multiple Holes returns all Metas', () => {
    // id _ _ where both _ should become metas
    // id : (A : Type) -> A -> A
    const hole1: TTKTerm = { tag: 'Hole', id: '_1' };
    const hole2: TTKTerm = { tag: 'Hole', id: '_2' };
    const term: TTKTerm = mkApp(mkApp(mkConst('id'), hole1), hole2);
    const env = createTestEnv(term);

    const result = checkType(env, mkConst('Nat'));

    // The result should be nested Apps with Metas
    expect(result.value.tag).toBe('App');
    if (result.value.tag === 'App') {
      expect(result.value.arg.tag).toBe('Meta'); // Outer arg elaborated
      expect(result.value.fn.tag).toBe('App');
      if (result.value.fn.tag === 'App') {
        expect(result.value.fn.arg.tag).toBe('Meta'); // Inner arg elaborated
      }
    }

    // Two metas should be created (one for each Hole)
    expect(result.metaVars.size).toBe(2);
  });

  test('Var returns same term (no elaboration needed)', () => {
    const term: TTKTerm = mkVar(0);
    const env = createTestEnv(term, [{ name: 'x', type: mkConst('Nat') }]);

    const result = checkType(env, mkConst('Nat'));

    // Var stays as Var - no elaboration needed
    expect(result.value).toEqual(mkVar(0));
  });

  test('Const returns same term (no elaboration needed)', () => {
    const term: TTKTerm = mkConst('Zero');
    const env = createTestEnv(term);

    const result = checkType(env, mkConst('Nat'));

    // Const stays as Const - no elaboration needed
    expect(result.value).toEqual(mkConst('Zero'));
  });
});

describe('inferType: built-in universe level operations', () => {
  test('USucc has type ULevel -> ULevel', () => {
    const env = createTestEnv(mkConst('USucc'));
    const result = inferType(env);
    // USucc : ULevel -> ULevel
    expect(result.value.tag).toBe('Binder');
    if (result.value.tag === 'Binder') {
      expect(result.value.domain).toEqual(mkULevel());
      expect(result.value.body).toEqual(mkULevel());
    }
  });

  test('UMax has type ULevel -> ULevel -> ULevel', () => {
    const env = createTestEnv(mkConst('UMax'));
    const result = inferType(env);
    // UMax : ULevel -> ULevel -> ULevel
    expect(result.value.tag).toBe('Binder');
    if (result.value.tag === 'Binder') {
      expect(result.value.domain).toEqual(mkULevel());
      expect(result.value.body.tag).toBe('Binder');
      if (result.value.body.tag === 'Binder') {
        expect(result.value.body.domain).toEqual(mkULevel());
        expect(result.value.body.body).toEqual(mkULevel());
      }
    }
  });

  test('UIMax has type ULevel -> ULevel -> ULevel', () => {
    const env = createTestEnv(mkConst('UIMax'));
    const result = inferType(env);
    expect(result.value.tag).toBe('Binder');
    if (result.value.tag === 'Binder') {
      expect(result.value.domain).toEqual(mkULevel());
      expect(result.value.body.tag).toBe('Binder');
    }
  });

  test('USucc applied to ULit(0) type-checks as ULevel', () => {
    // mkLSucc(ULit(0)) = App(Const('USucc'), ULit(0))
    const term = mkLSucc({ tag: 'ULit', n: 0 });
    const env = createTestEnv(term);
    const result = inferType(env);
    expect(result.value).toEqual(mkULevel());
  });

  test('UMax applied to two ULits type-checks as ULevel', () => {
    // mkLMax(ULit(0), ULit(1)) = App(App(Const('UMax'), ULit(0)), ULit(1))
    const term = mkLMax({ tag: 'ULit', n: 0 }, { tag: 'ULit', n: 1 });
    const env = createTestEnv(term);
    const result = inferType(env);
    expect(result.value).toEqual(mkULevel());
  });

  test('Sort containing USucc re-type-checks correctly', () => {
    // Type 1 = Sort(USucc(ULit(0))) — should infer to Type 2
    const term: TTKTerm = { tag: 'Sort', level: mkLSucc({ tag: 'ULit', n: 0 }) };
    const env = createTestEnv(term);
    const result = inferType(env);
    // Type 1 : Type 2 = Sort(USucc(USucc(ULit(0))))
    expect(result.value.tag).toBe('Sort');
  });
});

describe('createMetaForHole: duplicate hole ID handling', () => {
  test('single hole with ID "_" creates meta with same ID', () => {
    const hole: TTKTerm = { tag: 'Hole', id: '_' };
    const env = createTestEnv(hole);

    const result = checkType(env, mkConst('Nat'));

    // Should create a meta with ID '_'
    expect(result.value.tag).toBe('Meta');
    if (result.value.tag === 'Meta') {
      expect(result.value.id).toBe('_');
    }

    // Should have one meta registered
    expect(result.metaVars.size).toBe(1);
    expect(result.metaVars.has('_')).toBe(true);

    // The meta should have the expected type
    const metaInfo = result.metaVars.get('_');
    expect(metaInfo?.type).toEqual(mkConst('Nat'));
  });

  test('two holes with same ID "_" get distinct meta IDs', () => {
    // App with two holes: Succ (id _ _)
    // First _ is the type argument to id, second _ is the value argument
    const hole1: TTKTerm = { tag: 'Hole', id: '_' };
    const hole2: TTKTerm = { tag: 'Hole', id: '_' };
    const term: TTKTerm = mkApp(mkConst('Succ'), mkApp(mkApp(mkConst('id'), hole1), hole2));
    const env = createTestEnv(term);

    const result = checkType(env, mkConst('Nat'));

    // Should create two distinct metas
    expect(result.metaVars.size).toBe(2);

    // First hole should get ID '_', second should get '_$1'
    expect(result.metaVars.has('_')).toBe(true);
    expect(result.metaVars.has('_$1')).toBe(true);

    // Both metas should have different types (one is Type, one is the value)
    const meta1 = result.metaVars.get('_');
    const meta2 = result.metaVars.get('_$1');
    expect(meta1).toBeDefined();
    expect(meta2).toBeDefined();

    // They should have different types - one is Type (for id's type param), other is Nat
    expect(meta1?.type).not.toEqual(meta2?.type);
  });

  test('three holes with same ID get unique suffixes', () => {
    // Construct a term with three holes all having ID '_'
    // id _ (id _ _)
    const hole1: TTKTerm = { tag: 'Hole', id: '_' };
    const hole2: TTKTerm = { tag: 'Hole', id: '_' };
    const hole3: TTKTerm = { tag: 'Hole', id: '_' };
    const innerApp = mkApp(mkApp(mkConst('id'), hole2), hole3);
    const term: TTKTerm = mkApp(mkApp(mkConst('id'), hole1), innerApp);
    const env = createTestEnv(term);

    const result = checkType(env, mkConst('Nat'));

    // Should create three distinct metas
    expect(result.metaVars.size).toBeGreaterThanOrEqual(3);

    // Should have '_', '_$1', '_$2'
    expect(result.metaVars.has('_')).toBe(true);
    expect(result.metaVars.has('_$1')).toBe(true);
    expect(result.metaVars.has('_$2')).toBe(true);
  });

  test('holes with different IDs do not collide', () => {
    // id _a _b where _a and _b are different hole IDs
    const hole1: TTKTerm = { tag: 'Hole', id: '_a' };
    const hole2: TTKTerm = { tag: 'Hole', id: '_b' };
    const term: TTKTerm = mkApp(mkApp(mkConst('id'), hole1), hole2);
    const env = createTestEnv(term);

    const result = checkType(env, mkConst('Nat'));

    // Should create two metas with their original IDs
    expect(result.metaVars.size).toBe(2);
    expect(result.metaVars.has('_a')).toBe(true);
    expect(result.metaVars.has('_b')).toBe(true);

    // Should NOT create suffixed versions since IDs are different
    expect(result.metaVars.has('_a$1')).toBe(false);
    expect(result.metaVars.has('_b$1')).toBe(false);
  });

  test('mix of same and different hole IDs handled correctly', () => {
    // id _ _x where first is '_', second is '_x'
    const hole1: TTKTerm = { tag: 'Hole', id: '_' };
    const hole2: TTKTerm = { tag: 'Hole', id: '_x' };
    const hole3: TTKTerm = { tag: 'Hole', id: '_' }; // Another '_'

    // Build: id _ (id _x _)
    const innerApp = mkApp(mkApp(mkConst('id'), hole2), hole3);
    const term: TTKTerm = mkApp(mkApp(mkConst('id'), hole1), innerApp);
    const env = createTestEnv(term);

    const result = checkType(env, mkConst('Nat'));

    // Should create three metas
    expect(result.metaVars.size).toBeGreaterThanOrEqual(3);

    // Should have '_', '_$N' for the duplicate, and '_x' for the unique one
    expect(result.metaVars.has('_')).toBe(true);
    expect(result.metaVars.has('_x')).toBe(true);

    // There should be a suffixed version of '_' since we have two '_' holes
    const suffixedKeys = Array.from(result.metaVars.keys()).filter(k => k.startsWith('_$'));
    expect(suffixedKeys.length).toBeGreaterThanOrEqual(1);
  });

  test('each meta has correct context depth', () => {
    // Lambda with holes at different depths
    // \(x : Nat) => id _ _
    const hole1: TTKTerm = { tag: 'Hole', id: '_' };
    const hole2: TTKTerm = { tag: 'Hole', id: '_' };
    const bodyTerm = mkApp(mkApp(mkConst('id'), hole1), hole2);
    const term: TTKTerm = mkLambda(mkConst('Nat'), bodyTerm, 'x');
    const expectedType = mkPi(mkConst('Nat'), mkConst('Nat'), 'x');
    const env = createTestEnv(term);

    const result = checkType(env, expectedType);

    // Both holes are inside the lambda body, so they should have context length 1
    const meta1 = result.metaVars.get('_');
    const meta2 = result.metaVars.get('_$1');

    expect(meta1?.ctx.length).toBe(1); // Inside lambda with x bound
    expect(meta2?.ctx.length).toBe(1);
  });
});

describe('buildOfNatCoercionHoleId', () => {
  test('distinguishes different coercion sites deterministically', () => {
    const left = buildOfNatCoercionHoleId(
      [{ kind: 'field', name: 'value' }, { kind: 'array', index: 0 }],
      'Carrier',
      1,
      0
    );
    const right = buildOfNatCoercionHoleId(
      [{ kind: 'field', name: 'value' }, { kind: 'array', index: 1 }],
      'Carrier',
      1,
      0
    );

    expect(left).not.toBe(right);
    expect(left).toContain('Carrier');
    expect(left).toContain('value_0_');
  });

  test('includes context depth so the same path in a different scope stays distinct', () => {
    const outer = buildOfNatCoercionHoleId([], 'Carrier', 0, 0);
    const inner = buildOfNatCoercionHoleId([], 'Carrier', 1, 0);

    expect(outer).not.toBe(inner);
    expect(outer).toContain('_0_root_0');
    expect(inner).toContain('_1_root_0');
  });
});

describe('unifyTerms: level meta constraint depth in Pi bodies', () => {
  const checkOpts = { mode: 'check' as const };

  test('level meta in Pi body gets rhs shifted down correctly', () => {
    // Simulate the DPair3 bug:
    // Unifying Pi(Var(1), Sort(Var(3))) ≡ Pi(Var(1), Sort(Meta("?v")))
    //
    // This represents:
    //   inferred: (x : A) -> Type v   where A=Var(1), v=Var(3) at depth 5
    //   expected: (x : A) -> Type ?v  where A=Var(1), ?v=level meta
    //
    // Inside the Pi body (depth+1), Var(3) = v at context [x, B, A, v, u]
    // Outside the Pi (depth), v = Var(2) at context [B, A, v, u]
    //
    // The metaConstraint should have rhs = Var(2), NOT Var(3)
    const inferred = mkPi(mkVar(1), { tag: 'Sort', level: mkVar(3) }, 'x');
    const expected = mkPi(mkVar(1), { tag: 'Sort', level: mkMeta('?v') }, 'x');

    const result = unifyTerms(inferred, expected, checkOpts);

    expect(result.success).toBe(true);
    if (result.success) {
      // Should have a metaConstraint for ?v
      expect(result.metaConstraints.length).toBe(1);
      expect(result.metaConstraints[0].meta).toBe('?v');
      // The rhs should be Var(2) (shifted down from Var(3) in the body)
      // because the level meta ?v is used at the outer depth
      expect(result.metaConstraints[0].rhs).toEqual(mkVar(2));
    }
  });

  test('level meta in non-Pi position has correct rhs (no shift needed)', () => {
    // Unifying Sort(Var(2)) ≡ Sort(Meta("?v"))
    // No Pi body involved, so no shift needed
    const inferred: TTKTerm = { tag: 'Sort', level: mkVar(2) };
    const expected: TTKTerm = { tag: 'Sort', level: mkMeta('?v') };

    const result = unifyTerms(inferred, expected, checkOpts);

    expect(result.success).toBe(true);
    if (result.success) {
      expect(result.metaConstraints.length).toBe(1);
      expect(result.metaConstraints[0].meta).toBe('?v');
      // No shift: Var(2) stays Var(2)
      expect(result.metaConstraints[0].rhs).toEqual(mkVar(2));
    }
  });

  test('level meta in doubly-nested Pi body shifts down by 2', () => {
    // Pi(A, Pi(B, Sort(Var(4)))) ≡ Pi(A, Pi(B, Sort(Meta("?v"))))
    // Inside double body: Var(4) at depth+2
    // At outer level: Var(2)
    const inferred = mkPi(mkType(), mkPi(mkType(), { tag: 'Sort', level: mkVar(4) }, 'y'), 'x');
    const expected = mkPi(mkType(), mkPi(mkType(), { tag: 'Sort', level: mkMeta('?v') }, 'y'), 'x');

    const result = unifyTerms(inferred, expected, checkOpts);

    expect(result.success).toBe(true);
    if (result.success) {
      expect(result.metaConstraints.length).toBe(1);
      expect(result.metaConstraints[0].meta).toBe('?v');
      // Shifted down by 2 (two Pi body entries): Var(4) → Var(2)
      expect(result.metaConstraints[0].rhs).toEqual(mkVar(2));
    }
  });
});
