import { describe, test, expect } from 'vitest';
import { inferType, checkType } from './checker';
import { TTKTerm, mkVar, mkConst, mkType, mkPi, mkLambda, mkApp } from './kernel';
import { TCEnv, DefinitionsMap } from './term';

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
