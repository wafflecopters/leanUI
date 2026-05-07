import { describe, test, expect } from 'vitest';
import { inferType, checkType } from './checker';
import { TTKTerm, mkVar, mkConst, mkType, mkPi, mkLambda, mkApp, mkLet, mkHole, mkULit, mkSort } from './kernel';
import { TCEnv, DefinitionsMap } from './term';

// Helper to solve constraints and zonk result to get the final type with solved metas
function zonkResult(result: TCEnv<TTKTerm>): TTKTerm {
  const solved = result.solveMetasAndConstraints({ liftMetasToFullContext: false });
  return solved.zonkTerm(result.value);
}

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

  // Add Bool type for testing
  definitions.terms.set('Bool', { name: 'Bool', type: mkType() });
  definitions.terms.set('True', { name: 'True', type: mkConst('Bool') });
  definitions.terms.set('False', { name: 'False', type: mkConst('Bool') });

  // Add a simple identity function for testing
  // id : (A : Type) -> A -> A
  const idType = mkPi(mkType(), mkPi(mkVar(0), mkVar(1), 'x'), 'A');
  definitions.terms.set('id', { name: 'id', type: idType });

  // Add a const function for testing
  // const : (A : Type) -> (B : Type) -> A -> B -> A
  const constType = mkPi(mkType(), mkPi(mkType(), mkPi(mkVar(1), mkPi(mkVar(1), mkVar(2), 'y'), 'x'), 'B'), 'A');
  definitions.terms.set('const', { name: 'const', type: constType });

  // Add a simple add function
  // add : Nat -> Nat -> Nat
  const addType = mkPi(mkConst('Nat'), mkPi(mkConst('Nat'), mkConst('Nat'), 'y'), 'x');
  definitions.terms.set('add', { name: 'add', type: addType });

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

describe('Let Inference - Basic', () => {
  test('let with explicit type annotation', () => {
    // let x : Nat := Zero in x
    const term = mkLet('x', mkConst('Nat'), mkConst('Zero'), mkVar(0));
    const env = createTestEnv(term);

    const result = inferType(env);

    // The type of the whole let expression is Nat (type of body)
    expect(result.value).toEqual(mkConst('Nat'));
  });

  test('let with Hole type (inference)', () => {
    // let x : _ := Zero in x
    // The _ should be inferred as Nat
    const term = mkLet('x', mkHole('_'), mkConst('Zero'), mkVar(0));
    const env = createTestEnv(term);

    const result = inferType(env);

    // Type of the let expression is Nat (after zonking to resolve metas)
    expect(zonkResult(result)).toEqual(mkConst('Nat'));

    // The elaborated domain should be solved to Nat (not a Meta)
    // because we solve constraints before entering the body
    expect(result.elaboratedTerm?.tag).toBe('Binder');
    if (result.elaboratedTerm?.tag === 'Binder') {
      expect(result.elaboratedTerm.domain).toEqual(mkConst('Nat'));
    }
  });

  test('let bound variable is usable in body', () => {
    // let x : Nat := Zero in Succ x
    const term = mkLet('x', mkConst('Nat'), mkConst('Zero'), mkApp(mkConst('Succ'), mkVar(0)));
    const env = createTestEnv(term);

    const result = inferType(env);

    expect(result.value).toEqual(mkConst('Nat'));
  });

  test('let with inferred type used in function application', () => {
    // let x : _ := Zero in Succ x
    const term = mkLet('x', mkHole('_'), mkConst('Zero'), mkApp(mkConst('Succ'), mkVar(0)));
    const env = createTestEnv(term);

    const result = inferType(env);

    expect(result.value).toEqual(mkConst('Nat'));
  });

  test('let body can have different type than bound value', () => {
    // let x : Nat := Zero in True
    const term = mkLet('x', mkConst('Nat'), mkConst('Zero'), mkConst('True'));
    const env = createTestEnv(term);

    const result = inferType(env);

    // The type is Bool (type of the body), not Nat
    expect(result.value).toEqual(mkConst('Bool'));
  });

  test('let with inferred type, body has different type', () => {
    // let x : _ := Zero in True
    const term = mkLet('x', mkHole('_'), mkConst('Zero'), mkConst('True'));
    const env = createTestEnv(term);

    const result = inferType(env);

    expect(result.value).toEqual(mkConst('Bool'));
  });
});

describe('Let Inference - Nested Lets', () => {
  test('nested let expressions', () => {
    // let x : Nat := Zero in let y : Nat := Succ x in y
    const inner = mkLet('y', mkConst('Nat'), mkApp(mkConst('Succ'), mkVar(0)), mkVar(0));
    const outer = mkLet('x', mkConst('Nat'), mkConst('Zero'), inner);
    const env = createTestEnv(outer);

    const result = inferType(env);

    expect(result.value).toEqual(mkConst('Nat'));
  });

  test('nested let with both types inferred', () => {
    // let x : _ := Zero in let y : _ := Succ x in y
    const inner = mkLet('y', mkHole('_1'), mkApp(mkConst('Succ'), mkVar(0)), mkVar(0));
    const outer = mkLet('x', mkHole('_2'), mkConst('Zero'), inner);
    const env = createTestEnv(outer);

    const result = inferType(env);

    expect(zonkResult(result)).toEqual(mkConst('Nat'));
    // Both metas should be created
    expect(result.metaVars.size).toBe(2);
  });

  test('deeply nested lets', () => {
    // let a := Zero in let b := Succ a in let c := Succ b in c
    const c = mkLet('c', mkHole('_c'), mkApp(mkConst('Succ'), mkVar(0)), mkVar(0));
    const b = mkLet('b', mkHole('_b'), mkApp(mkConst('Succ'), mkVar(0)), c);
    const a = mkLet('a', mkHole('_a'), mkConst('Zero'), b);
    const env = createTestEnv(a);

    const result = inferType(env);

    expect(zonkResult(result)).toEqual(mkConst('Nat'));
    expect(result.metaVars.size).toBe(3);
  });

  test('nested let referencing outer binding', () => {
    // let x := Zero in let y := x in Succ y
    // y should have type Nat (from x)
    const inner = mkLet('y', mkHole('_y'), mkVar(0), mkApp(mkConst('Succ'), mkVar(0)));
    const outer = mkLet('x', mkHole('_x'), mkConst('Zero'), inner);
    const env = createTestEnv(outer);

    const result = inferType(env);

    expect(result.value).toEqual(mkConst('Nat'));
  });
});

describe('Let Inference - With Lambdas', () => {
  test('let binding a lambda', () => {
    // let f : Nat -> Nat := \(x : Nat) => Succ x in f Zero
    const lambda = mkLambda(mkConst('Nat'), mkApp(mkConst('Succ'), mkVar(0)), 'x');
    const piType = mkPi(mkConst('Nat'), mkConst('Nat'), 'x');
    const term = mkLet('f', piType, lambda, mkApp(mkVar(0), mkConst('Zero')));
    const env = createTestEnv(term);

    const result = inferType(env);

    expect(result.value).toEqual(mkConst('Nat'));
  });

  test('let binding a lambda with inferred type', () => {
    // let f : _ := \(x : Nat) => Succ x in f Zero
    const lambda = mkLambda(mkConst('Nat'), mkApp(mkConst('Succ'), mkVar(0)), 'x');
    const term = mkLet('f', mkHole('_'), lambda, mkApp(mkVar(0), mkConst('Zero')));
    const env = createTestEnv(term);

    const result = inferType(env);

    expect(zonkResult(result)).toEqual(mkConst('Nat'));
  });

  test('lambda with let in body', () => {
    // \(n : Nat) => let m := Succ n in m
    const letBody = mkLet('m', mkHole('_'), mkApp(mkConst('Succ'), mkVar(0)), mkVar(0));
    const lambda = mkLambda(mkConst('Nat'), letBody, 'n');
    const env = createTestEnv(lambda);

    const result = inferType(env);

    // Should infer Nat -> Nat (after zonking)
    const zonked = zonkResult(result);
    expect(zonked.tag).toBe('Binder');
    if (zonked.tag === 'Binder') {
      expect(zonked.binderKind.tag).toBe('BPi');
      expect(zonked.domain).toEqual(mkConst('Nat'));
      expect(zonked.body).toEqual(mkConst('Nat'));
    }
  });

  test('let inside lambda with captured variable', () => {
    // \(n : Nat) => let x := n in Succ x
    const letBody = mkLet('x', mkHole('_'), mkVar(0), mkApp(mkConst('Succ'), mkVar(0)));
    const lambda = mkLambda(mkConst('Nat'), letBody, 'n');
    const env = createTestEnv(lambda);

    const result = inferType(env);

    expect(result.value.tag).toBe('Binder');
    if (result.value.tag === 'Binder') {
      expect(result.value.binderKind.tag).toBe('BPi');
      expect(result.value.body).toEqual(mkConst('Nat'));
    }
  });
});

describe('Let Inference - With Application', () => {
  test('let used in application', () => {
    // let n := Zero in add n n
    const term = mkLet('n', mkHole('_'), mkConst('Zero'),
      mkApp(mkApp(mkConst('add'), mkVar(0)), mkVar(0)));
    const env = createTestEnv(term);

    const result = inferType(env);

    expect(result.value).toEqual(mkConst('Nat'));
  });

  test('let binding a partial application', () => {
    // let addZero : Nat -> Nat := add Zero in addZero (Succ Zero)
    const addZero = mkApp(mkConst('add'), mkConst('Zero'));
    const term = mkLet('addZero', mkPi(mkConst('Nat'), mkConst('Nat'), '_'), addZero,
      mkApp(mkVar(0), mkApp(mkConst('Succ'), mkConst('Zero'))));
    const env = createTestEnv(term);

    const result = inferType(env);

    expect(result.value).toEqual(mkConst('Nat'));
  });

  test('let binding a partial application with inferred type', () => {
    // let addZero := add Zero in addZero (Succ Zero)
    const addZero = mkApp(mkConst('add'), mkConst('Zero'));
    const term = mkLet('addZero', mkHole('_'), addZero,
      mkApp(mkVar(0), mkApp(mkConst('Succ'), mkConst('Zero'))));
    const env = createTestEnv(term);

    const result = inferType(env);

    expect(zonkResult(result)).toEqual(mkConst('Nat'));
  });
});

describe('Let Inference - With Holes in Value', () => {
  test('let with hole in value position', () => {
    // let x : Nat := _ in x
    // The hole in the value becomes a meta
    const term = mkLet('x', mkConst('Nat'), mkHole('_val'), mkVar(0));
    const env = createTestEnv(term);

    const result = inferType(env);

    expect(result.value).toEqual(mkConst('Nat'));

    // The value should be elaborated to a Meta
    expect(result.elaboratedTerm?.tag).toBe('Binder');
    if (result.elaboratedTerm?.tag === 'Binder' && result.elaboratedTerm.binderKind.tag === 'BLet') {
      expect(result.elaboratedTerm.binderKind.defVal.tag).toBe('Meta');
    }
  });

  test('let with holes in both type and value', () => {
    // let x : _ := _ in Succ x
    // Both should become metas, constrained to be Nat by usage
    const term = mkLet('x', mkHole('_type'), mkHole('_val'),
      mkApp(mkConst('Succ'), mkVar(0)));
    const env = createTestEnv(term);

    const result = inferType(env);

    expect(result.value).toEqual(mkConst('Nat'));
    // Should have metas for both type and value
    expect(result.metaVars.size).toBeGreaterThanOrEqual(2);
  });
});

describe('Let Inference - checkType mode', () => {
  test('let checked against expected type', () => {
    // let x := Zero in x checked against Nat
    const term = mkLet('x', mkHole('_'), mkConst('Zero'), mkVar(0));
    const env = createTestEnv(term);

    const result = checkType(env, mkConst('Nat'));

    // Should succeed with the elaborated let
    expect(result.value.tag).toBe('Binder');
  });

  test('let body checked against expected type', () => {
    // let x := True in x checked against Bool
    const term = mkLet('x', mkHole('_'), mkConst('True'), mkVar(0));
    const env = createTestEnv(term);

    const result = checkType(env, mkConst('Bool'));

    expect(result.value.tag).toBe('Binder');
  });

  test('let in lambda checked against pi type', () => {
    // \(n : Nat) => let x := n in x checked against Nat -> Nat
    const letBody = mkLet('x', mkHole('_'), mkVar(0), mkVar(0));
    const lambda = mkLambda(mkConst('Nat'), letBody, 'n');
    const env = createTestEnv(lambda);
    const expectedType = mkPi(mkConst('Nat'), mkConst('Nat'), 'n');

    const result = checkType(env, expectedType);

    expect(result.value.tag).toBe('Binder');
  });
});

describe('Let Inference - Error Cases', () => {
  test('let value type mismatch throws error', () => {
    // let x : Nat := True in x
    // True is Bool, not Nat
    const term = mkLet('x', mkConst('Nat'), mkConst('True'), mkVar(0));
    const env = createTestEnv(term);

    expect(() => inferType(env)).toThrow();
  });

  test('let body uses bound var with wrong type', () => {
    // let x : Bool := True in Succ x
    // Succ expects Nat, not Bool
    const term = mkLet('x', mkConst('Bool'), mkConst('True'),
      mkApp(mkConst('Succ'), mkVar(0)));
    const env = createTestEnv(term);

    expect(() => inferType(env)).toThrow();
  });
});

describe('Let Inference - Multiple Bindings', () => {
  test('sibling lets (sequential)', () => {
    // let a := Zero in let b := True in (a, b) conceptually
    // We'll just use both in applications
    // let a := Zero in let b := Succ a in b
    const inner = mkLet('b', mkHole('_b'), mkApp(mkConst('Succ'), mkVar(0)), mkVar(0));
    const outer = mkLet('a', mkHole('_a'), mkConst('Zero'), inner);
    const env = createTestEnv(outer);

    const result = inferType(env);

    expect(zonkResult(result)).toEqual(mkConst('Nat'));
  });

  test('let chain with dependencies', () => {
    // let a := Zero in
    // let b := Succ a in
    // let c := add a b in c
    const addAB = mkApp(mkApp(mkConst('add'), mkVar(1)), mkVar(0)); // a is index 1, b is index 0
    const letC = mkLet('c', mkHole('_c'), addAB, mkVar(0));
    const letB = mkLet('b', mkHole('_b'), mkApp(mkConst('Succ'), mkVar(0)), letC);
    const letA = mkLet('a', mkHole('_a'), mkConst('Zero'), letB);
    const env = createTestEnv(letA);

    const result = inferType(env);

    expect(zonkResult(result)).toEqual(mkConst('Nat'));
  });
});

describe('Let Inference - Type-Level Lets', () => {
  test('let binding a type', () => {
    // let T : Type := Nat in \(x : T) => x
    const lambda = mkLambda(mkVar(0), mkVar(0), 'x');
    const term = mkLet('T', mkType(), mkConst('Nat'), lambda);
    const env = createTestEnv(term);

    const result = inferType(env);

    // The lambda has type T -> T which after substitution is Nat -> Nat
    // But T is bound so we get Var(0) -> Var(0) which is T -> T
    expect(result.value.tag).toBe('Binder');
  });

  test('let binding a type with inferred kind', () => {
    // let T : _ := Nat in T
    // The _ should be inferred as Type
    const term = mkLet('T', mkHole('_'), mkConst('Nat'), mkVar(0));
    const env = createTestEnv(term);

    const result = inferType(env);

    // T has type Type, so the body (T) has type Type (after zonking)
    const zonked = zonkResult(result);
    expect(zonked.tag).toBe('Sort');
  });
});

describe('Let Inference - Elaboration', () => {
  test('solveMetasAndConstraints preserves zonked elaborated let', () => {
    // let x : _ := Zero in x
    const term = mkLet('x', mkHole('_'), mkConst('Zero'), mkVar(0));
    const env = createTestEnv(term);

    const result = inferType(env);
    const solved = result.solveMetasAndConstraints({ liftMetasToFullContext: false });

    expect(solved.elaboratedTerm?.tag).toBe('Binder');
    if (solved.elaboratedTerm?.tag === 'Binder' && solved.elaboratedTerm.binderKind.tag === 'BLet') {
      expect(solved.elaboratedTerm.domain).toEqual(mkConst('Nat'));
      expect(solved.elaboratedTerm.binderKind.defVal).toEqual(mkConst('Zero'));
      expect(solved.elaboratedTerm.body).toEqual(mkVar(0));
    }
  });

  test('elaborated let preserves structure', () => {
    // let x : _ := Zero in x
    const term = mkLet('x', mkHole('_'), mkConst('Zero'), mkVar(0));
    const env = createTestEnv(term);

    const result = inferType(env);

    // Check elaborated term structure
    const elab = result.elaboratedTerm;
    expect(elab?.tag).toBe('Binder');
    if (elab?.tag === 'Binder') {
      expect(elab.binderKind.tag).toBe('BLet');
      expect(elab.name).toBe('x');
      // Domain should be solved to Nat (not a Meta)
      // because we solve constraints before entering the body
      expect(elab.domain).toEqual(mkConst('Nat'));
      // Value should still be Zero (or elaborated Zero)
      if (elab.binderKind.tag === 'BLet') {
        expect(elab.binderKind.defVal).toEqual(mkConst('Zero'));
      }
      // Body should be Var(0)
      expect(elab.body).toEqual(mkVar(0));
    }
  });

  test('elaborated nested lets preserve structure', () => {
    // let x := Zero in let y := x in y
    const inner = mkLet('y', mkHole('_y'), mkVar(0), mkVar(0));
    const outer = mkLet('x', mkHole('_x'), mkConst('Zero'), inner);
    const env = createTestEnv(outer);

    const result = inferType(env);

    const elab = result.elaboratedTerm;
    expect(elab?.tag).toBe('Binder');
    if (elab?.tag === 'Binder') {
      expect(elab.name).toBe('x');
      expect(elab.body.tag).toBe('Binder');
      if (elab.body.tag === 'Binder') {
        expect(elab.body.name).toBe('y');
      }
    }
  });
});
