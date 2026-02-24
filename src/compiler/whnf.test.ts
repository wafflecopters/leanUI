import { describe, test, expect } from 'vitest';
import { whnf, areTypesDefEq, WhnfContext } from './whnf';
import { TTKTerm, TTKClause, mkVar, mkConst } from './kernel';
import { DefinitionsMap, createDefinitionsMap, addDefinition } from './term';

// Helper to create a lambda: λname:domain. body
function mkLam(name: string, domain: TTKTerm, body: TTKTerm): TTKTerm {
  return {
    tag: 'Binder',
    name,
    binderKind: { tag: 'BLam' },
    domain,
    body
  };
}

// Helper to create a Pi: (name : domain) -> body
function mkPi(name: string, domain: TTKTerm, body: TTKTerm): TTKTerm {
  return {
    tag: 'Binder',
    name,
    binderKind: { tag: 'BPi' },
    domain,
    body
  };
}

// Helper to create application: fn arg
function mkApp(fn: TTKTerm, arg: TTKTerm): TTKTerm {
  return { tag: 'App', fn, arg };
}

// Helper to create let: let name := defVal in body
function mkLet(name: string, domain: TTKTerm, defVal: TTKTerm, body: TTKTerm): TTKTerm {
  return {
    tag: 'Binder',
    name,
    binderKind: { tag: 'BLet', defVal },
    domain,
    body
  };
}

// Helper to create Match term
function mkMatch(scrutinee: TTKTerm, clauses: TTKClause[]): TTKTerm {
  return { tag: 'Match', scrutinee, clauses };
}

// Type constant
const natType: TTKTerm = mkConst('Nat');

describe('whnf β-reduction', () => {
  test('reduces simple beta redex: (λx. x) y → y', () => {
    // (λx:Nat. x) applied to var(0)
    const lam = mkLam('x', natType, mkVar(0));
    const app = mkApp(lam, mkVar(1));
    const result = whnf(app);
    // After beta reduction: x[x := var(1)] = var(1)
    // But var(1) becomes var(0) after shifting down
    expect(result).toEqual(mkVar(1));
  });

  test('reduces nested beta: (λx. λy. x) a b → a', () => {
    // (λx. λy. x) where inner body refers to outer var
    const inner = mkLam('y', natType, mkVar(1)); // refers to x (index 1)
    const outer = mkLam('x', natType, inner);
    // Apply to 'a' (const)
    const app1 = mkApp(outer, mkConst('a'));
    const result1 = whnf(app1);
    // Should get λy. a (a constant, not a var)
    expect(result1.tag).toBe('Binder');
    if (result1.tag === 'Binder') {
      expect(result1.binderKind.tag).toBe('BLam');
      expect(result1.body).toEqual(mkConst('a'));
    }

    // Apply again to 'b'
    const app2 = mkApp(app1, mkConst('b'));
    const result2 = whnf(app2);
    // Should get 'a'
    expect(result2).toEqual(mkConst('a'));
  });

  test('stops at non-reducible application', () => {
    // f x where f is just a constant
    const app = mkApp(mkConst('f'), mkConst('x'));
    const result = whnf(app);
    expect(result.tag).toBe('App');
    if (result.tag === 'App') {
      expect(result.fn).toEqual(mkConst('f'));
      expect(result.arg).toEqual(mkConst('x'));
    }
  });
});

describe('whnf ζ-reduction (let)', () => {
  test('reduces let: let x := a in x → a', () => {
    const letTerm = mkLet('x', natType, mkConst('a'), mkVar(0));
    const result = whnf(letTerm);
    expect(result).toEqual(mkConst('a'));
  });

  test('reduces nested let', () => {
    // let x := a in (let y := x in y) → a
    const inner = mkLet('y', natType, mkVar(0), mkVar(0)); // y := x, body = y
    const outer = mkLet('x', natType, mkConst('a'), inner);
    const result = whnf(outer);
    expect(result).toEqual(mkConst('a'));
  });
});

describe('whnf δ-reduction (unfold definitions)', () => {
  test('unfolds simple constant definition', () => {
    // Define: myConst = Zero
    let defs = createDefinitionsMap();
    defs = addDefinition(defs, 'myConst', natType, mkConst('Zero'));

    const term = mkConst('myConst');
    const result = whnf(term, { definitions: defs });
    expect(result).toEqual(mkConst('Zero'));
  });

  test('unfolds and continues reducing', () => {
    // Define: id = λx. x
    let defs = createDefinitionsMap();
    const idLam = mkLam('x', natType, mkVar(0));
    defs = addDefinition(defs, 'id', mkPi('x', natType, natType), idLam);

    // id Zero should reduce to Zero
    const app = mkApp(mkConst('id'), mkConst('Zero'));
    const result = whnf(app, { definitions: defs });
    expect(result).toEqual(mkConst('Zero'));
  });

  test('does not unfold without definitions', () => {
    const term = mkConst('undefined');
    const result = whnf(term);
    expect(result).toEqual(mkConst('undefined'));
  });

  test('unfolds chained definitions', () => {
    // Define: a = b, b = c, c = Zero
    let defs = createDefinitionsMap();
    defs = addDefinition(defs, 'a', natType, mkConst('b'));
    defs = addDefinition(defs, 'b', natType, mkConst('c'));
    defs = addDefinition(defs, 'c', natType, mkConst('Zero'));

    const term = mkConst('a');
    const result = whnf(term, { definitions: defs });
    expect(result).toEqual(mkConst('Zero'));
  });
});

describe('whnf ι-reduction (pattern matching)', () => {
  test('reduces match on constructor - Zero case', () => {
    // match Zero with | Zero => a | Succ n => b
    const clauses: TTKClause[] = [
      { patterns: [{ tag: 'PCtor', name: 'Zero', args: [] }], rhs: mkConst('a') },
      { patterns: [{ tag: 'PVar', name: 'n' }], rhs: mkConst('b') },
    ];
    const match = mkMatch(mkConst('Zero'), clauses);
    const result = whnf(match);
    expect(result).toEqual(mkConst('a'));
  });

  test('reduces match on constructor - Succ case', () => {
    // match (Succ Zero) with | Zero => a | Succ n => n
    const clauses: TTKClause[] = [
      { patterns: [{ tag: 'PCtor', name: 'Zero', args: [] }], rhs: mkConst('a') },
      { patterns: [{ tag: 'PCtor', name: 'Succ', args: [{ tag: 'PVar', name: 'n' }] }], rhs: mkVar(0) },
    ];
    const scrutinee = mkApp(mkConst('Succ'), mkConst('Zero'));
    const match = mkMatch(scrutinee, clauses);
    const result = whnf(match);
    expect(result).toEqual(mkConst('Zero'));
  });

  test('reduces match with variable pattern (catch-all)', () => {
    // match x with | n => n (where x is some constructor)
    const clauses: TTKClause[] = [
      { patterns: [{ tag: 'PVar', name: 'n' }], rhs: mkVar(0) },
    ];
    const match = mkMatch(mkConst('anything'), clauses);
    const result = whnf(match);
    expect(result).toEqual(mkConst('anything'));
  });

  test('reduces match with wildcard pattern', () => {
    // match x with | _ => result
    const clauses: TTKClause[] = [
      { patterns: [{ tag: 'PWild', name: '_' }], rhs: mkConst('result') },
    ];
    const match = mkMatch(mkConst('anything'), clauses);
    const result = whnf(match);
    expect(result).toEqual(mkConst('result'));
  });

  test('reduces match with nested constructor patterns', () => {
    // match (Succ (Succ Zero)) with | Succ (Succ n) => n
    const clauses: TTKClause[] = [
      {
        patterns: [{
          tag: 'PCtor',
          name: 'Succ',
          args: [{
            tag: 'PCtor',
            name: 'Succ',
            args: [{ tag: 'PVar', name: 'n' }]
          }]
        }],
        rhs: mkVar(0)
      },
    ];
    const scrutinee = mkApp(mkConst('Succ'), mkApp(mkConst('Succ'), mkConst('Zero')));
    const match = mkMatch(scrutinee, clauses);
    const result = whnf(match);
    expect(result).toEqual(mkConst('Zero'));
  });
});

describe('whnf combined reductions', () => {
  test('δ then ι: unfold definition then pattern match', () => {
    // Define: plus Zero n = n, plus (Succ m) n = Succ (plus m n)
    // But for this test, we'll simplify: plus defined as a Match term

    // First, let's define a simpler function: isZero
    // isZero = match scrutinee with | Zero => True | Succ _ => False
    const isZeroMatch: TTKTerm = mkMatch(
      mkVar(0), // scrutinee (will be the first argument)
      [
        { patterns: [{ tag: 'PCtor', name: 'Zero', args: [] }], rhs: mkConst('True') },
        { patterns: [{ tag: 'PCtor', name: 'Succ', args: [{ tag: 'PWild', name: '_' }] }], rhs: mkConst('False') },
      ]
    );

    // isZero is λn. match n with ...
    const isZeroLam = mkLam('n', natType, isZeroMatch);

    let defs = createDefinitionsMap();
    defs = addDefinition(defs, 'isZero', mkPi('n', natType, mkConst('Bool')), isZeroLam);

    // Test: isZero Zero → True
    const app1 = mkApp(mkConst('isZero'), mkConst('Zero'));
    const result1 = whnf(app1, { definitions: defs });
    expect(result1).toEqual(mkConst('True'));

    // Test: isZero (Succ Zero) → False
    const app2 = mkApp(mkConst('isZero'), mkApp(mkConst('Succ'), mkConst('Zero')));
    const result2 = whnf(app2, { definitions: defs });
    expect(result2).toEqual(mkConst('False'));
  });

  test('β then ι: beta reduce then pattern match', () => {
    // (λx. match x with Zero => a) Zero → a
    const matchTerm = mkMatch(mkVar(0), [
      { patterns: [{ tag: 'PCtor', name: 'Zero', args: [] }], rhs: mkConst('a') },
    ]);
    const lam = mkLam('x', natType, matchTerm);
    const app = mkApp(lam, mkConst('Zero'));
    const result = whnf(app);
    expect(result).toEqual(mkConst('a'));
  });
});

describe('whnf fuel limit', () => {
  test('stops reducing when fuel exhausted', () => {
    // Create a potentially infinite chain: a → b → c → a (cycle)
    // With limited fuel, it should stop
    let defs = createDefinitionsMap();
    defs = addDefinition(defs, 'a', natType, mkConst('b'));
    defs = addDefinition(defs, 'b', natType, mkConst('c'));
    defs = addDefinition(defs, 'c', natType, mkConst('a')); // cycle!

    // With fuel = 5, should stop before infinite loop
    const term = mkConst('a');
    const result = whnf(term, { definitions: defs, fuel: 5 });
    // Result could be 'a', 'b', or 'c' depending on where fuel ran out
    expect(['a', 'b', 'c']).toContain((result as { name: string }).name);
  });
});

describe('areTypesDefEq with definitions', () => {
  test('equal after delta reduction', () => {
    let defs = createDefinitionsMap();
    defs = addDefinition(defs, 'myNat', mkConst('Type'), natType);

    // myNat should be equal to Nat after unfolding
    expect(areTypesDefEq(mkConst('myNat'), natType, defs)).toBe(true);
  });

  test('equal after iota reduction', () => {
    // Define isZero as before
    const isZeroMatch: TTKTerm = mkMatch(
      mkVar(0),
      [
        { patterns: [{ tag: 'PCtor', name: 'Zero', args: [] }], rhs: mkConst('True') },
        { patterns: [{ tag: 'PCtor', name: 'Succ', args: [{ tag: 'PWild', name: '_' }] }], rhs: mkConst('False') },
      ]
    );
    const isZeroLam = mkLam('n', natType, isZeroMatch);

    let defs = createDefinitionsMap();
    defs = addDefinition(defs, 'isZero', mkPi('n', natType, mkConst('Bool')), isZeroLam);

    // isZero Zero = True
    const app = mkApp(mkConst('isZero'), mkConst('Zero'));
    expect(areTypesDefEq(app, mkConst('True'), defs)).toBe(true);
  });
});

describe('predecessor function reduction', () => {
  // Simpler test case: predecessor function (single argument, no nesting issues)
  // pred Zero = Zero
  // pred (Succ n) = n
  function createPredDefinitions(): DefinitionsMap {
    // pred = λx. match x with Zero => Zero | Succ n => n
    const predMatch: TTKTerm = mkMatch(
      mkVar(0), // x
      [
        {
          patterns: [{ tag: 'PCtor', name: 'Zero', args: [] }],
          rhs: mkConst('Zero')
        },
        {
          patterns: [{ tag: 'PCtor', name: 'Succ', args: [{ tag: 'PVar', name: 'n' }] }],
          rhs: mkVar(0) // n (the pattern variable)
        },
      ]
    );

    const predLam = mkLam('x', natType, predMatch);

    let defs = createDefinitionsMap();
    defs = addDefinition(defs, 'pred', mkPi('x', natType, natType), predLam);
    return defs;
  }

  test('pred Zero reduces to Zero', () => {
    const defs = createPredDefinitions();
    const predZero = mkApp(mkConst('pred'), mkConst('Zero'));
    const result = whnf(predZero, { definitions: defs });
    expect(result).toEqual(mkConst('Zero'));
  });

  test('pred (Succ Zero) reduces to Zero', () => {
    const defs = createPredDefinitions();
    const predSuccZero = mkApp(mkConst('pred'), mkApp(mkConst('Succ'), mkConst('Zero')));
    const result = whnf(predSuccZero, { definitions: defs });
    expect(result).toEqual(mkConst('Zero'));
  });

  test('pred (Succ (Succ Zero)) reduces to (Succ Zero)', () => {
    const defs = createPredDefinitions();
    const succZero = mkApp(mkConst('Succ'), mkConst('Zero'));
    const succSuccZero = mkApp(mkConst('Succ'), succZero);
    const predSuccSuccZero = mkApp(mkConst('pred'), succSuccZero);
    const result = whnf(predSuccSuccZero, { definitions: defs });
    expect(result).toEqual(succZero);
  });
});

describe('PWild binding alignment', () => {
  // These tests verify that PWild does NOT produce bindings during WHNF reduction.
  // Pattern-matching functions (compiled via checkTermValue) use RHS de Bruijn indices
  // relative to PVar bindings only. WHNF's matchPattern must follow the same convention.

  test('PWild before PVar in constructor: | Succ _ => result uses no binding', () => {
    // match (Succ Zero) with | Succ _ => True
    // PWild should not produce a binding; RHS has no variables
    const clauses: TTKClause[] = [
      {
        patterns: [{
          tag: 'PCtor',
          name: 'Succ',
          args: [{ tag: 'PWild', name: '_' }]
        }],
        rhs: mkConst('True')
      },
    ];
    const scrutinee = mkApp(mkConst('Succ'), mkConst('Zero'));
    const match = mkMatch(scrutinee, clauses);
    const result = whnf(match);
    expect(result).toEqual(mkConst('True'));
  });

  test('PWild before PVar in constructor: | Pair _ y => y binds to second field', () => {
    // match (MkPair a b) with | MkPair _ y => y
    // PWild should NOT produce a binding, so y (de Bruijn 0) should bind to b, not a
    const clauses: TTKClause[] = [
      {
        patterns: [{
          tag: 'PCtor',
          name: 'MkPair',
          args: [
            { tag: 'PWild', name: '_' },
            { tag: 'PVar', name: 'y' }
          ]
        }],
        rhs: mkVar(0) // y - should be the SECOND field (b)
      },
    ];
    // MkPair a b => (MkPair a) b
    const scrutinee = mkApp(mkApp(mkConst('MkPair'), mkConst('a')), mkConst('b'));
    const match = mkMatch(scrutinee, clauses);
    const result = whnf(match);
    // y should bind to 'b' (second arg), NOT 'a' (first arg)
    expect(result).toEqual(mkConst('b'));
  });

  test('PVar before PWild in constructor: | Pair x _ => x binds to first field', () => {
    // match (MkPair a b) with | MkPair x _ => x
    // Only PVar binds: x → bindings[0]
    // x is at Var(0)
    const clauses: TTKClause[] = [
      {
        patterns: [{
          tag: 'PCtor',
          name: 'MkPair',
          args: [
            { tag: 'PVar', name: 'x' },
            { tag: 'PWild', name: '_' }
          ]
        }],
        rhs: mkVar(0) // x - first field (a), only PVar binding
      },
    ];
    const scrutinee = mkApp(mkApp(mkConst('MkPair'), mkConst('a')), mkConst('b'));
    const match = mkMatch(scrutinee, clauses);
    const result = whnf(match);
    expect(result).toEqual(mkConst('a'));
  });

  test('multiple PWild in constructor: | Triple _ _ z => z', () => {
    // match (MkTriple a b c) with | MkTriple _ _ z => z
    // Two PWild produce 0 bindings, z (de Bruijn 0) should bind to c
    const clauses: TTKClause[] = [
      {
        patterns: [{
          tag: 'PCtor',
          name: 'MkTriple',
          args: [
            { tag: 'PWild', name: '_' },
            { tag: 'PWild', name: '_' },
            { tag: 'PVar', name: 'z' }
          ]
        }],
        rhs: mkVar(0) // z - should be the THIRD field (c)
      },
    ];
    const scrutinee = mkApp(mkApp(mkApp(mkConst('MkTriple'), mkConst('a')), mkConst('b')), mkConst('c'));
    const match = mkMatch(scrutinee, clauses);
    const result = whnf(match);
    expect(result).toEqual(mkConst('c'));
  });

  test('PWild with nested constructor: | Ctor _ (Succ y) => y', () => {
    // match (MkPair a (Succ Zero)) with | MkPair _ (Succ y) => y
    // PWild skips first arg, Succ y matches second arg, y binds to Zero
    const clauses: TTKClause[] = [
      {
        patterns: [{
          tag: 'PCtor',
          name: 'MkPair',
          args: [
            { tag: 'PWild', name: '_' },
            {
              tag: 'PCtor',
              name: 'Succ',
              args: [{ tag: 'PVar', name: 'y' }]
            }
          ]
        }],
        rhs: mkVar(0) // y - should be Zero
      },
    ];
    const scrutinee = mkApp(
      mkApp(mkConst('MkPair'), mkConst('a')),
      mkApp(mkConst('Succ'), mkConst('Zero'))
    );
    const match = mkMatch(scrutinee, clauses);
    const result = whnf(match);
    expect(result).toEqual(mkConst('Zero'));
  });

  test('mixed PVar and PWild: | Ctor x _ y => (x, y) binds correctly', () => {
    // match (MkTriple a b c) with | MkTriple x _ z => x
    // Only PVars bind: x=bindings[0], z=bindings[1]
    // x is at Var(1), z is at Var(0)
    const clauses_x: TTKClause[] = [
      {
        patterns: [{
          tag: 'PCtor',
          name: 'MkTriple',
          args: [
            { tag: 'PVar', name: 'x' },
            { tag: 'PWild', name: '_' },
            { tag: 'PVar', name: 'z' }
          ]
        }],
        rhs: mkVar(1) // x - first field (a), index 1 with 2 PVar bindings
      },
    ];
    const scrutinee = mkApp(mkApp(mkApp(mkConst('MkTriple'), mkConst('a')), mkConst('b')), mkConst('c'));
    const match_x = mkMatch(scrutinee, clauses_x);
    expect(whnf(match_x)).toEqual(mkConst('a'));

    // Same but return z
    const clauses_z: TTKClause[] = [
      {
        patterns: [{
          tag: 'PCtor',
          name: 'MkTriple',
          args: [
            { tag: 'PVar', name: 'x' },
            { tag: 'PWild', name: '_' },
            { tag: 'PVar', name: 'z' }
          ]
        }],
        rhs: mkVar(0) // z - should be c
      },
    ];
    const match_z = mkMatch(scrutinee, clauses_z);
    expect(whnf(match_z)).toEqual(mkConst('c'));
  });
});

describe('isZero function reduction', () => {
  // isZero Zero = True
  // isZero (Succ _) = False
  function createIsZeroDefinitions(): DefinitionsMap {
    const isZeroMatch: TTKTerm = mkMatch(
      mkVar(0),
      [
        { patterns: [{ tag: 'PCtor', name: 'Zero', args: [] }], rhs: mkConst('True') },
        { patterns: [{ tag: 'PCtor', name: 'Succ', args: [{ tag: 'PWild', name: '_' }] }], rhs: mkConst('False') },
      ]
    );
    const isZeroLam = mkLam('n', natType, isZeroMatch);

    let defs = createDefinitionsMap();
    defs = addDefinition(defs, 'isZero', mkPi('n', natType, mkConst('Bool')), isZeroLam);
    return defs;
  }

  test('isZero Zero reduces to True', () => {
    const defs = createIsZeroDefinitions();
    const isZeroZero = mkApp(mkConst('isZero'), mkConst('Zero'));
    const result = whnf(isZeroZero, { definitions: defs });
    expect(result).toEqual(mkConst('True'));
  });

  test('isZero (Succ Zero) reduces to False', () => {
    const defs = createIsZeroDefinitions();
    const isZeroSucc = mkApp(mkConst('isZero'), mkApp(mkConst('Succ'), mkConst('Zero')));
    const result = whnf(isZeroSucc, { definitions: defs });
    expect(result).toEqual(mkConst('False'));
  });
});
