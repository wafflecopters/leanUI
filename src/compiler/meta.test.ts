import { describe, test, expect } from 'vitest';
import { solveConstraints, normalizeConstraintDepth } from './meta';
import { mkVar, mkConst, mkApp, mkType, TTKTerm } from './kernel';
import { MetaVar, Constraint, DefinitionsMap, createDefinitionsMap, addInductiveDefinition, addDefinition } from './term';

// Helper: create a definitions map with Nat (Zero, Succ) defined as an inductive
function defsWithNat(): DefinitionsMap {
  return addInductiveDefinition(
    createDefinitionsMap(),
    'Nat',
    mkType(),
    [
      { name: 'Zero', type: mkConst('Nat') },
      { name: 'Succ', type: { tag: 'Binder', name: 'n', binderKind: { tag: 'BPi' }, domain: mkConst('Nat'), body: mkConst('Nat') } },
    ],
    []
  );
}

describe('solveConstraints', () => {
  test('solves a simple constraint when meta has no solution', () => {
    // Create a meta with no solution (solution is undefined)
    const metaVars = new Map<string, MetaVar>([
      ['?m0', { ctx: [{ name: 'x', type: mkType() }], type: mkType() }]
    ]);

    // Create a constraint that says ?m0 = Nat
    const constraints: Constraint[] = [
      { ctx: [], meta: '?m0', rhs: mkConst('Nat') }
    ];

    const result = solveConstraints(metaVars, constraints);

    // The constraint should be solved
    expect(result.constraints).toHaveLength(0);

    // The meta should now have a solution
    const solvedMeta = result.metaVars.get('?m0');
    expect(solvedMeta).toBeDefined();
    expect(solvedMeta?.solution).toEqual(mkConst('Nat'));
  });

  test('throws error for conflicting constraint with different Const', () => {
    // Create a meta that already has a solution
    const existingSolution = mkConst('Bool');
    const metaVars = new Map<string, MetaVar>([
      ['?m0', { ctx: [{ name: 'x', type: mkType() }], type: mkType(), solution: existingSolution }]
    ]);

    // Try to give it a conflicting solution (different Const name)
    const constraints: Constraint[] = [
      { ctx: [], meta: '?m0', rhs: mkConst('Nat') }
    ];

    // Should throw an error because Bool != Nat
    expect(() => solveConstraints(metaVars, constraints)).toThrow('Implicit argument conflict');
  });

  test('throws error for conflicting Const vs constructor App (Zero vs Succ x)', () => {
    // Meta already solved to Zero (a Const)
    const metaVars = new Map<string, MetaVar>([
      ['?m0', { ctx: [{ name: 'x', type: mkConst('Nat') }], type: mkConst('Nat'), solution: mkConst('Zero') }]
    ]);

    // New constraint says ?m0 = Succ x (an App)
    const constraints: Constraint[] = [
      { ctx: [{ name: 'x', type: mkConst('Nat') }], meta: '?m0', rhs: mkApp(mkConst('Succ'), mkVar(0)) }
    ];

    // Should detect conflict: Zero ≠ Succ x (different constructor heads)
    const definitions = defsWithNat();
    expect(() => solveConstraints(metaVars, constraints, undefined, definitions)).toThrow('Implicit argument conflict');
  });

  test('throws error for conflicting constructor Apps (Succ x vs Zero)', () => {
    // Meta already solved to Succ x (an App)
    const metaVars = new Map<string, MetaVar>([
      ['?m0', { ctx: [{ name: 'x', type: mkConst('Nat') }], type: mkConst('Nat'), solution: mkApp(mkConst('Succ'), mkVar(0)) }]
    ]);

    // New constraint says ?m0 = Zero (a Const)
    const constraints: Constraint[] = [
      { ctx: [], meta: '?m0', rhs: mkConst('Zero') }
    ];

    // Should detect conflict: Succ x ≠ Zero (different constructor heads)
    const definitions = defsWithNat();
    expect(() => solveConstraints(metaVars, constraints, undefined, definitions)).toThrow('Implicit argument conflict');
  });

  test('throws error for nested constructor conflict (Succ Zero vs Succ (Succ x))', () => {
    // Meta solved to Succ Zero
    const metaVars = new Map<string, MetaVar>([
      ['?m0', {
        ctx: [{ name: 'x', type: mkConst('Nat') }],
        type: mkConst('Nat'),
        solution: mkApp(mkConst('Succ'), mkConst('Zero'))
      }]
    ]);

    // New constraint: ?m0 = Succ (Succ x) — same outer head, different inner
    const constraints: Constraint[] = [
      { ctx: [{ name: 'x', type: mkConst('Nat') }], meta: '?m0', rhs: mkApp(mkConst('Succ'), mkApp(mkConst('Succ'), mkVar(0))) }
    ];

    const definitions = defsWithNat();
    // Should detect conflict: Succ Zero ≠ Succ (Succ x) because Zero ≠ Succ x
    expect(() => solveConstraints(metaVars, constraints, undefined, definitions)).toThrow('Implicit argument conflict');
  });

  test('throws for Succ x vs Succ y when x and y have different names (genuinely different vars)', () => {
    // Meta solved to Succ (Var 0) — i.e., Succ x in context [x, y]
    const metaVars = new Map<string, MetaVar>([
      ['?m0', {
        ctx: [{ name: 'x', type: mkConst('Nat') }, { name: 'y', type: mkConst('Nat') }],
        type: mkConst('Nat'),
        solution: mkApp(mkConst('Succ'), mkVar(0))
      }]
    ]);

    // New constraint: ?m0 = Succ (Var 1) — i.e., Succ y
    // x and y have different names → genuinely different variables → should throw
    const constraints: Constraint[] = [
      { ctx: [{ name: 'x', type: mkConst('Nat') }, { name: 'y', type: mkConst('Nat') }], meta: '?m0', rhs: mkApp(mkConst('Succ'), mkVar(1)) }
    ];

    const definitions = defsWithNat();
    expect(() => solveConstraints(metaVars, constraints, undefined, definitions)).toThrow('Implicit argument conflict');
  });

  test('does not conflict for Succ n vs Succ n at different indices with same name (context shift)', () => {
    // Models the plusZeroRight pattern: same variable 'n' at different de Bruijn
    // indices due to a let-binding (rec) shifting the context.
    // Meta solved in context [n, rec] where n is at Var(1)
    const metaVars = new Map<string, MetaVar>([
      ['?m0', {
        ctx: [{ name: 'n', type: mkConst('Nat') }, { name: 'rec', type: mkConst('Nat') }],
        type: mkConst('Nat'),
        solution: mkApp(mkConst('Succ'), mkVar(1))   // Succ n, where n = Var(1) in [n, rec]
      }]
    ]);

    // Constraint from context [n] where n is at Var(0) — no rec binding
    // Both refer to 'n' (same name) → might be the same variable → should NOT throw
    const constraints: Constraint[] = [
      { ctx: [{ name: 'n', type: mkConst('Nat') }], meta: '?m0', rhs: mkApp(mkConst('Succ'), mkVar(0)) }
    ];

    const definitions = defsWithNat();
    expect(() => solveConstraints(metaVars, constraints, undefined, definitions)).not.toThrow();
  });

  test('does not conflict for same constructor same Var arg (Succ x vs Succ x)', () => {
    // Meta solved to Succ x
    const metaVars = new Map<string, MetaVar>([
      ['?m0', {
        ctx: [{ name: 'x', type: mkConst('Nat') }],
        type: mkConst('Nat'),
        solution: mkApp(mkConst('Succ'), mkVar(0))
      }]
    ]);

    // New constraint: ?m0 = Succ x — same value, should NOT throw
    const constraints: Constraint[] = [
      { ctx: [{ name: 'x', type: mkConst('Nat') }], meta: '?m0', rhs: mkApp(mkConst('Succ'), mkVar(0)) }
    ];

    const definitions = defsWithNat();
    expect(() => solveConstraints(metaVars, constraints, undefined, definitions)).not.toThrow();
  });

  test('constraint with out-of-scope variable goes to stillStuck', () => {
    // Create a meta with empty context
    const metaVars = new Map<string, MetaVar>([
      ['?m0', { ctx: [], type: mkType() }]
    ]);

    // Constraint has a variable that's not in the meta's context
    const constraints: Constraint[] = [
      { ctx: [], meta: '?m0', rhs: mkVar(0) }  // Var(0) needs context length >= 1
    ];

    const result = solveConstraints(metaVars, constraints);

    // The constraint should be stuck (can't solve because variable is out of scope)
    expect(result.constraints).toHaveLength(1);

    // The meta should still have no solution
    const meta = result.metaVars.get('?m0');
    expect(meta?.solution).toBeUndefined();
  });
});

describe('normalizeConstraintDepth', () => {
  test('same depth: returns constraint unchanged', () => {
    const ctx = [{ name: 'x', type: mkType() }];
    const constraint: Constraint = { ctx, meta: '?m', rhs: mkVar(0) };
    const result = normalizeConstraintDepth(constraint, ctx);
    expect(result).not.toBeNull();
    expect(result!.shifted).toBe(false);
    expect(result!.normalized.rhs).toEqual(mkVar(0));
    expect(result!.normalized.ctx).toBe(ctx);
  });

  test('deeper constraint: shifts Var down', () => {
    // Constraint at depth 3 with Var(2) → target depth 1 → Var(0)
    const targetCtx = [{ name: 'x', type: mkType() }];
    const constraintCtx = [
      { name: 'x', type: mkType() },
      { name: 'y', type: mkType() },
      { name: 'z', type: mkType() },
    ];
    const constraint: Constraint = { ctx: constraintCtx, meta: '?m', rhs: mkVar(2) };
    const result = normalizeConstraintDepth(constraint, targetCtx);
    expect(result).not.toBeNull();
    expect(result!.shifted).toBe(true);
    expect(result!.normalized.rhs).toEqual(mkVar(0));
    expect(result!.normalized.ctx).toBe(targetCtx);
  });

  test('deeper constraint with inner-scope var: returns null (stuck)', () => {
    // Constraint at depth 3 with Var(1) → target depth 1
    // Var(1) references depth-3 inner scope, can't shift to depth 1
    const targetCtx = [{ name: 'x', type: mkType() }];
    const constraintCtx = [
      { name: 'x', type: mkType() },
      { name: 'y', type: mkType() },
      { name: 'z', type: mkType() },
    ];
    const constraint: Constraint = { ctx: constraintCtx, meta: '?m', rhs: mkVar(1) };
    const result = normalizeConstraintDepth(constraint, targetCtx);
    expect(result).toBeNull();
  });

  test('shallower constraint: shifts Var up', () => {
    // Constraint at depth 1 with Var(0) → target depth 3 → Var(2)
    const targetCtx = [
      { name: 'x', type: mkType() },
      { name: 'y', type: mkType() },
      { name: 'z', type: mkType() },
    ];
    const constraintCtx = [{ name: 'x', type: mkType() }];
    const constraint: Constraint = { ctx: constraintCtx, meta: '?m', rhs: mkVar(0) };
    const result = normalizeConstraintDepth(constraint, targetCtx);
    expect(result).not.toBeNull();
    expect(result!.shifted).toBe(true);
    expect(result!.normalized.rhs).toEqual(mkVar(2));
    expect(result!.normalized.ctx).toBe(targetCtx);
  });

  test('Const terms are unaffected by depth difference', () => {
    const targetCtx = [{ name: 'x', type: mkType() }];
    const constraintCtx = [
      { name: 'x', type: mkType() },
      { name: 'y', type: mkType() },
    ];
    const constraint: Constraint = { ctx: constraintCtx, meta: '?m', rhs: mkConst('Nat') };
    const result = normalizeConstraintDepth(constraint, targetCtx);
    expect(result).not.toBeNull();
    expect(result!.normalized.rhs).toEqual(mkConst('Nat'));
  });

  test('App with Var shifts correctly', () => {
    // App(Succ, Var(2)) at depth 3 → depth 1 → App(Succ, Var(0))
    const targetCtx = [{ name: 'x', type: mkType() }];
    const constraintCtx = [
      { name: 'x', type: mkType() },
      { name: 'y', type: mkType() },
      { name: 'z', type: mkType() },
    ];
    const constraint: Constraint = {
      ctx: constraintCtx, meta: '?m',
      rhs: mkApp(mkConst('Succ'), mkVar(2)),
    };
    const result = normalizeConstraintDepth(constraint, targetCtx);
    expect(result).not.toBeNull();
    expect(result!.normalized.rhs).toEqual(mkApp(mkConst('Succ'), mkVar(0)));
  });

  test('rhsType is also shifted', () => {
    const targetCtx = [{ name: 'x', type: mkType() }];
    const constraintCtx = [
      { name: 'x', type: mkType() },
      { name: 'y', type: mkType() },
      { name: 'z', type: mkType() },
    ];
    const constraint: Constraint = {
      ctx: constraintCtx, meta: '?m',
      rhs: mkVar(2), rhsType: mkVar(2),
    };
    const result = normalizeConstraintDepth(constraint, targetCtx);
    expect(result).not.toBeNull();
    expect(result!.normalized.rhs).toEqual(mkVar(0));
    expect(result!.normalized.rhsType).toEqual(mkVar(0));
  });

  test('deeper constraint at exact boundary: Var(depthDiff) shifts to Var(0)', () => {
    // depthDiff=2, Var(2) → Var(0). minFreeVarIndex(Var(2))=2 >= 2, OK
    const targetCtx = [{ name: 'x', type: mkType() }];
    const constraintCtx = [
      { name: 'x', type: mkType() },
      { name: 'y', type: mkType() },
      { name: 'z', type: mkType() },
    ];
    const constraint: Constraint = { ctx: constraintCtx, meta: '?m', rhs: mkVar(2) };
    const result = normalizeConstraintDepth(constraint, targetCtx);
    expect(result).not.toBeNull();
    expect(result!.normalized.rhs).toEqual(mkVar(0));
  });

  test('deeper constraint just below boundary: returns null', () => {
    // depthDiff=2, Var(1) → would need Var(-1). minFreeVarIndex(Var(1))=1 < 2, stuck
    const targetCtx = [{ name: 'x', type: mkType() }];
    const constraintCtx = [
      { name: 'x', type: mkType() },
      { name: 'y', type: mkType() },
      { name: 'z', type: mkType() },
    ];
    const constraint: Constraint = { ctx: constraintCtx, meta: '?m', rhs: mkVar(1) };
    const result = normalizeConstraintDepth(constraint, targetCtx);
    expect(result).toBeNull();
  });
});

describe('solveConstraints cross-depth', () => {
  test('cross-depth Var-vs-Var conflict detected after normalization', () => {
    // Meta at depth 2, solved to Var(0)=y. Constraint at depth 3 with Var(2).
    // After normalization: Var(2) at depth 3 → Var(1) at depth 2. Var(1) ≠ Var(0) → conflict.
    const metaCtx = [{ name: 'x', type: mkConst('Nat') }, { name: 'y', type: mkConst('Nat') }];
    const metaVars = new Map<string, MetaVar>([
      ['?m0', { ctx: metaCtx, type: mkConst('Nat'), solution: mkVar(0) }]
    ]);
    const constraintCtx = [
      { name: 'x', type: mkConst('Nat') },
      { name: 'y', type: mkConst('Nat') },
      { name: 'z', type: mkConst('Nat') },
    ];
    const constraints: Constraint[] = [
      { ctx: constraintCtx, meta: '?m0', rhs: mkVar(2) }  // x at depth 3 → Var(1) at depth 2
    ];
    const definitions = defsWithNat();
    expect(() => solveConstraints(metaVars, constraints, undefined, definitions)).toThrow('Implicit argument conflict');
  });

  test('cross-depth Var-vs-Var agreement after normalization', () => {
    // Meta at depth 2, solved to Var(0)=y. Constraint at depth 3 with Var(1).
    // After normalization: Var(1) at depth 3 → Var(0) at depth 2. Var(0) = Var(0) → no conflict.
    const metaCtx = [{ name: 'x', type: mkConst('Nat') }, { name: 'y', type: mkConst('Nat') }];
    const metaVars = new Map<string, MetaVar>([
      ['?m0', { ctx: metaCtx, type: mkConst('Nat'), solution: mkVar(0) }]
    ]);
    const constraintCtx = [
      { name: 'x', type: mkConst('Nat') },
      { name: 'y', type: mkConst('Nat') },
      { name: 'z', type: mkConst('Nat') },
    ];
    const constraints: Constraint[] = [
      { ctx: constraintCtx, meta: '?m0', rhs: mkVar(1) }  // y at depth 3 → Var(0) at depth 2
    ];
    const definitions = defsWithNat();
    expect(() => solveConstraints(metaVars, constraints, undefined, definitions)).not.toThrow();
  });

  test('inner-scope constraint for unsolved meta goes stuck', () => {
    // Meta at depth 1, NO solution. Constraint at depth 3 with Var(0) (inner scope).
    // Normalization returns null → can't solve (inner-scope var), constraint goes stuck.
    const metaCtx = [{ name: 'x', type: mkConst('Nat') }];
    const metaVars = new Map<string, MetaVar>([
      ['?m0', { ctx: metaCtx, type: mkConst('Nat') }]
    ]);
    const constraintCtx = [
      { name: 'x', type: mkConst('Nat') },
      { name: 'y', type: mkConst('Nat') },
      { name: 'z', type: mkConst('Nat') },
    ];
    const constraints: Constraint[] = [
      { ctx: constraintCtx, meta: '?m0', rhs: mkVar(0) }
    ];
    const definitions = defsWithNat();
    const result = solveConstraints(metaVars, constraints, undefined, definitions);
    expect(result.constraints).toHaveLength(1);
    expect(result.metaVars.get('?m0')?.solution).toBeUndefined();
  });

  test('inner-scope constraint for already-solved meta detects named-Var-vs-constructor conflict', () => {
    // Meta at depth 1, solved to Zero. Constraint at depth 3 with Var(0)=z (inner scope).
    // Normalization returns null, but named Var z ≠ constructor Zero → conflict detected.
    const metaCtx = [{ name: 'x', type: mkConst('Nat') }];
    const metaVars = new Map<string, MetaVar>([
      ['?m0', { ctx: metaCtx, type: mkConst('Nat'), solution: mkConst('Zero') }]
    ]);
    const constraintCtx = [
      { name: 'x', type: mkConst('Nat') },
      { name: 'y', type: mkConst('Nat') },
      { name: 'z', type: mkConst('Nat') },
    ];
    const constraints: Constraint[] = [
      { ctx: constraintCtx, meta: '?m0', rhs: mkVar(0) }
    ];
    const definitions = defsWithNat();
    expect(() => solveConstraints(metaVars, constraints, undefined, definitions)).toThrow('Implicit argument conflict');
  });

  test('cross-depth Const conflict detected after normalization', () => {
    // Meta at depth 1, solved to Zero. Constraint at depth 3 with Succ(Var(2)).
    // After normalization: Succ(Var(2)) → Succ(Var(0)). Zero ≠ Succ(Var(0)) → conflict.
    const metaCtx = [{ name: 'x', type: mkConst('Nat') }];
    const metaVars = new Map<string, MetaVar>([
      ['?m0', { ctx: metaCtx, type: mkConst('Nat'), solution: mkConst('Zero') }]
    ]);
    const constraintCtx = [
      { name: 'x', type: mkConst('Nat') },
      { name: 'y', type: mkConst('Nat') },
      { name: 'z', type: mkConst('Nat') },
    ];
    const constraints: Constraint[] = [
      { ctx: constraintCtx, meta: '?m0', rhs: mkApp(mkConst('Succ'), mkVar(2)) }
    ];
    const definitions = defsWithNat();
    expect(() => solveConstraints(metaVars, constraints, undefined, definitions)).toThrow('Implicit argument conflict');
  });

  test('named Var-vs-constructor conflict detected', () => {
    // Meta solved to named var y, constraint says Succ(x).
    // Named variable y ≠ constructor Succ(x) → conflict.
    const metaCtx = [{ name: 'x', type: mkConst('Nat') }, { name: 'y', type: mkConst('Nat') }];
    const metaVars = new Map<string, MetaVar>([
      ['?m0', { ctx: metaCtx, type: mkConst('Nat'), solution: mkVar(0) }]  // y
    ]);
    const constraints: Constraint[] = [
      { ctx: metaCtx, meta: '?m0', rhs: mkApp(mkConst('Succ'), mkVar(1)) }  // Succ(x)
    ];
    const definitions = defsWithNat();
    expect(() => solveConstraints(metaVars, constraints, undefined, definitions)).toThrow('Implicit argument conflict');
  });

  test('wildcard Var-vs-constructor does NOT conflict', () => {
    // Meta solved to wildcard ?0, constraint says Succ(x).
    // Wildcard ?0 is flexible — it can match a constructor.
    const metaCtx = [{ name: 'x', type: mkConst('Nat') }, { name: '?0', type: mkConst('Nat') }];
    const metaVars = new Map<string, MetaVar>([
      ['?m0', { ctx: metaCtx, type: mkConst('Nat'), solution: mkVar(0) }]  // ?0
    ]);
    const constraints: Constraint[] = [
      { ctx: metaCtx, meta: '?m0', rhs: mkApp(mkConst('Succ'), mkVar(1)) }  // Succ(x)
    ];
    const definitions = defsWithNat();
    expect(() => solveConstraints(metaVars, constraints, undefined, definitions)).not.toThrow();
  });
});

// Helper: create a definitions map with Nat AND a `plus` function defined by pattern matching
function defsWithNatAndPlus(): DefinitionsMap {
  let defs = defsWithNat();
  // plus : Nat -> Nat -> Nat, defined by matching:
  //   plus Zero m = m
  //   plus (Succ n) m = Succ (plus n m)
  // Stored as Match(Hole("_scrutinee"), [clause_zero, clause_succ])
  // where each clause has 2 patterns.
  const plusType: TTKTerm = {
    tag: 'Binder', name: 'a', binderKind: { tag: 'BPi' },
    domain: mkConst('Nat'),
    body: {
      tag: 'Binder', name: 'b', binderKind: { tag: 'BPi' },
      domain: mkConst('Nat'),
      body: mkConst('Nat')
    }
  };
  const plusValue: TTKTerm = {
    tag: 'Match',
    scrutinee: { tag: 'Hole', id: '_scrutinee' },
    clauses: [
      {
        // plus Zero m = m
        patterns: [
          { tag: 'PCtor', name: 'Zero', args: [] },
          { tag: 'PVar', name: 'm' }
        ],
        rhs: { tag: 'Var', index: 0 }  // m (innermost binding)
      },
      {
        // plus (Succ n) m = Succ (plus n m)
        patterns: [
          { tag: 'PCtor', name: 'Succ', args: [{ tag: 'PVar', name: 'n' }] },
          { tag: 'PVar', name: 'm' }
        ],
        rhs: mkApp(mkConst('Succ'), mkApp(mkApp(mkConst('plus'), { tag: 'Var', index: 1 }), { tag: 'Var', index: 0 }))
      }
    ]
  };
  defs = addDefinition(defs, 'plus', plusType, plusValue);
  return defs;
}

describe('solveConstraints — case inversion', () => {
  test('Succ(?x) vs plus(?m, ?n) triggers case inversion to solve ?m := Succ(?k)', () => {
    // This models the core scenario from the doubleSum proof:
    // A meta has solution Succ(?x), and a constraint says it should equal plus(?m, ?n).
    // Case inversion on `plus` matches the Succ clause and solves ?m := Succ(?k).
    const defs = defsWithNatAndPlus();
    const ctx = [{ name: 'a', type: mkConst('Nat') }];

    const metaVars = new Map<string, MetaVar>([
      ['?target', { ctx, type: mkConst('Nat'), solution: mkApp(mkConst('Succ'), { tag: 'Meta', id: '?x' }) }],
      ['?x', { ctx, type: mkConst('Nat') }],
      ['?m', { ctx, type: mkConst('Nat') }],
      ['?n', { ctx, type: mkConst('Nat') }],
    ]);

    const constraints: Constraint[] = [
      { ctx, meta: '?target', rhs: mkApp(mkApp(mkConst('plus'), { tag: 'Meta', id: '?m' }), { tag: 'Meta', id: '?n' }) }
    ];

    const result = solveConstraints(metaVars, constraints, undefined, defs);

    // ?m should be solved to Succ(?case_inv_...) via case inversion
    const mSolution = result.metaVars.get('?m')?.solution;
    expect(mSolution).toBeDefined();
    // The head of ?m's solution should be Succ
    if (mSolution && mSolution.tag === 'App') {
      expect(mSolution.fn).toEqual(mkConst('Succ'));
    } else {
      expect(mSolution?.tag).toBe('App'); // force failure with info
    }
  });

  test('Zero vs plus(?m, ?n) triggers case inversion to solve ?m := Zero', () => {
    // When the solution is Zero, case inversion on `plus` matches the Zero clause.
    // plus Zero m = m, so ?m := Zero and the clause RHS is just m, i.e., ?n.
    const defs = defsWithNatAndPlus();
    const ctx = [{ name: 'a', type: mkConst('Nat') }];

    const metaVars = new Map<string, MetaVar>([
      ['?target', { ctx, type: mkConst('Nat'), solution: mkConst('Zero') }],
      ['?m', { ctx, type: mkConst('Nat') }],
      ['?n', { ctx, type: mkConst('Nat') }],
    ]);

    const constraints: Constraint[] = [
      { ctx, meta: '?target', rhs: mkApp(mkApp(mkConst('plus'), { tag: 'Meta', id: '?m' }), { tag: 'Meta', id: '?n' }) }
    ];

    const result = solveConstraints(metaVars, constraints, undefined, defs);

    // ?m should be solved to Zero
    const mSolution = result.metaVars.get('?m')?.solution;
    expect(mSolution).toEqual(mkConst('Zero'));

    // ?n should be solved to Zero (the overall solution)
    const nSolution = result.metaVars.get('?n')?.solution;
    expect(nSolution).toEqual(mkConst('Zero'));
  });
});

describe('solveConstraints — unsolved meta deferral', () => {
  test('defers when unification fails and RHS has unsolved metas', () => {
    // Meta solved to Succ(Var(0)), constraint says ?target := plus(?m, ?n).
    // Without case inversion on a non-plus definition, this should defer (not throw).
    const defs = defsWithNat(); // NO plus definition, so case inversion won't apply
    const ctx = [{ name: 'x', type: mkConst('Nat') }];

    const metaVars = new Map<string, MetaVar>([
      ['?target', { ctx, type: mkConst('Nat'), solution: mkApp(mkConst('Succ'), mkVar(0)) }],
      ['?m', { ctx, type: mkConst('Nat') }],
    ]);

    const constraints: Constraint[] = [
      { ctx, meta: '?target', rhs: mkApp(mkConst('SomeFunc'), { tag: 'Meta', id: '?m' }) }
    ];

    // Should NOT throw — deferred because RHS has unsolved meta
    expect(() => solveConstraints(metaVars, constraints, undefined, defs)).not.toThrow();
  });

  test('conflict detected despite unsolved metas in implicit positions', () => {
    // Models the leqCanonical soundness fix: LeqSucc(?impl, pleq) vs LeqSucc(?impl2, qleq)
    // The implicit args are unsolved metas, but the explicit args (Var 0 vs Var 1)
    // are different named variables. areTermsDefinitelyDifferent should catch this.
    const defs = addInductiveDefinition(
      defsWithNat(),
      'Leq',
      mkType(),
      [
        { name: 'LeqZero', type: mkConst('Leq') },
        { name: 'LeqSucc', type: {
          tag: 'Binder', name: 'p', binderKind: { tag: 'BPi' },
          domain: mkConst('Leq'), body: mkConst('Leq')
        }},
      ],
      []
    );

    const ctx = [
      { name: 'pleq', type: mkConst('Leq') },
      { name: 'qleq', type: mkConst('Leq') },
    ];

    const metaVars = new Map<string, MetaVar>([
      ['?a', {
        ctx,
        type: mkConst('Leq'),
        // Solution: LeqSucc(?impl, pleq) where ?impl is unsolved
        solution: mkApp(mkApp(mkConst('LeqSucc'), { tag: 'Meta', id: '?impl1' }), mkVar(1))
      }],
      ['?impl1', { ctx, type: mkConst('Nat') }],
      ['?impl2', { ctx, type: mkConst('Nat') }],
    ]);

    const constraints: Constraint[] = [
      // ?a := LeqSucc(?impl2, qleq) — different explicit arg (Var 0 vs Var 1)
      { ctx, meta: '?a', rhs: mkApp(mkApp(mkConst('LeqSucc'), { tag: 'Meta', id: '?impl2' }), mkVar(0)) }
    ];

    // Should THROW — LeqSucc(_,pleq) vs LeqSucc(_,qleq) differ in explicit arg
    expect(() => solveConstraints(metaVars, constraints, undefined, defs)).toThrow('Implicit argument conflict');
  });
});

describe('solveConstraints — structural-first unification', () => {
  test('decomposition of plus(X,Y) vs plus(?m,?n) without definitions', () => {
    // When both sides are `plus(concrete, concrete)` vs `plus(?m, ?n)`,
    // structural unification (without definitions) decomposes directly,
    // avoiding stuck Match expressions from delta-reduction.
    const defs = defsWithNatAndPlus();
    const ctx = [{ name: 'x', type: mkConst('Nat') }];

    const metaVars = new Map<string, MetaVar>([
      ['?target', {
        ctx, type: mkConst('Nat'),
        // Solution: plus(Var(0), Zero)
        solution: mkApp(mkApp(mkConst('plus'), mkVar(0)), mkConst('Zero'))
      }],
      ['?m', { ctx, type: mkConst('Nat') }],
      ['?n', { ctx, type: mkConst('Nat') }],
    ]);

    const constraints: Constraint[] = [
      { ctx, meta: '?target', rhs: mkApp(mkApp(mkConst('plus'), { tag: 'Meta', id: '?m' }), { tag: 'Meta', id: '?n' }) }
    ];

    const result = solveConstraints(metaVars, constraints, undefined, defs);

    // Structural decomposition: plus head matches, so ?m := Var(0) and ?n := Zero
    expect(result.metaVars.get('?m')?.solution).toEqual(mkVar(0));
    expect(result.metaVars.get('?n')?.solution).toEqual(mkConst('Zero'));
  });
});

describe('solveConstraints — fuel', () => {
  test('solver handles deep constraint chains without fuel exhaustion', () => {
    // Create a chain of metas: ?m0 := ?m1, ?m1 := ?m2, ..., ?mN := Zero
    // This requires N+1 solver iterations. With the old fuel (queue.length * 3),
    // this would fail for moderate N.
    const defs = defsWithNat();
    const ctx = [{ name: 'x', type: mkConst('Nat') }];

    const N = 15;
    const metaVars = new Map<string, MetaVar>();
    const constraints: Constraint[] = [];

    for (let i = 0; i <= N; i++) {
      metaVars.set(`?m${i}`, { ctx, type: mkConst('Nat') });
    }

    // Chain: ?m0 := ?m1, ?m1 := ?m2, ..., ?m(N-1) := ?mN
    for (let i = 0; i < N; i++) {
      constraints.push({ ctx, meta: `?m${i}`, rhs: { tag: 'Meta', id: `?m${i + 1}` } });
    }
    // Terminal: ?mN := Zero
    constraints.push({ ctx, meta: `?m${N}`, rhs: mkConst('Zero') });

    const result = solveConstraints(metaVars, constraints, undefined, defs);

    // All metas should have solutions (each points to the next in chain)
    for (let i = 0; i <= N; i++) {
      expect(result.metaVars.get(`?m${i}`)?.solution).toBeDefined();
    }
    // Terminal meta should be solved to Zero
    expect(result.metaVars.get(`?m${N}`)?.solution).toEqual(mkConst('Zero'));
    // No constraints should remain unsolved
    expect(result.constraints.length).toBe(0);
  });
});
