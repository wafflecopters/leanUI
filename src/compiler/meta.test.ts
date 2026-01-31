import { describe, test, expect } from 'vitest';
import { solveConstraints } from './meta';
import { mkVar, mkConst, mkApp, mkType } from './kernel';
import { MetaVar, Constraint, DefinitionsMap, createDefinitionsMap, addInductiveDefinition } from './term';

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
