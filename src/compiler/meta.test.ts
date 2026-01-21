import { describe, test, expect } from 'vitest';
import { solveConstraints } from './meta';
import { mkVar, mkConst, mkType } from './kernel';
import { MetaVar, Constraint } from './term';

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

  test('does not solve if meta already has a solution', () => {
    // Create a meta that already has a solution
    const existingSolution = mkConst('Bool');
    const metaVars = new Map<string, MetaVar>([
      ['?m0', { ctx: [{ name: 'x', type: mkType() }], type: mkType(), solution: existingSolution }]
    ]);

    // Try to give it a different solution
    const constraints: Constraint[] = [
      { ctx: [], meta: '?m0', rhs: mkConst('Nat') }
    ];

    const result = solveConstraints(metaVars, constraints);

    // The solution should remain unchanged (Bool, not Nat)
    const solvedMeta = result.metaVars.get('?m0');
    expect(solvedMeta?.solution).toEqual(existingSolution);
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
