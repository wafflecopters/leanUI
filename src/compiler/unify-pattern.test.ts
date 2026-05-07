import { describe, expect, test } from 'vitest';
import { TTKClause, TTKTerm } from './kernel';
import { unifyTerms } from './unify';

describe('pattern unification', () => {
  test('named-pattern binders contribute to match-clause depth', () => {
    const lhs: TTKTerm = {
      tag: 'App',
      fn: { tag: 'Meta', id: '?m' },
      arg: { tag: 'Var', index: 0 },
    };

    const clause: TTKClause = {
      patterns: [],
      namedPatterns: [{ name: 'named', pattern: { tag: 'PVar', name: 'y' } }],
      // Inside the clause RHS, Var(0) is the named-pattern binder `y`
      // and Var(1) is the outer spine variable we are abstracting over.
      rhs: { tag: 'Var', index: 1 },
    };

    const rhs: TTKTerm = {
      tag: 'Match',
      scrutinee: { tag: 'Const', name: 'scrutinee' },
      clauses: [clause],
    };

    const result = unifyTerms(lhs, rhs, { mode: 'pattern' });
    expect(result.success).toBe(true);
    if (!result.success) return;

    expect(result.metaConstraints).toHaveLength(1);
    expect(result.metaConstraints[0].isPatternSolution).toBe(true);

    const solution = result.metaConstraints[0].rhs;
    expect(solution.tag).toBe('Binder');
    if (solution.tag !== 'Binder') return;
    expect(solution.body.tag).toBe('Match');
    if (solution.body.tag !== 'Match') return;

    const renamedClause = solution.body.clauses[0];
    expect(renamedClause.rhs).toEqual({ tag: 'Var', index: 1 });
  });
});
