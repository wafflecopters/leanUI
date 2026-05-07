import { describe, expect, test } from 'vitest';
import { shiftSurfaceTerm, substTT, replaceHoleTT, TClause, TTerm } from './surface';

const mkVar = (index: number): TTerm => ({ tag: 'Var', index });
const mkConst = (name: string): TTerm => ({ tag: 'Const', name });

describe('surface Match helpers', () => {
  test('substTT respects clause-level named-pattern binders', () => {
    const clause: TClause = {
      patterns: [],
      namedPatterns: [{ name: 'named', pattern: { tag: 'PVar', name: 'named' } }],
      rhs: mkVar(1),
    };
    const term: TTerm = {
      tag: 'Match',
      scrutinee: mkConst('scrutinee'),
      clauses: [clause],
    };

    const result = substTT(0, mkConst('replacement'), term);
    expect(result.tag).toBe('Match');
    if (result.tag !== 'Match') return;

    expect(result.clauses[0].rhs).toEqual(mkConst('replacement'));
    expect(result.clauses[0].namedPatterns).toEqual(clause.namedPatterns);
  });

  test('shiftSurfaceTerm shifts free vars past clause binders', () => {
    const clause: TClause = {
      patterns: [],
      namedPatterns: [{ name: 'named', pattern: { tag: 'PVar', name: 'named' } }],
      rhs: mkVar(1),
    };
    const term: TTerm = {
      tag: 'Match',
      scrutinee: mkConst('scrutinee'),
      clauses: [clause],
    };

    const result = shiftSurfaceTerm(1, term, 0);
    expect(result.tag).toBe('Match');
    if (result.tag !== 'Match') return;

    expect(result.clauses[0].rhs).toEqual(mkVar(2));
  });

  test('replaceHoleTT preserves named-pattern metadata in clauses', () => {
    const clause: TClause = {
      patterns: [],
      namedPatterns: [{ name: 'named', pattern: { tag: 'PVar', name: 'named' } }],
      rhs: { tag: 'Hole', id: 'goal', type: mkConst('Type'), context: [] },
    };
    const term: TTerm = {
      tag: 'Match',
      scrutinee: mkConst('scrutinee'),
      clauses: [clause],
    };

    const result = replaceHoleTT(term, 'goal', mkConst('done'));
    expect(result.tag).toBe('Match');
    if (result.tag !== 'Match') return;

    expect(result.clauses[0].rhs).toEqual(mkConst('done'));
    expect(result.clauses[0].namedPatterns).toEqual(clause.namedPatterns);
  });
});
