import { describe, expect, test } from 'vitest';
import {
  occursInTT,
  prettyPrintLatexTT,
  prettyPrintTT,
  prettyPrintTerseTT,
  replaceHoleTT,
  shiftSurfaceTerm,
  substTT,
  TClause,
  TTerm,
} from './surface';

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

  test('pretty printers extend clause context and show named patterns', () => {
    const term: TTerm = {
      tag: 'Match',
      scrutinee: mkConst('scrutinee'),
      clauses: [{
        patterns: [{
          tag: 'PCtor',
          name: 'Wrap',
          args: [],
          namedArgs: [{ name: 'inner', pattern: { tag: 'PVar', name: 'x' } }],
        }],
        namedPatterns: [{ name: 'named', pattern: { tag: 'PVar', name: 'y' } }],
        rhs: mkVar(0),
      }],
    };

    expect(prettyPrintTT(term)).toContain('Wrap inner := x');
    expect(prettyPrintTT(term)).toContain('named := y');
    expect(prettyPrintTT(term)).toContain('=> y');

    expect(prettyPrintTerseTT(term)).toContain('Wrap inner := x');
    expect(prettyPrintTerseTT(term)).toContain('named := y');
    expect(prettyPrintTerseTT(term)).toContain('=> y');
  });

  test('prettyPrintLatexTT extends clause context and escapes named patterns', () => {
    const term: TTerm = {
      tag: 'Match',
      scrutinee: mkConst('scrutinee'),
      clauses: [{
        patterns: [{
          tag: 'PCtor',
          name: 'Wrap_ctor',
          args: [],
          namedArgs: [{ name: 'inner_arg', pattern: { tag: 'PVar', name: 'x_val' } }],
        }],
        namedPatterns: [{ name: 'named_pat', pattern: { tag: 'PVar', name: 'y_val' } }],
        rhs: mkVar(0),
      }],
    };

    const latex = prettyPrintLatexTT(term);
    expect(latex).toContain('Wrap\\_ctor');
    expect(latex).toContain('inner\\_arg := x\\_val');
    expect(latex).toContain('named\\_pat := y\\_val');
    expect(latex).toContain('\\Rightarrow y\\_val');
  });

  test('occursInTT accounts for clause binders', () => {
    const term: TTerm = {
      tag: 'Match',
      scrutinee: mkConst('scrutinee'),
      clauses: [{
        patterns: [],
        namedPatterns: [{ name: 'named', pattern: { tag: 'PVar', name: 'named' } }],
        rhs: mkVar(1),
      }],
    };

    expect(occursInTT(0, term)).toBe(true);
    expect(occursInTT(1, term)).toBe(false);
  });
});
