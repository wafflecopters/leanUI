import { describe, expect, test } from 'vitest';
import { mkVar, TTKTerm } from './kernel';
import { transformVarsInTerm } from './term';

describe('transformVarsInTerm', () => {
  test('extends context through match-clause binders and preserves clause metadata', () => {
    const term: TTKTerm = {
      tag: 'Match',
      scrutinee: mkVar(0),
      clauses: [{
        patterns: [],
        namedPatterns: [{ name: 'named', pattern: { tag: 'PVar', name: 'named' } }],
        // Var(1) refers to the outer variable once the named pattern binder is in scope.
        rhs: mkVar(1),
      }],
    };

    const transformed = transformVarsInTerm(term, (index, context) => mkVar(index + context.length));
    expect(transformed.tag).toBe('Match');
    if (transformed.tag !== 'Match') return;

    expect(transformed.scrutinee).toEqual(mkVar(0));
    expect(transformed.clauses[0].namedPatterns).toEqual(term.clauses[0].namedPatterns);
    expect(transformed.clauses[0].rhs).toEqual(mkVar(2));
  });
});
