import { describe, test, expect } from 'vitest';
import { prettyPrint, TTKTerm, TTKClause, mkVar, mkConst, mkType } from './kernel';

describe('prettyPrint', () => {
  test('prints Var with correct name from context', () => {
    // de Bruijn index 0 should refer to context[0] (most recent binding)
    const term: TTKTerm = { tag: 'Var', index: 0 };

    // Context: most recent at index 0
    expect(prettyPrint(term, ['x', 'y', 'z'])).toBe('x');

    const term1: TTKTerm = { tag: 'Var', index: 1 };
    expect(prettyPrint(term1, ['x', 'y', 'z'])).toBe('y');

    const term2: TTKTerm = { tag: 'Var', index: 2 };
    expect(prettyPrint(term2, ['x', 'y', 'z'])).toBe('z');
  });

  test('prints Match clause with contextNames in correct order', () => {
    // Test that contextNames is used correctly for printing clause RHS
    // If context was built with: first 'A', then 'n', then 'h', then 'v', then 'fin'
    // then de Bruijn index 0 = fin, 1 = v, 2 = h, 3 = n, 4 = A
    // So contextNames should be ['fin', 'v', 'h', 'n', 'A'] (most recent first)

    const scrutinee: TTKTerm = mkVar(0); // dummy

    // RHS refers to variable at index 2 (should be 'h')
    const clause: TTKClause = {
      patterns: [{ tag: 'PWild', name: '_' }],
      rhs: mkVar(2),
      contextNames: ['fin', 'v', 'h', 'n', 'A'], // most recent first
    };

    const matchTerm: TTKTerm = {
      tag: 'Match',
      scrutinee,
      clauses: [clause],
    };

    const result = prettyPrint(matchTerm, []);
    // The RHS is Var(2), contextNames[2] = 'h', so it should print 'h'
    expect(result).toContain('=> h');
  });

  test('prints Match clause with contextNames - index 0 is most recent', () => {
    // Simulate what happens after checking:
    // Bindings were introduced in order: A, n, h (oldest to newest)
    // So de Bruijn index 0 = h (most recent), index 1 = n, index 2 = A
    // contextNames should be ['h', 'n', 'A'] (most recent first)

    const scrutinee: TTKTerm = mkVar(0);

    const clause: TTKClause = {
      patterns: [{ tag: 'PWild', name: '_' }],
      rhs: mkVar(0), // Should print as 'h' (most recent)
      contextNames: ['h', 'n', 'A'],
    };

    const matchTerm: TTKTerm = {
      tag: 'Match',
      scrutinee,
      clauses: [clause],
    };

    const result = prettyPrint(matchTerm, []);
    expect(result).toContain('=> h');

    // Now test index 2 which should be 'A' (oldest)
    const clause2: TTKClause = {
      patterns: [{ tag: 'PWild', name: '_' }],
      rhs: mkVar(2), // Should print as 'A'
      contextNames: ['h', 'n', 'A'],
    };

    const matchTerm2: TTKTerm = {
      tag: 'Match',
      scrutinee,
      clauses: [clause2],
    };

    const result2 = prettyPrint(matchTerm2, []);
    expect(result2).toContain('=> A');
  });

  test('elabArgs with contextNames prints correctly', () => {
    // When we have elabArgs, they should be printed using contextNames
    const scrutinee: TTKTerm = mkVar(0);

    const clause: TTKClause = {
      patterns: [{ tag: 'PWild', name: '_' }],
      rhs: mkConst('result'),
      elabArgs: [mkVar(2), mkVar(0), mkVar(1)], // A, h, n
      contextNames: ['h', 'n', 'A'], // most recent first: h=0, n=1, A=2
    };

    const matchTerm: TTKTerm = {
      tag: 'Match',
      scrutinee,
      clauses: [clause],
    };

    const result = prettyPrint(matchTerm, []);
    // elabArgs[0] = Var(2) = A, elabArgs[1] = Var(0) = h, elabArgs[2] = Var(1) = n
    expect(result).toContain('A h n => result');
  });
});
