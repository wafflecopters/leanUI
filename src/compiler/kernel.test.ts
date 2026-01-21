import { describe, test, expect } from 'vitest';
import { prettyPrint, prettyPrintFormatted, TTKTerm, TTKClause, mkVar, mkConst, mkType } from './kernel';

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

describe('prettyPrintFormatted', () => {
  test('formats Match clauses on separate lines with indentation', () => {
    const scrutinee: TTKTerm = mkVar(0);

    const clause1: TTKClause = {
      patterns: [{ tag: 'PCtor', name: 'Zero', args: [] }],
      rhs: mkConst('result1'),
      contextNames: [],
    };

    const clause2: TTKClause = {
      patterns: [{ tag: 'PCtor', name: 'Succ', args: [{ tag: 'PVar', name: 'n' }] }],
      rhs: mkConst('result2'),
      contextNames: ['n'],
    };

    const matchTerm: TTKTerm = {
      tag: 'Match',
      scrutinee,
      clauses: [clause1, clause2],
    };

    const result = prettyPrintFormatted(matchTerm, ['x']);
    // Should have clauses on separate lines
    expect(result).toContain('\n');
    expect(result).toContain('| Zero => result1');
    expect(result).toContain('| (Succ n) => result2');
  });

  test('formats nested Match with proper indentation', () => {
    // Inner match
    const innerMatch: TTKTerm = {
      tag: 'Match',
      scrutinee: mkVar(0),
      clauses: [{
        patterns: [{ tag: 'PCtor', name: 'True', args: [] }],
        rhs: mkConst('yes'),
        contextNames: [],
      }, {
        patterns: [{ tag: 'PCtor', name: 'False', args: [] }],
        rhs: mkConst('no'),
        contextNames: [],
      }],
    };

    // Outer match with inner match as RHS
    const outerMatch: TTKTerm = {
      tag: 'Match',
      scrutinee: mkVar(1),
      clauses: [{
        patterns: [{ tag: 'PCtor', name: 'Some', args: [{ tag: 'PVar', name: 'x' }] }],
        rhs: innerMatch,
        contextNames: ['x'],
      }],
    };

    const result = prettyPrintFormatted(outerMatch, ['b', 'a']);
    // Outer match and inner match should both have newlines
    const lines = result.split('\n');
    expect(lines.length).toBeGreaterThan(2);
    // Inner clauses should be more indented than outer
    expect(result).toMatch(/\| \(Some x\) =>/);
  });

  test('formats Let body on new line with indentation', () => {
    const letTerm: TTKTerm = {
      tag: 'Binder',
      name: 'x',
      domain: mkType(),
      binderKind: {
        tag: 'BLet',
        defVal: mkConst('someValue'),
      },
      body: mkVar(0), // x
    };

    const result = prettyPrintFormatted(letTerm, []);
    expect(result).toContain('\n');
    expect(result).toContain('let x : Type = someValue in');
    // Body should be on the next line, indented
    const lines = result.split('\n');
    expect(lines.length).toBe(2);
    expect(lines[1]).toMatch(/^\s+x\)$/);
  });

  test('formats nested Let with increasing indentation', () => {
    // let x = 1 in let y = 2 in (x, y)
    const innerLet: TTKTerm = {
      tag: 'Binder',
      name: 'y',
      domain: mkConst('Nat'),
      binderKind: {
        tag: 'BLet',
        defVal: mkConst('two'),
      },
      body: {
        tag: 'App',
        fn: { tag: 'App', fn: mkConst('pair'), arg: mkVar(1) }, // x
        arg: mkVar(0), // y
      },
    };

    const outerLet: TTKTerm = {
      tag: 'Binder',
      name: 'x',
      domain: mkConst('Nat'),
      binderKind: {
        tag: 'BLet',
        defVal: mkConst('one'),
      },
      body: innerLet,
    };

    const result = prettyPrintFormatted(outerLet, []);
    const lines = result.split('\n');
    // Should have 3 lines: outer let, inner let, body
    expect(lines.length).toBe(3);
    // Each level should be more indented
    // Line 0: "(let x : Nat = one in"
    // Line 1: "  (let y : Nat = two in"
    // Line 2: "    (pair x y)))"
    expect(lines[1]).toMatch(/^\s{2}\(let y/);
    expect(lines[2]).toMatch(/^\s{4}\(pair/);
  });

  test('custom indent size', () => {
    const letTerm: TTKTerm = {
      tag: 'Binder',
      name: 'x',
      domain: mkType(),
      binderKind: {
        tag: 'BLet',
        defVal: mkConst('val'),
      },
      body: mkVar(0),
    };

    const result = prettyPrintFormatted(letTerm, [], undefined, { indentSize: 4 });
    const lines = result.split('\n');
    expect(lines.length).toBe(2);
    // Body should be indented by 4 spaces
    expect(lines[1]).toMatch(/^\s{4}x\)$/);
  });

  test('Match with elabArgs formats correctly', () => {
    const scrutinee: TTKTerm = { tag: 'Hole', id: '_scrutinee' };

    const clause: TTKClause = {
      patterns: [{ tag: 'PWild', name: '_' }],
      rhs: mkVar(0),
      elabArgs: [mkConst('A'), mkVar(0), mkConst('VCons')],
      contextNames: ['h', 'n', 'A'],
    };

    const matchTerm: TTKTerm = {
      tag: 'Match',
      scrutinee,
      clauses: [clause],
    };

    const result = prettyPrintFormatted(matchTerm, []);
    expect(result).toContain('\n');
    expect(result).toContain('| A h VCons => h');
  });
});
