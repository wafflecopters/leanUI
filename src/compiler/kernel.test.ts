import { describe, test, expect } from 'vitest';
import {
  prettyPrint, prettyPrintFormatted, prettyPrintLatex, occursIn, isDefinitionallyEqual, fillHole, TTKTerm, TTKClause, mkVar, mkConst, mkType,
  mkULit, mkLSucc, mkLMax, mkLIMax, levelLeq, collectLevelVars, levelGeq
} from './kernel';

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

  test('prints named ctor args and clause-level named patterns', () => {
    const clause: TTKClause = {
      patterns: [{
        tag: 'PCtor',
        name: 'Wrap',
        args: [],
        namedArgs: [{ name: 'inner', pattern: { tag: 'PVar', name: 'x' } }],
      }],
      namedPatterns: [{ name: 'named', pattern: { tag: 'PVar', name: 'y' } }],
      rhs: mkVar(0),
    };

    const result = prettyPrint({
      tag: 'Match',
      scrutinee: mkConst('scrutinee'),
      clauses: [clause],
    }, []);

    expect(result).toContain('Wrap inner := x');
    expect(result).toContain('named := y');
    expect(result).toContain('=> y');
  });

  test('fillHole preserves clause metadata on match terms', () => {
    const clause: TTKClause = {
      patterns: [],
      namedPatterns: [{ name: 'named', pattern: { tag: 'PVar', name: 'y' } }],
      rhs: { tag: 'Hole', id: 'goal' },
      contextNames: ['y'],
    };

    const result = fillHole({
      tag: 'Match',
      scrutinee: mkConst('scrutinee'),
      clauses: [clause],
    }, 'goal', mkConst('done'));

    expect(result.tag).toBe('Match');
    if (result.tag !== 'Match') return;

    expect(result.clauses[0].rhs).toEqual(mkConst('done'));
    expect(result.clauses[0].namedPatterns).toEqual(clause.namedPatterns);
    expect(result.clauses[0].contextNames).toEqual(clause.contextNames);
  });
});

describe('prettyPrintLatex', () => {
  test('escapes context names and named patterns in match clauses', () => {
    const clause: TTKClause = {
      patterns: [{
        tag: 'PCtor',
        name: 'Wrap_ctor',
        args: [],
        namedArgs: [{ name: 'inner_arg', pattern: { tag: 'PVar', name: 'x_val' } }],
      }],
      namedPatterns: [{ name: 'named_pat', pattern: { tag: 'PVar', name: 'y_val' } }],
      rhs: mkVar(0),
    };

    const latex = prettyPrintLatex({
      tag: 'Match',
      scrutinee: mkConst('scrutinee'),
      clauses: [clause],
    });

    expect(latex).toContain('Wrap\\_ctor');
    expect(latex).toContain('inner\\_arg := x\\_val');
    expect(latex).toContain('named\\_pat := y\\_val');
    expect(latex).toContain('\\Rightarrow y\\_val');
  });
});

describe('occursIn', () => {
  test('accounts for clause binders in match branches', () => {
    const term: TTKTerm = {
      tag: 'Match',
      scrutinee: mkConst('scrutinee'),
      clauses: [{
        patterns: [],
        namedPatterns: [{ name: 'named', pattern: { tag: 'PVar', name: 'named' } }],
        rhs: mkVar(1),
      }],
    };

    expect(occursIn(0, term)).toBe(true);
    expect(occursIn(1, term)).toBe(false);
  });
});

describe('isDefinitionallyEqual', () => {
  test('distinguishes stuck matches with different patterns', () => {
    const left: TTKTerm = {
      tag: 'Match',
      scrutinee: mkConst('scrutinee'),
      clauses: [{
        patterns: [{ tag: 'PCtor', name: 'Zero', args: [] }],
        rhs: mkConst('same'),
      }],
    };
    const right: TTKTerm = {
      tag: 'Match',
      scrutinee: mkConst('scrutinee'),
      clauses: [{
        patterns: [{ tag: 'PCtor', name: 'Succ', args: [{ tag: 'PVar', name: 'n' }] }],
        rhs: mkConst('same'),
      }],
    };

    expect(isDefinitionallyEqual(left, right)).toBe(false);
  });

  test('preserves parentheses for function type domains', () => {
    // Type: ((A : Type) -> A -> A) -> Nat -> Nat
    // The domain is itself a function type, so parens must be preserved
    const innerPi: TTKTerm = {
      tag: 'Binder',
      binderKind: { tag: 'BPi' },
      name: 'A',
      domain: mkType(0), // Type 0
      body: {
        tag: 'Binder',
        binderKind: { tag: 'BPi' },
        name: '_',
        domain: mkVar(0), // A
        body: mkVar(1), // A (shifted)
      },
    };

    const outerPi: TTKTerm = {
      tag: 'Binder',
      binderKind: { tag: 'BPi' },
      name: 'f',
      domain: innerPi,
      body: {
        tag: 'Binder',
        binderKind: { tag: 'BPi' },
        name: '_',
        domain: mkConst('Nat'),
        body: mkConst('Nat'),
      },
    };

    const result = prettyPrint(outerPi, []);
    // Should keep parentheses around the function type domain
    // Not flatten to "(A : Type) -> A -> A -> Nat -> Nat"
    expect(result).toContain('((A : Type) -> A -> A)');
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

// ============================================================================
// Level Comparison Tests (levelLeq)
// ============================================================================

describe('levelLeq - Symbolic Universe Level Comparison', () => {
  // Helper to create a level variable (Var with de Bruijn index)
  const mkLevelVar = (index: number): TTKTerm => mkVar(index);

  describe('Concrete level comparisons', () => {
    test('0 ≤ 0', () => {
      expect(levelLeq(mkULit(0), mkULit(0))).toBe(true);
    });

    test('0 ≤ 1', () => {
      expect(levelLeq(mkULit(0), mkULit(1))).toBe(true);
    });

    test('0 ≤ 5', () => {
      expect(levelLeq(mkULit(0), mkULit(5))).toBe(true);
    });

    test('1 ≤ 1', () => {
      expect(levelLeq(mkULit(1), mkULit(1))).toBe(true);
    });

    test('1 ≤ 2', () => {
      expect(levelLeq(mkULit(1), mkULit(2))).toBe(true);
    });

    test('2 ≤ 1 is false', () => {
      expect(levelLeq(mkULit(2), mkULit(1))).toBe(false);
    });

    test('5 ≤ 3 is false', () => {
      expect(levelLeq(mkULit(5), mkULit(3))).toBe(false);
    });

    test('1 ≤ 0 is false', () => {
      expect(levelLeq(mkULit(1), mkULit(0))).toBe(false);
    });
  });

  describe('Successor (Succ) comparisons', () => {
    test('Succ(0) ≤ Succ(0)', () => {
      expect(levelLeq(mkLSucc(mkULit(0)), mkLSucc(mkULit(0)))).toBe(true);
    });

    test('Succ(0) ≤ Succ(1)', () => {
      expect(levelLeq(mkLSucc(mkULit(0)), mkLSucc(mkULit(1)))).toBe(true);
    });

    test('Succ(Succ(0)) ≤ Succ(0) is false', () => {
      expect(levelLeq(mkLSucc(mkLSucc(mkULit(0))), mkLSucc(mkULit(0)))).toBe(false);
    });

    test('0 ≤ Succ(0)', () => {
      expect(levelLeq(mkULit(0), mkLSucc(mkULit(0)))).toBe(true);
    });

    test('Succ(0) ≤ 0 is false', () => {
      expect(levelLeq(mkLSucc(mkULit(0)), mkULit(0))).toBe(false);
    });

    test('u ≤ Succ(u) - variable under successor', () => {
      const u = mkLevelVar(0);
      expect(levelLeq(u, mkLSucc(u))).toBe(true);
    });

    test('Succ(u) ≤ u is false', () => {
      const u = mkLevelVar(0);
      expect(levelLeq(mkLSucc(u), u)).toBe(false);
    });

    test('Succ(u) ≤ Succ(u)', () => {
      const u = mkLevelVar(0);
      expect(levelLeq(mkLSucc(u), mkLSucc(u))).toBe(true);
    });

    test('Succ(Succ(u)) ≤ Succ(u) is false', () => {
      const u = mkLevelVar(0);
      expect(levelLeq(mkLSucc(mkLSucc(u)), mkLSucc(u))).toBe(false);
    });
  });

  describe('Max comparisons', () => {
    test('u ≤ Max(u, v)', () => {
      const u = mkLevelVar(0);
      const v = mkLevelVar(1);
      expect(levelLeq(u, mkLMax(u, v))).toBe(true);
    });

    test('v ≤ Max(u, v)', () => {
      const u = mkLevelVar(0);
      const v = mkLevelVar(1);
      expect(levelLeq(v, mkLMax(u, v))).toBe(true);
    });

    test('Max(u, v) ≤ Max(u, v)', () => {
      const u = mkLevelVar(0);
      const v = mkLevelVar(1);
      expect(levelLeq(mkLMax(u, v), mkLMax(u, v))).toBe(true);
    });

    test('Max(u, v) ≤ u is unknown (cannot determine)', () => {
      const u = mkLevelVar(0);
      const v = mkLevelVar(1);
      // We can't prove Max(u,v) ≤ u unless we know v ≤ u
      expect(levelLeq(mkLMax(u, v), u)).toBe('unknown');
    });

    test('Max(0, 1) ≤ 1', () => {
      expect(levelLeq(mkLMax(mkULit(0), mkULit(1)), mkULit(1))).toBe(true);
    });

    test('Max(0, 1) ≤ 0 is false', () => {
      expect(levelLeq(mkLMax(mkULit(0), mkULit(1)), mkULit(0))).toBe(false);
    });

    test('Max(2, 3) ≤ 3', () => {
      expect(levelLeq(mkLMax(mkULit(2), mkULit(3)), mkULit(3))).toBe(true);
    });

    test('Max(2, 3) ≤ 4', () => {
      expect(levelLeq(mkLMax(mkULit(2), mkULit(3)), mkULit(4))).toBe(true);
    });

    test('0 ≤ Max(u, v)', () => {
      const u = mkLevelVar(0);
      const v = mkLevelVar(1);
      expect(levelLeq(mkULit(0), mkLMax(u, v))).toBe(true);
    });

    test('Max(u, 0) = u semantically, u ≤ Max(u, 0)', () => {
      const u = mkLevelVar(0);
      expect(levelLeq(u, mkLMax(u, mkULit(0)))).toBe(true);
    });
  });

  describe('Variable comparisons', () => {
    test('Var(0) ≤ Var(0) - same variable', () => {
      expect(levelLeq(mkLevelVar(0), mkLevelVar(0))).toBe(true);
    });

    test('Var(1) ≤ Var(1) - same variable', () => {
      expect(levelLeq(mkLevelVar(1), mkLevelVar(1))).toBe(true);
    });

    test('Var(0) ≤ Var(1) - different variables, unknown', () => {
      expect(levelLeq(mkLevelVar(0), mkLevelVar(1))).toBe('unknown');
    });

    test('0 ≤ Var(0) - zero is smallest', () => {
      expect(levelLeq(mkULit(0), mkLevelVar(0))).toBe(true);
    });

    test('Var(0) ≤ 0 is unknown', () => {
      // We don't know if u ≥ 0 without more info (though in practice levels are ≥ 0)
      // Conservative: return 'unknown' or we could return true since all levels ≥ 0
      // Following Lean: levels are always ≥ 0, so this should be 'unknown'
      // Actually, Var(0) could be 0, in which case 0 ≤ 0 is true
      // So this is actually determinable as true (all levels are ≥ 0)
      expect(levelLeq(mkLevelVar(0), mkULit(0))).toBe('unknown');
    });

    test('1 ≤ Var(0) is unknown', () => {
      // 1 might be > u if u = 0
      expect(levelLeq(mkULit(1), mkLevelVar(0))).toBe('unknown');
    });
  });

  describe('IMax comparisons', () => {
    // IMax(a, b) = if b = 0 then 0 else Max(a, b)

    test('IMax(u, 0) = 0, so IMax(u, 0) ≤ 0', () => {
      const u = mkLevelVar(0);
      expect(levelLeq(mkLIMax(u, mkULit(0)), mkULit(0))).toBe(true);
    });

    test('IMax(u, 0) ≤ v', () => {
      const u = mkLevelVar(0);
      const v = mkLevelVar(1);
      // IMax(u, 0) = 0, and 0 ≤ v
      expect(levelLeq(mkLIMax(u, mkULit(0)), v)).toBe(true);
    });

    test('IMax(u, Succ(v)) behaves like Max(u, Succ(v))', () => {
      const u = mkLevelVar(0);
      const v = mkLevelVar(1);
      // IMax(u, Succ(v)) = Max(u, Succ(v)) since Succ(v) ≠ 0
      // u ≤ IMax(u, Succ(v)) should be true
      expect(levelLeq(u, mkLIMax(u, mkLSucc(v)))).toBe(true);
    });

    test('IMax(1, 2) = Max(1, 2) = 2, so IMax(1, 2) ≤ 2', () => {
      expect(levelLeq(mkLIMax(mkULit(1), mkULit(2)), mkULit(2))).toBe(true);
    });

    test('3 ≤ IMax(1, 2) is false (IMax(1,2) = 2)', () => {
      expect(levelLeq(mkULit(3), mkLIMax(mkULit(1), mkULit(2)))).toBe(false);
    });
  });

  describe('Complex/nested comparisons', () => {
    test('Max(u, v) ≤ Max(Max(u, v), w)', () => {
      const u = mkLevelVar(0);
      const v = mkLevelVar(1);
      const w = mkLevelVar(2);
      expect(levelLeq(mkLMax(u, v), mkLMax(mkLMax(u, v), w))).toBe(true);
    });

    test('u ≤ Max(u, Max(v, w))', () => {
      const u = mkLevelVar(0);
      const v = mkLevelVar(1);
      const w = mkLevelVar(2);
      expect(levelLeq(u, mkLMax(u, mkLMax(v, w)))).toBe(true);
    });

    test('Succ(Max(u, v)) ≤ Max(Succ(u), Succ(v))', () => {
      const u = mkLevelVar(0);
      const v = mkLevelVar(1);
      // Succ(Max(u,v)) = Max(Succ(u), Succ(v))
      expect(levelLeq(mkLSucc(mkLMax(u, v)), mkLMax(mkLSucc(u), mkLSucc(v)))).toBe(true);
    });
  });
});

// ============================================================================
// collectLevelVars Tests
// ============================================================================

describe('collectLevelVars', () => {
  const mkLevelVar = (index: number): TTKTerm => mkVar(index);

  test('concrete level has no vars', () => {
    expect(collectLevelVars(mkULit(5))).toEqual(new Set());
  });

  test('single variable', () => {
    expect(collectLevelVars(mkLevelVar(0))).toEqual(new Set([0]));
  });

  test('Succ of variable', () => {
    expect(collectLevelVars(mkLSucc(mkLevelVar(2)))).toEqual(new Set([2]));
  });

  test('Max of two different variables', () => {
    const u = mkLevelVar(0);
    const v = mkLevelVar(1);
    expect(collectLevelVars(mkLMax(u, v))).toEqual(new Set([0, 1]));
  });

  test('Max of same variable', () => {
    const u = mkLevelVar(0);
    expect(collectLevelVars(mkLMax(u, u))).toEqual(new Set([0]));
  });

  test('nested Max with three variables', () => {
    const u = mkLevelVar(0);
    const v = mkLevelVar(1);
    const w = mkLevelVar(2);
    expect(collectLevelVars(mkLMax(u, mkLMax(v, w)))).toEqual(new Set([0, 1, 2]));
  });

  test('IMax collects vars from both sides', () => {
    const u = mkLevelVar(0);
    const v = mkLevelVar(1);
    expect(collectLevelVars(mkLIMax(u, v))).toEqual(new Set([0, 1]));
  });

  test('complex expression with repeated vars', () => {
    const u = mkLevelVar(0);
    const v = mkLevelVar(1);
    // Max(Succ(u), Max(v, Succ(Succ(u))))
    const expr = mkLMax(mkLSucc(u), mkLMax(v, mkLSucc(mkLSucc(u))));
    expect(collectLevelVars(expr)).toEqual(new Set([0, 1]));
  });
});

// ============================================================================
// levelGeq Tests (convenience wrapper)
// ============================================================================

describe('levelGeq', () => {
  test('levelGeq(a, b) = levelLeq(b, a)', () => {
    expect(levelGeq(mkULit(2), mkULit(1))).toBe(true);
    expect(levelGeq(mkULit(1), mkULit(2))).toBe(false);
    expect(levelGeq(mkULit(1), mkULit(1))).toBe(true);
  });

  test('levelGeq with variables', () => {
    const u = mkVar(0);
    const v = mkVar(1);
    expect(levelGeq(mkLMax(u, v), u)).toBe(true);
    expect(levelGeq(u, mkLMax(u, v))).toBe('unknown');
  });
});
