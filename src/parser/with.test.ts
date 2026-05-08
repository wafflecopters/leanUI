import { describe, test, expect } from 'vitest';
import { Parser, tokenize } from './parser';

describe('with syntax parsing', () => {
  test('with keyword is tokenized', () => {
    const tokens = tokenize('with');
    expect(tokens.length).toBe(2); // WITH + EOF
    expect(tokens[0].type).toBe('WITH');
    expect(tokens[0].value).toBe('with');
  });

  test('ellipsis is tokenized', () => {
    const tokens = tokenize('...');
    expect(tokens.length).toBe(2); // ELLIPSIS + EOF
    expect(tokens[0].type).toBe('ELLIPSIS');
    expect(tokens[0].value).toBe('...');
  });

  test('dot is not confused with ellipsis', () => {
    // x.y is parsed as a qualified identifier (single IDENT token)
    // Let's test with a space-separated case instead
    const tokens = tokenize('. x');
    const types = tokens.map(t => t.type);
    expect(types).toContain('DOT');
    expect(types).not.toContain('ELLIPSIS');
  });

  test('ellipsis vs multiple dots', () => {
    // Three dots should be ELLIPSIS
    const ellipsis = tokenize('...');
    expect(ellipsis[0].type).toBe('ELLIPSIS');

    // Two dots should be DOT DOT
    const twoDots = tokenize('..');
    expect(twoDots[0].type).toBe('DOT');
    expect(twoDots[1].type).toBe('DOT');
  });

  test('parse basic with clause', () => {
    const source = `
isZero : Nat -> Bool
isZero n with n
  | Zero => True
  | Succ m => False
`;
    const parser = new Parser();
    const result = parser.parseDeclarations(source);

    expect(result).toHaveLength(1);
    const decl = result[0];
    expect(decl.kind).toBe('def');
    expect(decl.name).toBe('isZero');
    expect(decl.value?.tag).toBe('Match');

    const clause = (decl.value as any).clauses[0];
    expect(clause.rhs.tag).toBe('WithClause');
    expect(clause.rhs.scrutinees).toHaveLength(1);
    expect(clause.rhs.scrutinees[0]).toMatchObject({ tag: 'Var', index: 0 });
    expect(clause.rhs.clauses).toHaveLength(2);
    expect(clause.rhs.clauses[0].patterns[0]).toMatchObject({ tag: 'PCtor', name: 'Zero' });
    expect(clause.rhs.clauses[1].patterns[0]).toMatchObject({ tag: 'PCtor', name: 'Succ' });
  });

  test('parse with clause with multiple scrutinees', () => {
    const source = `
sameLeft : Nat -> Nat -> Nat
sameLeft x y with x, y
  | Zero, Zero => Zero
  | Zero, Succ y1 => Zero
  | Succ x1, Zero => Succ x1
  | Succ x1, Succ y1 => Succ x1
`;
    const parser = new Parser();
    const result = parser.parseDeclarations(source);

    expect(result).toHaveLength(1);
    const decl = result[0];
    const clause = (decl.value as any).clauses[0];
    expect(clause.rhs.tag).toBe('WithClause');
    expect(clause.rhs.scrutinees).toHaveLength(2);
    expect(clause.rhs.scrutinees[0]).toMatchObject({ tag: 'Var', index: 1 });
    expect(clause.rhs.scrutinees[1]).toMatchObject({ tag: 'Var', index: 0 });
    expect(clause.rhs.clauses).toHaveLength(4);
    expect(clause.rhs.clauses[0].patterns).toHaveLength(2);
    expect(clause.rhs.clauses[0].patterns[0]).toMatchObject({ tag: 'PCtor', name: 'Zero' });
    expect(clause.rhs.clauses[0].patterns[1]).toMatchObject({ tag: 'PCtor', name: 'Zero' });
  });
});
