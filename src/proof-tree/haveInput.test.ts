import { describe, expect, test } from 'vitest';
import { parseHaveInput } from './haveInput';

describe('parseHaveInput', () => {
  test('`h := expr` is a term have — the expression is the proof', () => {
    expect(parseHaveInput('h := divTwoPos ε epsPos')).toEqual({
      kind: 'term',
      name: 'h',
      expr: 'divTwoPos ε epsPos',
    });
  });

  test('`h : T` is a typed have — the proof is an open goal', () => {
    expect(parseHaveInput('h1 : 0 < ε / 2')).toEqual({
      kind: 'typed',
      name: 'h1',
      typeExpr: '0 < ε / 2',
    });
  });

  test.each(['?', '?_', '_', 'sorry'])('`h : T := %s` is the same as `h : T`', (hole) => {
    expect(parseHaveInput(`h1 : 0 < ε / 2 := ${hole}`)).toEqual({
      kind: 'typed',
      name: 'h1',
      typeExpr: '0 < ε / 2',
    });
  });

  test('`h : T := e` states the type AND gives the proof', () => {
    expect(parseHaveInput('h : 0 < ε := epsPos')).toEqual({
      kind: 'term',
      name: 'h',
      expr: 'epsPos',
    });
  });

  test('a type containing a colon-free binary operator survives intact', () => {
    expect(parseHaveInput('hb : ∀ x ∈ ℝ, 0 < x')).toEqual({
      kind: 'typed',
      name: 'hb',
      typeExpr: '∀ x ∈ ℝ, 0 < x',
    });
  });

  test.each([
    ['empty', ''],
    ['whitespace', '   '],
    ['a bare name', 'h'],
    ['a name with no proof and no type', 'h := '],
    ['a multi-word name', 'h k := e'],
  ])('%s is not a have', (_name, input) => {
    expect(parseHaveInput(input)).toBeNull();
  });

  test('surrounding whitespace is trimmed everywhere', () => {
    expect(parseHaveInput('   h1   :   0 < ε   ')).toEqual({
      kind: 'typed',
      name: 'h1',
      typeExpr: '0 < ε',
    });
  });
});
