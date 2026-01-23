/**
 * Tests for elaboration of implicit arguments
 * Verifies that pattern padding and RHS de Bruijn indices are correct
 */

import { describe, test, expect } from 'bun:test';
import { parseDeclarations } from '../parser/parser';
import { elabToKernelWithMap, extractNamedArgMap, countParameters } from './elab';
import { prettyPrintPattern } from './kernel';
import { TTKTerm, TTKPattern } from './kernel';

function getPatterns(term: TTKTerm): TTKPattern[] {
  if (term.tag === 'Match' && term.clauses.length > 0) {
    return term.clauses[0].patterns;
  }
  return [];
}

function getRhs(term: TTKTerm): TTKTerm | null {
  if (term.tag === 'Match' && term.clauses.length > 0) {
    return term.clauses[0].rhs;
  }
  return null;
}

function getVarIndex(term: TTKTerm): number | null {
  if (term.tag === 'Var') return term.index;
  return null;
}

function getLambdaBody(term: TTKTerm): TTKTerm | null {
  if (term.tag === 'Binder' && term.binderKind.tag === 'BLam') {
    return term.body;
  }
  return null;
}

function getAppArgs(term: TTKTerm): { fn: TTKTerm, args: TTKTerm[] } | null {
  const args: TTKTerm[] = [];
  let current = term;
  while (current.tag === 'App') {
    args.unshift(current.arg);
    current = current.fn;
  }
  if (args.length > 0) {
    return { fn: current, args };
  }
  return null;
}

describe('Implicit argument elaboration', () => {
  describe('const function', () => {
    // const : {A : Type} -> {B : Type} -> A -> B -> A
    // const a = \ _ => a
    // Expected: 3 patterns [_, _, a], RHS lambda with body = Var(1)

    const source = `
const : {A : Type} -> {B : Type} -> A -> B -> A
const a = \\ _ => a
`;
    const decls = parseDeclarations(source);
    const decl = decls.find(d => d.name === 'const')!;
    const namedArgMap = extractNamedArgMap(decl.type!);
    const totalArity = countParameters(decl.type!);
    const kernel = elabToKernelWithMap(decl.value!, new Map(), [], [], namedArgMap, undefined, totalArity);
    const patterns = getPatterns(kernel);
    const rhs = getRhs(kernel);

    test('has 3 patterns', () => {
      expect(patterns.length).toBe(3);
    });

    test('first two are wildcards for implicit params', () => {
      expect(patterns[0].tag).toBe('PWild');
      expect(patterns[1].tag).toBe('PWild');
    });

    test('third is var pattern for explicit param a', () => {
      expect(patterns[2].tag).toBe('PCtor');
      if (patterns[2].tag === 'PCtor') {
        expect(patterns[2].name).toBe('a');
        expect(patterns[2].args.length).toBe(0);
      }
    });

    test('RHS is lambda', () => {
      expect(rhs?.tag).toBe('Binder');
      if (rhs?.tag === 'Binder') {
        expect(rhs.binderKind.tag).toBe('BLam');
      }
    });

    test('lambda body correctly refers to a at index 1', () => {
      const body = getLambdaBody(rhs!);
      expect(getVarIndex(body!)).toBe(1);
    });
  });

  describe('swap function', () => {
    // swap : {A B C : Type} -> (f : A -> B -> C) -> B -> A -> C
    // swap f = \ x y => f y x
    // Expected: 4 patterns [_, _, _, f], RHS = \x => \y => (f y x)

    const source = `
swap : {A B C : Type} -> (f : A -> B -> C) -> B -> A -> C
swap f = \\ x y => f y x
`;
    const decls = parseDeclarations(source);
    const decl = decls.find(d => d.name === 'swap')!;
    const namedArgMap = extractNamedArgMap(decl.type!);
    const totalArity = countParameters(decl.type!);
    const kernel = elabToKernelWithMap(decl.value!, new Map(), [], [], namedArgMap, undefined, totalArity);
    const patterns = getPatterns(kernel);
    const rhs = getRhs(kernel);

    test('has 4 patterns', () => {
      expect(patterns.length).toBe(4);
    });

    test('first three are wildcards for implicit params', () => {
      expect(patterns[0].tag).toBe('PWild');
      expect(patterns[1].tag).toBe('PWild');
      expect(patterns[2].tag).toBe('PWild');
    });

    test('fourth is var pattern for explicit param f', () => {
      expect(patterns[3].tag).toBe('PCtor');
      if (patterns[3].tag === 'PCtor') {
        expect(patterns[3].name).toBe('f');
        expect(patterns[3].args.length).toBe(0);
      }
    });

    test('RHS is nested lambda', () => {
      expect(rhs?.tag).toBe('Binder');
      if (rhs?.tag === 'Binder') {
        expect(rhs.binderKind.tag).toBe('BLam');
        expect(rhs.body.tag).toBe('Binder');
      }
    });

    test('inner application has correct de Bruijn indices', () => {
      // f y x = #2 #0 #1 (where y=#0, x=#1, f=#2)
      const lambdaX = rhs;
      const lambdaY = getLambdaBody(lambdaX!);
      const appBody = getLambdaBody(lambdaY!);
      const app = getAppArgs(appBody!);

      expect(app).not.toBeNull();
      expect(getVarIndex(app!.fn)).toBe(2);  // f
      expect(getVarIndex(app!.args[0])).toBe(0);  // y
      expect(getVarIndex(app!.args[1])).toBe(1);  // x
    });
  });

  describe('sym pattern (constructor matching)', () => {
    // sym : {A : Type} -> {u : A} -> {v : A} -> Equal u v -> Equal v u
    // sym refl = refl
    // Expected: 4 patterns [_, _, _, refl]

    const source = `
sym : {A : Type} -> {u : A} -> {v : A} -> Equal u v -> Equal v u
sym refl = refl
`;
    const decls = parseDeclarations(source);
    const decl = decls.find(d => d.name === 'sym')!;
    const namedArgMap = extractNamedArgMap(decl.type!);
    const totalArity = countParameters(decl.type!);
    const kernel = elabToKernelWithMap(decl.value!, new Map(), [], [], namedArgMap, undefined, totalArity);
    const patterns = getPatterns(kernel);

    test('has 4 patterns', () => {
      expect(patterns.length).toBe(4);
    });

    test('first three are wildcards for implicit params', () => {
      expect(patterns[0].tag).toBe('PWild');
      expect(patterns[1].tag).toBe('PWild');
      expect(patterns[2].tag).toBe('PWild');
    });

    test('fourth is PCtor for constructor refl', () => {
      expect(patterns[3].tag).toBe('PCtor');
      if (patterns[3].tag === 'PCtor') {
        expect(patterns[3].name).toBe('refl');
      }
    });
  });
});
