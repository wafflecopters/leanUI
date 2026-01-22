/**
 * Unit tests for elaboratePatternsToPositionalArguments
 */

import { describe, test, expect, beforeEach } from 'bun:test';
import {
  elaboratePatternsToPositionalArguments,
  adjustRhsWithMapping,
  resetWildcardCounter,
  type ParamInfo,
  type PatternElabResult
} from './pattern-elab';
import type { TPattern } from './surface';
import type { TTKPattern } from './kernel';

// Helper to create patterns
const PVar = (name: string): TPattern => ({ tag: 'PVar', name });
const PWild = (): TPattern => ({ tag: 'PWild' });
const PCtor = (name: string, args: TPattern[] = [], namedArgs?: Array<{ name: string; pattern: TPattern }>): TPattern =>
  ({ tag: 'PCtor', name, args, namedArgs });

// Helper to create param info
const explicit = (name: string): ParamInfo => ({ name, implicitness: 'explicit' });
const implicit = (name: string): ParamInfo => ({ name, implicitness: 'implicit' });

// Helper to check if result is an error
function isError(result: PatternElabResult | { error: string }): result is { error: string } {
  return 'error' in result;
}

describe('elaboratePatternsToPositionalArguments', () => {
  beforeEach(() => {
    resetWildcardCounter();
  });

  describe('Basic cases - no implicits', () => {
    test('single explicit parameter with PVar', () => {
      const result = elaboratePatternsToPositionalArguments(
        [PVar('x')],
        undefined,
        [explicit('x')],
        new Set()
      );

      expect(isError(result)).toBe(false);
      if (!isError(result)) {
        expect(result.patterns).toHaveLength(1);
        expect(result.patterns[0]).toEqual({ tag: 'PVar', name: 'x' });
        expect(result.boundNames).toEqual(['x']);
      }
    });

    test('two explicit parameters', () => {
      const result = elaboratePatternsToPositionalArguments(
        [PVar('x'), PVar('y')],
        undefined,
        [explicit('a'), explicit('b')],
        new Set()
      );

      expect(isError(result)).toBe(false);
      if (!isError(result)) {
        expect(result.patterns).toHaveLength(2);
        expect(result.patterns[0]).toEqual({ tag: 'PVar', name: 'x' });
        expect(result.patterns[1]).toEqual({ tag: 'PVar', name: 'y' });
        expect(result.boundNames).toEqual(['x', 'y']);
      }
    });

    test('wildcard pattern', () => {
      const result = elaboratePatternsToPositionalArguments(
        [PWild()],
        undefined,
        [explicit('x')],
        new Set()
      );

      expect(isError(result)).toBe(false);
      if (!isError(result)) {
        expect(result.patterns).toHaveLength(1);
        expect(result.patterns[0].tag).toBe('PWild');
        expect(result.boundNames).toEqual(['_']);
      }
    });
  });

  describe('Implicit parameter filling', () => {
    test('single implicit parameter gets filled with wildcard', () => {
      const result = elaboratePatternsToPositionalArguments(
        [],
        undefined,
        [implicit('A')],
        new Set()
      );

      expect(isError(result)).toBe(false);
      if (!isError(result)) {
        expect(result.patterns).toHaveLength(1);
        expect(result.patterns[0].tag).toBe('PWild');
        expect(result.boundNames).toEqual(['_']);
      }
    });

    test('implicit before explicit - implicit gets wildcard', () => {
      // {A : Type} -> (x : A) -> ...
      const result = elaboratePatternsToPositionalArguments(
        [PVar('x')],
        undefined,
        [implicit('A'), explicit('x')],
        new Set()
      );

      expect(isError(result)).toBe(false);
      if (!isError(result)) {
        expect(result.patterns).toHaveLength(2);
        expect(result.patterns[0].tag).toBe('PWild'); // implicit A
        expect(result.patterns[1]).toEqual({ tag: 'PVar', name: 'x' }); // explicit x
        expect(result.boundNames).toEqual(['_', 'x']);
      }
    });

    test('multiple implicits mixed with explicits', () => {
      // {A : Type} -> (x : A) -> {B : Type} -> (y : B) -> ...
      const result = elaboratePatternsToPositionalArguments(
        [PVar('x'), PVar('y')],
        undefined,
        [implicit('A'), explicit('x'), implicit('B'), explicit('y')],
        new Set()
      );

      expect(isError(result)).toBe(false);
      if (!isError(result)) {
        expect(result.patterns).toHaveLength(4);
        expect(result.patterns[0].tag).toBe('PWild'); // implicit A
        expect(result.patterns[1]).toEqual({ tag: 'PVar', name: 'x' });
        expect(result.patterns[2].tag).toBe('PWild'); // implicit B
        expect(result.patterns[3]).toEqual({ tag: 'PVar', name: 'y' });
        expect(result.boundNames).toEqual(['_', 'x', '_', 'y']);
      }
    });
  });

  describe('Named patterns', () => {
    test('named pattern fills specific slot', () => {
      // {A : Type} -> {B : Type} -> (x : A) -> ...
      // User writes: foo {B := MyType} x
      const result = elaboratePatternsToPositionalArguments(
        [PVar('x')],
        [{ name: 'B', pattern: PCtor('MyType') }],
        [implicit('A'), implicit('B'), explicit('x')],
        new Set(['MyType'])
      );

      expect(isError(result)).toBe(false);
      if (!isError(result)) {
        expect(result.patterns).toHaveLength(3);
        expect(result.patterns[0].tag).toBe('PWild'); // implicit A (unfilled)
        expect(result.patterns[1]).toEqual({ tag: 'PCtor', name: 'MyType', args: [] }); // {B := MyType}
        expect(result.patterns[2]).toEqual({ tag: 'PVar', name: 'x' });
      }
    });

    test('named pattern with variable (not constructor)', () => {
      // {A : Type} -> (x : A) -> Type
      // User writes: getType {A := T} _
      const result = elaboratePatternsToPositionalArguments(
        [PWild()],
        [{ name: 'A', pattern: PCtor('T') }], // T is not a constructor
        [implicit('A'), explicit('x')],
        new Set() // T is NOT a constructor
      );

      expect(isError(result)).toBe(false);
      if (!isError(result)) {
        expect(result.patterns).toHaveLength(2);
        // T should become PVar since it's not a constructor
        expect(result.patterns[0]).toEqual({ tag: 'PVar', name: 'T' });
        expect(result.patterns[1].tag).toBe('PWild');
        expect(result.boundNames).toEqual(['T', '_']);
      }
    });

    test('error on unknown named parameter', () => {
      const result = elaboratePatternsToPositionalArguments(
        [],
        [{ name: 'Unknown', pattern: PVar('x') }],
        [implicit('A')],
        new Set()
      );

      expect(isError(result)).toBe(true);
      if (isError(result)) {
        expect(result.error).toContain('Unknown');
      }
    });

    test('error on duplicate named parameter', () => {
      const result = elaboratePatternsToPositionalArguments(
        [],
        [
          { name: 'A', pattern: PVar('x') },
          { name: 'A', pattern: PVar('y') }
        ],
        [implicit('A')],
        new Set()
      );

      expect(isError(result)).toBe(true);
      if (isError(result)) {
        expect(result.error).toContain('multiple');
      }
    });
  });

  describe('Constructor patterns', () => {
    test('constructor with no args - recognized as constructor', () => {
      const result = elaboratePatternsToPositionalArguments(
        [PCtor('Zero')],
        undefined,
        [explicit('n')],
        new Set(['Zero', 'Succ'])
      );

      expect(isError(result)).toBe(false);
      if (!isError(result)) {
        expect(result.patterns[0]).toEqual({ tag: 'PCtor', name: 'Zero', args: [] });
        expect(result.boundNames).toEqual([]); // Zero binds nothing
      }
    });

    test('constructor with args', () => {
      // Succ n pattern
      const result = elaboratePatternsToPositionalArguments(
        [PCtor('Succ', [PVar('n')])],
        undefined,
        [explicit('x')],
        new Set(['Zero', 'Succ'])
      );

      expect(isError(result)).toBe(false);
      if (!isError(result)) {
        expect(result.patterns[0]).toEqual({
          tag: 'PCtor',
          name: 'Succ',
          args: [{ tag: 'PVar', name: 'n' }]
        });
        expect(result.boundNames).toEqual(['n']);
      }
    });

    test('nested constructor patterns', () => {
      // Succ (Succ n) pattern
      const result = elaboratePatternsToPositionalArguments(
        [PCtor('Succ', [PCtor('Succ', [PVar('n')])])],
        undefined,
        [explicit('x')],
        new Set(['Zero', 'Succ'])
      );

      expect(isError(result)).toBe(false);
      if (!isError(result)) {
        expect(result.patterns[0]).toEqual({
          tag: 'PCtor',
          name: 'Succ',
          args: [{
            tag: 'PCtor',
            name: 'Succ',
            args: [{ tag: 'PVar', name: 'n' }]
          }]
        });
        expect(result.boundNames).toEqual(['n']);
      }
    });

    test('lowercase leaf becomes PVar if not a constructor', () => {
      // Pattern: foo x where x is not a constructor
      const result = elaboratePatternsToPositionalArguments(
        [PCtor('x')], // Parser creates PCtor for all identifiers
        undefined,
        [explicit('a')],
        new Set(['Zero', 'Succ']) // x is NOT a constructor
      );

      expect(isError(result)).toBe(false);
      if (!isError(result)) {
        // x should become PVar since it's not a constructor
        expect(result.patterns[0]).toEqual({ tag: 'PVar', name: 'x' });
        expect(result.boundNames).toEqual(['x']);
      }
    });

    test('lowercase leaf stays PCtor if it IS a constructor (like refl)', () => {
      // Pattern: refl where refl IS a constructor
      const result = elaboratePatternsToPositionalArguments(
        [PCtor('refl')],
        undefined,
        [explicit('p')],
        new Set(['refl']) // refl IS a constructor
      );

      expect(isError(result)).toBe(false);
      if (!isError(result)) {
        expect(result.patterns[0]).toEqual({ tag: 'PCtor', name: 'refl', args: [] });
        expect(result.boundNames).toEqual([]); // refl binds nothing
      }
    });

    test('error on unknown constructor with args', () => {
      // Pattern: Foo x where Foo is not a constructor
      const result = elaboratePatternsToPositionalArguments(
        [PCtor('Foo', [PVar('x')])],
        undefined,
        [explicit('a')],
        new Set(['Zero', 'Succ']) // Foo is NOT a constructor
      );

      expect(isError(result)).toBe(true);
      if (isError(result)) {
        expect(result.error).toContain('Foo');
        expect(result.error).toContain('not a known constructor');
      }
    });
  });

  describe('Variable mapping', () => {
    test('simple case - no reordering', () => {
      const result = elaboratePatternsToPositionalArguments(
        [PVar('x'), PVar('y')],
        undefined,
        [explicit('a'), explicit('b')],
        new Set()
      );

      expect(isError(result)).toBe(false);
      if (!isError(result)) {
        // Parser vars: [x, y] at indices 0, 1
        // Elab vars: [x, y] at indices 0, 1
        // Mapping: 0→0, 1→1
        expect(result.varMapping.get(0)).toBe(0);
        expect(result.varMapping.get(1)).toBe(1);
      }
    });

    test('implicit insertion shifts indices', () => {
      // {A : Type} -> (x : A) -> ...
      // Surface: [x]
      // Elab: [_, x]
      const result = elaboratePatternsToPositionalArguments(
        [PVar('x')],
        undefined,
        [implicit('A'), explicit('x')],
        new Set()
      );

      expect(isError(result)).toBe(false);
      if (!isError(result)) {
        // Parser vars: [x] at index 0
        // Elab vars: [_, x] at indices 0, 1
        // Mapping: parser 0 (x) → elab 1 (x)
        expect(result.varMapping.get(0)).toBe(1);
      }
    });

    test('phantom binding - lowercase constructor', () => {
      // Pattern: refl (where refl is a constructor)
      // Parser thinks refl is a variable and assigns index 0
      // Elaborator recognizes it's a constructor
      const result = elaboratePatternsToPositionalArguments(
        [PCtor('refl')],
        undefined,
        [explicit('p')],
        new Set(['refl'])
      );

      expect(isError(result)).toBe(false);
      if (!isError(result)) {
        // Parser vars: [refl] at index 0
        // Elab vars: [] (refl is a constructor, doesn't bind)
        // Mapping: parser 0 → { ctor: 'refl' }
        expect(result.varMapping.get(0)).toEqual({ ctor: 'refl' });
      }
    });

    test('mixed phantom and regular bindings', () => {
      // Pattern: (VCons h tail) where we have h, tail as vars
      // and VCons as constructor
      const result = elaboratePatternsToPositionalArguments(
        [PCtor('VCons', [PVar('h'), PVar('tail')])],
        undefined,
        [explicit('v')],
        new Set(['VCons', 'VNil'])
      );

      expect(isError(result)).toBe(false);
      if (!isError(result)) {
        // Parser vars: [h, tail] at indices 0, 1
        // Elab vars: [h, tail] at indices 0, 1
        expect(result.varMapping.get(0)).toBe(0);
        expect(result.varMapping.get(1)).toBe(1);
      }
    });
  });

  describe('Error cases', () => {
    test('too many positional patterns', () => {
      const result = elaboratePatternsToPositionalArguments(
        [PVar('x'), PVar('y'), PVar('z')],
        undefined,
        [explicit('a'), explicit('b')],
        new Set()
      );

      expect(isError(result)).toBe(true);
      if (isError(result)) {
        expect(result.error).toContain('Too many');
      }
    });

    test('missing explicit pattern', () => {
      const result = elaboratePatternsToPositionalArguments(
        [PVar('x')],
        undefined,
        [explicit('a'), explicit('b'), explicit('c')],
        new Set()
      );

      expect(isError(result)).toBe(true);
      if (isError(result)) {
        expect(result.error).toContain('Missing');
      }
    });
  });

  describe('Complex real-world cases', () => {
    test('Vec/Fin nth pattern - VCons case', () => {
      // nth : {A : Type} -> {n : Nat} -> Vec A n -> Fin n -> A
      // nth (VCons h tail) (FSucc f) = nth tail f
      const result = elaboratePatternsToPositionalArguments(
        [
          PCtor('VCons', [PVar('h'), PVar('tail')]),
          PCtor('FSucc', [PVar('f')])
        ],
        undefined,
        [implicit('A'), implicit('n'), explicit('v'), explicit('i')],
        new Set(['VCons', 'VNil', 'FZero', 'FSucc', 'Zero', 'Succ'])
      );

      expect(isError(result)).toBe(false);
      if (!isError(result)) {
        expect(result.patterns).toHaveLength(4);
        expect(result.patterns[0].tag).toBe('PWild'); // A
        expect(result.patterns[1].tag).toBe('PWild'); // n
        expect(result.patterns[2]).toEqual({
          tag: 'PCtor',
          name: 'VCons',
          args: [{ tag: 'PVar', name: 'h' }, { tag: 'PVar', name: 'tail' }]
        });
        expect(result.patterns[3]).toEqual({
          tag: 'PCtor',
          name: 'FSucc',
          args: [{ tag: 'PVar', name: 'f' }]
        });
        expect(result.boundNames).toEqual(['_', '_', 'h', 'tail', 'f']);
      }
    });

    test('Equal refl pattern - symm case', () => {
      // symm : {A : Type} -> {x : A} -> {y : A} -> Equal x y -> Equal y x
      // symm refl = refl
      const result = elaboratePatternsToPositionalArguments(
        [PCtor('refl')],
        undefined,
        [implicit('A'), implicit('x'), implicit('y'), explicit('p')],
        new Set(['refl'])
      );

      expect(isError(result)).toBe(false);
      if (!isError(result)) {
        expect(result.patterns).toHaveLength(4);
        expect(result.patterns[0].tag).toBe('PWild'); // A
        expect(result.patterns[1].tag).toBe('PWild'); // x
        expect(result.patterns[2].tag).toBe('PWild'); // y
        expect(result.patterns[3]).toEqual({ tag: 'PCtor', name: 'refl', args: [] });
        // refl is a constructor, so no binding
        expect(result.boundNames).toEqual(['_', '_', '_']);

        // Parser would have assigned refl index 0 (lowercase heuristic)
        // But it's actually a constructor
        expect(result.varMapping.get(0)).toEqual({ ctor: 'refl' });
      }
    });

    test('Named arg in constructor pattern - VCons {A := _}', () => {
      // nth (VCons {A := _} {n := _} h tail) ...
      const result = elaboratePatternsToPositionalArguments(
        [
          PCtor('VCons', [PVar('h'), PVar('tail')], [
            { name: 'A', pattern: PWild() },
            { name: 'n', pattern: PWild() }
          ])
        ],
        undefined,
        [explicit('v')],
        new Set(['VCons', 'VNil'])
      );

      expect(isError(result)).toBe(false);
      if (!isError(result)) {
        expect(result.patterns).toHaveLength(1);
        // The constructor should have all its args
        expect(result.patterns[0].tag).toBe('PCtor');
        const ctor = result.patterns[0] as { tag: 'PCtor'; name: string; args: TTKPattern[] };
        expect(ctor.name).toBe('VCons');
        // Should have h, tail, and the named args
        expect(ctor.args.length).toBeGreaterThanOrEqual(2);
      }
    });
  });
});

describe('adjustRhsWithMapping', () => {
  // Helper to create terms
  const Var = (index: number) => ({ tag: 'Var' as const, index });
  const Const = (name: string) => ({ tag: 'Const' as const, name });

  test('simple index adjustment', () => {
    // Parser: [x] → RHS x is Var(0)
    // Elab: [_, x] → x should be Var(0) (last bound is at 0)
    const mapping = new Map<number, number | { ctor: string }>();
    mapping.set(0, 1); // parser x at 0 → elab x at 1

    const rhs = Var(0);
    const adjusted = adjustRhsWithMapping(rhs, mapping, 1, 2);

    // Parser: totalParserVars=1, rhsIndex=0, parserIdx=0
    // Elab: totalElabVars=2, mapped=1, newRhsIdx=2-1-1=0
    expect(adjusted).toEqual(Var(0));
  });

  test('phantom binding becomes Const', () => {
    // Parser thinks refl is a variable at index 0
    // But refl is actually a constructor
    const mapping = new Map<number, number | { ctor: string }>();
    mapping.set(0, { ctor: 'refl' });

    const rhs = Var(0);
    const adjusted = adjustRhsWithMapping(rhs, mapping, 1, 0);

    expect(adjusted).toEqual(Const('refl'));
  });

  test('multiple variables with shifted indices', () => {
    // Parser: [x, y] → x is Var(1), y is Var(0) (reversed)
    // Elab: [_, x, y] → x should be Var(1), y should be Var(0)
    const mapping = new Map<number, number | { ctor: string }>();
    mapping.set(0, 1); // parser x → elab x at index 1
    mapping.set(1, 2); // parser y → elab y at index 2

    // Test x (parser Var(1), parserIdx=0)
    const rhsX = Var(1);
    const adjustedX = adjustRhsWithMapping(rhsX, mapping, 2, 3);
    // parserIdx = 2-1-1 = 0, mapped = 1, newRhsIdx = 3-1-1 = 1
    expect(adjustedX).toEqual(Var(1));

    // Test y (parser Var(0), parserIdx=1)
    const rhsY = Var(0);
    const adjustedY = adjustRhsWithMapping(rhsY, mapping, 2, 3);
    // parserIdx = 2-1-0 = 1, mapped = 2, newRhsIdx = 3-1-2 = 0
    expect(adjustedY).toEqual(Var(0));
  });
});
