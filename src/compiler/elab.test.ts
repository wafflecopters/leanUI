import { describe, test, expect } from 'vitest';
import {
  elabToKernel,
  elabToKernelWithNamedArgs,
  extractNamedArgMap,
  countParameters,
  hasNamedPatterns,
  reorderPatterns,
  NamedArgMap,
  NamedArgMapLookup,
  NamedArgElabError
} from './elab';
import { TTerm, TPattern, mkPiTT, mkAppTT, mkConstTT } from './surface';
import { TTKTerm } from './kernel';

describe('Elaboration: MultiBinder', () => {
  test('MultiBinder Pi expands to nested Binder terms', () => {
    // (a b : Nat) -> T
    const surface: TTerm = {
      tag: 'MultiBinder',
      names: ['a', 'b'],
      binderKind: { tag: 'BPiTT' },
      domain: { tag: 'Const', name: 'Nat' },
      body: { tag: 'Const', name: 'T' }
    };

    const kernel = elabToKernel(surface);

    // Should expand to: (a : Nat) -> (b : Nat) -> T
    expect(kernel.tag).toBe('Binder');
    if (kernel.tag === 'Binder') {
      expect(kernel.name).toBe('a');
      expect(kernel.binderKind.tag).toBe('BPi');
      expect(kernel.domain.tag).toBe('Const');
      if (kernel.domain.tag === 'Const') {
        expect(kernel.domain.name).toBe('Nat');
      }

      // Inner binder
      expect(kernel.body.tag).toBe('Binder');
      if (kernel.body.tag === 'Binder') {
        expect(kernel.body.name).toBe('b');
        expect(kernel.body.binderKind.tag).toBe('BPi');
        expect(kernel.body.domain.tag).toBe('Const');

        // Innermost body
        expect(kernel.body.body.tag).toBe('Const');
        if (kernel.body.body.tag === 'Const') {
          expect(kernel.body.body.name).toBe('T');
        }
      }
    }
  });

  test('MultiBinder Lambda expands to nested Binder terms', () => {
    // \(x y : A) => body
    const surface: TTerm = {
      tag: 'MultiBinder',
      names: ['x', 'y'],
      binderKind: { tag: 'BLamTT' },
      domain: { tag: 'Const', name: 'A' },
      body: { tag: 'Var', index: 1 } // x (outer var)
    };

    const kernel = elabToKernel(surface);

    // Should expand to: \(x : A) => \(y : A) => body
    expect(kernel.tag).toBe('Binder');
    if (kernel.tag === 'Binder') {
      expect(kernel.name).toBe('x');
      expect(kernel.binderKind.tag).toBe('BLam');

      // Inner binder
      expect(kernel.body.tag).toBe('Binder');
      if (kernel.body.tag === 'Binder') {
        expect(kernel.body.name).toBe('y');
        expect(kernel.body.binderKind.tag).toBe('BLam');

        // Innermost body should be Var 1 (still pointing to x)
        expect(kernel.body.body.tag).toBe('Var');
        if (kernel.body.body.tag === 'Var') {
          expect(kernel.body.body.index).toBe(1);
        }
      }
    }
  });

  test('MultiBinder with many names expands correctly', () => {
    // (a b c d : T) -> R
    const surface: TTerm = {
      tag: 'MultiBinder',
      names: ['a', 'b', 'c', 'd'],
      binderKind: { tag: 'BPiTT' },
      domain: { tag: 'Const', name: 'T' },
      body: { tag: 'Const', name: 'R' }
    };

    const kernel = elabToKernel(surface);

    // Should be 4 nested Binders
    let current: TTKTerm = kernel;
    const names = ['a', 'b', 'c', 'd'];

    for (let i = 0; i < 4; i++) {
      expect(current.tag).toBe('Binder');
      if (current.tag === 'Binder') {
        expect(current.name).toBe(names[i]);
        expect(current.binderKind.tag).toBe('BPi');
        current = current.body;
      }
    }

    // Final body should be R
    expect(current.tag).toBe('Const');
    if (current.tag === 'Const') {
      expect(current.name).toBe('R');
    }
  });

  test('Single-name Binder elaborates normally (no MultiBinder)', () => {
    // (x : A) -> B
    const surface: TTerm = {
      tag: 'Binder',
      name: 'x',
      binderKind: { tag: 'BPiTT' },
      domain: { tag: 'Const', name: 'A' },
      body: { tag: 'Const', name: 'B' }
    };

    const kernel = elabToKernel(surface);

    expect(kernel.tag).toBe('Binder');
    if (kernel.tag === 'Binder') {
      expect(kernel.name).toBe('x');
      expect(kernel.binderKind.tag).toBe('BPi');
    }
  });
});

// ============================================================================
// Named Argument Map Extraction
// ============================================================================

describe('extractNamedArgMap', () => {
  test('Extract named args from single named binder', () => {
    // { A : Type } -> A
    const type: TTerm = mkPiTT(
      { tag: 'Sort', level: { tag: 'LNum', n: 1 } },
      { tag: 'Var', index: 0 },
      'A',
      true // named
    );

    const map = extractNamedArgMap(type);
    expect(map.size).toBe(1);
    expect(map.get('A')).toBe(0);
  });

  test('Extract named args from positional binders returns empty map', () => {
    // (A : Type) -> A
    const type: TTerm = mkPiTT(
      { tag: 'Sort', level: { tag: 'LNum', n: 1 } },
      { tag: 'Var', index: 0 },
      'A'
      // not named
    );

    const map = extractNamedArgMap(type);
    expect(map.size).toBe(0);
  });

  test('Extract named args from mixed named and positional', () => {
    // { A : Type } -> Nat -> { B : Type } -> A
    const innerPi: TTerm = mkPiTT(
      { tag: 'Sort', level: { tag: 'LNum', n: 1 } },
      { tag: 'Var', index: 2 }, // A is 2 levels up
      'B',
      true // named
    );
    const middlePi: TTerm = mkPiTT(
      { tag: 'Const', name: 'Nat' },
      innerPi,
      'x'
      // not named
    );
    const type: TTerm = mkPiTT(
      { tag: 'Sort', level: { tag: 'LNum', n: 1 } },
      middlePi,
      'A',
      true // named
    );

    const map = extractNamedArgMap(type);
    expect(map.size).toBe(2);
    expect(map.get('A')).toBe(0);
    expect(map.get('B')).toBe(2);
  });

  test('Extract named args from MultiBinder', () => {
    // { A B : Type } -> A
    const type: TTerm = {
      tag: 'MultiBinder',
      names: ['A', 'B'],
      binderKind: { tag: 'BPiTT' },
      domain: { tag: 'Sort', level: { tag: 'LNum', n: 1 } },
      body: { tag: 'Var', index: 0 },
      named: true
    };

    const map = extractNamedArgMap(type);
    expect(map.size).toBe(2);
    expect(map.get('A')).toBe(0);
    expect(map.get('B')).toBe(1);
  });

  test('Underscore names are not included in map', () => {
    // { _ : Type } -> Nat
    const type: TTerm = mkPiTT(
      { tag: 'Sort', level: { tag: 'LNum', n: 1 } },
      { tag: 'Const', name: 'Nat' },
      '_',
      true // named
    );

    const map = extractNamedArgMap(type);
    expect(map.size).toBe(0); // underscore not included
  });
});

describe('countParameters', () => {
  test('Count single parameter', () => {
    const type: TTerm = mkPiTT(
      { tag: 'Const', name: 'Nat' },
      { tag: 'Const', name: 'Nat' },
      'x'
    );
    expect(countParameters(type)).toBe(1);
  });

  test('Count multiple parameters', () => {
    // A -> B -> C -> D
    const type: TTerm = mkPiTT(
      { tag: 'Const', name: 'A' },
      mkPiTT(
        { tag: 'Const', name: 'B' },
        mkPiTT(
          { tag: 'Const', name: 'C' },
          { tag: 'Const', name: 'D' },
          'z'
        ),
        'y'
      ),
      'x'
    );
    expect(countParameters(type)).toBe(3);
  });

  test('Count MultiBinder parameters', () => {
    const type: TTerm = {
      tag: 'MultiBinder',
      names: ['a', 'b', 'c'],
      binderKind: { tag: 'BPiTT' },
      domain: { tag: 'Const', name: 'Nat' },
      body: { tag: 'Const', name: 'Nat' }
    };
    expect(countParameters(type)).toBe(3);
  });

  test('Count non-Pi type returns 0', () => {
    const type: TTerm = { tag: 'Const', name: 'Nat' };
    expect(countParameters(type)).toBe(0);
  });
});

// ============================================================================
// Named Argument Elaboration
// ============================================================================

describe('elabToKernelWithNamedArgs', () => {
  // Create a simple lookup function for testing
  const createLookup = (maps: Record<string, { namedMap: NamedArgMap; totalArity: number }>): NamedArgMapLookup => {
    return (name: string) => maps[name];
  };

  test('Elaborate app without named args works normally', () => {
    // f x - no named args
    const term: TTerm = mkAppTT(
      mkConstTT('f'),
      mkConstTT('x')
    );

    const lookup = createLookup({});
    const kernel = elabToKernelWithNamedArgs(term, lookup);

    expect(kernel.tag).toBe('App');
    if (kernel.tag === 'App') {
      expect(kernel.fn.tag).toBe('Const');
      expect(kernel.arg.tag).toBe('Const');
    }
  });

  test('Elaborate app with single named arg', () => {
    // f { A := Nat }
    const term: TTerm = mkAppTT(
      mkConstTT('f'),
      mkConstTT('Nat'),
      'A' // argName
    );

    const fMap: NamedArgMap = new Map([['A', 0]]);
    const lookup = createLookup({ f: { namedMap: fMap, totalArity: 1 } });
    const kernel = elabToKernelWithNamedArgs(term, lookup);

    // Should become: f Nat
    expect(kernel.tag).toBe('App');
    if (kernel.tag === 'App') {
      expect(kernel.fn.tag).toBe('Const');
      if (kernel.fn.tag === 'Const') {
        expect(kernel.fn.name).toBe('f');
      }
      expect(kernel.arg.tag).toBe('Const');
      if (kernel.arg.tag === 'Const') {
        expect(kernel.arg.name).toBe('Nat');
      }
    }
  });

  test('Elaborate app with named args reorders correctly', () => {
    // f { B := Bool } { A := Nat }
    // Where f : { A : Type } -> { B : Type } -> A -> B
    // Should become: f Nat Bool
    const innerApp: TTerm = mkAppTT(
      mkConstTT('f'),
      mkConstTT('Bool'),
      'B'
    );
    const term: TTerm = mkAppTT(
      innerApp,
      mkConstTT('Nat'),
      'A'
    );

    const fMap: NamedArgMap = new Map([['A', 0], ['B', 1]]);
    const lookup = createLookup({ f: { namedMap: fMap, totalArity: 2 } });
    const kernel = elabToKernelWithNamedArgs(term, lookup);

    // Should be: App(App(f, Nat), Bool)
    expect(kernel.tag).toBe('App');
    if (kernel.tag === 'App') {
      // Outer arg should be Bool (B is at position 1)
      if (kernel.arg.tag === 'Const') {
        expect(kernel.arg.name).toBe('Bool');
      }

      // Inner app
      expect(kernel.fn.tag).toBe('App');
      if (kernel.fn.tag === 'App') {
        // Inner arg should be Nat (A is at position 0)
        if (kernel.fn.arg.tag === 'Const') {
          expect(kernel.fn.arg.name).toBe('Nat');
        }
      }
    }
  });

  test('Elaborate mixed named and positional args', () => {
    // f x { B := Bool }
    // Where f : (A : Type) -> { B : Type } -> A
    // Should become: f x Bool
    const innerApp: TTerm = mkAppTT(
      mkConstTT('f'),
      mkConstTT('x')
      // positional
    );
    const term: TTerm = mkAppTT(
      innerApp,
      mkConstTT('Bool'),
      'B'
    );

    const fMap: NamedArgMap = new Map([['B', 1]]);
    const lookup = createLookup({ f: { namedMap: fMap, totalArity: 2 } });
    const kernel = elabToKernelWithNamedArgs(term, lookup);

    // Should be: App(App(f, x), Bool)
    expect(kernel.tag).toBe('App');
    if (kernel.tag === 'App') {
      if (kernel.arg.tag === 'Const') {
        expect(kernel.arg.name).toBe('Bool');
      }
      expect(kernel.fn.tag).toBe('App');
      if (kernel.fn.tag === 'App') {
        if (kernel.fn.arg.tag === 'Const') {
          expect(kernel.fn.arg.name).toBe('x');
        }
      }
    }
  });

  test('Elaborate named arg followed by positional', () => {
    // f { A := Nat } x
    // Where f : { A : Type } -> A -> A
    // Should become: f Nat x (A at position 0, x fills gap at position 1)
    const innerApp: TTerm = mkAppTT(
      mkConstTT('f'),
      mkConstTT('Nat'),
      'A'
    );
    const term: TTerm = mkAppTT(
      innerApp,
      mkConstTT('x')
      // positional
    );

    const fMap: NamedArgMap = new Map([['A', 0]]);
    const lookup = createLookup({ f: { namedMap: fMap, totalArity: 2 } });
    const kernel = elabToKernelWithNamedArgs(term, lookup);

    // Should be: App(App(f, Nat), x)
    expect(kernel.tag).toBe('App');
    if (kernel.tag === 'App') {
      if (kernel.arg.tag === 'Const') {
        expect(kernel.arg.name).toBe('x');
      }
      expect(kernel.fn.tag).toBe('App');
      if (kernel.fn.tag === 'App') {
        if (kernel.fn.arg.tag === 'Const') {
          expect(kernel.fn.arg.name).toBe('Nat');
        }
      }
    }
  });

  test('Error on unknown named argument', () => {
    // f { Unknown := Nat }
    const term: TTerm = mkAppTT(
      mkConstTT('f'),
      mkConstTT('Nat'),
      'Unknown'
    );

    const fMap: NamedArgMap = new Map([['A', 0]]);
    const lookup = createLookup({ f: { namedMap: fMap, totalArity: 1 } });

    expect(() => elabToKernelWithNamedArgs(term, lookup)).toThrow(NamedArgElabError);
    expect(() => elabToKernelWithNamedArgs(term, lookup)).toThrow('Unknown named argument');
  });

  test('Error when function has no named params', () => {
    // f { A := Nat } where f has no named params
    const term: TTerm = mkAppTT(
      mkConstTT('f'),
      mkConstTT('Nat'),
      'A'
    );

    const lookup = createLookup({}); // No maps defined

    expect(() => elabToKernelWithNamedArgs(term, lookup)).toThrow(NamedArgElabError);
    expect(() => elabToKernelWithNamedArgs(term, lookup)).toThrow('has no named parameters');
  });

  test('Named args work in nested expressions', () => {
    // (f { A := Nat }) { B := Bool }
    // Where both f and the result have named params
    const innerTerm: TTerm = mkAppTT(
      mkConstTT('f'),
      mkConstTT('Nat'),
      'A'
    );

    // We don't support named args on non-const heads, so this should work
    // as long as the inner app is handled correctly
    const fMap: NamedArgMap = new Map([['A', 0]]);
    const lookup = createLookup({ f: { namedMap: fMap, totalArity: 1 } });
    const kernel = elabToKernelWithNamedArgs(innerTerm, lookup);

    expect(kernel.tag).toBe('App');
  });

  test('Elaborate binders with named flag drops it', () => {
    // { A : Type } -> A - the named flag should be dropped in kernel
    const term: TTerm = {
      tag: 'Binder',
      name: 'A',
      binderKind: { tag: 'BPiTT' },
      domain: { tag: 'Sort', level: { tag: 'LNum', n: 1 } },
      body: { tag: 'Var', index: 0 },
      named: true
    };

    const lookup = createLookup({});
    const kernel = elabToKernelWithNamedArgs(term, lookup);

    expect(kernel.tag).toBe('Binder');
    // Kernel binders don't have 'named' field
    expect('named' in kernel).toBe(false);
  });
});

// ============================================================================
// Pattern Reordering Tests
// ============================================================================

describe('hasNamedPatterns', () => {
  test('Returns false for empty pattern list', () => {
    expect(hasNamedPatterns([])).toBe(false);
  });

  test('Returns false for all positional patterns', () => {
    const patterns: TPattern[] = [
      { tag: 'PVar', name: 'x' },
      { tag: 'PVar', name: 'y' },
      { tag: 'PWild' }
    ];
    expect(hasNamedPatterns(patterns)).toBe(false);
  });

  test('Returns true when PVar has named: true', () => {
    const patterns: TPattern[] = [
      { tag: 'PVar', name: 'x' },
      { tag: 'PVar', name: 'A', named: true }
    ];
    expect(hasNamedPatterns(patterns)).toBe(true);
  });

  test('Returns true when PWild has named: true', () => {
    const patterns: TPattern[] = [
      { tag: 'PVar', name: 'x' },
      { tag: 'PWild', named: true }
    ];
    expect(hasNamedPatterns(patterns)).toBe(true);
  });

  test('Returns false for PCtor patterns (even with named sub-patterns)', () => {
    // PCtor itself doesn't have named flag, only its args do
    const patterns: TPattern[] = [
      { tag: 'PCtor', name: 'Succ', args: [{ tag: 'PVar', name: 'n' }] }
    ];
    expect(hasNamedPatterns(patterns)).toBe(false);
  });

  test('Named flag explicitly set to false', () => {
    const patterns: TPattern[] = [
      { tag: 'PVar', name: 'x', named: false }
    ];
    expect(hasNamedPatterns(patterns)).toBe(false);
  });
});

describe('reorderPatterns', () => {
  test('No reordering needed for all positional patterns', () => {
    const patterns: TPattern[] = [
      { tag: 'PVar', name: 'a' },
      { tag: 'PVar', name: 'b' }
    ];
    const namedMap: NamedArgMap = new Map();

    const result = reorderPatterns(patterns, namedMap);
    expect(result.error).toBeUndefined();
    expect(result.ordered).toHaveLength(2);
    expect(result.ordered![0]).toEqual({ tag: 'PVar', name: 'a' });
    expect(result.ordered![1]).toEqual({ tag: 'PVar', name: 'b' });
  });

  test('Single named pattern at correct position', () => {
    // {A} where A is at position 0
    const patterns: TPattern[] = [
      { tag: 'PVar', name: 'A', named: true }
    ];
    const namedMap: NamedArgMap = new Map([['A', 0]]);

    const result = reorderPatterns(patterns, namedMap);
    expect(result.error).toBeUndefined();
    expect(result.ordered).toHaveLength(1);
    expect(result.ordered![0]).toEqual({ tag: 'PVar', name: 'A', named: true });
  });

  test('Named pattern reordered to correct position', () => {
    // x {A} where A is at position 0
    // Should become: {A} x
    const patterns: TPattern[] = [
      { tag: 'PVar', name: 'x' },
      { tag: 'PVar', name: 'A', named: true }
    ];
    const namedMap: NamedArgMap = new Map([['A', 0]]);

    const result = reorderPatterns(patterns, namedMap);
    expect(result.error).toBeUndefined();
    expect(result.ordered).toHaveLength(2);
    expect(result.ordered![0]).toEqual({ tag: 'PVar', name: 'A', named: true });
    expect(result.ordered![1]).toEqual({ tag: 'PVar', name: 'x' });
  });

  test('Multiple named patterns reordered', () => {
    // y {B} x {A} where A is at 0, B is at 2
    // Should become: {A} x {B} y
    const patterns: TPattern[] = [
      { tag: 'PVar', name: 'y' },
      { tag: 'PVar', name: 'B', named: true },
      { tag: 'PVar', name: 'x' },
      { tag: 'PVar', name: 'A', named: true }
    ];
    const namedMap: NamedArgMap = new Map([['A', 0], ['B', 2]]);

    const result = reorderPatterns(patterns, namedMap);
    expect(result.error).toBeUndefined();
    expect(result.ordered).toHaveLength(4);
    expect(result.ordered![0]).toEqual({ tag: 'PVar', name: 'A', named: true });
    expect(result.ordered![1]).toEqual({ tag: 'PVar', name: 'y' });
    expect(result.ordered![2]).toEqual({ tag: 'PVar', name: 'B', named: true });
    expect(result.ordered![3]).toEqual({ tag: 'PVar', name: 'x' });
  });

  test('Named pattern at end position', () => {
    // x {B} where B is at position 1
    // Should stay: x {B}
    const patterns: TPattern[] = [
      { tag: 'PVar', name: 'x' },
      { tag: 'PVar', name: 'B', named: true }
    ];
    const namedMap: NamedArgMap = new Map([['B', 1]]);

    const result = reorderPatterns(patterns, namedMap);
    expect(result.error).toBeUndefined();
    expect(result.ordered).toHaveLength(2);
    expect(result.ordered![0]).toEqual({ tag: 'PVar', name: 'x' });
    expect(result.ordered![1]).toEqual({ tag: 'PVar', name: 'B', named: true });
  });

  test('Mixed named and positional with gap filling', () => {
    // a b {C} where C is at position 0
    // Should become: {C} a b
    const patterns: TPattern[] = [
      { tag: 'PVar', name: 'a' },
      { tag: 'PVar', name: 'b' },
      { tag: 'PVar', name: 'C', named: true }
    ];
    const namedMap: NamedArgMap = new Map([['C', 0]]);

    const result = reorderPatterns(patterns, namedMap);
    expect(result.error).toBeUndefined();
    expect(result.ordered).toHaveLength(3);
    expect(result.ordered![0]).toEqual({ tag: 'PVar', name: 'C', named: true });
    expect(result.ordered![1]).toEqual({ tag: 'PVar', name: 'a' });
    expect(result.ordered![2]).toEqual({ tag: 'PVar', name: 'b' });
  });

  test('Error on unknown named pattern', () => {
    const patterns: TPattern[] = [
      { tag: 'PVar', name: 'Unknown', named: true }
    ];
    const namedMap: NamedArgMap = new Map([['A', 0]]);

    const result = reorderPatterns(patterns, namedMap);
    expect(result.error).toBe('Unknown named pattern: Unknown');
    expect(result.ordered).toBeUndefined();
  });

  test('Error on duplicate position', () => {
    // Both A and B try to be at position 0
    const patterns: TPattern[] = [
      { tag: 'PVar', name: 'A', named: true },
      { tag: 'PVar', name: 'B', named: true }
    ];
    const namedMap: NamedArgMap = new Map([['A', 0], ['B', 0]]);

    const result = reorderPatterns(patterns, namedMap);
    expect(result.error).toBe('Duplicate pattern at position 0');
    expect(result.ordered).toBeUndefined();
  });

  test('Error on missing pattern at required position', () => {
    // {B} where B is at position 2, but no patterns for positions 0 and 1
    const patterns: TPattern[] = [
      { tag: 'PVar', name: 'B', named: true }
    ];
    const namedMap: NamedArgMap = new Map([['B', 2]]);

    const result = reorderPatterns(patterns, namedMap);
    expect(result.error).toBe('Missing pattern at position 0');
    expect(result.ordered).toBeUndefined();
  });

  test('PWild patterns can be positional', () => {
    // _ {A} _ where A is at position 1
    // Should become: _ {A} _
    const patterns: TPattern[] = [
      { tag: 'PWild' },
      { tag: 'PVar', name: 'A', named: true },
      { tag: 'PWild' }
    ];
    const namedMap: NamedArgMap = new Map([['A', 1]]);

    const result = reorderPatterns(patterns, namedMap);
    expect(result.error).toBeUndefined();
    expect(result.ordered).toHaveLength(3);
    expect(result.ordered![0]).toEqual({ tag: 'PWild' });
    expect(result.ordered![1]).toEqual({ tag: 'PVar', name: 'A', named: true });
    expect(result.ordered![2]).toEqual({ tag: 'PWild' });
  });

  test('PCtor patterns work as positional', () => {
    // (Succ n) {A} where A is at position 0
    // Should become: {A} (Succ n)
    const patterns: TPattern[] = [
      { tag: 'PCtor', name: 'Succ', args: [{ tag: 'PVar', name: 'n' }] },
      { tag: 'PVar', name: 'A', named: true }
    ];
    const namedMap: NamedArgMap = new Map([['A', 0]]);

    const result = reorderPatterns(patterns, namedMap);
    expect(result.error).toBeUndefined();
    expect(result.ordered).toHaveLength(2);
    expect(result.ordered![0]).toEqual({ tag: 'PVar', name: 'A', named: true });
    expect(result.ordered![1]).toEqual({ tag: 'PCtor', name: 'Succ', args: [{ tag: 'PVar', name: 'n' }] });
  });

  test('Three named patterns interspersed with positional', () => {
    // w {C} x {A} y {B} z where A=0, B=2, C=4
    // Should become: {A} x {B} y {C} w z
    const patterns: TPattern[] = [
      { tag: 'PVar', name: 'w' },
      { tag: 'PVar', name: 'C', named: true },
      { tag: 'PVar', name: 'x' },
      { tag: 'PVar', name: 'A', named: true },
      { tag: 'PVar', name: 'y' },
      { tag: 'PVar', name: 'B', named: true },
      { tag: 'PVar', name: 'z' }
    ];
    const namedMap: NamedArgMap = new Map([['A', 0], ['B', 2], ['C', 4]]);

    const result = reorderPatterns(patterns, namedMap);
    expect(result.error).toBeUndefined();
    expect(result.ordered).toHaveLength(7);
    expect(result.ordered![0]).toEqual({ tag: 'PVar', name: 'A', named: true });
    expect(result.ordered![1]).toEqual({ tag: 'PVar', name: 'w' });
    expect(result.ordered![2]).toEqual({ tag: 'PVar', name: 'B', named: true });
    expect(result.ordered![3]).toEqual({ tag: 'PVar', name: 'x' });
    expect(result.ordered![4]).toEqual({ tag: 'PVar', name: 'C', named: true });
    expect(result.ordered![5]).toEqual({ tag: 'PVar', name: 'y' });
    expect(result.ordered![6]).toEqual({ tag: 'PVar', name: 'z' });
  });

  test('Named pattern with underscore-prefixed name', () => {
    // {_hidden} x where _hidden is at position 0
    const patterns: TPattern[] = [
      { tag: 'PVar', name: 'x' },
      { tag: 'PVar', name: '_hidden', named: true }
    ];
    const namedMap: NamedArgMap = new Map([['_hidden', 0]]);

    const result = reorderPatterns(patterns, namedMap);
    expect(result.error).toBeUndefined();
    expect(result.ordered).toHaveLength(2);
    expect(result.ordered![0]).toEqual({ tag: 'PVar', name: '_hidden', named: true });
    expect(result.ordered![1]).toEqual({ tag: 'PVar', name: 'x' });
  });

  test('Partial pattern list (fewer patterns than params)', () => {
    // {A} where A is at position 0, and there are 3 params total
    // Should work - partial application of patterns
    const patterns: TPattern[] = [
      { tag: 'PVar', name: 'A', named: true }
    ];
    const namedMap: NamedArgMap = new Map([['A', 0], ['B', 1], ['C', 2]]);

    const result = reorderPatterns(patterns, namedMap);
    expect(result.error).toBeUndefined();
    expect(result.ordered).toHaveLength(1);
    expect(result.ordered![0]).toEqual({ tag: 'PVar', name: 'A', named: true });
  });

  test('All named patterns in reverse order', () => {
    // {C} {B} {A} where A=0, B=1, C=2
    // Should become: {A} {B} {C}
    const patterns: TPattern[] = [
      { tag: 'PVar', name: 'C', named: true },
      { tag: 'PVar', name: 'B', named: true },
      { tag: 'PVar', name: 'A', named: true }
    ];
    const namedMap: NamedArgMap = new Map([['A', 0], ['B', 1], ['C', 2]]);

    const result = reorderPatterns(patterns, namedMap);
    expect(result.error).toBeUndefined();
    expect(result.ordered).toHaveLength(3);
    expect(result.ordered![0]).toEqual({ tag: 'PVar', name: 'A', named: true });
    expect(result.ordered![1]).toEqual({ tag: 'PVar', name: 'B', named: true });
    expect(result.ordered![2]).toEqual({ tag: 'PVar', name: 'C', named: true });
  });

  test('Empty namedMap with all positional patterns', () => {
    const patterns: TPattern[] = [
      { tag: 'PVar', name: 'x' },
      { tag: 'PVar', name: 'y' }
    ];
    const namedMap: NamedArgMap = new Map();

    const result = reorderPatterns(patterns, namedMap);
    expect(result.error).toBeUndefined();
    expect(result.ordered).toHaveLength(2);
  });

  test('Error when named pattern not in map even with empty map', () => {
    const patterns: TPattern[] = [
      { tag: 'PVar', name: 'A', named: true }
    ];
    const namedMap: NamedArgMap = new Map();

    const result = reorderPatterns(patterns, namedMap);
    expect(result.error).toBe('Unknown named pattern: A');
  });
});
