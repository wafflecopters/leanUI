import { describe, it, expect } from 'vitest';
import { padPatternsForMissingNamedArgs } from './patterns';
import { TTKPattern } from './kernel';
import { DefinitionsMap, createDefinitionsMap, NamedArgMap } from './term';

describe('padPatternsForMissingNamedArgs', () => {
  // Helper to create a simple definitions map with some constructors
  function createTestDefinitions(): DefinitionsMap {
    const defs = createDefinitionsMap();

    // Add List type with Nil and Cons constructors
    // List : {A : Type} -> Type
    // Nil : {A : Type} -> List A
    // Cons : {A : Type} -> A -> List A -> List A

    // namedArgMap for Nil: A is at position 0
    const nilNamedArgMap: NamedArgMap = new Map([['A', 0]]);

    // namedArgMap for Cons: A is at position 0
    const consNamedArgMap: NamedArgMap = new Map([['A', 0]]);

    defs.inductiveTypes.set('List', {
      name: 'List',
      type: {
        tag: 'Binder',
        name: 'A',
        binderKind: { tag: 'BPi' },
        domain: { tag: 'Sort', level: { tag: 'ULit', n: 1 } },
        body: { tag: 'Sort', level: { tag: 'ULit', n: 1 } }
      },
      constructors: [
        {
          name: 'Nil',
          type: {
            tag: 'Binder',
            name: 'A',
            binderKind: { tag: 'BPi' },
            domain: { tag: 'Sort', level: { tag: 'ULit', n: 1 } },
            body: { tag: 'App', fn: { tag: 'Const', name: 'List' }, arg: { tag: 'Var', index: 0 } }
          },
          namedArgMap: nilNamedArgMap  // A is a named parameter
        },
        {
          name: 'Cons',
          type: {
            tag: 'Binder',
            name: 'A',
            binderKind: { tag: 'BPi' },
            domain: { tag: 'Sort', level: { tag: 'ULit', n: 1 } },
            body: {
              tag: 'Binder',
              name: 'head',
              binderKind: { tag: 'BPi' },
              domain: { tag: 'Var', index: 0 },
              body: {
                tag: 'Binder',
                name: 'tail',
                binderKind: { tag: 'BPi' },
                domain: { tag: 'App', fn: { tag: 'Const', name: 'List' }, arg: { tag: 'Var', index: 1 } },
                body: { tag: 'App', fn: { tag: 'Const', name: 'List' }, arg: { tag: 'Var', index: 2 } }
              }
            }
          },
          namedArgMap: consNamedArgMap  // A is a named parameter (position 0), head and tail are positional
        }
      ],
      indexPositions: []  // List has no indices (it's not an indexed type)
    });

    return defs;
  }

  describe('top-level function named parameters', () => {
    it('should pad top-level patterns for missing named function params', () => {
      const definitions = createTestDefinitions();

      // listLen : {A : Type} -> List A -> Nat
      // namedArgMap: A is at position 0
      // totalArity: 2
      const namedArgMap: NamedArgMap = new Map([['A', 0]]);
      const totalArity = 2;

      // User writes: listLen Nil = Zero
      // Patterns: [Nil]
      const inputPatterns: TTKPattern[] = [
        { tag: 'PCtor', name: 'Nil', args: [] }
      ];

      // Expected: [_, (Nil _)]
      // - Insert wildcard for {A : Type} at position 0
      // - Nil gets a wildcard for its named A param
      const result = padPatternsForMissingNamedArgs(inputPatterns, namedArgMap, totalArity, definitions);

      expect(result.length).toBe(2);
      expect(result[0]).toEqual({ tag: 'PWild', name: '_' });
      expect(result[1].tag).toBe('PCtor');
      if (result[1].tag === 'PCtor') {
        expect(result[1].name).toBe('Nil');
        expect(result[1].args.length).toBe(1);
        expect(result[1].args[0]).toEqual({ tag: 'PWild', name: '_' });
      }
    });

    it('should not pad when all named params are provided', () => {
      const definitions = createTestDefinitions();

      // listLen : {A : Type} -> List A -> Nat
      const namedArgMap: NamedArgMap = new Map([['A', 0]]);
      const totalArity = 2;

      // User writes: listLen _ Nil = Zero (explicit wildcard for A)
      const inputPatterns: TTKPattern[] = [
        { tag: 'PWild', name: '_' },
        { tag: 'PCtor', name: 'Nil', args: [] }
      ];

      const result = padPatternsForMissingNamedArgs(inputPatterns, namedArgMap, totalArity, definitions);

      // Top level should stay [_, (Nil _)] - no change to count
      // But Nil still gets padded for its named param
      expect(result.length).toBe(2);
      expect(result[0]).toEqual({ tag: 'PWild', name: '_' });
      expect(result[1].tag).toBe('PCtor');
      if (result[1].tag === 'PCtor') {
        expect(result[1].name).toBe('Nil');
        expect(result[1].args.length).toBe(1);
      }
    });
  });

  describe('constructor named parameters', () => {
    it('should recursively pad constructor patterns for missing named args', () => {
      const definitions = createTestDefinitions();

      // Function without named params: length : List Nat -> Nat
      // No top-level named params
      const namedArgMap: NamedArgMap = new Map();
      const totalArity = 1;

      // User writes: length (Cons x xs) = ...
      // Cons has {A : Type} -> A -> List A -> List A
      // So Cons needs 1 named param + 2 positional
      const inputPatterns: TTKPattern[] = [
        {
          tag: 'PCtor',
          name: 'Cons',
          args: [
            { tag: 'PVar', name: 'x' },
            { tag: 'PVar', name: 'xs' }
          ]
        }
      ];

      const result = padPatternsForMissingNamedArgs(inputPatterns, namedArgMap, totalArity, definitions);

      // Should become: [(Cons _ x xs)]
      expect(result.length).toBe(1);
      expect(result[0].tag).toBe('PCtor');
      if (result[0].tag === 'PCtor') {
        expect(result[0].name).toBe('Cons');
        expect(result[0].args.length).toBe(3);
        expect(result[0].args[0]).toEqual({ tag: 'PWild', name: '_' });
        expect(result[0].args[1]).toEqual({ tag: 'PVar', name: 'x' });
        expect(result[0].args[2]).toEqual({ tag: 'PVar', name: 'xs' });
      }
    });

    it('should handle nested constructors', () => {
      const definitions = createTestDefinitions();

      // Function: f : List (List Nat) -> Nat
      // No top-level named params
      const namedArgMap: NamedArgMap = new Map();
      const totalArity = 1;

      // User writes: f (Cons Nil xs) = ...
      // Both Cons and Nil have named params
      const inputPatterns: TTKPattern[] = [
        {
          tag: 'PCtor',
          name: 'Cons',
          args: [
            { tag: 'PCtor', name: 'Nil', args: [] },
            { tag: 'PVar', name: 'xs' }
          ]
        }
      ];

      const result = padPatternsForMissingNamedArgs(inputPatterns, namedArgMap, totalArity, definitions);

      // Should become: [(Cons _ (Nil _) xs)]
      expect(result.length).toBe(1);
      expect(result[0].tag).toBe('PCtor');
      if (result[0].tag === 'PCtor') {
        expect(result[0].name).toBe('Cons');
        expect(result[0].args.length).toBe(3);
        expect(result[0].args[0]).toEqual({ tag: 'PWild', name: '_' });
        // Nested Nil should also be padded
        const nilArg = result[0].args[1];
        expect(nilArg.tag).toBe('PCtor');
        if (nilArg.tag === 'PCtor') {
          expect(nilArg.name).toBe('Nil');
          expect(nilArg.args.length).toBe(1);
          expect(nilArg.args[0]).toEqual({ tag: 'PWild', name: '_' });
        }
      }
    });
  });

  describe('both top-level and constructor padding', () => {
    it('should handle both levels of padding together', () => {
      const definitions = createTestDefinitions();

      // listLen : {A : Type} -> List A -> Nat
      const namedArgMap: NamedArgMap = new Map([['A', 0]]);
      const totalArity = 2;

      // User writes: listLen (Cons x xs) = ...
      // Missing: top-level A, Cons's A param
      const inputPatterns: TTKPattern[] = [
        {
          tag: 'PCtor',
          name: 'Cons',
          args: [
            { tag: 'PVar', name: 'x' },
            { tag: 'PVar', name: 'xs' }
          ]
        }
      ];

      const result = padPatternsForMissingNamedArgs(inputPatterns, namedArgMap, totalArity, definitions);

      // Should become: [_, (Cons _ x xs)]
      expect(result.length).toBe(2);
      expect(result[0]).toEqual({ tag: 'PWild', name: '_' });
      expect(result[1].tag).toBe('PCtor');
      if (result[1].tag === 'PCtor') {
        expect(result[1].name).toBe('Cons');
        expect(result[1].args.length).toBe(3);
        expect(result[1].args[0]).toEqual({ tag: 'PWild', name: '_' });
      }
    });
  });

  describe('no named parameters', () => {
    it('should return patterns unchanged when no named params exist', () => {
      const definitions = createDefinitionsMap();  // Empty definitions

      // Function: f : Nat -> Nat (no named params)
      const namedArgMap: NamedArgMap = new Map();
      const totalArity = 1;

      const inputPatterns: TTKPattern[] = [
        { tag: 'PVar', name: 'n' }
      ];

      const result = padPatternsForMissingNamedArgs(inputPatterns, namedArgMap, totalArity, definitions);

      expect(result.length).toBe(1);
      expect(result[0]).toEqual({ tag: 'PVar', name: 'n' });
    });

    it('should handle undefined namedArgMap', () => {
      const definitions = createDefinitionsMap();

      const inputPatterns: TTKPattern[] = [
        { tag: 'PVar', name: 'n' }
      ];

      const result = padPatternsForMissingNamedArgs(inputPatterns, undefined, undefined, definitions);

      expect(result.length).toBe(1);
      expect(result[0]).toEqual({ tag: 'PVar', name: 'n' });
    });
  });
});
