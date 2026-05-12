import { describe, expect, test } from 'vitest';

import { computeBlockContributions, applyBlockContributions } from './compile-incremental-state';
import { createDefinitionsMap } from './term';

describe('incremental contribution helpers', () => {
  test('computeBlockContributions captures new definitions, symbols, and ctor params', () => {
    const beforeDefs = createDefinitionsMap();
    const afterDefs = createDefinitionsMap();

    afterDefs.terms.set('foo', {
      name: 'foo',
      type: { tag: 'Const', name: 'Nat' } as any,
    });
    afterDefs.inductiveTypes.set('Nat', {
      name: 'Nat',
      type: { tag: 'Const', name: 'Type' } as any,
      constructors: [{ name: 'Zero', type: { tag: 'Const', name: 'Nat' } as any }],
      indexPositions: [],
    });
    afterDefs.inductiveNameOfConstructor.set('Zero', 'Nat');

    const contributions = computeBlockContributions(
      beforeDefs,
      afterDefs,
      new Set<string>(),
      new Set<string>(['foo', 'Nat', 'Zero']),
      new Map(),
      new Map([['Zero', [] as any]]),
    );

    expect(contributions.terms.map(([name]) => name)).toEqual(['foo']);
    expect(contributions.inductiveTypes.map(([name]) => name)).toEqual(['Nat']);
    expect(contributions.constructorMappings).toEqual([['Zero', 'Nat']]);
    expect(contributions.symbolNames).toEqual(['foo', 'Nat', 'Zero']);
    expect(contributions.constructorParamEntries.map(([name]) => name)).toEqual(['Zero']);
  });

  test('applyBlockContributions replays captured state into fresh accumulators', () => {
    const baseDefs = createDefinitionsMap();
    const contributions = {
      terms: [['foo', { name: 'foo', type: { tag: 'Const', name: 'Nat' } as any }]] as [string, any][],
      inductiveTypes: [[
        'Nat',
        {
          name: 'Nat',
          type: { tag: 'Const', name: 'Type' } as any,
          constructors: [{ name: 'Zero', type: { tag: 'Const', name: 'Nat' } as any }],
          indexPositions: [],
        },
      ]] as [string, any][],
      constructorMappings: [['Zero', 'Nat']] as [string, string][],
      symbolNames: ['foo', 'Nat', 'Zero'],
      constructorParamEntries: [['Zero', [] as any]] as [string, unknown[]][],
    };

    const replayed = applyBlockContributions(
      baseDefs,
      new Set<string>(),
      new Map(),
      contributions,
    );

    expect(replayed.definitions.terms.has('foo')).toBe(true);
    expect(replayed.definitions.inductiveTypes.has('Nat')).toBe(true);
    expect(replayed.definitions.inductiveNameOfConstructor.get('Zero')).toBe('Nat');
    expect(replayed.symbolContext.has('foo')).toBe(true);
    expect(replayed.symbolContext.has('Nat')).toBe(true);
    expect(replayed.constructorParamNames.has('Zero')).toBe(true);
  });
});
