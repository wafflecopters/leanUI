import { describe, test, expect } from 'vitest';
import { solveConstraints } from './meta';
import { MetaVar, Constraint } from '../types/tt-kernel';
import { mkLevelNum } from './kernel';

describe('Meta solving with universe level checking', () => {
  test('should reject solving Type-valued meta with Type when universe levels mismatch', () => {
    // Scenario: ?A : Type 0, trying to solve with Type 0
    // But Type 0 : Type 1, not Type 0!

    const metaVars = new Map<string, MetaVar>();
    metaVars.set('?A', {
      id: '?A',
      type: { tag: 'Sort', level: mkLevelNum(0) }, // ?A : Type 0
      ctx: [],
      isHole: false,
    });

    const constraints: Constraint[] = [
      {
        meta: '?A',
        rhs: { tag: 'Sort', level: mkLevelNum(0) }, // trying to solve with Type 0
        ctx: [],
      },
    ];

    // This should throw because Type 0 : Type 1, not Type 0
    expect(() => solveConstraints(metaVars, constraints)).toThrow(/universe level|type mismatch/i);
  });

  test('should accept solving Type-valued meta with Type when universe levels match', () => {
    // Scenario: ?A : Type 1, solving with Type 0
    // Type 0 : Type 1, so this is correct

    const metaVars = new Map<string, MetaVar>();
    metaVars.set('?A', {
      id: '?A',
      type: { tag: 'Sort', level: mkLevelNum(1) }, // ?A : Type 1
      ctx: [],
      isHole: false,
    });

    const constraints: Constraint[] = [
      {
        meta: '?A',
        rhs: { tag: 'Sort', level: mkLevelNum(0) }, // solving with Type 0
        ctx: [],
      },
    ];

    // This should succeed because Type 0 : Type 1
    expect(() => solveConstraints(metaVars, constraints)).not.toThrow();

    const result = solveConstraints(metaVars, constraints);
    expect(result.metaVars.get('?A')?.solution).toEqual({ tag: 'Sort', level: mkLevelNum(0) });
  });
});
