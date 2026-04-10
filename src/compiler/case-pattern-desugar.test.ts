import { describe, test, expect } from 'vitest';
import { desugarNestedCaseBranch } from './case-pattern-desugar';
import type { CaseBranch } from './surface';

describe('desugarNestedCaseBranch', () => {
  test('flat pattern is unchanged', () => {
    const branch: CaseBranch = {
      constructor: 'MkPair',
      params: [
        { tag: 'var', name: 'a' },
        { tag: 'var', name: 'b' },
      ],
      tactics: [{ name: 'exact', args: [{ tag: 'Const', name: 'a' }] }],
    };
    const result = desugarNestedCaseBranch(branch);
    expect(result).toBe(branch);  // No change for flat
  });

  test('single nested param desugars to inner cases', () => {
    const branch: CaseBranch = {
      constructor: 'MkDPair',
      params: [
        { tag: 'var', name: 'a' },
        { tag: 'ctor', constructor: 'MkPair', params: [
          { tag: 'var', name: 'x' },
          { tag: 'var', name: 'y' },
        ]},
      ],
      tactics: [{ name: 'exact', args: [{ tag: 'Const', name: 'a' }] }],
    };
    const result = desugarNestedCaseBranch(branch);

    // Top branch has flat params: [a, _nested?]
    expect(result.params).toHaveLength(2);
    expect(result.params[0]).toEqual({ tag: 'var', name: 'a' });
    expect(result.params[1].tag).toBe('var');
    const freshName = (result.params[1] as any).name;
    expect(freshName).toMatch(/^_nested\d+$/);

    // Tactics now wrap in inner cases
    expect(result.tactics).toHaveLength(1);
    expect(result.tactics[0].name).toBe('cases');
    expect(result.tactics[0].args[0]).toEqual({ tag: 'Const', name: freshName });
    const innerBranches = result.tactics[0].caseBranches!;
    expect(innerBranches).toHaveLength(1);
    expect(innerBranches[0].constructor).toBe('MkPair');
    expect(innerBranches[0].params).toEqual([
      { tag: 'var', name: 'x' },
      { tag: 'var', name: 'y' },
    ]);
    // Innermost tactics are the original ones
    expect(innerBranches[0].tactics).toEqual([{ name: 'exact', args: [{ tag: 'Const', name: 'a' }] }]);
  });

  test('deeply nested: | A (B (C x)) => exact x', () => {
    const branch: CaseBranch = {
      constructor: 'A',
      params: [{
        tag: 'ctor', constructor: 'B', params: [{
          tag: 'ctor', constructor: 'C', params: [
            { tag: 'var', name: 'x' },
          ],
        }],
      }],
      tactics: [{ name: 'exact', args: [{ tag: 'Const', name: 'x' }] }],
    };
    const result = desugarNestedCaseBranch(branch);

    // Top: | A _f1 =>
    expect(result.params).toHaveLength(1);
    expect(result.params[0].tag).toBe('var');

    // Tactic: cases _f1 with | B _f2 =>
    const outerCases = result.tactics[0];
    expect(outerCases.name).toBe('cases');
    const outerBranch = outerCases.caseBranches![0];
    expect(outerBranch.constructor).toBe('B');
    expect(outerBranch.params[0].tag).toBe('var');

    // Middle: cases _f2 with | C x =>
    const middleCases = outerBranch.tactics[0];
    expect(middleCases.name).toBe('cases');
    const middleBranch = middleCases.caseBranches![0];
    expect(middleBranch.constructor).toBe('C');
    expect(middleBranch.params).toEqual([{ tag: 'var', name: 'x' }]);

    // Innermost: original exact tactic
    expect(middleBranch.tactics).toEqual([{ name: 'exact', args: [{ tag: 'Const', name: 'x' }] }]);
  });
});
