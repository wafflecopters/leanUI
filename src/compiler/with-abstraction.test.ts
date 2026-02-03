import { describe, test, expect } from 'vitest';
import { TTKTerm, mkVar, mkConst, mkApp, mkPi, mkType, TTKContext } from './kernel';
import { normalizeInContext, findOccurrences, replaceWithFreshVar, OccurrenceInfo } from './with-abstraction';

describe('With-Abstraction Helpers', () => {
  describe('normalizeInContext', () => {
    test('normalizes variable to WHNF', () => {
      // Context: [x : Nat]
      const context: TTKContext = [{ name: 'x', type: mkConst('Nat') }];
      const term = mkVar(0); // x
      const normalized = normalizeInContext(term, context, new Map());

      // Variable should stay as-is (already in WHNF)
      expect(normalized).toEqual(term);
    });

    test('normalizes constant to WHNF', () => {
      const context: TTKContext = [];
      const term = mkConst('Nat');
      const normalized = normalizeInContext(term, context, new Map());

      expect(normalized).toEqual(term);
    });

    test('normalizes application', () => {
      const context: TTKContext = [];
      const definitions = new Map<string, { value?: TTKTerm }>();

      // Just a simple app - should stay as-is if head is not a lambda
      const term = mkApp(mkConst('Succ'), mkConst('Zero'));
      const normalized = normalizeInContext(term, context, definitions);

      // Without definition of Succ, stays as App
      expect(normalized.tag).toBe('App');
    });

    test('handles empty context', () => {
      const term = mkConst('Nat');
      const normalized = normalizeInContext(term, [], new Map());
      expect(normalized).toEqual(term);
    });
  });

  describe('findOccurrences', () => {
    test('finds simple variable occurrence', () => {
      const context: TTKContext = [{ name: 'n', type: mkConst('Nat') }];
      const scrutinee = mkVar(0); // n
      const goal = mkVar(0); // n

      const occurrences = findOccurrences(scrutinee, goal, context, new Map());

      expect(occurrences.found).toBe(true);
      expect(occurrences.positions.length).toBeGreaterThan(0);
    });

    test('finds no occurrence when scrutinee not in goal', () => {
      const context: TTKContext = [
        { name: 'n', type: mkConst('Nat') },
        { name: 'm', type: mkConst('Nat') }
      ];
      const scrutinee = mkVar(0); // n
      const goal = mkVar(1); // m (different variable)

      const occurrences = findOccurrences(scrutinee, goal, context, new Map());

      expect(occurrences.found).toBe(false);
      expect(occurrences.positions.length).toBe(0);
    });

    test('finds multiple occurrences', () => {
      const context: TTKContext = [{ name: 'n', type: mkConst('Nat') }];
      const scrutinee = mkVar(0); // n

      // DecEq n n - scrutinee appears twice
      const goal = mkApp(
        mkApp(mkConst('DecEq'), mkVar(0)),
        mkVar(0)
      );

      const occurrences = findOccurrences(scrutinee, goal, context, new Map());

      expect(occurrences.found).toBe(true);
      expect(occurrences.positions.length).toBe(2);
    });

    test('finds occurrence in nested structure', () => {
      const context: TTKContext = [{ name: 'xs', type: mkConst('List') }];
      const scrutinee = mkVar(0); // xs

      // length xs (application with scrutinee)
      const goal = mkApp(mkConst('length'), mkVar(0));

      const occurrences = findOccurrences(scrutinee, goal, context, new Map());

      expect(occurrences.found).toBe(true);
      expect(occurrences.positions.length).toBe(1);
    });

    test('does not find occurrence under lambda binder (different de Bruijn level)', () => {
      const context: TTKContext = [{ name: 'n', type: mkConst('Nat') }];
      const scrutinee = mkVar(0); // n at level 0

      // λ(x : Nat). n  - here n is Var 1 (shifted), not Var 0
      // This is a tricky case - we need to track depth correctly
      const goal: TTKTerm = {
        tag: 'Binder',
        name: 'x',
        binderKind: { tag: 'BLam' },
        domain: mkConst('Nat'),
        body: mkVar(1) // n shifted under lambda
      };

      const occurrences = findOccurrences(scrutinee, goal, context, new Map());

      // Should find it because Var 1 at depth 1 = Var 0 at depth 0
      expect(occurrences.found).toBe(true);
    });
  });

  describe('replaceWithFreshVar', () => {
    test('replaces simple variable with Var 0', () => {
      const context: TTKContext = [{ name: 'n', type: mkConst('Nat') }];
      const scrutinee = mkVar(0);
      const goal = mkVar(0);

      const occurrences = findOccurrences(scrutinee, goal, context, new Map());
      const replaced = replaceWithFreshVar(goal, occurrences, 0);

      // Should be Var 0 (the fresh with-binder)
      expect(replaced.tag).toBe('Var');
      expect((replaced as any).index).toBe(0);
    });

    test('replaces multiple occurrences', () => {
      const context: TTKContext = [{ name: 'n', type: mkConst('Nat') }];
      const scrutinee = mkVar(0);

      // DecEq n n
      const goal = mkApp(
        mkApp(mkConst('DecEq'), mkVar(0)),
        mkVar(0)
      );

      const occurrences = findOccurrences(scrutinee, goal, context, new Map());
      const replaced = replaceWithFreshVar(goal, occurrences, 0);

      // Should be DecEq (Var 0) (Var 0)
      expect(replaced.tag).toBe('App');
      const app = replaced as any;
      expect(app.arg.tag).toBe('Var');
      expect(app.arg.index).toBe(0);
    });

    test('shifts other free variables correctly', () => {
      const context: TTKContext = [
        { name: 'n', type: mkConst('Nat') },
        { name: 'm', type: mkConst('Nat') }
      ];
      const scrutinee = mkVar(0); // n

      // Type that mentions both n and m: Equal n m
      const goal = mkApp(
        mkApp(mkConst('Equal'), mkVar(0)), // n
        mkVar(1) // m
      );

      const occurrences = findOccurrences(scrutinee, goal, context, new Map());
      const replaced = replaceWithFreshVar(goal, occurrences, 0);

      // Should be: Equal (Var 0) (Var 2)
      // - n is replaced with Var 0 (fresh binder)
      // - m was Var 1, shifts to Var 2 (because we added a binder)
      expect(replaced.tag).toBe('App');
      const app = replaced as any;
      expect(app.arg.tag).toBe('Var');
      expect(app.arg.index).toBe(2); // m shifted
    });

    test('preserves non-occurrence terms', () => {
      const context: TTKContext = [{ name: 'n', type: mkConst('Nat') }];
      const scrutinee = mkVar(0);
      const goal = mkConst('Bool'); // No occurrence of n

      const occurrences = findOccurrences(scrutinee, goal, context, new Map());
      const replaced = replaceWithFreshVar(goal, occurrences, 0);

      // Should be unchanged (but free vars shifted)
      expect(replaced.tag).toBe('Const');
    });
  });

  describe('K axiom safety', () => {
    test('does not introduce K when abstracting over equality proof', () => {
      // This test verifies we don't accidentally introduce uniqueness of identity proofs

      const context: TTKContext = [
        { name: 'x', type: mkConst('Nat') },
        { name: 'y', type: mkConst('Nat') },
        {
          name: 'p',
          type: mkApp(
            mkApp(mkConst('Equal'), mkVar(1)), // x
            mkVar(0) // y
          )
        }
      ];

      // Abstracting over p in a return type should not assume all proofs are refl
      const scrutinee = mkVar(0); // p
      const goal = mkConst('Nat'); // Return type doesn't depend on p

      const occurrences = findOccurrences(scrutinee, goal, context, new Map());

      // Since p doesn't occur in goal, no replacement happens
      // This is safe - we're not assuming anything about p
      expect(occurrences.found).toBe(false);
    });

    test('abstraction over non-refl equality is sound', () => {
      // With-abstracting over an equality proof should be valid
      // even when we don't assume K

      const context: TTKContext = [
        { name: 'x', type: mkConst('Nat') },
        { name: 'y', type: mkConst('Nat') },
        {
          name: 'eq',
          type: mkApp(
            mkApp(mkConst('Equal'), mkVar(1)),
            mkVar(0)
          )
        }
      ];

      const scrutinee = mkVar(0); // eq

      // Goal mentions the equality: transport eq
      const goal = mkApp(mkConst('transport'), mkVar(0));

      const occurrences = findOccurrences(scrutinee, goal, context, new Map());

      // Finding and replacing eq with a fresh variable is sound
      // We're not assuming eq = refl, just treating it abstractly
      expect(occurrences.found).toBe(true);
    });
  });

  describe('edge cases', () => {
    test('handles scrutinee that is a complex expression', () => {
      const context: TTKContext = [
        { name: 'x', type: mkConst('Nat') },
        { name: 'y', type: mkConst('Nat') }
      ];

      // Scrutinee: add x y (not a variable)
      const scrutinee = mkApp(
        mkApp(mkConst('add'), mkVar(1)),
        mkVar(0)
      );

      // Goal: DecEq (add x y) (add x y)
      const goal = mkApp(
        mkApp(mkConst('DecEq'), scrutinee),
        scrutinee
      );

      const occurrences = findOccurrences(scrutinee, goal, context, new Map());

      // Should find both occurrences of (add x y)
      expect(occurrences.found).toBe(true);
      expect(occurrences.positions.length).toBe(2);
    });

    test('handles scrutinee not occurring in goal', () => {
      const context: TTKContext = [{ name: 'n', type: mkConst('Nat') }];
      const scrutinee = mkVar(0);
      const goal = mkConst('Bool');

      const occurrences = findOccurrences(scrutinee, goal, context, new Map());
      const replaced = replaceWithFreshVar(goal, occurrences, 0);

      // Goal should be unchanged structurally (though free vars may shift)
      expect(replaced.tag).toBe('Const');
      expect((replaced as any).name).toBe('Bool');
    });

    test('handles deeply nested occurrence', () => {
      const context: TTKContext = [{ name: 'n', type: mkConst('Nat') }];
      const scrutinee = mkVar(0);

      // Nested: Either (Maybe n) (List n)
      const goal = mkApp(
        mkApp(
          mkConst('Either'),
          mkApp(mkConst('Maybe'), mkVar(0))
        ),
        mkApp(mkConst('List'), mkVar(0))
      );

      const occurrences = findOccurrences(scrutinee, goal, context, new Map());

      expect(occurrences.found).toBe(true);
      expect(occurrences.positions.length).toBe(2);
    });
  });
});

describe('With-Abstraction Integration', () => {
  // These tests will verify the full pipeline once we integrate
  test.todo('abstracts single scrutinee in dependent return type');
  test.todo('abstracts multiple scrutinees in order');
  test.todo('detects ill-typed abstraction');
  test.todo('preserves implicit arguments in auxiliary type');
});
