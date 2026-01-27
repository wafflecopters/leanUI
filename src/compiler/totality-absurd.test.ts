import { describe, test, expect } from 'vitest';
import { compileSource } from '../test-utils';
import { CaseTree } from './totality';

/**
 * Tests for case tree structure when all clauses are absurd.
 *
 * When a function has all absurd clauses (either zero clauses with uninhabited
 * argument type, or all clauses marked with #absurd), the case tree should
 * be { tag: 'Absurd' }, not { tag: 'Uncovered' }.
 */
describe('Totality - Absurd Case Trees', () => {
  describe('Zero-clause functions with uninhabited types', () => {
    test('absurd : Void -> A should have Absurd case tree, not Uncovered', () => {
      const source = `
inductive Void : Type where

absurd : {A : Type} -> Void -> A
`;
      const results = compileSource(source);
      const absurdBlock = results.find(r => r.name === 'absurd');

      expect(absurdBlock).toBeDefined();
      expect(absurdBlock!.checkSuccess).toBe(true);

      const absurdDecl = absurdBlock!.declarations[0];
      expect(absurdDecl.totalityResult).toBeDefined();

      const caseTree = absurdDecl.totalityResult!.caseTree;
      expect(caseTree).toBeDefined();

      // The case tree should be Absurd, not Uncovered
      expect(caseTree!.tag).toBe('Absurd');
    });

    test('absurd with explicit A parameter should have Absurd case tree', () => {
      const source = `
inductive Void : Type where

absurd : (A : Type) -> Void -> A
`;
      const results = compileSource(source);
      const absurdBlock = results.find(r => r.name === 'absurd');

      expect(absurdBlock).toBeDefined();
      expect(absurdBlock!.checkSuccess).toBe(true);

      const absurdDecl = absurdBlock!.declarations[0];
      expect(absurdDecl.totalityResult).toBeDefined();

      const caseTree = absurdDecl.totalityResult!.caseTree;
      expect(caseTree!.tag).toBe('Absurd');
    });
  });

  describe('#absurd clauses with impossible patterns', () => {
    test('zeroNeqSucc with refl pattern should have Absurd case tree', () => {
      const source = `
inductive Void : Type where

inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Equal : {A : Type} -> A -> A -> Type where
  refl : {A : Type} -> {a : A} -> Equal a a

zeroNeqSucc : {n : Nat} -> Equal Zero (Succ n) -> Void
zeroNeqSucc refl = #absurd
`;
      const results = compileSource(source);
      const fnBlock = results.find(r => r.name === 'zeroNeqSucc');

      expect(fnBlock).toBeDefined();
      expect(fnBlock!.checkSuccess).toBe(true);

      const fnDecl = fnBlock!.declarations[0];
      expect(fnDecl.totalityResult).toBeDefined();

      const caseTree = fnDecl.totalityResult!.caseTree;
      expect(caseTree).toBeDefined();

      // The case tree should be Absurd since the only clause is absurd
      expect(caseTree!.tag).toBe('Absurd');
    });

    test('Vec head with nil absurd clause and cons valid clause', () => {
      const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Vec : Type -> Nat -> Type where
  nil : (A : Type) -> Vec A Zero
  cons : (A : Type) -> (n : Nat) -> A -> Vec A n -> Vec A (Succ n)

head : (A : Type) -> (n : Nat) -> Vec A (Succ n) -> A
head A n (nil _) = #absurd
head A n (cons _ _ x _) = x
`;
      const results = compileSource(source);
      const fnBlock = results.find(r => r.name === 'head');

      expect(fnBlock).toBeDefined();
      expect(fnBlock!.checkSuccess).toBe(true);

      const fnDecl = fnBlock!.declarations[0];
      expect(fnDecl.totalityResult).toBeDefined();

      // This is a mixed case - one absurd clause (filtered), one valid clause
      // The case tree structure depends on how #absurd clauses are filtered
      // The important thing is that the function is exhaustive
      expect(fnDecl.totalityResult!.isExhaustive).toBe(true);
    });
  });

  describe('Empty type splits', () => {
    test('function taking Void should have Split with no branches (empty)', () => {
      const source = `
inductive Void : Type where

id : Void -> Void
`;
      const results = compileSource(source);
      const fnBlock = results.find(r => r.name === 'id');

      expect(fnBlock).toBeDefined();
      expect(fnBlock!.checkSuccess).toBe(true);

      const fnDecl = fnBlock!.declarations[0];
      expect(fnDecl.totalityResult).toBeDefined();

      const caseTree = fnDecl.totalityResult!.caseTree;
      // Should be Absurd since Void has no constructors
      expect(caseTree!.tag).toBe('Absurd');
    });
  });

  describe('isExhaustive flag for absurd cases', () => {
    test('absurd function should be exhaustive', () => {
      const source = `
inductive Void : Type where

absurd : {A : Type} -> Void -> A
`;
      const results = compileSource(source);
      const absurdBlock = results.find(r => r.name === 'absurd');

      const absurdDecl = absurdBlock!.declarations[0];
      expect(absurdDecl.totalityResult!.isExhaustive).toBe(true);
    });

    test('zeroNeqSucc should be exhaustive', () => {
      const source = `
inductive Void : Type where

inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Equal : {A : Type} -> A -> A -> Type where
  refl : {A : Type} -> {a : A} -> Equal a a

zeroNeqSucc : {n : Nat} -> Equal Zero (Succ n) -> Void
zeroNeqSucc refl = #absurd
`;
      const results = compileSource(source);
      const fnBlock = results.find(r => r.name === 'zeroNeqSucc');

      const fnDecl = fnBlock!.declarations[0];
      expect(fnDecl.totalityResult!.isExhaustive).toBe(true);
    });
  });
});
