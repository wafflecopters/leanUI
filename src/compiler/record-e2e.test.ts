/**
 * End-to-end tests for record declarations.
 * Tests the full pipeline: parse → elaborate → type check.
 *
 * NOTE: Simple record tests have been migrated to .tt files in src/test-programs/records/.
 * This file contains only tests that require programmatic assertions beyond what .tt files support.
 */

import { describe, test, expect } from 'vitest';
import { compileTTFromText, CompiledDeclaration } from './compile';

// Helper to find a declaration by name across all blocks
function findDecl(result: ReturnType<typeof compileTTFromText>, name: string): CompiledDeclaration | undefined {
  return result.blocks.flatMap(b => b.declarations).find(d => d.name === name);
}

describe('Record E2E Tests', () => {
  describe('Record type annotations', () => {
    test('record with Prop annotation has Prop type', () => {
      const source = `
record TrueProof : Prop where
`;
      const result = compileTTFromText(source);
      expect(result.success).toBe(true);

      const decl = findDecl(result, 'TrueProof');
      expect(decl).toBeDefined();
      expect(decl?.checkSuccess).toBe(true);

      // Verify the kernel type is actually Prop (Sort with level 0), not Type
      // The record type should be: Prop (= Sort 0)
      const kernelType = decl?.kernelType;
      expect(kernelType?.tag).toBe('Sort');
      if (kernelType?.tag === 'Sort') {
        // Prop = Sort 0, Type n = Sort (n+1)
        // Check it's universe level 0 (Prop)
        expect(kernelType.level.tag).toBe('ULit');
        if (kernelType.level.tag === 'ULit') {
          expect(kernelType.level.n).toBe(0);
        }
      }
    });

    test('parameterized record with Type annotation has Type type', () => {
      const source = `
record Box (A : Type) : Type where
  contents : A
`;
      const result = compileTTFromText(source);
      expect(result.success).toBe(true);

      const boxDecl = findDecl(result, 'Box');
      expect(boxDecl).toBeDefined();
      expect(boxDecl?.checkSuccess).toBe(true);

      // Verify the kernel type ends in Type (not Prop)
      // Box : (A : Type) → Type
      // Find the result sort by traversing through the Pi binders
      let currentType = boxDecl?.kernelType;
      while (currentType?.tag === 'Binder' && currentType.binderKind.tag === 'BPi') {
        currentType = currentType.body;
      }
      // Now currentType should be the result sort: Type = Sort (some level > 0)
      expect(currentType?.tag).toBe('Sort');
      if (currentType?.tag === 'Sort') {
        // Type has level > 0 (not ULit 0 which is Prop)
        // It's represented as App(Const("USucc"), ULit(0)) or similar
        // Just verify it's not the Prop level
        const isNotProp = !(currentType.level.tag === 'ULit' && currentType.level.n === 0);
        expect(isNotProp).toBe(true);
      }
    });

    test('record with universe level in type annotation parses', () => {
      const source = `
record Box {u : ULevel} (A : Type u) : Type (USucc u) where
  unbox : A
`;
      const result = compileTTFromText(source);
      // Note: Full type checking of universe-polymorphic records is not yet implemented.
      // This test just verifies that the parser handles the syntax correctly.
      expect(result.blocks[0].parseErrors).toHaveLength(0);

      const boxDecl = findDecl(result, 'Box');
      expect(boxDecl).toBeDefined();
    });

    test('record type annotation with extends parses', () => {
      const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

record Base : Type where
  x : Nat

record Extended : Type extends Base where
  y : Nat
`;
      const result = compileTTFromText(source);
      // Note: extends is not fully implemented yet, so we just check parsing works
      // The extends clause may cause check errors until fully implemented
      expect(result.blocks[0].parseErrors).toHaveLength(0);
    });
  });

  describe('Extends clause with parameters', () => {
    test('extends with applied type parameter parses', () => {
      const source = `
record Pred (alpha : Type) : Prop where
  p : alpha

record DecPred (alpha : Type) extends Pred alpha where
  extra : alpha
`;
      const result = compileTTFromText(source);
      // Just verify parsing works - full extends implementation is separate
      expect(result.blocks[0].parseErrors).toHaveLength(0);
    });
  });

  describe('Custom constructor names', () => {
    test('record with custom constructor name compiles', () => {
      const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

record Point where
  constructor MkPoint
  x : Nat
  y : Nat
`;
      const result = compileTTFromText(source);
      expect(result.success).toBe(true);

      const pointDecl = findDecl(result, 'Point');
      expect(pointDecl).toBeDefined();
      expect(pointDecl?.checkSuccess).toBe(true);

      // Verify constructor name is MkPoint
      const ctors = pointDecl?.kernelConstructors;
      expect(ctors).toHaveLength(1);
      expect(ctors?.[0].name).toBe('MkPoint');
    });
  });
});
