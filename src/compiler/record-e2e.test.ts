/**
 * End-to-end tests for record declarations.
 * Tests the full pipeline: parse → elaborate → type check.
 */

import { describe, test, expect } from 'vitest';
import { compileTTFromText, CompiledDeclaration } from './compile';

// Helper to find a declaration by name across all blocks
function findDecl(result: ReturnType<typeof compileTTFromText>, name: string): CompiledDeclaration | undefined {
  return result.blocks.flatMap(b => b.declarations).find(d => d.name === name);
}

describe('Record E2E Tests', () => {
  describe('Simple records', () => {
    test('empty record compiles', () => {
      const source = `
record Unit where
`;
      const result = compileTTFromText(source);
      expect(result.success).toBe(true);
      expect(result.blocks[0].declarations).toHaveLength(1);
      expect(result.blocks[0].declarations[0].name).toBe('Unit');
      expect(result.blocks[0].declarations[0].kind).toBe('inductive');
    });

    test('record with single field compiles', () => {
      const source = `inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

record Wrapper where
  value : Nat`;
      const result = compileTTFromText(source);
      if (!result.success) {
        console.log('Blocks:', result.blocks.length);
        console.log('Decl names:', result.blocks.flatMap(b => b.declarations.map(d => d.name)));
        console.log('Parse errors:', result.blocks.flatMap(b => b.parseErrors));
        console.log('Check errors:', JSON.stringify(result.blocks.flatMap(b => b.declarations.flatMap(d => d.checkErrors?.map(e => e.message) || [])), null, 2));
      }
      expect(result.success).toBe(true);

      // Should have Nat inductive and Wrapper record
      const wrapperDecl = findDecl(result, 'Wrapper');
      expect(wrapperDecl).toBeDefined();
      expect(wrapperDecl?.kind).toBe('inductive');
      expect(wrapperDecl?.checkSuccess).toBe(true);
    });

    test('record with multiple fields compiles', () => {
      const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

record Point where
  x : Nat
  y : Nat
`;
      const result = compileTTFromText(source);
      expect(result.success).toBe(true);

      const pointDecl = findDecl(result, 'Point');
      expect(pointDecl).toBeDefined();
      expect(pointDecl?.checkSuccess).toBe(true);
    });
  });

  describe('Parameterized records', () => {
    test('record with type parameter compiles', () => {
      const source = `
record Box (A : Type) where
  contents : A
`;
      const result = compileTTFromText(source);
      expect(result.success).toBe(true);

      const boxDecl = findDecl(result, 'Box');
      expect(boxDecl).toBeDefined();
      expect(boxDecl?.checkSuccess).toBe(true);
    });

    test('Pair record with two type parameters compiles', () => {
      const source = `
record Pair (A : Type) (B : Type) where
  fst : A
  snd : B
`;
      const result = compileTTFromText(source);
      expect(result.success).toBe(true);

      const pairDecl = findDecl(result, 'Pair');
      expect(pairDecl).toBeDefined();
      expect(pairDecl?.checkSuccess).toBe(true);
    });

    test('record with multi-var binder compiles', () => {
      const source = `
record Pair (A B : Type) where
  fst : A
  snd : B
`;
      const result = compileTTFromText(source);
      expect(result.success).toBe(true);

      const pairDecl = findDecl(result, 'Pair');
      expect(pairDecl).toBeDefined();
      expect(pairDecl?.checkSuccess).toBe(true);
    });

    test('record with mixed explicit and implicit multi-var binders compiles', () => {
      const source = `
record Foo (A B : Type) {C D : Type} where
  x : A
  y : C
`;
      const result = compileTTFromText(source);
      if (!result.success) {
        console.log('Parse errors:', result.blocks.flatMap(b => b.parseErrors.map(e => e.message || e)));
        console.log('Check errors:', result.blocks.flatMap(b => b.declarations.flatMap(d => d.checkErrors?.map(e => e.message) || [])));
      }
      expect(result.success).toBe(true);

      const fooDecl = findDecl(result, 'Foo');
      expect(fooDecl).toBeDefined();
      expect(fooDecl?.checkSuccess).toBe(true);
    });
  });

  describe('Record type annotations', () => {
    test('record with explicit Type annotation parses', () => {
      const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

record Point : Type where
  x : Nat
  y : Nat
`;
      const result = compileTTFromText(source);
      expect(result.success).toBe(true);

      const pointDecl = findDecl(result, 'Point');
      expect(pointDecl).toBeDefined();
      expect(pointDecl?.checkSuccess).toBe(true);
    });

    test('record with Prop annotation parses', () => {
      const source = `
record TrueProof : Prop where
`;
      const result = compileTTFromText(source);
      expect(result.success).toBe(true);

      const decl = findDecl(result, 'TrueProof');
      expect(decl).toBeDefined();
      expect(decl?.checkSuccess).toBe(true);
    });

    test('parameterized record with type annotation parses', () => {
      const source = `
record Box (A : Type) : Type where
  contents : A
`;
      const result = compileTTFromText(source);
      expect(result.success).toBe(true);

      const boxDecl = findDecl(result, 'Box');
      expect(boxDecl).toBeDefined();
      expect(boxDecl?.checkSuccess).toBe(true);
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

  describe('Record usage', () => {
    test('can construct a record value', () => {
      const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

record Point where
  constructor MkPoint
  x : Nat
  y : Nat

origin : Point
origin = MkPoint Zero Zero
`;
      const result = compileTTFromText(source);
      if (!result.success) {
        console.log('Parse errors:', result.blocks.flatMap(b => b.parseErrors.map(e => e.message || e)));
        console.log('Check errors:', result.blocks.flatMap(b => b.declarations.flatMap(d => d.checkErrors?.map(e => e.message) || [])));
        console.log('Name errors:', result.blocks.flatMap(b => b.nameResolutionErrors));
        console.log('Decl check success:', result.blocks.flatMap(b => b.declarations.map(d => `${d.name}: ${d.checkSuccess}`)));
      }
      expect(result.success).toBe(true);

      const originDecl = findDecl(result, 'origin');
      expect(originDecl).toBeDefined();
      expect(originDecl?.checkSuccess).toBe(true);
    });

    test('can construct parameterized record value', () => {
      const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

record Pair (A : Type) (B : Type) where
  constructor MkPair
  fst : A
  snd : B

pair12 : Pair Nat Nat
pair12 = MkPair Nat Nat (Succ Zero) (Succ (Succ Zero))
`;
      const result = compileTTFromText(source);
      if (!result.success) {
        console.log('Parse errors:', result.blocks.flatMap(b => b.parseErrors.map(e => e.message || e)));
        console.log('Check errors:', result.blocks.flatMap(b => b.declarations.flatMap(d => d.checkErrors?.map(e => e.message) || [])));
        console.log('Name errors:', result.blocks.flatMap(b => b.nameResolutionErrors));
      }
      expect(result.success).toBe(true);

      const pairDecl = findDecl(result, 'pair12');
      expect(pairDecl).toBeDefined();
      expect(pairDecl?.checkSuccess).toBe(true);
    });
  });

  describe('Error cases', () => {
    test('record with undefined type in field reports error', () => {
      const source = `
record Bad where
  x : UndefinedType
`;
      const result = compileTTFromText(source);
      expect(result.success).toBe(false);
    });
  });

  describe('Projections', () => {
    test('projection functions are generated and usable', () => {
      const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

record Point where
  constructor MkPoint
  x : Nat
  y : Nat

getX : Point -> Nat
getX p = Point.x p
`;
      const result = compileTTFromText(source);
      if (!result.success) {
        console.log('Parse errors:', result.blocks.flatMap(b => b.parseErrors.map(e => e.message || e)));
        console.log('Check errors:', result.blocks.flatMap(b => b.declarations.flatMap(d => d.checkErrors?.map(e => e.message) || [])));
        console.log('Name errors:', result.blocks.flatMap(b => b.nameResolutionErrors));
      }
      expect(result.success).toBe(true);

      const getXDecl = findDecl(result, 'getX');
      expect(getXDecl).toBeDefined();
      expect(getXDecl?.checkSuccess).toBe(true);
    });

    test('projection on parameterized record works', () => {
      const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

record Pair (A : Type) (B : Type) where
  constructor MkPair
  fst : A
  snd : B

getFst : Pair Nat Nat -> Nat
getFst p = Pair.fst Nat Nat p
`;
      const result = compileTTFromText(source);
      if (!result.success) {
        console.log('Parse errors:', result.blocks.flatMap(b => b.parseErrors.map(e => e.message || e)));
        console.log('Check errors:', result.blocks.flatMap(b => b.declarations.flatMap(d => d.checkErrors?.map(e => e.message) || [])));
        console.log('Name errors:', result.blocks.flatMap(b => b.nameResolutionErrors));
      }
      expect(result.success).toBe(true);

      const getFstDecl = findDecl(result, 'getFst');
      expect(getFstDecl).toBeDefined();
      expect(getFstDecl?.checkSuccess).toBe(true);
    });
  });
});
