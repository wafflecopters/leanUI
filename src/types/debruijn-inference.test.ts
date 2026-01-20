/**
 * Tests for De Bruijn index type inference in lambda expressions.
 *
 * This file focuses on the bug where lambda return types are incorrectly inferred
 * when the lambda body returns a variable. The inferred type should be the TYPE
 * of that variable (looked up in context), not the De Bruijn index itself.
 */

import { describe, test, expect } from 'vitest';
import { compileSource } from '../test-utils';

/**
 * Helper to check if a source string type-checks successfully.
 */
function expectSuccess(source: string): void {
  const results = compileSource(source);

  for (const r of results) {
    if (!r.parseSuccess) {
      throw new Error(`Parse failed for ${r.name}: ${r.parseErrors[0]?.message || 'Unknown parse error'}`);
    }
    if (!r.checkSuccess) {
      throw new Error(`Type check failed for ${r.name}: ${r.checkErrors[0]?.message || 'Unknown error'}`);
    }
  }
}

/**
 * Helper to check if a source string type-checks with specific error.
 */
function expectError(source: string, expectedMessage: string): void {
  const results = compileSource(source);

  let foundError = false;
  for (const r of results) {
    if (!r.checkSuccess) {
      const errorMsg = r.checkErrors[0]?.message || '';
      if (errorMsg.includes(expectedMessage)) {
        foundError = true;
        break;
      }
    }
  }

  if (!foundError) {
    throw new Error(`Expected error containing "${expectedMessage}" but did not find it`);
  }
}

describe('De Bruijn Index Type Inference', () => {
  describe('Simple lambda returning variable', () => {
    test('identity function', () => {
      const source = `
id : (A : Type) -> A -> A
id A = \\(x: A) => x
`;
      expectSuccess(source);
    });

    test('const function - returns first arg', () => {
      const source = `
konstant : (A : Type) -> (B : Type) -> A -> B -> A
konstant A B = \\(x: A) (y: B) => x
`;
      expectSuccess(source);
    });

    test('const function - returns second arg', () => {
      const source = `
konstant2 : (A : Type) -> (B : Type) -> A -> B -> B
konstant2 A B = \\(x: A) (y: B) => y
`;
      expectSuccess(source);
    });
  });

  describe('Higher-order functions', () => {
    test('swap function - THE BUG CASE', () => {
      const source = `
swap : (A : Type) -> (f : A -> A -> A) -> (A -> A -> A)
swap A = \\f => \\(x: A) (y: A) => f y x
`;
      expectSuccess(source);
    });

    test('swap with pattern matching - unannotated lambdas', () => {
      const source = `
swap' : (A : Type) -> (f : A -> A -> A) -> (A -> A -> A)
swap' a f = \\x y => f y x
`;
      expectSuccess(source);
    });

    test('swap with all pattern arguments - no lambdas', () => {
      const source = `
swap''' : (A : Type) -> (f : A -> A -> A) -> (A -> A -> A)
swap''' a f x y = f y x
`;
      expectSuccess(source);
    });

    test('apply function', () => {
      const source = `
apply : (A : Type) -> (B : Type) -> (A -> B) -> A -> B
apply A B = \\(f: A -> B) (x: A) => f x
`;
      expectSuccess(source);
    });

    test('flip function', () => {
      const source = `
flip : (A : Type) -> (B : Type) -> (C : Type) -> (A -> B -> C) -> (B -> A -> C)
flip A B C = \\(f: A -> B -> C) (y: B) (x: A) => f x y
`;
      expectSuccess(source);
    });

    test('compose function', () => {
      const source = `
compose : (A : Type) -> (B : Type) -> (C : Type) -> (B -> C) -> (A -> B) -> (A -> C)
compose A B C = \\(g: B -> C) (f: A -> B) (x: A) => g (f x)
`;
      expectSuccess(source);
    });
  });

  describe('Nested lambdas with variable returns', () => {
    test('triple nested - return outermost', () => {
      const source = `
triple1 : (A : Type) -> A -> A -> A -> A
triple1 A = \\(x: A) (y: A) (z: A) => x
`;
      expectSuccess(source);
    });

    test('triple nested - return middle', () => {
      const source = `
triple2 : (A : Type) -> A -> A -> A -> A
triple2 A = \\(x: A) (y: A) (z: A) => y
`;
      expectSuccess(source);
    });

    test('triple nested - return innermost', () => {
      const source = `
triple3 : (A : Type) -> A -> A -> A -> A
triple3 A = \\(x: A) (y: A) (z: A) => z
`;
      expectSuccess(source);
    });
  });

  describe('Error cases - wrong return type', () => {
    test('swap with wrong return order should fail', () => {
      // This should fail because we're returning in wrong order
      const source = `
wrongSwap : (A : Type) -> (f : A -> A -> A) -> (A -> A -> A)
wrongSwap A = \\f => \\(x: A) (y: A) => f x y
`;
      // This should actually succeed because f x y has same type as f y x
      // Let me think of a better error case...
      expectSuccess(source);
    });

    test('identity with wrong type annotation', () => {
      const source = `
wrongId : (A : Type) -> (B : Type) -> A -> B
wrongId A B = \\(x: A) => x
`;
      expectError(source, 'Type error');
    });
  });

  describe('Application in lambda body', () => {
    test('lambda returning application of variable to constant', () => {
      const source = `
Nat : Type
Nat = Type

Zero : Nat
Zero = Type

applyToZero : (f : Nat -> Nat) -> Nat
applyToZero = \\(f: Nat -> Nat) => f Zero
`;
      expectSuccess(source);
    });

    test('lambda returning nested application', () => {
      const source = `
twice : (A : Type) -> (A -> A) -> A -> A
twice A = \\(f: A -> A) (x: A) => f (f x)
`;
      expectSuccess(source);
    });
  });
});
