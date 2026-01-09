/**
 * Tests for Totality/Exhaustiveness Checking
 *
 * Tests cover:
 * 1. Complete coverage (all constructors covered)
 * 2. Missing single constructor
 * 3. Wildcard covers all
 * 4. Wildcard fallthrough with explicit cases
 * 5. Nested patterns
 * 6. Multiple arguments (Bool -> Bool -> Bool example)
 * 7. Parameterized types (List A)
 */

import { describe, test, expect } from 'vitest';
import { checkSourceBlocks } from '../parser/block-checker';

// ============================================================================
// Helper Functions
// ============================================================================

/**
 * Check that parsing and type-checking both succeed.
 */
function expectSuccess(source: string): void {
  const results = checkSourceBlocks(source);
  for (const r of results) {
    if (!r.parseSuccess) {
      throw new Error(`Parse failed for ${r.name}: ${r.parseErrors.map(e => e.message).join(', ')}`);
    }
    if (!r.checkSuccess) {
      throw new Error(`Type check failed for ${r.name}: ${r.checkErrors.map(e => e.error.message).join(', ')}`);
    }
  }
}

/**
 * Check that we get a specific type error (including exhaustiveness errors).
 */
function expectTypeError(source: string, blockName: string, errorSubstring: string): void {
  const results = checkSourceBlocks(source);
  const block = results.find(r => r.name === blockName);
  if (!block) {
    throw new Error(`Block '${blockName}' not found. Available: ${results.map(r => r.name).join(', ')}`);
  }
  if (block.checkSuccess) {
    throw new Error(`Expected type error for '${blockName}' but it succeeded`);
  }
  const hasExpectedError = block.checkErrors.some(e =>
    e.error.message.toLowerCase().includes(errorSubstring.toLowerCase())
  );
  if (!hasExpectedError) {
    throw new Error(
      `Expected error containing '${errorSubstring}' for '${blockName}', ` +
      `but got: ${block.checkErrors.map(e => e.error.message).join(', ')}`
    );
  }
}

// ============================================================================
// Unit Tests for the Algorithm
// ============================================================================

import {
  analyzeTotality,
  getConstructorsForType,
  prettyPrintSplitTree
} from './ttk-totality-check';
import { TTKContext, TTKTerm, mkPi, mkConst, mkType } from './tt-kernel';
import { TTKClause } from './tt-kernel';
import { TPattern } from './tt-core';

describe('Totality Checking - Unit Tests', () => {
  // Build a simple context with Bool and its constructors
  function makeBoolContext(): TTKContext {
    const boolType: TTKTerm = mkType(1);
    const trueType: TTKTerm = mkConst('Bool', boolType);
    const falseType: TTKTerm = mkConst('Bool', boolType);

    return [
      { name: 'Bool', type: boolType },
      { name: 'True', type: trueType },
      { name: 'False', type: falseType }
    ];
  }

  // Build context with Nat and its constructors
  function makeNatContext(): TTKContext {
    const natType: TTKTerm = mkType(1);
    const zeroType: TTKTerm = mkConst('Nat', natType);
    const succType: TTKTerm = mkPi(mkConst('Nat', natType), mkConst('Nat', natType), 'n');

    return [
      { name: 'Nat', type: natType },
      { name: 'Zero', type: zeroType },
      { name: 'Succ', type: succType }
    ];
  }

  describe('getConstructorsForType', () => {
    test('finds Bool constructors', () => {
      const ctx = makeBoolContext();
      const ctors = getConstructorsForType('Bool', ctx);
      expect(ctors).toContain('True');
      expect(ctors).toContain('False');
      expect(ctors.length).toBe(2);
    });

    test('finds Nat constructors', () => {
      const ctx = makeNatContext();
      const ctors = getConstructorsForType('Nat', ctx);
      expect(ctors).toContain('Zero');
      expect(ctors).toContain('Succ');
      expect(ctors.length).toBe(2);
    });

    test('returns empty for unknown type', () => {
      const ctx = makeBoolContext();
      const ctors = getConstructorsForType('Unknown', ctx);
      expect(ctors.length).toBe(0);
    });
  });

  describe('analyzeTotality', () => {
    test('complete coverage - both Bool constructors', () => {
      const ctx = makeBoolContext();
      const boolType: TTKTerm = mkConst('Bool', mkType(1));

      const clauses: TTKClause[] = [
        { patterns: [{ tag: 'PCtor', name: 'True', args: [] }], rhs: mkConst('True', boolType) },
        { patterns: [{ tag: 'PCtor', name: 'False', args: [] }], rhs: mkConst('False', boolType) }
      ];

      const result = analyzeTotality(clauses, [boolType], ctx);
      expect(result.exhaustive).toBe(true);
      expect(result.missingCases.length).toBe(0);
    });

    test('missing constructor - only True covered', () => {
      const ctx = makeBoolContext();
      const boolType: TTKTerm = mkConst('Bool', mkType(1));

      const clauses: TTKClause[] = [
        { patterns: [{ tag: 'PCtor', name: 'True', args: [] }], rhs: mkConst('True', boolType) }
      ];

      const result = analyzeTotality(clauses, [boolType], ctx);
      expect(result.exhaustive).toBe(false);
      expect(result.missingCases.length).toBeGreaterThan(0);
    });

    test('wildcard covers all', () => {
      const ctx = makeBoolContext();
      const boolType: TTKTerm = mkConst('Bool', mkType(1));

      const clauses: TTKClause[] = [
        { patterns: [{ tag: 'PVar', name: '_' }], rhs: mkConst('True', boolType) }
      ];

      const result = analyzeTotality(clauses, [boolType], ctx);
      expect(result.exhaustive).toBe(true);
      expect(result.missingCases.length).toBe(0);
    });

    test('variable pattern covers all', () => {
      const ctx = makeBoolContext();
      const boolType: TTKTerm = mkConst('Bool', mkType(1));

      const clauses: TTKClause[] = [
        { patterns: [{ tag: 'PVar', name: 'x' }], rhs: mkConst('True', boolType) }
      ];

      const result = analyzeTotality(clauses, [boolType], ctx);
      expect(result.exhaustive).toBe(true);
      expect(result.missingCases.length).toBe(0);
    });

    test('explicit + wildcard fallthrough', () => {
      const ctx = makeBoolContext();
      const boolType: TTKTerm = mkConst('Bool', mkType(1));

      // True explicit, wildcard covers False
      const clauses: TTKClause[] = [
        { patterns: [{ tag: 'PCtor', name: 'True', args: [] }], rhs: mkConst('True', boolType) },
        { patterns: [{ tag: 'PVar', name: '_' }], rhs: mkConst('False', boolType) }
      ];

      const result = analyzeTotality(clauses, [boolType], ctx);
      expect(result.exhaustive).toBe(true);
      expect(result.missingCases.length).toBe(0);
    });

    test('empty clauses is non-exhaustive', () => {
      const ctx = makeBoolContext();
      const boolType: TTKTerm = mkConst('Bool', mkType(1));

      const clauses: TTKClause[] = [];

      const result = analyzeTotality(clauses, [boolType], ctx);
      expect(result.exhaustive).toBe(false);
    });

    test('no arguments - first clause covers all', () => {
      const ctx = makeBoolContext();
      const boolType: TTKTerm = mkConst('Bool', mkType(1));

      const clauses: TTKClause[] = [
        { patterns: [], rhs: mkConst('True', boolType) }
      ];

      const result = analyzeTotality(clauses, [], ctx);
      expect(result.exhaustive).toBe(true);
    });

    test('detects inaccessible clause - duplicate pattern', () => {
      const ctx = makeBoolContext();
      const boolType: TTKTerm = mkConst('Bool', mkType(1));

      const clauses: TTKClause[] = [
        { patterns: [{ tag: 'PCtor', name: 'True', args: [] }], rhs: mkConst('True', boolType) },
        { patterns: [{ tag: 'PCtor', name: 'False', args: [] }], rhs: mkConst('False', boolType) },
        { patterns: [{ tag: 'PCtor', name: 'True', args: [] }], rhs: mkConst('False', boolType) }  // Duplicate!
      ];

      const result = analyzeTotality(clauses, [boolType], ctx);
      expect(result.exhaustive).toBe(true);  // Still exhaustive
      expect(result.inaccessibleClauses).toEqual([2]);  // Third clause is inaccessible
    });

    test('detects inaccessible clause - after wildcard', () => {
      const ctx = makeBoolContext();
      const boolType: TTKTerm = mkConst('Bool', mkType(1));

      const clauses: TTKClause[] = [
        { patterns: [{ tag: 'PVar', name: '_' }], rhs: mkConst('True', boolType) },
        { patterns: [{ tag: 'PCtor', name: 'False', args: [] }], rhs: mkConst('False', boolType) }  // Inaccessible!
      ];

      const result = analyzeTotality(clauses, [boolType], ctx);
      expect(result.exhaustive).toBe(true);
      expect(result.inaccessibleClauses).toEqual([1]);
    });

    test('no inaccessible clauses with disjoint patterns', () => {
      const ctx = makeBoolContext();
      const boolType: TTKTerm = mkConst('Bool', mkType(1));

      const clauses: TTKClause[] = [
        { patterns: [{ tag: 'PCtor', name: 'True', args: [] }], rhs: mkConst('False', boolType) },
        { patterns: [{ tag: 'PCtor', name: 'False', args: [] }], rhs: mkConst('True', boolType) }
      ];

      const result = analyzeTotality(clauses, [boolType], ctx);
      expect(result.exhaustive).toBe(true);
      expect(result.inaccessibleClauses).toEqual([]);
    });

    test('no arguments - extra clauses are inaccessible', () => {
      const ctx = makeBoolContext();
      const boolType: TTKTerm = mkConst('Bool', mkType(1));

      const clauses: TTKClause[] = [
        { patterns: [], rhs: mkConst('True', boolType) },
        { patterns: [], rhs: mkConst('False', boolType) },  // Inaccessible!
        { patterns: [], rhs: mkConst('True', boolType) }    // Inaccessible!
      ];

      const result = analyzeTotality(clauses, [], ctx);
      expect(result.exhaustive).toBe(true);
      expect(result.inaccessibleClauses).toEqual([1, 2]);
    });
  });

  describe('prettyPrintSplitTree', () => {
    test('prints leaf node', () => {
      const ctx = makeBoolContext();
      const boolType: TTKTerm = mkConst('Bool', mkType(1));

      const clauses: TTKClause[] = [
        { patterns: [{ tag: 'PVar', name: '_' }], rhs: mkConst('True', boolType) }
      ];

      const result = analyzeTotality(clauses, [boolType], ctx);
      const printed = prettyPrintSplitTree(result.splitTree);
      expect(printed).toContain('Leaf');
    });
  });
});

// ============================================================================
// Integration Tests (End-to-End with Parser)
// ============================================================================

describe('Totality Checking - Integration Tests', () => {
  describe('Complete coverage', () => {
    test('Bool -> Bool with both constructors', () => {
      const source = `
inductive Bool : Type where
  True : Bool
  False : Bool

not : Bool -> Bool
not True = False
not False = True
`;
      expectSuccess(source);
    });

    test('Nat -> Nat with Zero and Succ', () => {
      const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

isZero : Nat -> Nat
isZero Zero = Zero
isZero (Succ n) = Zero
`;
      expectSuccess(source);
    });

    test('Multiple arguments - all combinations', () => {
      const source = `
inductive Bool : Type where
  True : Bool
  False : Bool

and : Bool -> Bool -> Bool
and True True = True
and True False = False
and False True = False
and False False = False
`;
      expectSuccess(source);
    });
  });

  describe('Wildcard coverage', () => {
    test('Single wildcard covers all', () => {
      const source = `
inductive Bool : Type where
  True : Bool
  False : Bool

const : Bool -> Bool
const _ = True
`;
      expectSuccess(source);
    });

    test('Wildcard fallthrough after explicit cases', () => {
      const source = `
inductive Bool : Type where
  True : Bool
  False : Bool

isTrue : Bool -> Bool
isTrue True = True
isTrue _ = False
`;
      expectSuccess(source);
    });

    test('Variable pattern covers all', () => {
      const source = `
inductive Bool : Type where
  True : Bool
  False : Bool

id : Bool -> Bool
id x = x
`;
      expectSuccess(source);
    });
  });

  describe('Multiple argument patterns', () => {
    test('Bool -> Bool -> Bool with wildcards', () => {
      // This is the example from the requirements
      const source = `
inductive Bool : Type where
  True : Bool
  False : Bool

foo : Bool -> Bool -> Bool
foo True True = True
foo False _ = True
foo _ _ = False
`;
      expectSuccess(source);
    });

    test('Mixed explicit and wildcard in second argument', () => {
      const source = `
inductive Bool : Type where
  True : Bool
  False : Bool

bar : Bool -> Bool -> Bool
bar True True = True
bar True False = False
bar False _ = True
`;
      expectSuccess(source);
    });
  });

  describe('Nested patterns', () => {
    test('Nested constructor patterns', () => {
      const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

pred2 : Nat -> Nat
pred2 Zero = Zero
pred2 (Succ Zero) = Zero
pred2 (Succ (Succ n)) = n
`;
      expectSuccess(source);
    });
  });

  describe('Parameterized types', () => {
    test('List A with Nil and Cons', () => {
      const source = `
inductive List : Type -> Type where
  Nil : (A : Type) -> List A
  Cons : (A : Type) -> A -> List A -> List A

isEmpty : (A : Type) -> List A -> A -> A
isEmpty _ (Nil _) default = default
isEmpty _ (Cons _ x _) _ = x
`;
      expectSuccess(source);
    });
  });
});

// ============================================================================
// Non-exhaustive Pattern Tests (Should Fail)
// ============================================================================

describe('Totality Checking - Non-exhaustive Patterns', () => {
  test('Missing False case for Bool', () => {
    const source = `
inductive Bool : Type where
  True : Bool
  False : Bool

bad : Bool -> Bool
bad True = True
`;
    expectTypeError(source, 'bad', 'exhaustive');
  });

  test('Missing Succ case for Nat', () => {
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

bad : Nat -> Nat
bad Zero = Zero
`;
    expectTypeError(source, 'bad', 'exhaustive');
  });

  test('Missing case in second argument', () => {
    const source = `
inductive Bool : Type where
  True : Bool
  False : Bool

bad : Bool -> Bool -> Bool
bad True True = True
bad False False = False
`;
    // Missing: True False, False True
    expectTypeError(source, 'bad', 'exhaustive');
  });

  test('Missing nested case', () => {
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

bad : Nat -> Nat
bad Zero = Zero
bad (Succ Zero) = Zero
`;
    // Missing: Succ (Succ _)
    expectTypeError(source, 'bad', 'exhaustive');
  });

  test('Missing case in multi-arg Nat function', () => {
    // This is the exact case the user reported:
    // plus Zero b = b
    // plus (Succ a) Zero = a
    // Missing: plus (Succ a) (Succ b)
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

plus : Nat -> Nat -> Nat
plus Zero b = b
plus (Succ a) Zero = a
`;
    expectTypeError(source, 'plus', 'exhaustive');
  });
});

// ============================================================================
// Inaccessible Clause Tests (Excess Patterns)
// ============================================================================

describe('Totality Checking - Inaccessible Clauses', () => {
  test('Duplicate clause is inaccessible', () => {
    const source = `
inductive Bool : Type where
  True : Bool
  False : Bool

bad : Bool -> Bool
bad True = True
bad False = False
bad True = False
`;
    // The third clause (bad True = False) is inaccessible
    expectTypeError(source, 'bad', 'inaccessible');
  });

  test('Clause after wildcard is inaccessible', () => {
    const source = `
inductive Bool : Type where
  True : Bool
  False : Bool

bad : Bool -> Bool
bad _ = True
bad False = False
`;
    // The second clause (bad False = False) is inaccessible because _ already covers all
    expectTypeError(source, 'bad', 'inaccessible');
  });

  test('Multiple inaccessible clauses', () => {
    const source = `
inductive Bool : Type where
  True : Bool
  False : Bool

bad : Bool -> Bool
bad x = x
bad True = False
bad False = True
`;
    // Both second and third clauses are inaccessible
    expectTypeError(source, 'bad', 'inaccessible');
  });

  test('Inaccessible clause in multi-arg function', () => {
    const source = `
inductive Bool : Type where
  True : Bool
  False : Bool

bad : Bool -> Bool -> Bool
bad True _ = True
bad False _ = False
bad True True = False
`;
    // The third clause is inaccessible (True True already covered by True _)
    expectTypeError(source, 'bad', 'inaccessible');
  });

  test('Inaccessible nested pattern', () => {
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

bad : Nat -> Nat
bad Zero = Zero
bad (Succ _) = Zero
bad (Succ Zero) = Zero
`;
    // The third clause (Succ Zero) is already covered by (Succ _)
    expectTypeError(source, 'bad', 'inaccessible');
  });

  test('No inaccessible clauses when order matters', () => {
    // This should succeed - order matters for pattern matching
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

pred : Nat -> Nat
pred Zero = Zero
pred (Succ Zero) = Zero
pred (Succ (Succ n)) = Succ n
`;
    expectSuccess(source);
  });

  test('No inaccessible clauses with disjoint patterns', () => {
    const source = `
inductive Bool : Type where
  True : Bool
  False : Bool

not : Bool -> Bool
not True = False
not False = True
`;
    expectSuccess(source);
  });

  test('Inaccessible clause with single-constructor type (Equal/Refl)', () => {
    // When a type has only one constructor (like Equal with Refl),
    // a wildcard after matching that constructor is inaccessible
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Equal : (A : Type) -> A -> A -> Type where
  Refl : (A : Type) -> (x : A) -> Equal A x x

foo : (a : Nat) -> (b : Nat) -> Equal Nat a b -> Nat
foo _ _ (Refl _ _) = Zero
foo _ _ _ = Zero
`;
    // The second clause is inaccessible because Refl is the only constructor
    expectTypeError(source, 'foo', 'inaccessible');
  });

  test('No inaccessible clause when single-constructor is covered by wildcard', () => {
    // This should succeed - just using wildcard for the only constructor
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Equal : (A : Type) -> A -> A -> Type where
  Refl : (A : Type) -> (x : A) -> Equal A x x

foo : (a : Nat) -> (b : Nat) -> Equal Nat a b -> Nat
foo _ _ _ = Zero
`;
    expectSuccess(source);
  });
});

// ============================================================================
// Constructor vs Function Identification
// ============================================================================

describe('Totality Checking - Constructor vs Function', () => {
  test('Function returning Nat is not a constructor', () => {
    // This tests that `plus` is NOT identified as a constructor for Nat.
    // The totality checker should only consider Zero and Succ as constructors.
    // If `plus` were treated as a constructor, missing cases would include `plus _ _`.
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

plus : Nat -> Nat -> Nat
plus Zero b = b
plus (Succ a) b = Succ (plus a b)

-- This function should type-check without issues
double : Nat -> Nat
double Zero = Zero
double (Succ n) = Succ (Succ (double n))
`;
    expectSuccess(source);
  });

  test('vecConcat with wildcards should work (no plus as constructor)', () => {
    // This tests that `plus` is NOT identified as a constructor for Nat.
    // Previously, this would fail with "missing case: vecConcat _ (plus _ _) _ (VNil _) _"
    // because functions returning Nat were incorrectly treated as constructors.
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

plus : Nat -> Nat -> Nat
plus Zero b = b
plus (Succ a) b = Succ (plus a b)

inductive Vec : Type -> Nat -> Type where
  VNil : (A : Type) -> Vec A Zero
  VCons : (A : Type) -> (n : Nat) -> A -> Vec A n -> Vec A (Succ n)

vecConcat : (A : Type) -> (a : Nat) -> (b : Nat) -> Vec A a -> Vec A b -> Vec A (plus a b)
vecConcat _ _ _ (VNil _) v = v
vecConcat _ _ _ (VCons _ _ h tail) v = VCons _ _ h (vecConcat _ _ _ tail v)
`;
    expectSuccess(source);
  });

  test('vecConcat with explicit Zero pattern (dependent type refinement)', () => {
    // When matching a=Zero, the type Vec A a refines to Vec A Zero,
    // making VCons impossible and VNil the only valid constructor.
    // When matching a=Succ n, the type Vec A a refines to Vec A (Succ n),
    // making VNil impossible and VCons the only valid constructor.
    // The totality checker uses index bindings to track these refinements.
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

plus : Nat -> Nat -> Nat
plus Zero b = b
plus (Succ a) b = Succ (plus a b)

inductive Vec : Type -> Nat -> Type where
  VNil : (A : Type) -> Vec A Zero
  VCons : (A : Type) -> (n : Nat) -> A -> Vec A n -> Vec A (Succ n)

vecConcat : (A : Type) -> (a : Nat) -> (b : Nat) -> Vec A a -> Vec A b -> Vec A (plus a b)
vecConcat _ Zero _ (VNil _) v = v
vecConcat _ _ _ (VCons _ _ h tail) v = VCons _ _ h (vecConcat _ _ _ tail v)
`;
    expectSuccess(source);
  });

  test('vecConcat with inaccessible third clause (wildcard after explicit VNil in Zero branch)', () => {
    // When matching a=Zero, the type Vec A a refines to Vec A Zero,
    // making VCons impossible. In this branch:
    // - Clause 1 covers VNil explicitly
    // - Clause 3 has a wildcard, but since VCons is impossible and VNil is covered,
    //   clause 3 is INACCESSIBLE (can never match any case)
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

plus : Nat -> Nat -> Nat
plus Zero b = b
plus (Succ a) b = Succ (plus a b)

inductive Vec : Type -> Nat -> Type where
  VNil : (A : Type) -> Vec A Zero
  VCons : (A : Type) -> (n : Nat) -> A -> Vec A n -> Vec A (Succ n)

vecConcat : (A : Type) -> (a : Nat) -> (b : Nat) -> Vec A a -> Vec A b -> Vec A (plus a b)
vecConcat _ Zero _ (VNil _) v = v
vecConcat _ _ _ (VCons _ _ h tail) v = VCons _ _ h (vecConcat _ _ _ tail v)
vecConcat _ Zero _ _ p = p
`;
    expectTypeError(source, 'vecConcat', 'inaccessible');
  });

  test('Multiple functions returning same type should not be constructors', () => {
    // Ensure multiple functions returning Nat don't appear as constructors
    // If both plus and mult were constructors, we'd see them in missing cases
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

plus : Nat -> Nat -> Nat
plus Zero b = b
plus (Succ a) b = Succ (plus a b)

mult : Nat -> Nat -> Nat
mult Zero _ = Zero
mult (Succ a) b = plus b (mult a b)

-- This function should only require Zero and Succ coverage
isEven : Nat -> Nat
isEven Zero = Succ Zero
isEven (Succ Zero) = Zero
isEven (Succ (Succ n)) = isEven n
`;
    expectSuccess(source);
  });
});
