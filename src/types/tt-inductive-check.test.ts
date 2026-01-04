/**
 * Tests for Inductive Type Validity Checking
 *
 * These tests verify the three core validity checks for inductive types:
 * 1. Constructor return type must be the inductive type
 * 2. Strict positivity (no negative occurrences)
 * 3. Universe constraints
 */

import { mkType, mkVar, mkConst, mkPi, mkApp } from './tt-core';
import { elabToKernel } from './tt-elab';
import { checkInductiveValidity, containsConstant } from './tt-inductive-check';
import { TTKTerm } from './tt-kernel';

// ============================================================================
// Test Helpers
// ============================================================================

function test(description: string, fn: () => void): void {
  try {
    fn();
    console.log(`✓ ${description}`);
  } catch (error) {
    console.error(`✗ ${description}`);
    throw error;
  }
}

function assert(condition: boolean, message?: string): void {
  if (!condition) {
    throw new Error(message || 'Assertion failed');
  }
}

/**
 * Universe hierarchy in this codebase:
 * - Sort 0 = Prop (the type of propositions)
 * - Sort 1 = Type (the type of data types like Nat, Bool)
 * - Sort 2 = Type 1 (universe above Type)
 *
 * When we say "Nat : Type", we mean Nat has type Sort 1.
 *
 * NOTE: tt-examples.ts uses `const Type = mkType(0)` which is
 * actually Prop, not Type! This is a naming inconsistency in the codebase.
 * For these tests, we use the correct convention.
 */

/** Sort 1 = Type (the sort that contains types like Nat, Bool, List) */
const Type = mkType(1);

/** Sort 2 = Type 1 (universe above Type) */
const Type1 = mkType(2);

/** Helper to create a reference to an inductive type */
function mkInductiveRef(name: string, kind: ReturnType<typeof mkType>): ReturnType<typeof mkType> {
  return mkConst(name, kind);
}

/** Helper to create an arrow type A -> B */
function mkArrow(domain: ReturnType<typeof mkType>, codomain: ReturnType<typeof mkType>): ReturnType<typeof mkType> {
  return mkPi(domain, codomain, '_');
}

console.log('\n' + '='.repeat(80));
console.log('INDUCTIVE TYPE VALIDITY CHECKING TESTS');
console.log('='.repeat(80) + '\n');

// ============================================================================
// 1. Constructor Return Type Tests
// ============================================================================

console.log('\n--- Constructor Return Type Tests ---\n');

test('Valid: simple inductive with correct return type (Nat)', () => {
  const Nat = mkInductiveRef('Nat', Type);

  const result = checkInductiveValidity(
    'Nat',
    elabToKernel(Type) as TTKTerm,
    [
      { name: 'zero', type: elabToKernel(Nat) as TTKTerm },
      { name: 'succ', type: elabToKernel(mkArrow(Nat, Nat)) as TTKTerm }
    ],
    []
  );

  assert(result.success, `Expected success, got errors: ${result.errors.map(e => e.message).join(', ')}`);
});

test('Valid: Bool with two constructors', () => {
  const Bool = mkInductiveRef('Bool', Type);

  const result = checkInductiveValidity(
    'Bool',
    elabToKernel(Type) as TTKTerm,
    [
      { name: 'true', type: elabToKernel(Bool) as TTKTerm },
      { name: 'false', type: elabToKernel(Bool) as TTKTerm }
    ],
    []
  );

  assert(result.success, `Expected success, got errors: ${result.errors.map(e => e.message).join(', ')}`);
});

test('Invalid: constructor returns wrong type', () => {
  const Nat = mkInductiveRef('Nat', Type);
  const Bool = mkInductiveRef('Bool', Type);

  const result = checkInductiveValidity(
    'Nat',
    elabToKernel(Type) as TTKTerm,
    [
      { name: 'zero', type: elabToKernel(Nat) as TTKTerm },
      { name: 'bad', type: elabToKernel(Bool) as TTKTerm }  // Returns Bool, not Nat!
    ],
    []
  );

  assert(!result.success, 'Expected failure for wrong return type');
  assert(
    result.errors.some(e => e.message.includes('bad') && e.message.includes('Nat')),
    'Error should mention the bad constructor and expected type'
  );
});

test('Invalid: constructor returns arbitrary type (Type itself)', () => {
  const result = checkInductiveValidity(
    'Weird',
    elabToKernel(Type) as TTKTerm,
    [
      { name: 'bad', type: elabToKernel(Type) as TTKTerm }  // Returns Type, not Weird!
    ],
    []
  );

  assert(!result.success, 'Expected failure when constructor returns Type');
});

test('Valid: List with polymorphic constructors (in Type 1)', () => {
  // List : Type -> Type 1
  // Note: Without universe polymorphism, a polymorphic type must be in a higher universe
  // because constructors quantify over Type, and Type_0 is Sort 1,
  // so we need the inductive in Sort 2 (Type 1) or higher.
  //
  // In Lean 4 with universe polymorphism, List.{u} : Type u → Type u
  // But without polymorphism, we need List : Type → Type 1
  const ListKind = mkArrow(Type, Type1);  // Type -> Type 1
  const List = mkInductiveRef('List', ListKind);

  // nil : (A : Type) -> List A
  const nilType = mkPi(Type, mkApp(List, mkVar(0)), 'A');

  // cons : (A : Type) -> A -> List A -> List A
  const consType = mkPi(
    Type,
    mkPi(
      mkVar(0),
      mkPi(
        mkApp(List, mkVar(1)),
        mkApp(List, mkVar(2)),
        '_'
      ),
      '_'
    ),
    'A'
  );

  const result = checkInductiveValidity(
    'List',
    elabToKernel(ListKind) as TTKTerm,
    [
      { name: 'nil', type: elabToKernel(nilType) as TTKTerm },
      { name: 'cons', type: elabToKernel(consType) as TTKTerm }
    ],
    []
  );

  assert(result.success, `Expected success, got errors: ${result.errors.map(e => e.message).join(', ')}`);
});

// ============================================================================
// 2. Strict Positivity Tests
// ============================================================================

console.log('\n--- Strict Positivity Tests ---\n');

test('Valid: strictly positive occurrence in succ (Nat -> Nat)', () => {
  const Nat = mkInductiveRef('Nat', Type);

  const result = checkInductiveValidity(
    'Nat',
    elabToKernel(Type) as TTKTerm,
    [
      { name: 'zero', type: elabToKernel(Nat) as TTKTerm },
      { name: 'succ', type: elabToKernel(mkArrow(Nat, Nat)) as TTKTerm }
    ],
    []
  );

  assert(result.success, `Expected success for strictly positive occurrence`);
});

test('Invalid: negative occurrence (Bad -> X) -> Bad', () => {
  // This is the classic bad case: (Bad -> X) -> Bad
  // Bad occurs to the left of an arrow
  const Bad = mkInductiveRef('Bad', Type);
  const X = mkInductiveRef('X', Type);

  // bad : (Bad -> X) -> Bad
  // In this case, Bad appears in the domain of the outer Pi,
  // which means it's in a negative position
  const badCtorType = mkPi(
    mkArrow(Bad, X),  // (Bad -> X) - Bad is negative here
    Bad,              // -> Bad
    '_'
  );

  const result = checkInductiveValidity(
    'Bad',
    elabToKernel(Type) as TTKTerm,
    [
      { name: 'bad', type: elabToKernel(badCtorType) as TTKTerm }
    ],
    []
  );

  assert(!result.success, 'Expected failure for negative occurrence');
  assert(
    result.errors.some(e => e.message.includes('negative') || e.message.includes('positiv')),
    'Error should mention positivity violation'
  );
});

test('Invalid: non-strictly positive ((Bad -> X) -> X) -> Bad', () => {
  // This is the subtler case: ((Bad -> X) -> X) -> Bad
  // Bad appears to the left of an even number of arrows (2),
  // so it's positive but NOT strictly positive
  const Bad = mkInductiveRef('Bad', Type);
  const X = mkInductiveRef('X', Type);

  // ((Bad -> X) -> X) -> Bad
  const badCtorType = mkPi(
    mkPi(
      mkArrow(Bad, X),  // Bad -> X (Bad is negative here)
      X,
      '_'
    ),
    Bad,
    '_'
  );

  const result = checkInductiveValidity(
    'Bad',
    elabToKernel(Type) as TTKTerm,
    [
      { name: 'bad', type: elabToKernel(badCtorType) as TTKTerm }
    ],
    []
  );

  assert(!result.success, 'Expected failure for non-strictly positive occurrence');
  assert(
    result.errors.some(e => e.message.includes('positiv')),
    'Error should mention positivity violation'
  );
});

test('Valid: Tree with nested List (nested inductive)', () => {
  // inductive Tree where
  //   | node : List Tree -> Tree
  // This is a nested inductive type - Tree under List
  // This should be VALID because Tree appears strictly positively
  // (List is a strictly positive type constructor)

  // For simplicity, we'll model this as:
  // node : ListOfTree -> Tree
  // where ListOfTree is a separate type

  const Tree = mkInductiveRef('Tree', Type);
  const ListOfTree = mkInductiveRef('ListOfTree', Type);

  const result = checkInductiveValidity(
    'Tree',
    elabToKernel(Type) as TTKTerm,
    [
      { name: 'node', type: elabToKernel(mkArrow(ListOfTree, Tree)) as TTKTerm }
    ],
    []
  );

  assert(result.success, 'Nested inductive should be valid (Tree in strictly positive position)');
});

test('Invalid: Tree in contravariant position of function argument', () => {
  // inductive Bad where
  //   | bad : ((Bad -> Nat) -> Nat) -> Bad
  // This should be INVALID - Bad appears in contravariant position

  const Bad = mkInductiveRef('Bad', Type);
  const Nat = mkInductiveRef('Nat', Type);

  // ((Bad -> Nat) -> Nat) -> Bad
  const badType = mkPi(
    mkPi(
      mkArrow(Bad, Nat),  // Bad -> Nat: Bad is in negative position
      Nat,
      '_'
    ),
    Bad,
    '_'
  );

  const result = checkInductiveValidity(
    'Bad',
    elabToKernel(Type) as TTKTerm,
    [
      { name: 'bad', type: elabToKernel(badType) as TTKTerm }
    ],
    []
  );

  assert(!result.success, 'Expected failure - Bad in contravariant position');
});

// ============================================================================
// 3. Universe Constraint Tests
// ============================================================================

console.log('\n--- Universe Constraint Tests ---\n');

test('Valid: Nat in Type with Nat arguments', () => {
  const Nat = mkInductiveRef('Nat', Type);

  const result = checkInductiveValidity(
    'Nat',
    elabToKernel(Type) as TTKTerm,
    [
      { name: 'zero', type: elabToKernel(Nat) as TTKTerm },
      { name: 'succ', type: elabToKernel(mkArrow(Nat, Nat)) as TTKTerm }
    ],
    []
  );

  assert(result.success, 'Nat in Type with Nat arguments should be valid');
});

test('Invalid: Type in Type_0 (universe too large)', () => {
  // inductive Bad : Type where
  //   | mk : Type -> Bad
  // This should fail because Type (= Sort 1) is not < Sort 1

  const Bad = mkInductiveRef('Bad', Type);

  // mk : Type -> Bad
  const mkType_arrow_Bad = mkArrow(Type, Bad);

  const result = checkInductiveValidity(
    'Bad',
    elabToKernel(Type) as TTKTerm,
    [
      { name: 'mk', type: elabToKernel(mkType_arrow_Bad) as TTKTerm }
    ],
    []
  );

  assert(!result.success, 'Expected failure - Type argument in Type_0 inductive');
  assert(
    result.errors.some(e => e.message.includes('universe') || e.message.includes('Universe')),
    'Error should mention universe constraint'
  );
});

test('Valid: Large type in Type_1', () => {
  // inductive Large : Type 1 where
  //   | mk : Type -> Large
  // This SHOULD be valid because Type (Sort 1) < Type 1 (Sort 2)

  const Large = mkInductiveRef('Large', Type1);

  // mk : Type -> Large
  const mkType_arrow_Large = mkArrow(Type, Large);

  const result = checkInductiveValidity(
    'Large',
    elabToKernel(Type1) as TTKTerm,
    [
      { name: 'mk', type: elabToKernel(mkType_arrow_Large) as TTKTerm }
    ],
    []
  );

  assert(result.success, `Type argument in Type_1 inductive should be valid, got: ${result.errors.map(e => e.message).join(', ')}`);
});

test('Invalid: Type_1 argument in Type_1 inductive', () => {
  // inductive Bad : Type 1 where
  //   | mk : Type 1 -> Bad
  // This should fail because Type 1 (Sort 2) is not < Sort 2

  const Bad = mkInductiveRef('Bad', Type1);

  // mk : Type 1 -> Bad
  const mkType1_arrow_Bad = mkArrow(Type1, Bad);

  const result = checkInductiveValidity(
    'Bad',
    elabToKernel(Type1) as TTKTerm,
    [
      { name: 'mk', type: elabToKernel(mkType1_arrow_Bad) as TTKTerm }
    ],
    []
  );

  assert(!result.success, 'Expected failure - Type 1 argument in Type_1 inductive');
});

// ============================================================================
// 4. Combined Tests
// ============================================================================

console.log('\n--- Combined Tests ---\n');

test('Invalid: multiple violations at once', () => {
  // inductive Bad : Type where
  //   | bad1 : OtherType        -- Wrong return type
  //   | bad2 : (Bad -> X) -> Bad  -- Negative occurrence
  //   | bad3 : Type -> Bad      -- Universe violation

  const Bad = mkInductiveRef('Bad', Type);
  const OtherType = mkInductiveRef('OtherType', Type);
  const X = mkInductiveRef('X', Type);

  const result = checkInductiveValidity(
    'Bad',
    elabToKernel(Type) as TTKTerm,
    [
      { name: 'bad1', type: elabToKernel(OtherType) as TTKTerm },
      { name: 'bad2', type: elabToKernel(mkPi(mkArrow(Bad, X), Bad, '_')) as TTKTerm },
      { name: 'bad3', type: elabToKernel(mkArrow(Type, Bad)) as TTKTerm }
    ],
    []
  );

  assert(!result.success, 'Expected failure with multiple violations');
  assert(result.errors.length >= 2, `Expected multiple errors, got ${result.errors.length}`);
});

test('Valid: empty type (no constructors)', () => {
  const result = checkInductiveValidity(
    'Void',
    elabToKernel(Type) as TTKTerm,
    [],
    []
  );

  assert(result.success, 'Empty type with no constructors should be valid');
});

test('Valid: Unit type (one nullary constructor)', () => {
  const Unit = mkInductiveRef('Unit', Type);

  const result = checkInductiveValidity(
    'Unit',
    elabToKernel(Type) as TTKTerm,
    [
      { name: 'tt', type: elabToKernel(Unit) as TTKTerm }
    ],
    []
  );

  assert(result.success, 'Unit type should be valid');
});

// ============================================================================
// 5. Helper Function Tests
// ============================================================================

console.log('\n--- Helper Function Tests ---\n');

test('containsConstant: finds constant in simple term', () => {
  const Nat = elabToKernel(mkInductiveRef('Nat', Type)) as TTKTerm;

  assert(containsConstant(Nat, 'Nat'), 'Should find Nat in Nat');
  assert(!containsConstant(Nat, 'Bool'), 'Should not find Bool in Nat');
});

test('containsConstant: finds constant in arrow type', () => {
  const Nat = mkInductiveRef('Nat', Type);
  const arrow = elabToKernel(mkArrow(Nat, Nat)) as TTKTerm;

  assert(containsConstant(arrow, 'Nat'), 'Should find Nat in Nat -> Nat');
  assert(!containsConstant(arrow, 'Bool'), 'Should not find Bool in Nat -> Nat');
});

test('containsConstant: finds constant nested in Pi', () => {
  const Nat = mkInductiveRef('Nat', Type);
  const complex = elabToKernel(mkPi(Type, mkArrow(mkVar(0), Nat), 'A')) as TTKTerm;

  assert(containsConstant(complex, 'Nat'), 'Should find Nat in (A : Type) -> A -> Nat');
});

// ============================================================================
// 6. Constructor Argument Type Validation Tests
// ============================================================================

console.log('\n--- Constructor Argument Type Validation Tests ---\n');

test('Invalid: wrong number of arguments to inductive type (also universe violation)', () => {
  // Vec : Nat -> Type
  // VNil : (A: Type) -> Vec Zero A  -- WRONG! Vec takes 1 arg, given 2
  //
  // This test has multiple issues:
  // 1. Arity error: Vec Zero A applies 2 args to 1-arg type (caught by type-checker)
  // 2. Universe violation: A : Type in a Type-level inductive (caught here)
  //
  // Since we're calling checkInductiveValidity directly without indexPositions,
  // we're conservative and treat all positions as indices. The constructor has
  // (A: Type) which is a type-level argument, violating universe constraints.
  const Nat = mkInductiveRef('Nat', Type);
  const Zero = mkInductiveRef('Zero', Nat);

  // Vec : Nat -> Type
  const VecKind = mkArrow(Nat, Type);
  const Vec = mkInductiveRef('Vec', VecKind);

  // VNil : (A: Type) -> Vec Zero A
  // This applies 2 arguments (Zero, A) to Vec, but Vec only takes 1 (Nat)
  const VNilType = mkPi(
    Type,
    mkApp(mkApp(Vec, Zero), mkVar(0)),  // Vec Zero A - 2 arguments!
    'A'
  );

  const result = checkInductiveValidity(
    'Vec',
    elabToKernel(VecKind) as TTKTerm,
    [
      { name: 'VNil', type: elabToKernel(VNilType) as TTKTerm }
    ],
    []
  );

  // Without indexPositions, we're conservative and catch universe violations
  assert(!result.success, 'Expected failure - universe constraint violation');
  assert(
    result.errors.some(e => e.message.includes('universe')),
    `Error should mention universe, got: ${result.errors.map(e => e.message).join(', ')}`
  );
});

test('Invalid: wrong type of argument to inductive type', () => {
  // Vec : Nat -> Type
  // Bad : (A: Type) -> Vec A  -- WRONG! A is Type, but Vec expects Nat
  const Nat = mkInductiveRef('Nat', Type);

  // Vec : Nat -> Type
  const VecKind = mkArrow(Nat, Type);
  const Vec = mkInductiveRef('Vec', VecKind);

  // Bad : (A: Type) -> Vec A
  // This applies Type to where Nat is expected
  const BadType = mkPi(
    Type,
    mkApp(Vec, mkVar(0)),  // Vec A - but A : Type, and Vec expects Nat!
    'A'
  );

  const result = checkInductiveValidity(
    'Vec',
    elabToKernel(VecKind) as TTKTerm,
    [
      { name: 'Bad', type: elabToKernel(BadType) as TTKTerm }
    ],
    []
  );

  assert(!result.success, 'Expected failure - Type passed where Nat expected');
  // Note: The type mismatch (expected Nat, got Type) is now caught by the main
  // type-checker in checkInductiveDeclaration. checkInductiveValidity still catches
  // this case via universe constraints (Type argument in Type-level inductive).
  assert(
    result.errors.some(e => e.message.includes('universe') || e.message.includes('Type')),
    `Error should mention universe or type issue, got: ${result.errors.map(e => e.message).join(', ')}`
  );
});

test('Valid from validity perspective: arguments in wrong order (type-checker catches this)', () => {
  // Vec : Type -> Nat -> Type 1 (parametric)
  // VNil : (n : Nat) -> (A : Type) -> Vec n A  -- WRONG! Args are swapped
  //
  // NOTE: This test verifies that checkInductiveValidity passes because:
  // - The return type head IS Vec (passes return type check)
  // - No positivity violations (Vec doesn't appear negatively)
  // - No universe violations (arguments are Nat and Type which are fine)
  //
  // The actual type mismatch (passing Nat where Type is expected) is caught
  // by the main type-checker in checkInductiveDeclaration, not by checkInductiveValidity.
  const Nat = mkInductiveRef('Nat', Type);

  // Vec : Type -> Nat -> Type 1
  const VecKind = mkPi(Type, mkArrow(Nat, Type1), 'A');
  const Vec = mkInductiveRef('Vec', VecKind);

  // VNil : (n : Nat) -> (A : Type) -> Vec n A
  // This passes (n : Nat) first, then (A : Type), but Vec expects Type first then Nat
  const VNilType = mkPi(
    Nat,
    mkPi(
      Type,
      mkApp(mkApp(Vec, mkVar(1)), mkVar(0)),  // Vec n A - n:Nat where Type expected!
      'A'
    ),
    'n'
  );

  const result = checkInductiveValidity(
    'Vec',
    elabToKernel(VecKind) as TTKTerm,
    [
      { name: 'VNil', type: elabToKernel(VNilType) as TTKTerm }
    ],
    []
  );

  // checkInductiveValidity passes - type mismatch is caught by type-checker
  assert(result.success, 'checkInductiveValidity passes; type-checker catches the type mismatch');
});

test('Valid: correctly typed Vec constructors', () => {
  // Vec : Type -> Nat -> Type 1
  // VNil : (A : Type) -> Vec A Zero
  // VCons : (A : Type) -> (n : Nat) -> A -> Vec A n -> Vec A (Succ n)
  //
  // Note: Vec must be in Type 1 (Sort 2) because it takes a Type parameter,
  // and the universe constraint requires Type (Sort 1) < Type 1 (Sort 2)
  const Nat = mkInductiveRef('Nat', Type);
  const Zero = mkInductiveRef('Zero', Nat);
  const Succ = mkInductiveRef('Succ', mkArrow(Nat, Nat));

  // Vec : Type -> Nat -> Type 1
  const VecKind = mkPi(Type, mkArrow(Nat, Type1), 'A');
  const Vec = mkInductiveRef('Vec', VecKind);

  // VNil : (A : Type) -> Vec A Zero
  const VNilType = mkPi(
    Type,
    mkApp(mkApp(Vec, mkVar(0)), Zero),
    'A'
  );

  // VCons : (A : Type) -> (n : Nat) -> A -> Vec A n -> Vec A (Succ n)
  const VConsType = mkPi(
    Type,  // A : Type
    mkPi(
      Nat,  // n : Nat
      mkPi(
        mkVar(1),  // _ : A
        mkPi(
          mkApp(mkApp(Vec, mkVar(2)), mkVar(1)),  // _ : Vec A n
          mkApp(mkApp(Vec, mkVar(3)), mkApp(Succ, mkVar(2))),  // Vec A (Succ n)
          '_'
        ),
        '_'
      ),
      'n'
    ),
    'A'
  );

  const result = checkInductiveValidity(
    'Vec',
    elabToKernel(VecKind) as TTKTerm,
    [
      { name: 'VNil', type: elabToKernel(VNilType) as TTKTerm },
      { name: 'VCons', type: elabToKernel(VConsType) as TTKTerm }
    ],
    []
  );

  assert(result.success, `Expected success for correctly typed Vec, got: ${result.errors.map(e => e.message).join(', ')}`);
});

test('Valid from validity perspective: Fin with wrong index type (type-checker catches this)', () => {
  // Fin : Nat -> Type
  // BadFZero : (b : Bool) -> Fin b  -- WRONG! b is Bool, not Nat
  //
  // NOTE: checkInductiveValidity passes because:
  // - Return type head IS Fin (passes return type check)
  // - No positivity violations
  // - No universe violations (Bool is in Type which is fine)
  //
  // The type mismatch (Bool vs Nat) is caught by the main type-checker.
  const Nat = mkInductiveRef('Nat', Type);
  const Bool = mkInductiveRef('Bool', Type);

  // Fin : Nat -> Type
  const FinKind = mkArrow(Nat, Type);
  const Fin = mkInductiveRef('Fin', FinKind);

  // BadFZero : (b : Bool) -> Fin b
  const BadFZeroType = mkPi(
    Bool,
    mkApp(Fin, mkVar(0)),  // Fin b - but b : Bool, not Nat!
    'b'
  );

  const result = checkInductiveValidity(
    'Fin',
    elabToKernel(FinKind) as TTKTerm,
    [
      { name: 'BadFZero', type: elabToKernel(BadFZeroType) as TTKTerm }
    ],
    []
  );

  // checkInductiveValidity passes - type mismatch is caught by type-checker
  assert(result.success, 'checkInductiveValidity passes; type-checker catches the type mismatch');
});

test('Valid: Eq with correct identity type', () => {
  // Eq : (A : Type) -> A -> A -> Type 1
  // refl : (A : Type) -> (x : A) -> Eq A x x
  //
  // Note: Eq must be in Type 1 (Sort 2) because it takes a Type parameter

  // Eq : (A : Type) -> A -> A -> Type 1
  const EqKind = mkPi(Type, mkPi(mkVar(0), mkArrow(mkVar(1), Type1), 'x'), 'A');
  const Eq = mkInductiveRef('Eq', EqKind);

  // refl : (A : Type) -> (x : A) -> Eq A x x
  const reflType = mkPi(
    Type,
    mkPi(
      mkVar(0),  // x : A
      mkApp(mkApp(mkApp(Eq, mkVar(1)), mkVar(0)), mkVar(0)),  // Eq A x x
      'x'
    ),
    'A'
  );

  const result = checkInductiveValidity(
    'Eq',
    elabToKernel(EqKind) as TTKTerm,
    [
      { name: 'refl', type: elabToKernel(reflType) as TTKTerm }
    ],
    []
  );

  assert(result.success, `Expected success for Eq, got: ${result.errors.map(e => e.message).join(', ')}`);
});

console.log('\n' + '='.repeat(80));
console.log('ALL INDUCTIVE TYPE VALIDITY TESTS PASSED! ✓');
console.log('='.repeat(80) + '\n');
