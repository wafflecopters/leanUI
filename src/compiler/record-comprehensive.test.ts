/**
 * Comprehensive tests for record declarations.
 * Tests the full pipeline including algebraic structures, type classes,
 * projections, eta equality, and error cases.
 *
 * Test organization:
 * - PASSING TESTS: Features that work correctly
 * - FUTURE TESTS: Features that need implementation (marked with .todo or .skip)
 * - NEGATIVE TESTS: Things that should fail (type errors, invalid syntax)
 */

import { describe, test, expect } from 'vitest';
import { compileTTFromText, CompiledDeclaration } from './compile';
import { areTypesDefEq } from './whnf';

// Helper to find a declaration by name across all blocks
function findDecl(result: ReturnType<typeof compileTTFromText>, name: string): CompiledDeclaration | undefined {
  return result.blocks.flatMap(b => b.declarations).find(d => d.name === name);
}

// Helper to check compilation success and print errors on failure
function expectSuccess(result: ReturnType<typeof compileTTFromText>, declName?: string) {
  if (!result.success) {
    console.log('Parse errors:', result.blocks.flatMap(b => b.parseErrors.map(e => e.message || JSON.stringify(e))));
    console.log('Check errors:', result.blocks.flatMap(b =>
      b.declarations.flatMap(d => d.checkErrors?.map(e => e.message) || [])
    ));
    console.log('Name errors:', result.blocks.flatMap(b => b.nameResolutionErrors));
  }
  expect(result.success).toBe(true);
  if (declName) {
    const decl = findDecl(result, declName);
    expect(decl).toBeDefined();
    expect(decl?.checkSuccess).toBe(true);
  }
}

// Helper to check compilation failure
function expectFailure(result: ReturnType<typeof compileTTFromText>) {
  expect(result.success).toBe(false);
}

// Helper to check parse success but type check failure
function expectParseSuccessCheckFailure(result: ReturnType<typeof compileTTFromText>) {
  expect(result.blocks[0].parseErrors).toHaveLength(0);
  expect(result.success).toBe(false);
}

// Common prelude for Nat
const NAT_PRELUDE = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat
`;

// Common prelude for Bool
const BOOL_PRELUDE = `
inductive Bool : Type where
  True : Bool
  False : Bool
`;

// Common prelude for List
// Note: Parser doesn't support `inductive Name (A : Type)` syntax yet,
// so we use indices with explicit constructors
const LIST_PRELUDE = `
inductive List : Type -> Type where
  Nil : {A : Type} -> List A
  Cons : {A : Type} -> A -> List A -> List A
`;

// Common prelude for Maybe
const MAYBE_PRELUDE = `
inductive Maybe : Type -> Type where
  Nothing : {A : Type} -> Maybe A
  Just : {A : Type} -> A -> Maybe A
`;

// Common prelude for Vec (indexed type)
const VEC_PRELUDE = NAT_PRELUDE + `
inductive Vec : Type -> Nat -> Type where
  VNil : {A : Type} -> Vec A Zero
  VCons : {A : Type} -> {n : Nat} -> A -> Vec A n -> Vec A (Succ n)
`;

// ============================================================================
// SECTION 1: BASIC RECORDS (All passing)
// ============================================================================

describe('Basic Records', () => {
  test('Unit record (empty)', () => {
    const source = `
record Unit where
`;
    const result = compileTTFromText(source);
    expectSuccess(result, 'Unit');
  });

  test('record with single field', () => {
    const source = NAT_PRELUDE + `
record Wrapper where
  value : Nat
`;
    const result = compileTTFromText(source);
    expectSuccess(result, 'Wrapper');
  });

  test('Point record with two fields', () => {
    const source = NAT_PRELUDE + `
record Point where
  x : Nat
  y : Nat
`;
    const result = compileTTFromText(source);
    expectSuccess(result, 'Point');
  });

  test('Point with custom constructor name', () => {
    const source = NAT_PRELUDE + `
record Point where
  constructor MkPoint
  x : Nat
  y : Nat
`;
    const result = compileTTFromText(source);
    expectSuccess(result, 'Point');
    const pointDecl = findDecl(result, 'Point');
    expect(pointDecl?.kernelConstructors?.[0].name).toBe('MkPoint');
  });

  test('RGB color record with three fields', () => {
    const source = NAT_PRELUDE + `
record RGB where
  red : Nat
  green : Nat
  blue : Nat
`;
    const result = compileTTFromText(source);
    expectSuccess(result, 'RGB');
  });

  test('record with Type annotation', () => {
    const source = NAT_PRELUDE + `
record Point : Type where
  x : Nat
  y : Nat
`;
    const result = compileTTFromText(source);
    expectSuccess(result, 'Point');
  });

  test('record with Prop annotation', () => {
    const source = `
record TrueProof : Prop where
`;
    const result = compileTTFromText(source);
    expectSuccess(result, 'TrueProof');

    // Verify it's actually Prop (Sort 0)
    const decl = findDecl(result, 'TrueProof');
    const kernelType = decl?.kernelType;
    expect(kernelType?.tag).toBe('Sort');
    if (kernelType?.tag === 'Sort') {
      expect(kernelType.level.tag).toBe('ULit');
      if (kernelType.level.tag === 'ULit') {
        expect(kernelType.level.n).toBe(0);
      }
    }
  });
});

// ============================================================================
// SECTION 2: PARAMETERIZED RECORDS (Simple cases passing)
// ============================================================================

describe('Parameterized Records', () => {
  test('Box - single type parameter', () => {
    const source = `
record Box (A : Type) where
  contents : A
`;
    const result = compileTTFromText(source);
    expectSuccess(result, 'Box');
  });

  test('Pair - two type parameters', () => {
    const source = `
record Pair (A : Type) (B : Type) where
  fst : A
  snd : B
`;
    const result = compileTTFromText(source);
    expectSuccess(result, 'Pair');
  });

  test('Pair with multi-var binder syntax', () => {
    const source = `
record Pair (A B : Type) where
  fst : A
  snd : B
`;
    const result = compileTTFromText(source);
    expectSuccess(result, 'Pair');
  });

  test('Triple - three type parameters', () => {
    const source = `
record Triple (A B C : Type) where
  first : A
  second : B
  third : C
`;
    const result = compileTTFromText(source);
    expectSuccess(result, 'Triple');
  });

  test('parameterized record with Type annotation', () => {
    const source = `
record Box (A : Type) : Type where
  contents : A
`;
    const result = compileTTFromText(source);
    expectSuccess(result, 'Box');
  });

  // Dependent parameters - field type references earlier field
  test('DPair - dependent pair (Sigma type)', () => {
    const source = `
record DPair (A : Type) (B : A -> Type) where
  fst : A
  snd : B fst
`;
    const result = compileTTFromText(source);
    expectSuccess(result, 'DPair');
  });

  // Fields depending on earlier fields
  test('record field depending on previous field (SizedVec)', () => {
    const source = VEC_PRELUDE + `
record SizedVec (A : Type) where
  size : Nat
  vec : Vec A size
`;
    const result = compileTTFromText(source);
    expectSuccess(result, 'SizedVec');
  });
});

// ============================================================================
// SECTION 3: IMPLICIT PARAMETERS
// ============================================================================

describe('Implicit Parameters', () => {
  test('record with single implicit parameter', () => {
    const source = `
record Box {A : Type} where
  contents : A
`;
    const result = compileTTFromText(source);
    expectSuccess(result, 'Box');
  });

  test('record with mixed explicit and implicit parameters', () => {
    const source = `
record Tagged (tag : Type) {A : Type} where
  theTag : tag
  contents : A
`;
    const result = compileTTFromText(source);
    expectSuccess(result, 'Tagged');
  });

  test('record with implicit parameter before explicit', () => {
    const source = `
record Foo {A : Type} (x : A) where
  value : A
`;
    const result = compileTTFromText(source);
    expectSuccess(result, 'Foo');
  });

  test('record with multiple implicit parameters', () => {
    const source = `
record AllImplicit {A B C : Type} where
  x : A
  y : B
  z : C
`;
    const result = compileTTFromText(source);
    expectSuccess(result, 'AllImplicit');
  });

  test('record with alternating explicit and implicit', () => {
    const source = `
record Alternating (A : Type) {B : Type} (C : Type) {D : Type} where
  a : A
  b : B
  c : C
  d : D
`;
    const result = compileTTFromText(source);
    expectSuccess(result, 'Alternating');
  });
});

// ============================================================================
// SECTION 4: RECORD CONSTRUCTION
// ============================================================================

describe('Record Construction', () => {
  test('construct simple record', () => {
    const source = NAT_PRELUDE + `
record Point where
  constructor MkPoint
  x : Nat
  y : Nat

origin : Point
origin = MkPoint Zero Zero
`;
    const result = compileTTFromText(source);
    expectSuccess(result, 'origin');
  });

  test('construct record with inferred type params', () => {
    const source = NAT_PRELUDE + `
record Pair (A B : Type) where
  constructor MkPair
  fst : A
  snd : B

pair : Pair Nat Nat
pair = MkPair Zero (Succ Zero)
`;
    const result = compileTTFromText(source);
    expectSuccess(result, 'pair');
  });

  test('construct nested records', () => {
    const source = NAT_PRELUDE + `
record Point where
  constructor MkPoint
  x : Nat
  y : Nat

record Line where
  constructor MkLine
  start : Point
  end : Point

horizontalLine : Line
horizontalLine = MkLine (MkPoint Zero Zero) (MkPoint (Succ Zero) Zero)
`;
    const result = compileTTFromText(source);
    expectSuccess(result, 'horizontalLine');
  });

  test('construct Box with Nat', () => {
    const source = NAT_PRELUDE + `
record Box (A : Type) where
  constructor MkBox
  contents : A

natBox : Box Nat
natBox = MkBox (Succ Zero)
`;
    const result = compileTTFromText(source);
    expectSuccess(result, 'natBox');
  });

  test('construct Box with Bool', () => {
    const source = BOOL_PRELUDE + `
record Box (A : Type) where
  constructor MkBox
  contents : A

boolBox : Box Bool
boolBox = MkBox True
`;
    const result = compileTTFromText(source);
    expectSuccess(result, 'boolBox');
  });
});

// ============================================================================
// SECTION 5: PROJECTIONS
// ============================================================================

describe('Projections', () => {
  test('simple projection usage', () => {
    const source = NAT_PRELUDE + `
record Point where
  constructor MkPoint
  x : Nat
  y : Nat

getX : Point -> Nat
getX p = Point.x p
`;
    const result = compileTTFromText(source);
    expectSuccess(result, 'getX');
  });

  test('multiple projections from same record', () => {
    const source = NAT_PRELUDE + `
record Point where
  constructor MkPoint
  x : Nat
  y : Nat

getY : Point -> Nat
getY p = Point.y p
`;
    const result = compileTTFromText(source);
    expectSuccess(result, 'getY');
  });

  test('projection used in expression', () => {
    const source = NAT_PRELUDE + `
record Point where
  constructor MkPoint
  x : Nat
  y : Nat

addCoords : Point -> Nat
addCoords p = Point.x p
`;
    const result = compileTTFromText(source);
    expectSuccess(result, 'addCoords');
  });

  test('projection on parameterized record', () => {
    const source = NAT_PRELUDE + `
record Pair (A B : Type) where
  constructor MkPair
  fst : A
  snd : B

getFst : Pair Nat Nat -> Nat
getFst p = Pair.fst p

getSnd : Pair Nat Nat -> Nat
getSnd p = Pair.snd p
`;
    const result = compileTTFromText(source);
    expectSuccess(result, 'getFst');
    expectSuccess(result, 'getSnd');
  });

  test('chained projections', () => {
    const source = NAT_PRELUDE + `
record Inner where
  constructor MkInner
  value : Nat

record Outer where
  constructor MkOuter
  inner : Inner

getValue : Outer -> Nat
getValue o = Inner.value (Outer.inner o)
`;
    const result = compileTTFromText(source);
    expectSuccess(result, 'getValue');
  });

  test('projection passed to function', () => {
    const source = NAT_PRELUDE + `
record Point where
  constructor MkPoint
  x : Nat
  y : Nat

id : Nat -> Nat
id n = n

useProjection : Point -> Nat
useProjection p = id (Point.x p)
`;
    const result = compileTTFromText(source);
    expectSuccess(result, 'useProjection');
  });
});

// ============================================================================
// SECTION 6: PATTERN MATCHING ON RECORDS
// ============================================================================

describe('Pattern Matching on Records', () => {
  test('pattern match on simple record constructor', () => {
    const source = NAT_PRELUDE + `
record Point where
  constructor MkPoint
  x : Nat
  y : Nat

getX : Point -> Nat
getX (MkPoint a b) = a
`;
    const result = compileTTFromText(source);
    expectSuccess(result, 'getX');
  });

  test('pattern match with wildcards', () => {
    const source = NAT_PRELUDE + `
record Point where
  constructor MkPoint
  x : Nat
  y : Nat

getX : Point -> Nat
getX (MkPoint a _) = a

getY : Point -> Nat
getY (MkPoint _ b) = b
`;
    const result = compileTTFromText(source);
    expectSuccess(result, 'getX');
    expectSuccess(result, 'getY');
  });

  test('nested pattern match', () => {
    const source = NAT_PRELUDE + `
record Point where
  constructor MkPoint
  x : Nat
  y : Nat

record Line where
  constructor MkLine
  start : Point
  end : Point

getStartX : Line -> Nat
getStartX (MkLine (MkPoint x _) _) = x
`;
    const result = compileTTFromText(source);
    expectSuccess(result, 'getStartX');
  });

  test('pattern match on parameterized record (implicit type args)', () => {
    const source = NAT_PRELUDE + `
record Pair (A B : Type) where
  constructor MkPair
  fst : A
  snd : B

swap : {A B : Type} -> Pair A B -> Pair B A
swap (MkPair a b) = MkPair b a
`;
    const result = compileTTFromText(source);
    expectSuccess(result, 'swap');
  });
});

// ============================================================================
// SECTION 7: ALGEBRAIC STRUCTURES
// ============================================================================

describe('Algebraic Structures', () => {
  test('Magma - basic binary operation', () => {
    const source = `
record Magma (A : Type) where
  op : A -> A -> A
`;
    const result = compileTTFromText(source);
    expectSuccess(result, 'Magma');
  });

  test('Semigroup - operation carrier', () => {
    const source = `
record Semigroup (A : Type) where
  op : A -> A -> A
`;
    const result = compileTTFromText(source);
    expectSuccess(result, 'Semigroup');
  });

  test('Monoid - with identity', () => {
    const source = `
record Monoid (A : Type) where
  e : A
  op : A -> A -> A
`;
    const result = compileTTFromText(source);
    expectSuccess(result, 'Monoid');
  });

  test('create Nat add Monoid instance', () => {
    const source = NAT_PRELUDE + `
record Monoid (A : Type) where
  constructor MkMonoid
  e : A
  op : A -> A -> A

add : Nat -> Nat -> Nat
add Zero n = n
add (Succ m) n = Succ (add m n)

natAddMonoid : Monoid Nat
natAddMonoid = MkMonoid Zero add
`;
    const result = compileTTFromText(source);
    expectSuccess(result, 'natAddMonoid');
  });

  test('create Nat mul Monoid instance', () => {
    const source = NAT_PRELUDE + `
record Monoid (A : Type) where
  constructor MkMonoid
  e : A
  op : A -> A -> A

mul : Nat -> Nat -> Nat
mul Zero n = Zero
mul (Succ m) n = n

natMulMonoid : Monoid Nat
natMulMonoid = MkMonoid (Succ Zero) mul
`;
    const result = compileTTFromText(source);
    expectSuccess(result, 'natMulMonoid');
  });

  test('Group - with inverses', () => {
    const source = `
record Group (A : Type) where
  e : A
  op : A -> A -> A
  inv : A -> A
`;
    const result = compileTTFromText(source);
    expectSuccess(result, 'Group');
  });

  test('Abelian Group', () => {
    const source = `
record AbelianGroup (A : Type) where
  e : A
  op : A -> A -> A
  inv : A -> A
`;
    const result = compileTTFromText(source);
    expectSuccess(result, 'AbelianGroup');
  });

  test('Ring', () => {
    const source = `
record Ring (A : Type) where
  zero : A
  one : A
  add : A -> A -> A
  mul : A -> A -> A
  neg : A -> A
`;
    const result = compileTTFromText(source);
    expectSuccess(result, 'Ring');
  });

  test('Field', () => {
    const source = `
record Field (A : Type) where
  zero : A
  one : A
  add : A -> A -> A
  mul : A -> A -> A
  neg : A -> A
  recip : A -> A
`;
    const result = compileTTFromText(source);
    expectSuccess(result, 'Field');
  });
});

// ============================================================================
// SECTION 8: TYPE CLASS PATTERNS (Functor, Monad, etc.)
// ============================================================================

describe('Type Class Patterns', () => {
  // Note: Type class records with polymorphic fields like `{A B : Type} -> ...`
  // need to be at Type 1, not Type, because the polymorphic function type has
  // type Sort 2. This is the predicativity constraint.
  test('Functor', () => {
    const source = `
record Functor (F : Type -> Type) : Type 1 where
  map : {A B : Type} -> (A -> B) -> F A -> F B
`;
    const result = compileTTFromText(source);
    expectSuccess(result, 'Functor');
  });

  test('Applicative', () => {
    const source = `
record Applicative (F : Type -> Type) : Type 1 where
  pure : {A : Type} -> A -> F A
  ap : {A B : Type} -> F (A -> B) -> F A -> F B
`;
    const result = compileTTFromText(source);
    expectSuccess(result, 'Applicative');
  });

  test('Monad', () => {
    const source = `
record Monad (M : Type -> Type) : Type 1 where
  pure : {A : Type} -> A -> M A
  bind : {A B : Type} -> M A -> (A -> M B) -> M B
`;
    const result = compileTTFromText(source);
    expectSuccess(result, 'Monad');
  });

  test('MonadTrans', () => {
    const source = `
record MonadTrans (T : (Type -> Type) -> Type -> Type) : Type 1 where
  lift : {M : Type -> Type} -> {A : Type} -> M A -> T M A
`;
    const result = compileTTFromText(source);
    expectSuccess(result, 'MonadTrans');
  });

  test('Foldable', () => {
    const source = `
record Foldable (F : Type -> Type) : Type 1 where
  foldr : {A B : Type} -> (A -> B -> B) -> B -> F A -> B
`;
    const result = compileTTFromText(source);
    expectSuccess(result, 'Foldable');
  });

  test('Traversable', () => {
    const source = `
record Traversable (T : Type -> Type) : Type 1 where
  traverse : {F : Type -> Type} -> {A B : Type} -> (A -> F B) -> T A -> F (T B)
`;
    const result = compileTTFromText(source);
    expectSuccess(result, 'Traversable');
  });

  // Creating instances with pattern match on parameterized types - now works!
  test('create Maybe Functor instance', () => {
    const source = MAYBE_PRELUDE + `
record Functor (F : Type -> Type) : Type 1 where
  constructor MkFunctor
  map : {A B : Type} -> (A -> B) -> F A -> F B

mapMaybe : {A B : Type} -> (A -> B) -> Maybe A -> Maybe B
mapMaybe f Nothing = Nothing
mapMaybe f (Just x) = Just (f x)

maybeFunctor : Functor Maybe
maybeFunctor = MkFunctor mapMaybe
`;
    const result = compileTTFromText(source);
    expectSuccess(result, 'maybeFunctor');
  });
});

// ============================================================================
// SECTION 9: COMPLEX RECORDS (Self-referential, nested types)
// ============================================================================

describe('Complex Records', () => {
  test('State monad carrier', () => {
    const source = `
record State (S A : Type) where
  constructor MkState
  runState : S -> S
`;
    const result = compileTTFromText(source);
    expectSuccess(result, 'State');
  });

  test('Reader monad carrier', () => {
    const source = `
record Reader (R A : Type) where
  constructor MkReader
  runReader : R -> A
`;
    const result = compileTTFromText(source);
    expectSuccess(result, 'Reader');
  });

  test('Writer monad carrier', () => {
    const source = `
record Writer (W A : Type) where
  constructor MkWriter
  runWriter : A
  log : W
`;
    const result = compileTTFromText(source);
    expectSuccess(result, 'Writer');
  });

  test('Equivalence relation carrier', () => {
    const source = `
record Equiv (A : Type) where
  rel : A -> A -> Prop
`;
    const result = compileTTFromText(source);
    expectSuccess(result, 'Equiv');
  });

  test('Preorder', () => {
    const source = `
record Preorder (A : Type) where
  leq : A -> A -> Prop
`;
    const result = compileTTFromText(source);
    expectSuccess(result, 'Preorder');
  });

  // Self-referential fields (field type references earlier field)
  test('DPair (dependent pair / Sigma type)', () => {
    const source = `
record DPair {u v : ULevel} (A : Type u) (B : A -> Type v) : Type (UMax u v) where
  constructor MkDPair
  dfst: A
  dsnd: B dfst
`;
    const result = compileTTFromText(source);
    expectSuccess(result, 'DPair');
  });

  test('Category record (Hom depends on Obj)', () => {
    const source = `
record Category where
  Obj : Type
  Hom : Obj -> Obj -> Type
  id : {A : Obj} -> Hom A A
  comp : {A B C : Obj} -> Hom B C -> Hom A B -> Hom A C
`;
    const result = compileTTFromText(source);
    expectSuccess(result, 'Category');
  });
});

// ============================================================================
// SECTION 10: EXTENDS (Inheritance) - FUTURE
// ============================================================================

describe('Record Extension (extends)', () => {
  test('extends clause parses correctly', () => {
    const source = NAT_PRELUDE + `
record Base where
  x : Nat

record Extended extends Base where
  y : Nat
`;
    const result = compileTTFromText(source);
    // Just check parsing works - full extends not implemented
    expect(result.blocks[0].parseErrors).toHaveLength(0);
  });

  test('extends with type annotation parses', () => {
    const source = NAT_PRELUDE + `
record Base : Type where
  x : Nat

record Extended : Type extends Base where
  y : Nat
`;
    const result = compileTTFromText(source);
    expect(result.blocks[0].parseErrors).toHaveLength(0);
  });

  test('extends with applied type parameter parses', () => {
    const source = `
record Pred (alpha : Type) : Prop where
  p : alpha

record DecPred (alpha : Type) extends Pred alpha where
  extra : alpha
`;
    const result = compileTTFromText(source);
    expect(result.blocks[0].parseErrors).toHaveLength(0);
  });

  // Extends inlining implementation
  test('extended record includes parent fields', () => {
    const source = NAT_PRELUDE + `
record Base where
  constructor MkBase
  x : Nat

record Extended extends Base where
  constructor MkExtended
  y : Nat

-- Extended should have both x and y fields
ext : Extended
ext = MkExtended Zero (Succ Zero)
`;
    const result = compileTTFromText(source);
    expectSuccess(result, 'ext');
  });
});

// ============================================================================
// SECTION 11: NEGATIVE TESTS (Should fail)
// ============================================================================

describe('Error Cases - Should Fail', () => {
  test('record with undefined type in field', () => {
    const source = `
record Bad where
  x : UndefinedType
`;
    const result = compileTTFromText(source);
    expectFailure(result);
  });

  test('record with undefined type parameter', () => {
    const source = `
record Bad (A : UndefinedType) where
  x : A
`;
    const result = compileTTFromText(source);
    expectFailure(result);
  });

  test('constructor type mismatch - wrong types', () => {
    const source = NAT_PRELUDE + BOOL_PRELUDE + `
record Point where
  constructor MkPoint
  x : Nat
  y : Nat

bad : Point
bad = MkPoint True False
`;
    const result = compileTTFromText(source);
    expectFailure(result);
  });

  test('constructor wrong number of arguments - too few', () => {
    const source = NAT_PRELUDE + `
record Point where
  constructor MkPoint
  x : Nat
  y : Nat

bad : Point
bad = MkPoint Zero
`;
    const result = compileTTFromText(source);
    expectFailure(result);
  });

  test('projection on wrong record type', () => {
    const source = NAT_PRELUDE + `
record Point where
  x : Nat
  y : Nat

record RGB where
  red : Nat
  green : Nat
  blue : Nat

bad : RGB -> Nat
bad r = Point.x r
`;
    const result = compileTTFromText(source);
    expectFailure(result);
  });

  test('field type kind mismatch', () => {
    // A is a Type, can't apply it to itself
    const source = `
record Bad (A : Type) where
  x : A A
`;
    const result = compileTTFromText(source);
    expectFailure(result);
  });

  test('non-existent projection', () => {
    const source = NAT_PRELUDE + `
record Point where
  x : Nat
  y : Nat

bad : Point -> Nat
bad p = Point.z p
`;
    const result = compileTTFromText(source);
    expectFailure(result);
  });

  test('using wrong projection prefix', () => {
    const source = NAT_PRELUDE + `
record Point where
  x : Nat
  y : Nat

record Other where
  z : Nat

bad : Point -> Nat
bad p = Other.z p
`;
    const result = compileTTFromText(source);
    expectFailure(result);
  });
});

// ============================================================================
// SECTION 12: FUNCTIONS USING RECORDS
// ============================================================================

describe('Functions Using Records', () => {
  test('function returning record', () => {
    const source = NAT_PRELUDE + `
record Point where
  constructor MkPoint
  x : Nat
  y : Nat

makePoint : Nat -> Nat -> Point
makePoint a b = MkPoint a b
`;
    const result = compileTTFromText(source);
    expectSuccess(result, 'makePoint');
  });

  test('function transforming record', () => {
    const source = NAT_PRELUDE + `
record Point where
  constructor MkPoint
  x : Nat
  y : Nat

setX : Nat -> Point -> Point
setX newX (MkPoint _ y) = MkPoint newX y
`;
    const result = compileTTFromText(source);
    expectSuccess(result, 'setX');
  });

  test('function with record in middle of args', () => {
    const source = NAT_PRELUDE + `
record Point where
  constructor MkPoint
  x : Nat
  y : Nat

addToX : Nat -> Point -> Nat -> Point
addToX n (MkPoint x y) m = MkPoint x y
`;
    const result = compileTTFromText(source);
    expectSuccess(result, 'addToX');
  });

  test('curried record transformer', () => {
    const source = NAT_PRELUDE + `
record Point where
  constructor MkPoint
  x : Nat
  y : Nat

curried : Nat -> Point -> Point
curried n = fun (p : Point) => MkPoint (Point.x p) (Point.y p)
`;
    const result = compileTTFromText(source);
    expectSuccess(result, 'curried');
  });

  test('record as return type of pattern match', () => {
    const source = NAT_PRELUDE + `
record Point where
  constructor MkPoint
  x : Nat
  y : Nat

pointFromNat : Nat -> Point
pointFromNat Zero = MkPoint Zero Zero
pointFromNat (Succ n) = MkPoint (Succ n) (Succ n)
`;
    const result = compileTTFromText(source);
    expectSuccess(result, 'pointFromNat');
  });
});

// ============================================================================
// SECTION 13: UNIVERSE POLYMORPHISM - FUTURE
// ============================================================================

describe('Universe Polymorphism', () => {
  test('universe level annotation parses', () => {
    const source = `
record Box {u : ULevel} (A : Type u) : Type (USucc u) where
  unbox : A
`;
    const result = compileTTFromText(source);
    // Just check parsing works
    expect(result.blocks[0].parseErrors).toHaveLength(0);
  });

  // Universe polymorphic record with level variable
  test('universe polymorphic record fully checks', () => {
    const source = `
record Box {u : ULevel} (A : Type u) : Type (USucc u) where
  unbox : A
`;
    const result = compileTTFromText(source);
    expectSuccess(result, 'Box');
  });
});

// ============================================================================
// SECTION 14: EDGE CASES
// ============================================================================

describe('Edge Cases', () => {
  test('empty record with Prop type', () => {
    const source = `
record True : Prop where
`;
    const result = compileTTFromText(source);
    expectSuccess(result, 'True');
  });

  test('record with single implicit param and single field', () => {
    const source = `
record Id {A : Type} where
  unId : A
`;
    const result = compileTTFromText(source);
    expectSuccess(result, 'Id');
  });

  test('long chain of projections', () => {
    const source = NAT_PRELUDE + `
record A where
  constructor MkA
  valA : Nat

record B where
  constructor MkB
  innerA : A

record C where
  constructor MkC
  innerB : B

getDeepValue : C -> Nat
getDeepValue c = A.valA (B.innerA (C.innerB c))
`;
    const result = compileTTFromText(source);
    expectSuccess(result, 'getDeepValue');
  });

  test('record used as type argument', () => {
    const source = NAT_PRELUDE + `
record Point where
  constructor MkPoint
  x : Nat
  y : Nat

record Box (A : Type) where
  constructor MkBox
  contents : A

pointBox : Box Point
pointBox = MkBox (MkPoint Zero Zero)
`;
    const result = compileTTFromText(source);
    expectSuccess(result, 'pointBox');
  });
});

// ============================================================================
// SECTION 15: ETA EQUALITY - FUTURE
// ============================================================================

describe('Eta Equality', () => {
test('eta expansion: mk (proj1 r) (proj2 r) = r', () => {
    const source = NAT_PRELUDE + `
record Point where
  constructor MkPoint
  x : Nat
  y : Nat

-- This requires eta: MkPoint (Point.x p) (Point.y p) = p
etaPoint : (p : Point) -> Point
etaPoint p = MkPoint (Point.x p) (Point.y p)

-- These should be definitionally equal
id1 : Point -> Point
id1 p = p

id2 : Point -> Point
id2 p = MkPoint (Point.x p) (Point.y p)
`;
    const result = compileTTFromText(source);
    expectSuccess(result, 'id1');
    expectSuccess(result, 'id2');

    const p = { tag: 'Var' as const, index: 0 };
    const lhs = { tag: 'App' as const, fn: { tag: 'Const' as const, name: 'id1' }, arg: p };
    const rhs = { tag: 'App' as const, fn: { tag: 'Const' as const, name: 'id2' }, arg: p };
    expect(areTypesDefEq(lhs, rhs, result.definitions, [
      { name: 'p', type: { tag: 'Const' as const, name: 'Point' } },
    ])).toBe(true);
  });
});
