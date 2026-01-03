/**
 * Tests for Parameter/Index Inference Algorithm
 *
 * Tests the algorithm that classifies inductive type arguments as
 * either parameters (fixed across constructors) or indices (varying).
 */

import { inferParameterIndices } from './tt-inductive-inference';
import { InductiveTypeDef } from './tt-examples';
import { TTerm, mkType, mkPi, mkConst, mkApp, mkVar } from './tt-core';

// ============================================================================
// Test Helpers
// ============================================================================

const Type0 = mkType(0);

function mkInductiveRef(name: string, kind: TTerm): TTerm {
  return mkConst(name, kind);
}

function mkArrow(domain: TTerm, codomain: TTerm): TTerm {
  return mkPi(domain, codomain, '_');
}

/**
 * Run a test with description
 */
function test(description: string, fn: () => void): void {
  try {
    fn();
    console.log(`✓ ${description}`);
  } catch (error) {
    console.error(`✗ ${description}`);
    throw error;
  }
}

/**
 * Assert arrays are equal
 */
function assertArrayEqual(actual: number[], expected: number[], message?: string): void {
  const actualStr = JSON.stringify(actual.sort());
  const expectedStr = JSON.stringify(expected.sort());

  if (actualStr !== expectedStr) {
    console.error('Arrays not equal!');
    if (message) console.error('Test:', message);
    console.error('Expected:', expectedStr);
    console.error('Actual:', actualStr);
    throw new Error(`Array equality assertion failed: ${message || ''}`);
  }
}

// ============================================================================
// Example Type Definitions
// ============================================================================

/**
 * Natural numbers: Nat : Type
 *
 * inductive Nat : Type where
 *   | zero : Nat
 *   | succ : Nat -> Nat
 *
 * Expected: [] (no parameters, no indices - it's a simple type)
 */
function makeNat(): InductiveTypeDef {
  const Nat = mkInductiveRef('Nat', Type0);

  return {
    name: 'Nat',
    type: Type0,
    constructors: [
      {
        name: 'zero',
        type: Nat,
      },
      {
        name: 'succ',
        type: mkArrow(Nat, Nat),
      },
    ],
  };
}

/**
 * Vector: Vec : Type -> Nat -> Type
 *
 * inductive Vec : Type -> Nat -> Type where
 *   | vnil  : (A : Type) -> Vec A 0
 *   | vcons : (A : Type) -> (n : Nat) -> A -> Vec A n -> Vec A (succ n)
 *
 * Expected: [1] (position 0 is parameter (Type), position 1 is index (Nat))
 */
function makeVec(): InductiveTypeDef {
  const Nat = mkInductiveRef('Nat', Type0);
  const succ = mkConst('succ', mkArrow(Nat, Nat));
  const zero = mkConst('zero', Nat);

  // Vec : Type -> Nat -> Type
  const VecKind = mkPi(Type0, mkArrow(Nat, Type0), 'A');
  const Vec = mkInductiveRef('Vec', VecKind);

  return {
    name: 'Vec',
    type: VecKind,
    constructors: [
      {
        name: 'vnil',
        // vnil : (A : Type) -> Vec A 0
        type: mkPi(
          Type0,
          mkApp(mkApp(Vec, mkVar(0)), zero),
          'A'
        ),
      },
      {
        name: 'vcons',
        // vcons : (A : Type) -> (n : Nat) -> A -> Vec A n -> Vec A (succ n)
        // (A : Type) ->           -- A at 0
        //   (n : Nat) ->          -- A at 1, n at 0
        //     (_ : A) ->          -- A at 2, n at 1
        //       (_ : Vec A n) ->  -- A at 3, n at 2
        //         Vec A (succ n)  -- A at 4, n at 3
        type: mkPi(
          Type0,
          mkPi(
            Nat,
            mkPi(
              mkVar(1), // A
              mkPi(
                mkApp(mkApp(Vec, mkVar(2)), mkVar(1)), // Vec A n
                mkApp(mkApp(Vec, mkVar(3)), mkApp(succ, mkVar(2))), // Vec A (succ n)
                '_'
              ),
              '_'
            ),
            'n'
          ),
          'A'
        ),
      },
    ],
  };
}

/**
 * Fin: Fin : Nat -> Type
 *
 * inductive Fin : Nat -> Type where
 *   | fzero : (n : Nat) -> Fin (succ n)
 *   | fsucc : (n : Nat) -> Fin n -> Fin (succ n)
 *
 * Expected: [0] (position 0 is index - it's not a simple variable)
 */
function makeFin(): InductiveTypeDef {
  const Nat = mkInductiveRef('Nat', Type0);
  const succ = mkConst('succ', mkArrow(Nat, Nat));

  // Fin : Nat -> Type
  const FinKind = mkArrow(Nat, Type0);
  const Fin = mkInductiveRef('Fin', FinKind);

  return {
    name: 'Fin',
    type: FinKind,
    constructors: [
      {
        name: 'fzero',
        // fzero : (n : Nat) -> Fin (succ n)
        type: mkPi(
          Nat,
          mkApp(Fin, mkApp(succ, mkVar(0))),
          'n'
        ),
      },
      {
        name: 'fsucc',
        // fsucc : (n : Nat) -> Fin n -> Fin (succ n)
        type: mkPi(
          Nat,
          mkPi(
            mkApp(Fin, mkVar(0)), // Fin n
            mkApp(Fin, mkApp(succ, mkVar(1))), // Fin (succ n)
            '_'
          ),
          'n'
        ),
      },
    ],
  };
}

/**
 * Equality: Eq : (A : Type) -> A -> A -> Type
 *
 * inductive Eq : (A : Type) -> A -> A -> Type where
 *   | refl : (A : Type) -> (x : A) -> Eq A x x
 *
 * Expected: [2] (positions 0 and 1 are parameters, position 2 is index)
 * This is the J eliminator case where x is promoted to parameter.
 */
function makeEq(): InductiveTypeDef {
  // Eq : (A : Type) -> A -> A -> Type
  // (A : Type) ->     -- A at 0
  //   (_ : A) ->      -- A at 1, first A at 0
  //     (_ : A) ->    -- A at 2, first A at 1, second A at 0
  //       Type        -- A at 3
  const EqKind = mkPi(
    Type0,
    mkPi(
      mkVar(0), // A
      mkPi(
        mkVar(1), // A
        Type0,
        '_'
      ),
      '_'
    ),
    'A'
  );
  const Eq = mkInductiveRef('Eq', EqKind);

  return {
    name: 'Eq',
    type: EqKind,
    constructors: [
      {
        name: 'refl',
        // refl : (A : Type) -> (x : A) -> Eq A x x
        // (A : Type) ->    -- A at 0
        //   (x : A) ->     -- A at 1, x at 0
        //     Eq A x x     -- A at 2, x at 1
        type: mkPi(
          Type0,
          mkPi(
            mkVar(0), // A
            mkApp(
              mkApp(
                mkApp(Eq, mkVar(1)), // Eq A
                mkVar(0)             // x
              ),
              mkVar(0)               // x
            ),
            'x'
          ),
          'A'
        ),
      },
    ],
  };
}

/**
 * List: List : Type -> Type
 *
 * inductive List : Type -> Type where
 *   | nil  : (A : Type) -> List A
 *   | cons : (A : Type) -> A -> List A -> List A
 *
 * Expected: [] (position 0 is parameter, no indices)
 */
function makeList(): InductiveTypeDef {
  // List : Type -> Type
  const ListKind = mkArrow(Type0, Type0);
  const List = mkInductiveRef('List', ListKind);

  return {
    name: 'List',
    type: ListKind,
    constructors: [
      {
        name: 'nil',
        // nil : (A : Type) -> List A
        type: mkPi(
          Type0,
          mkApp(List, mkVar(0)),
          'A'
        ),
      },
      {
        name: 'cons',
        // cons : (A : Type) -> A -> List A -> List A
        // (A : Type) ->      -- A at 0
        //   (_ : A) ->       -- A at 1
        //     (_ : List A) -> -- A at 2
        //       List A       -- A at 3
        type: mkPi(
          Type0,
          mkPi(
            mkVar(0), // A
            mkPi(
              mkApp(List, mkVar(1)), // List A
              mkApp(List, mkVar(2)), // List A
              '_'
            ),
            '_'
          ),
          'A'
        ),
      },
    ],
  };
}

/**
 * Weird example from the spec:
 *
 * inductive Weird : (n : Nat) -> (v : Vec Bool n) -> Type where
 *   | mk0 : (v : Vec Bool 0) -> Weird 0 v
 *   | mkS : (n : Nat) -> (v : Vec Bool (succ n)) -> Weird (succ n) v
 *
 * Expected: [0, 1] (both are indices due to dependency validation)
 * Position 1 depends on position 0, so even though position 1 looks like
 * a parameter, it must be demoted to index.
 */
function makeWeird(): InductiveTypeDef {
  const Nat = mkInductiveRef('Nat', Type0);
  const succ = mkConst('succ', mkArrow(Nat, Nat));
  const zero = mkConst('zero', Nat);
  const Bool = mkConst('Bool', Type0);

  // Vec : Type -> Nat -> Type (simplified)
  const VecKind = mkPi(Type0, mkArrow(Nat, Type0), 'A');
  const Vec = mkInductiveRef('Vec', VecKind);

  // Weird : (n : Nat) -> (v : Vec Bool n) -> Type
  // (n : Nat) ->           -- n at 0
  //   (_ : Vec Bool n) ->  -- n at 1
  //     Type
  const WeirdKind = mkPi(
    Nat,
    mkPi(
      mkApp(mkApp(Vec, Bool), mkVar(0)), // Vec Bool n
      Type0,
      '_'
    ),
    'n'
  );
  const Weird = mkInductiveRef('Weird', WeirdKind);

  return {
    name: 'Weird',
    type: WeirdKind,
    constructors: [
      {
        name: 'mk0',
        // mk0 : (v : Vec Bool 0) -> Weird 0 v
        type: mkPi(
          mkApp(mkApp(Vec, Bool), zero), // Vec Bool 0
          mkApp(
            mkApp(Weird, zero), // Weird 0
            mkVar(0)            // v
          ),
          'v'
        ),
      },
      {
        name: 'mkS',
        // mkS : (n : Nat) -> (v : Vec Bool (succ n)) -> Weird (succ n) v
        // (n : Nat) ->                 -- n at 0
        //   (v : Vec Bool (succ n)) -> -- n at 1, v at 0
        //     Weird (succ n) v         -- n at 2, v at 1
        type: mkPi(
          Nat,
          mkPi(
            mkApp(mkApp(Vec, Bool), mkApp(succ, mkVar(0))), // Vec Bool (succ n)
            mkApp(
              mkApp(Weird, mkApp(succ, mkVar(1))), // Weird (succ n)
              mkVar(0)                               // v
            ),
            'v'
          ),
          'n'
        ),
      },
    ],
  };
}

/**
 * Bool: Bool : Type
 *
 * inductive Bool : Type where
 *   | true : Bool
 *   | false : Bool
 *
 * Expected: [] (no parameters, no indices - it's a simple type)
 */
function makeBool(): InductiveTypeDef {
  const Bool = mkInductiveRef('Bool', Type0);

  return {
    name: 'Bool',
    type: Type0,
    constructors: [
      {
        name: 'true',
        type: Bool,
      },
      {
        name: 'false',
        type: Bool,
      },
    ],
  };
}

/**
 * Empty: Empty : Type
 *
 * inductive Empty : Type where
 *   (no constructors)
 *
 * Expected: [] (no indices, it's a simple uninhabited type)
 */
function makeEmpty(): InductiveTypeDef {
  return {
    name: 'Empty',
    type: Type0,
    constructors: [],
  };
}

/**
 * Unit: Unit : Type
 *
 * inductive Unit : Type where
 *   | unit : Unit
 *
 * Expected: [] (no indices)
 */
function makeUnit(): InductiveTypeDef {
  const Unit = mkInductiveRef('Unit', Type0);

  return {
    name: 'Unit',
    type: Type0,
    constructors: [
      {
        name: 'unit',
        type: Unit,
      },
    ],
  };
}

// ============================================================================
// Tests
// ============================================================================

function runTests(): void {
  console.log('Running Parameter/Index Inference Tests...\n');

  console.log('=== Simple Types (No Arguments) ===');

  test('Nat has no indices (simple type)', () => {
    const nat = makeNat();
    const indices = inferParameterIndices(nat);
    assertArrayEqual(indices, [], 'Nat should have no indices');
  });

  test('Bool has no indices (simple type)', () => {
    const bool = makeBool();
    const indices = inferParameterIndices(bool);
    assertArrayEqual(indices, [], 'Bool should have no indices');
  });

  test('Empty has no indices (no constructors)', () => {
    const empty = makeEmpty();
    const indices = inferParameterIndices(empty);
    assertArrayEqual(indices, [], 'Empty should have no indices');
  });

  test('Unit has no indices (single constructor)', () => {
    const unit = makeUnit();
    const indices = inferParameterIndices(unit);
    assertArrayEqual(indices, [], 'Unit should have no indices');
  });

  console.log('\n=== Parameterized Types ===');

  test('List has Type as parameter, no indices', () => {
    const list = makeList();
    const indices = inferParameterIndices(list);
    assertArrayEqual(indices, [], 'List should have no indices');
  });

  test('Vec has Type as parameter, Nat as index', () => {
    const vec = makeVec();
    const indices = inferParameterIndices(vec);
    assertArrayEqual(indices, [1], 'Vec should have position 1 as index');
  });

  console.log('\n=== Indexed Types ===');

  test('Fin has Nat as index (complex term)', () => {
    const fin = makeFin();
    const indices = inferParameterIndices(fin);
    assertArrayEqual(indices, [0], 'Fin should have position 0 as index');
  });

  console.log('\n=== Advanced: Index Promotion ===');

  test('Eq promotes second argument to parameter (J eliminator)', () => {
    const eq = makeEq();
    const indices = inferParameterIndices(eq);
    assertArrayEqual(indices, [2], 'Eq should have position 2 as index (positions 0,1 are params)');
  });

  console.log('\n=== Advanced: Dependency Validation ===');

  test('Weird has both positions as indices (dependency validation)', () => {
    const weird = makeWeird();
    const indices = inferParameterIndices(weird);
    assertArrayEqual(indices, [0, 1], 'Weird should have both positions as indices');
  });

  console.log('\n✅ All tests passed!');
}

// Run tests
runTests();
