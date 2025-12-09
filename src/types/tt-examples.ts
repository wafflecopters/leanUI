/**
 * TT Examples - Inductive Type Definitions
 *
 * This file contains example inductive type definitions built using the
 * TT (Typed Terms) data structures from tt-core.ts.
 *
 * Each inductive type is defined by:
 * - name: The name of the type (e.g., "Nat", "List")
 * - type: The kind/sort of the type (e.g., Type_0, Type_0 → Type_0)
 * - constructors: Array of constructors, each with name and type
 */

import {
  TTerm,
  mkType,
  mkPi,
  mkConst,
  mkApp,
  mkVar,
} from './tt-core';

// ============================================================================
// Inductive Type Definition Interface
// ============================================================================

/**
 * An inductive type definition.
 *
 * This mirrors the structure used in InductiveTypeEditor but is a pure
 * data structure without UI concerns.
 */
export interface InductiveTypeDef {
  name: string;
  type: TTerm;
  constructors: InductiveConstructor[];
}

export interface InductiveConstructor {
  name: string;
  type: TTerm;
}

// ============================================================================
// Helper Functions for Building Inductive Types
// ============================================================================

/** Type_0 (the type of types at level 0) */
const Type0 = mkType(0);

/**
 * Create a constant reference to an inductive type.
 * The type parameter should be the kind of the inductive type.
 */
function mkInductiveRef(name: string, kind: TTerm): TTerm {
  return mkConst(name, kind);
}

/**
 * Create a non-dependent function type: A → B
 * (This is just Pi where the body doesn't use the bound variable)
 */
function mkArrow(domain: TTerm, codomain: TTerm): TTerm {
  return mkPi(domain, codomain, '_');
}

// ============================================================================
// Nat - Natural Numbers
// ============================================================================

/**
 * Natural numbers
 *
 * inductive Nat : Type where
 *   | zero : Nat
 *   | succ : Nat → Nat
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
        // succ : Nat → Nat
        type: mkArrow(Nat, Nat),
      },
    ],
  };
}

// ============================================================================
// Bool - Boolean Type
// ============================================================================

/**
 * Boolean type
 *
 * inductive Bool : Type where
 *   | true : Bool
 *   | false : Bool
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

// ============================================================================
// Void - Empty Type
// ============================================================================

/**
 * Empty type (no constructors)
 *
 * inductive Void : Type where
 *   -- no constructors
 */
function makeVoid(): InductiveTypeDef {
  return {
    name: 'Void',
    type: Type0,
    constructors: [],
  };
}

// ============================================================================
// List A - Polymorphic List
// ============================================================================

/**
 * Polymorphic list
 *
 * inductive List (A : Type) : Type where
 *   | nil : List A
 *   | cons : A → List A → List A
 *
 * Note: We represent this with explicit type parameter quantification:
 *   nil : Π (A : Type). List A
 *   cons : Π (A : Type). A → List A → List A
 */
function makeList(): InductiveTypeDef {
  // List : Type → Type
  const ListKind = mkArrow(Type0, Type0);
  const List = mkInductiveRef('List', ListKind);

  return {
    name: 'List',
    type: ListKind,
    constructors: [
      {
        name: 'nil',
        // nil : Π (A : Type). List A
        // Inside the Π, A is at index 0
        type: mkPi(
          Type0,
          mkApp(List, mkVar(0)),
          'A'
        ),
      },
      {
        name: 'cons',
        // cons : Π (A : Type). A → List A → List A
        // Building from outside in:
        // Π (A : Type).       -- A at index 0 in next level
        //   Π (_ : A).        -- A at index 1, _ at index 0 in next level
        //     Π (_ : List A). -- A at index 2 in next level
        //       List A        -- A at index 2
        type: mkPi(
          Type0,
          mkPi(
            mkVar(0), // A (at index 0)
            mkPi(
              mkApp(List, mkVar(1)), // List A (A at index 1)
              mkApp(List, mkVar(2)), // List A (A at index 2)
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

// ============================================================================
// Vec A n - Length-Indexed Vector
// ============================================================================

/**
 * Length-indexed vector
 *
 * inductive Vec (A : Type) : Nat → Type where
 *   | vnil : Vec A 0
 *   | vcons : Π (n : Nat). A → Vec A n → Vec A (succ n)
 *
 * Note: Vec is an indexed family - the constructor return types differ in the index.
 */
function makeVec(): InductiveTypeDef {
  const Nat = mkInductiveRef('Nat', Type0);
  const succ = mkConst('succ', mkArrow(Nat, Nat));

  // Vec : Type → Nat → Type
  const VecKind = mkPi(Type0, mkArrow(Nat, Type0), 'A');
  const Vec = mkInductiveRef('Vec', VecKind);

  const zero = mkConst('zero', Nat);

  return {
    name: 'Vec',
    type: VecKind,
    constructors: [
      {
        name: 'vnil',
        // vnil : Π (A : Type). Vec A 0
        type: mkPi(
          Type0,
          mkApp(mkApp(Vec, mkVar(0)), zero),
          'A'
        ),
      },
      {
        name: 'vcons',
        // vcons : Π (A : Type). Π (n : Nat). A → Vec A n → Vec A (succ n)
        // Levels:
        // Π (A : Type).           -- A at 0
        //   Π (n : Nat).          -- A at 1, n at 0
        //     Π (_ : A).          -- A at 2, n at 1, _ at 0
        //       Π (_ : Vec A n).  -- A at 3, n at 2
        //         Vec A (succ n)  -- A at 3, n at 2
        type: mkPi(
          Type0,
          mkPi(
            Nat,
            mkPi(
              mkVar(1), // A (at index 1)
              mkPi(
                mkApp(mkApp(Vec, mkVar(2)), mkVar(1)), // Vec A n (A at 2, n at 1)
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

// ============================================================================
// Fin n - Finite Set
// ============================================================================

/**
 * Finite set type (numbers less than n)
 *
 * inductive Fin : Nat → Type where
 *   | fzero : Π (n : Nat). Fin (succ n)
 *   | fsucc : Π (n : Nat). Fin n → Fin (succ n)
 */
function makeFin(): InductiveTypeDef {
  const Nat = mkInductiveRef('Nat', Type0);
  const succ = mkConst('succ', mkArrow(Nat, Nat));

  // Fin : Nat → Type
  const FinKind = mkArrow(Nat, Type0);
  const Fin = mkInductiveRef('Fin', FinKind);

  return {
    name: 'Fin',
    type: FinKind,
    constructors: [
      {
        name: 'fzero',
        // fzero : Π (n : Nat). Fin (succ n)
        type: mkPi(
          Nat,
          mkApp(Fin, mkApp(succ, mkVar(0))),
          'n'
        ),
      },
      {
        name: 'fsucc',
        // fsucc : Π (n : Nat). Fin n → Fin (succ n)
        // Π (n : Nat).     -- n at 0
        //   Π (_ : Fin n). -- n at 1
        //     Fin (succ n) -- n at 1
        type: mkPi(
          Nat,
          mkPi(
            mkApp(Fin, mkVar(0)), // Fin n (n at 0)
            mkApp(Fin, mkApp(succ, mkVar(1))), // Fin (succ n) (n at 1)
            '_'
          ),
          'n'
        ),
      },
    ],
  };
}

// ============================================================================
// Magma A - Type with Binary Operation
// ============================================================================

/**
 * Magma - A type equipped with a binary operation
 *
 * inductive Magma (A : Type) : Type where
 *   | mkMagma : (A → A → A) → Magma A
 *
 * A magma is the simplest algebraic structure - just a set with a
 * binary operation. No laws (associativity, identity, etc.) required.
 */
function makeMagma(): InductiveTypeDef {
  // Magma : Type → Type
  const MagmaKind = mkArrow(Type0, Type0);
  const Magma = mkInductiveRef('Magma', MagmaKind);

  return {
    name: 'Magma',
    type: MagmaKind,
    constructors: [
      {
        name: 'mkMagma',
        // mkMagma : Π (A : Type). (A → A → A) → Magma A
        // The binary operation type is: A → A → A
        // Π (A : Type).              -- A at 0
        //   Π (_ : A → A → A).       -- A at 1
        //     Magma A                -- A at 1
        type: mkPi(
          Type0,
          mkPi(
            mkArrow(mkVar(0), mkArrow(mkVar(0), mkVar(0))), // A → A → A
            mkApp(Magma, mkVar(1)), // Magma A (A at 1)
            'op'
          ),
          'A'
        ),
      },
    ],
  };
}

// ============================================================================
// Unit - Singleton Type
// ============================================================================

/**
 * Unit type (singleton)
 *
 * inductive Unit : Type where
 *   | tt : Unit
 */
function makeUnit(): InductiveTypeDef {
  const Unit = mkInductiveRef('Unit', Type0);

  return {
    name: 'Unit',
    type: Type0,
    constructors: [
      {
        name: 'tt',
        type: Unit,
      },
    ],
  };
}

// ============================================================================
// Sum A B - Disjoint Union / Either Type
// ============================================================================

/**
 * Sum type (disjoint union, Either)
 *
 * inductive Sum (A B : Type) : Type where
 *   | inl : A → Sum A B
 *   | inr : B → Sum A B
 */
function makeSum(): InductiveTypeDef {
  // Sum : Type → Type → Type
  const SumKind = mkArrow(Type0, mkArrow(Type0, Type0));
  const Sum = mkInductiveRef('Sum', SumKind);

  return {
    name: 'Sum',
    type: SumKind,
    constructors: [
      {
        name: 'inl',
        // inl : Π (A : Type). Π (B : Type). A → Sum A B
        // Π (A : Type).       -- A at 0
        //   Π (B : Type).     -- A at 1, B at 0
        //     Π (_ : A).      -- A at 2, B at 1
        //       Sum A B       -- A at 2, B at 1
        type: mkPi(
          Type0,
          mkPi(
            Type0,
            mkPi(
              mkVar(1), // A (at 1)
              mkApp(mkApp(Sum, mkVar(2)), mkVar(1)), // Sum A B
              '_'
            ),
            'B'
          ),
          'A'
        ),
      },
      {
        name: 'inr',
        // inr : Π (A : Type). Π (B : Type). B → Sum A B
        type: mkPi(
          Type0,
          mkPi(
            Type0,
            mkPi(
              mkVar(0), // B (at 0)
              mkApp(mkApp(Sum, mkVar(2)), mkVar(1)), // Sum A B
              '_'
            ),
            'B'
          ),
          'A'
        ),
      },
    ],
  };
}

// ============================================================================
// Prod A B - Product Type
// ============================================================================

/**
 * Product type (pairs)
 *
 * inductive Prod (A B : Type) : Type where
 *   | pair : A → B → Prod A B
 */
function makeProd(): InductiveTypeDef {
  // Prod : Type → Type → Type
  const ProdKind = mkArrow(Type0, mkArrow(Type0, Type0));
  const Prod = mkInductiveRef('Prod', ProdKind);

  return {
    name: 'Prod',
    type: ProdKind,
    constructors: [
      {
        name: 'pair',
        // pair : Π (A : Type). Π (B : Type). A → B → Prod A B
        // Π (A : Type).       -- A at 0
        //   Π (B : Type).     -- A at 1, B at 0
        //     Π (_ : A).      -- A at 2, B at 1
        //       Π (_ : B).    -- A at 3, B at 2
        //         Prod A B    -- A at 3, B at 2
        type: mkPi(
          Type0,
          mkPi(
            Type0,
            mkPi(
              mkVar(1), // A (at 1)
              mkPi(
                mkVar(1), // B (at 1, was at 0 before entering this Π)
                mkApp(mkApp(Prod, mkVar(3)), mkVar(2)), // Prod A B
                '_'
              ),
              '_'
            ),
            'B'
          ),
          'A'
        ),
      },
    ],
  };
}

// ============================================================================
// Exported Examples Object
// ============================================================================

/**
 * Collection of TT inductive type examples.
 *
 * Each type is a complete InductiveTypeDef that can be used as test data
 * or examples for the type system.
 */
export const TTExamples = {
  inductiveTypes: {
    /** Natural numbers: zero, succ */
    Nat: makeNat(),

    /** Booleans: true, false */
    Bool: makeBool(),

    /** Empty type (no constructors) */
    Void: makeVoid(),

    /** Unit type (singleton) */
    Unit: makeUnit(),

    /** Polymorphic list: nil, cons */
    List: makeList(),

    /** Length-indexed vector: vnil, vcons */
    Vec: makeVec(),

    /** Finite set (numbers less than n): fzero, fsucc */
    Fin: makeFin(),

    /** Magma: type with binary operation */
    Magma: makeMagma(),

    /** Sum type (disjoint union): inl, inr */
    Sum: makeSum(),

    /** Product type (pairs): pair */
    Prod: makeProd(),
  },
} as const;

// ============================================================================
// Type-level convenience exports
// ============================================================================

export type TTExamplesInductiveTypes = typeof TTExamples.inductiveTypes;
export type TTExampleTypeName = keyof TTExamplesInductiveTypes;

