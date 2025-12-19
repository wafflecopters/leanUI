/**
 * TT Examples - Inductive Type and Record Definitions
 *
 * This file contains example type definitions built using the
 * TT (Typed Terms) data structures from tt-core.ts.
 *
 * Inductive types are defined by:
 * - name: The name of the type (e.g., "Nat", "List")
 * - type: The kind/sort of the type (e.g., Type_0, Type_0 → Type_0)
 * - constructors: Array of constructors, each with name and type
 *
 * Record types are defined by:
 * - name: The name of the record (e.g., "Magma", "Semigroup")
 * - type: The kind/sort of the type
 * - fields: Array of fields, each with name and type
 */

import {
  TTerm,
  mkType,
  mkPi,
  mkConst,
  mkApp,
  mkVar,
  RecordDef,
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
// Magma A - Type with Binary Operation (Record)
// ============================================================================

/**
 * Magma - A type equipped with a binary operation
 *
 * structure Magma (A : Type) where
 *   op : A → A → A
 *
 * A magma is the simplest algebraic structure - just a set with a
 * binary operation. No laws (associativity, identity, etc.) required.
 */
function makeMagmaRecord(): RecordDef {
  // Magma : Type → Type
  const MagmaKind = mkArrow(Type0, Type0);

  return {
    name: 'Magma',
    type: MagmaKind,
    fields: [
      {
        name: 'op',
        // op : Π (A : Type). A → A → A
        // De Bruijn indices shift as we go under each arrow binder:
        // - First arg domain: A at index 0
        // - Second arg domain: A at index 1 (under one _ binder)
        // - Return type: A at index 2 (under two _ binders)
        type: mkPi(
          Type0,
          mkPi(
            mkVar(0),
            mkPi(mkVar(1), mkVar(2), '_'),
            '_'
          ),
          'A'
        ),
      },
    ],
  };
}

// ============================================================================
// Semigroup A - Magma with Associativity Proof (Record)
// ============================================================================

/**
 * Semigroup - A magma where the operation is associative
 *
 * structure Semigroup (A : Type) where
 *   op : A → A → A
 *   assoc : ∀ x y z, op (op x y) z = op x (op y z)
 */
function makeSemigroupRecord(): RecordDef {
  const SemigroupKind = mkArrow(Type0, Type0);
  const Prop = mkType(0);

  return {
    name: 'Semigroup',
    type: SemigroupKind,
    fields: [
      {
        name: 'op',
        // op : Π (A : Type). A → A → A
        type: mkPi(
          Type0,
          mkPi(
            mkVar(0),
            mkPi(mkVar(1), mkVar(2), '_'),
            '_'
          ),
          'A'
        ),
      },
      {
        name: 'assoc',
        // assoc : Π (A : Type). Prop
        type: mkPi(Type0, Prop, 'A'),
      },
    ],
  };
}

// ============================================================================
// Monoid A - Semigroup with Identity (Record)
// ============================================================================

/**
 * Monoid - A semigroup with an identity element
 *
 * structure Monoid (A : Type) where
 *   op : A → A → A
 *   e : A
 *   assoc : ∀ x y z, op (op x y) z = op x (op y z)
 *   left_id : ∀ x, op e x = x
 *   right_id : ∀ x, op x e = x
 */
function makeMonoidRecord(): RecordDef {
  const MonoidKind = mkArrow(Type0, Type0);
  const Prop = mkType(0);

  return {
    name: 'Monoid',
    type: MonoidKind,
    fields: [
      {
        name: 'op',
        // op : Π (A : Type). A → A → A
        type: mkPi(
          Type0,
          mkPi(
            mkVar(0),
            mkPi(mkVar(1), mkVar(2), '_'),
            '_'
          ),
          'A'
        ),
      },
      {
        name: 'e',
        // e : Π (A : Type). A
        type: mkPi(Type0, mkVar(0), 'A'),
      },
      {
        name: 'assoc',
        // assoc : Π (A : Type). Prop
        type: mkPi(Type0, Prop, 'A'),
      },
      {
        name: 'left_id',
        // left_id : Π (A : Type). Prop
        type: mkPi(Type0, Prop, 'A'),
      },
      {
        name: 'right_id',
        // right_id : Π (A : Type). Prop
        type: mkPi(Type0, Prop, 'A'),
      },
    ],
  };
}

// ============================================================================
// Point - Simple 2D Point (Record)
// ============================================================================

/**
 * Point - A simple 2D point with x and y coordinates
 *
 * structure Point where
 *   x : Nat
 *   y : Nat
 */
function makePointRecord(): RecordDef {
  const Nat = mkInductiveRef('Nat', Type0);

  return {
    name: 'Point',
    type: Type0,
    fields: [
      {
        name: 'x',
        type: Nat,
      },
      {
        name: 'y',
        type: Nat,
      },
    ],
  };
}

// ============================================================================
// Prod A B - Product Type (Record)
// ============================================================================

/**
 * Product type (pairs) as a record
 *
 * structure Prod (A B : Type) where
 *   fst : A
 *   snd : B
 */
function makeProdRecord(): RecordDef {
  // Prod : Type → Type → Type
  const ProdKind = mkArrow(Type0, mkArrow(Type0, Type0));

  return {
    name: 'Prod',
    type: ProdKind,
    fields: [
      {
        name: 'fst',
        // fst : Π (A : Type). Π (B : Type). A
        // A is at index 1 inside the nested Pi
        type: mkPi(
          Type0,
          mkPi(Type0, mkVar(1), 'B'),
          'A'
        ),
      },
      {
        name: 'snd',
        // snd : Π (A : Type). Π (B : Type). B
        // B is at index 0 inside the nested Pi
        type: mkPi(
          Type0,
          mkPi(Type0, mkVar(0), 'B'),
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
 * Collection of TT type examples.
 *
 * Each type is a complete definition that can be used as test data
 * or examples for the type system.
 */
export const TTExamples = {
  /** Inductive types with constructors */
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

    /** Sum type (disjoint union): inl, inr */
    Sum: makeSum(),
  },

  /** Record types (structures) with named fields */
  recordTypes: {
    /** Magma: type with binary operation */
    Magma: makeMagmaRecord(),

    /** Semigroup: magma with associativity */
    Semigroup: makeSemigroupRecord(),

    /** Monoid: semigroup with identity */
    Monoid: makeMonoidRecord(),

    /** Point: simple 2D point */
    Point: makePointRecord(),

    /** Product type (pairs): fst, snd */
    Prod: makeProdRecord(),
  },
} as const;

// ============================================================================
// Type-level convenience exports
// ============================================================================

export type TTExamplesInductiveTypes = typeof TTExamples.inductiveTypes;
export type TTExampleInductiveTypeName = keyof TTExamplesInductiveTypes;

export type TTExamplesRecordTypes = typeof TTExamples.recordTypes;
export type TTExampleRecordTypeName = keyof TTExamplesRecordTypes;

// Legacy alias for backward compatibility
export type TTExampleTypeName = TTExampleInductiveTypeName;
