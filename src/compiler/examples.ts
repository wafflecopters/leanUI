/**
 * TT Examples - Inductive Type and Record Definitions
 *
 * This file contains example type definitions built using the
 * TT (Typed Terms) data structures from tt-core.ts.
 *
 * Inductive types are defined by:
 * - name: The name of the type (e.g., "Nat", "List")
 * - type: The kind/sort of the type (e.g., Type_0, Type_0 -> Type_0)
 * - constructors: Array of constructors, each with name and type
 *
 * Record types are defined by:
 * - name: The name of the record (e.g., "Magma", "Semigroup")
 * - type: The kind/sort of the type
 * - fields: Array of fields, each with name and type
 */

import {
  TTerm,
  mkTypeTT,
  mkPiTT,
  mkConstTT,
  mkAppTT,
  mkVarTT,
  RecordDef,
} from './surface';

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
const Type0 = mkTypeTT(0);

/**
 * Create a constant reference to an inductive type.
 * The type parameter should be the kind of the inductive type.
 */
function mkInductiveRef(name: string, kind: TTerm): TTerm {
  return mkConstTT(name, kind);
}

/**
 * Create a non-dependent function type: A -> B
 * (This is just Pi where the body doesn't use the bound variable)
 */
function mkArrow(domain: TTerm, codomain: TTerm): TTerm {
  return mkPiTT(domain, codomain, '_');
}

// ============================================================================
// Nat - Natural Numbers
// ============================================================================

/**
 * Natural numbers
 *
 * inductive Nat : Type where
 *   | zero : Nat
 *   | succ : Nat -> Nat
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
        // succ : Nat -> Nat
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
 *   | cons : A -> List A -> List A
 *
 * Note: We represent this with explicit type parameter quantification:
 *   nil : (A : Type) -> List A
 *   cons : (A : Type) -> A -> List A -> List A
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
        // Inside the Pi, A is at index 0
        type: mkPiTT(
          Type0,
          mkAppTT(List, mkVarTT(0)),
          'A'
        ),
      },
      {
        name: 'cons',
        // cons : (A : Type) -> A -> List A -> List A
        // Building from outside in:
        // (A : Type) ->       -- A at index 0 in next level
        //   (_ : A) ->        -- A at index 1, _ at index 0 in next level
        //     (_ : List A) -> -- A at index 2 in next level
        //       List A        -- A at index 2
        type: mkPiTT(
          Type0,
          mkPiTT(
            mkVarTT(0), // A (at index 0)
            mkPiTT(
              mkAppTT(List, mkVarTT(1)), // List A (A at index 1)
              mkAppTT(List, mkVarTT(2)), // List A (A at index 2)
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
 * inductive Vec (A : Type) : Nat -> Type where
 *   | vnil : Vec A 0
 *   | vcons : (n : Nat) -> A -> Vec A n -> Vec A (succ n)
 *
 * Note: Vec is an indexed family - the constructor return types differ in the index.
 */
function makeVec(): InductiveTypeDef {
  const Nat = mkInductiveRef('Nat', Type0);
  const succ = mkConstTT('succ', mkArrow(Nat, Nat));

  // Vec : Type -> Nat -> Type
  const VecKind = mkPiTT(Type0, mkArrow(Nat, Type0), 'A');
  const Vec = mkInductiveRef('Vec', VecKind);

  const zero = mkConstTT('zero', Nat);

  return {
    name: 'Vec',
    type: VecKind,
    constructors: [
      {
        name: 'vnil',
        // vnil : (A : Type) -> Vec A 0
        type: mkPiTT(
          Type0,
          mkAppTT(mkAppTT(Vec, mkVarTT(0)), zero),
          'A'
        ),
      },
      {
        name: 'vcons',
        // vcons : (A : Type) -> (n : Nat) -> A -> Vec A n -> Vec A (succ n)
        // Levels:
        // (A : Type) ->           -- A at 0
        //   (n : Nat) ->          -- A at 1, n at 0
        //     (_ : A) ->          -- A at 2, n at 1, _ at 0
        //       (_ : Vec A n) ->  -- A at 3, n at 2
        //         Vec A (succ n)  -- A at 3, n at 2
        type: mkPiTT(
          Type0,
          mkPiTT(
            Nat,
            mkPiTT(
              mkVarTT(1), // A (at index 1)
              mkPiTT(
                mkAppTT(mkAppTT(Vec, mkVarTT(2)), mkVarTT(1)), // Vec A n (A at 2, n at 1)
                mkAppTT(mkAppTT(Vec, mkVarTT(3)), mkAppTT(succ, mkVarTT(2))), // Vec A (succ n)
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
 * inductive Fin : Nat -> Type where
 *   | fzero : (n : Nat) -> Fin (succ n)
 *   | fsucc : (n : Nat) -> Fin n -> Fin (succ n)
 */
function makeFin(): InductiveTypeDef {
  const Nat = mkInductiveRef('Nat', Type0);
  const succ = mkConstTT('succ', mkArrow(Nat, Nat));

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
        type: mkPiTT(
          Nat,
          mkAppTT(Fin, mkAppTT(succ, mkVarTT(0))),
          'n'
        ),
      },
      {
        name: 'fsucc',
        // fsucc : (n : Nat) -> Fin n -> Fin (succ n)
        // (n : Nat) ->     -- n at 0
        //   (_ : Fin n) -> -- n at 1
        //     Fin (succ n) -- n at 1
        type: mkPiTT(
          Nat,
          mkPiTT(
            mkAppTT(Fin, mkVarTT(0)), // Fin n (n at 0)
            mkAppTT(Fin, mkAppTT(succ, mkVarTT(1))), // Fin (succ n) (n at 1)
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
 *   | inl : A -> Sum A B
 *   | inr : B -> Sum A B
 */
function makeSum(): InductiveTypeDef {
  // Sum : Type -> Type -> Type
  const SumKind = mkArrow(Type0, mkArrow(Type0, Type0));
  const Sum = mkInductiveRef('Sum', SumKind);

  return {
    name: 'Sum',
    type: SumKind,
    constructors: [
      {
        name: 'inl',
        // inl : (A : Type) -> (B : Type) -> A -> Sum A B
        // (A : Type) ->       -- A at 0
        //   (B : Type) ->     -- A at 1, B at 0
        //     (_ : A) ->      -- A at 2, B at 1
        //       Sum A B       -- A at 2, B at 1
        type: mkPiTT(
          Type0,
          mkPiTT(
            Type0,
            mkPiTT(
              mkVarTT(1), // A (at 1)
              mkAppTT(mkAppTT(Sum, mkVarTT(2)), mkVarTT(1)), // Sum A B
              '_'
            ),
            'B'
          ),
          'A'
        ),
      },
      {
        name: 'inr',
        // inr : (A : Type) -> (B : Type) -> B -> Sum A B
        type: mkPiTT(
          Type0,
          mkPiTT(
            Type0,
            mkPiTT(
              mkVarTT(0), // B (at 0)
              mkAppTT(mkAppTT(Sum, mkVarTT(2)), mkVarTT(1)), // Sum A B
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
 *   op : A -> A -> A
 *
 * A magma is the simplest algebraic structure - just a set with a
 * binary operation. No laws (associativity, identity, etc.) required.
 */
function makeMagmaRecord(): RecordDef {
  // Magma : Type -> Type
  const MagmaKind = mkArrow(Type0, Type0);

  // In the field context, A is at De Bruijn index 0
  // op : A -> A -> A = (_ : A) -> (_ : A) -> A
  // Under first binder: A is at index 1
  // Under second binder: A is at index 2
  const opType = mkPiTT(
    mkVarTT(0),  // First arg: A (at index 0 in param context)
    mkPiTT(
      mkVarTT(1),  // Second arg: A (shifted to index 1)
      mkVarTT(2),  // Result: A (shifted to index 2)
      '_'
    ),
    '_'
  );

  return {
    name: 'Magma',
    type: MagmaKind,
    params: [
      { name: 'A', type: Type0 }
    ],
    fields: [
      { name: 'op', type: opType },
    ],
  };
}

// ============================================================================
// Semigroup A - Magma with Associativity Proof (Record)
// ============================================================================

/**
 * Semigroup - A magma where the operation is associative
 *
 * structure Semigroup (A : Type) extends Magma A where
 *   assoc : ∀ a b c, op a (op b c) = op (op a b) c
 *
 * Note: Semigroup extends Magma, so it inherits the `op` field.
 * The `op` field will be inlined during elaboration.
 */
function makeSemigroupRecord(): RecordDef {
  const SemigroupKind = mkArrow(Type0, Type0);
  const Prop = mkTypeTT(0);

  // In field context: A is at index 0 (from params)
  //
  // op is a Const that takes A and two values: op : A -> A -> A
  // When we use op in a context, we don't need to pass A explicitly
  // since it's in scope from params. But for now, op is defined as
  // taking A -> A -> A in the Magma field context.
  //
  // Actually, since op is inherited from Magma and Magma has params,
  // the inherited op field type is: A -> A -> A (not (A:Type) -> A -> A -> A)
  // So op is just: (_ : Var(0)) -> (_ : Var(1)) -> Var(2) in param context

  // For assoc, we need to reference op as a constant
  // op as a projection has type: Magma A -> (A -> A -> A)
  // But in this context, op is a field so we treat it as a constant
  // The type of op (as used in the field) is: A -> A -> A
  const opFieldType = mkPiTT(mkVarTT(0), mkPiTT(mkVarTT(1), mkVarTT(2), '_'), '_');
  const op = mkConstTT('op', opFieldType);

  // Eq : (A : Type) -> A -> A -> Type_0
  // In the body of assoc, we apply Eq to (A, lhs, rhs) - 3 args
  const EqType = mkPiTT(Type0, mkPiTT(mkVarTT(0), mkPiTT(mkVarTT(1), Prop, '_'), '_'), 'A');
  const Eq = mkConstTT('Eq', EqType);

  // Build assoc : (a b c : A) -> Eq A (op a (op b c)) (op (op a b) c)
  //
  // In param context: A is at index 0
  // After binding a: a=0, A=1
  // After binding b: b=0, a=1, A=2
  // After binding c: c=0, b=1, a=2, A=3

  // In the innermost context (under a, b, c binders):
  // c = Var(0), b = Var(1), a = Var(2), A = Var(3)
  //
  // op b c = App(App(op, Var(1)), Var(0))
  const op_b_c = mkAppTT(mkAppTT(op, mkVarTT(1)), mkVarTT(0));
  // op a (op b c)
  const lhs = mkAppTT(mkAppTT(op, mkVarTT(2)), op_b_c);
  // op a b
  const op_a_b = mkAppTT(mkAppTT(op, mkVarTT(2)), mkVarTT(1));
  // op (op a b) c
  const rhs = mkAppTT(mkAppTT(op, op_a_b), mkVarTT(0));
  // Eq A lhs rhs (A is at index 3)
  const eqBody = mkAppTT(mkAppTT(mkAppTT(Eq, mkVarTT(3)), lhs), rhs);

  // Build the full type: (a : A) -> (b : A) -> (c : A) -> Eq ...
  // In param context, A is at index 0
  // Binding a: domain = Var(0), then a is at 0, A is at 1
  // Binding b: domain = Var(1), then b is at 0, a is at 1, A is at 2
  // Binding c: domain = Var(2), then c is at 0, b is at 1, a is at 2, A is at 3
  const assocType = mkPiTT(
    mkVarTT(0),     // a : A (A at index 0)
    mkPiTT(
      mkVarTT(1),   // b : A (A at index 1)
      mkPiTT(
        mkVarTT(2), // c : A (A at index 2)
        eqBody,   // body with c=0, b=1, a=2, A=3
        'c'
      ),
      'b'
    ),
    'a'
  );

  return {
    name: 'Semigroup',
    type: SemigroupKind,
    params: [
      { name: 'A', type: Type0 }
    ],
    extends: ['Magma'],  // Inherits `op` field from Magma
    fields: [
      { name: 'assoc', type: assocType },
    ],
  };
}

// ============================================================================
// Monoid A - Semigroup with Identity (Record)
// ============================================================================

/**
 * Monoid - A semigroup with an identity element
 *
 * structure Monoid (A : Type) extends Semigroup A where
 *   e : A
 *   left_id : ∀ x, op e x = x
 *   right_id : ∀ x, op x e = x
 *
 * Note: Monoid extends Semigroup, which extends Magma.
 * It inherits `op` from Magma and `assoc` from Semigroup.
 */
function makeMonoidRecord(): RecordDef {
  const MonoidKind = mkArrow(Type0, Type0);
  const Prop = mkTypeTT(0);

  // In param context: A is at index 0
  //
  // op : A -> A -> A (field type, not (A:Type) -> ...)
  const opFieldType = mkPiTT(mkVarTT(0), mkPiTT(mkVarTT(1), mkVarTT(2), '_'), '_');
  const op = mkConstTT('op', opFieldType);

  // e : A (field type in param context where A is at index 0)
  const eFieldType = mkVarTT(0);
  const e = mkConstTT('e', eFieldType);

  // Eq : (A : Type) -> A -> A -> Type_0
  const EqType = mkPiTT(Type0, mkPiTT(mkVarTT(0), mkPiTT(mkVarTT(1), Prop, '_'), '_'), 'A');
  const Eq = mkConstTT('Eq', EqType);

  // Build left_id : (x : A) -> Eq A (op e x) x
  // In param context: A is at index 0
  // After binding x: x=0, A=1
  //
  // op e x = App(App(op, e), x)
  const op_e_x = mkAppTT(mkAppTT(op, e), mkVarTT(0));
  // Eq A (op e x) x  (A is at index 1)
  const leftIdBody = mkAppTT(mkAppTT(mkAppTT(Eq, mkVarTT(1)), op_e_x), mkVarTT(0));
  const leftIdType = mkPiTT(
    mkVarTT(0),     // x : A (A at index 0)
    leftIdBody,   // body with x=0, A=1
    'x'
  );

  // Build right_id : (x : A) -> Eq A (op x e) x
  // After binding x: x=0, A=1
  // op x e = App(App(op, x), e)
  const op_x_e = mkAppTT(mkAppTT(op, mkVarTT(0)), e);
  // Eq A (op x e) x  (A is at index 1)
  const rightIdBody = mkAppTT(mkAppTT(mkAppTT(Eq, mkVarTT(1)), op_x_e), mkVarTT(0));
  const rightIdType = mkPiTT(
    mkVarTT(0),     // x : A (A at index 0)
    rightIdBody,  // body with x=0, A=1
    'x'
  );

  return {
    name: 'Monoid',
    type: MonoidKind,
    params: [
      { name: 'A', type: Type0 }
    ],
    extends: ['Semigroup'],  // Inherits `op` and `assoc` from Semigroup (which extends Magma)
    fields: [
      { name: 'e', type: eFieldType },
      { name: 'left_id', type: leftIdType },
      { name: 'right_id', type: rightIdType },
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
    params: [],  // No parameters
    fields: [
      { name: 'x', type: Nat },
      { name: 'y', type: Nat },
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
  // Prod : Type -> Type -> Type
  const ProdKind = mkArrow(Type0, mkArrow(Type0, Type0));

  // Params: A at index 0, B at index 1
  // In field context: A = Var(0), B = Var(1)
  return {
    name: 'Prod',
    type: ProdKind,
    params: [
      { name: 'A', type: Type0 },
      { name: 'B', type: Type0 },
    ],
    fields: [
      { name: 'fst', type: mkVarTT(0) },  // A
      { name: 'snd', type: mkVarTT(1) },  // B
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
