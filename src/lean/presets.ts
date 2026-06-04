/**
 * Lean-native example programs for the editor preset picker.
 *
 * These replace the old TT/TTK presets (which used the now-superseded surface
 * syntax). Core-mode friendly: none require Mathlib. The Mathlib toggle unlocks
 * the richer examples that import it.
 */

export interface LeanPreset {
  name: string;
  /** If true, only meaningful with the Mathlib toggle on. */
  mathlib?: boolean;
  code: string;
}

const BASICS = `-- Basics: definitions, #check, and a simple proof.

def double (n : Nat) : Nat := n + n

#check double
#eval double 21

theorem double_eq_two_mul (n : Nat) : double n = 2 * n := by
  unfold double
  omega
`;

const INDUCTION = `-- Induction over Nat.

theorem add_zero_ex (n : Nat) : n + 0 = n := by
  rfl

theorem add_comm_ex (a b : Nat) : a + b = b + a := by
  induction a with
  | zero => simp
  | succ k ih => rw [Nat.succ_add, ih, Nat.add_succ]
`;

const INDUCTIVE = `-- An inductive type and a function over it.

inductive Color where
  | red
  | green
  | blue

def next : Color → Color
  | .red => .green
  | .green => .blue
  | .blue => .red

theorem next_thrice (c : Color) : next (next (next c)) = c := by
  cases c <;> rfl
`;

const LISTS = `-- Lists and a length lemma.

def myLength {α : Type} : List α → Nat
  | [] => 0
  | _ :: xs => myLength xs + 1

theorem length_append {α : Type} (xs ys : List α) :
    myLength (xs ++ ys) = myLength xs + myLength ys := by
  induction xs with
  | nil => simp [myLength]
  | cons x xs ih => simp [myLength, ih, Nat.succ_add]
`;

// Ported (verbatim-as-possible) from the TT/TTK "Nat Math" preset: a from-scratch
// MyNat with its own Equal, plus, mul, and the semiring laws by structural
// recursion. Core Lean, no Mathlib. Verified to compile clean.
const NAT_MATH = `-- Nat Math (from scratch): semiring laws by structural recursion.
-- A hand-rolled MyNat with its own Equal, plus, mul, and the semiring slate
-- (commutativity, associativity, distributivity) proved by pattern matching.

inductive MyNat where
  | zero : MyNat
  | succ : MyNat → MyNat

inductive Equal {A : Type} : A → A → Type where
  | refl : {a : A} → Equal a a

def plus : MyNat → MyNat → MyNat
  | .zero,   m => m
  | .succ n, m => .succ (plus n m)

def mul : MyNat → MyNat → MyNat
  | .zero,   _ => .zero
  | .succ n, m => plus m (mul n m)

def one : MyNat := .succ .zero

-- Helpers
def congSucc {n m : MyNat} : Equal n m → Equal (MyNat.succ n) (MyNat.succ m)
  | .refl => .refl

def succInj {n m : MyNat} : Equal (MyNat.succ n) (.succ m) → Equal n m
  | .refl => .refl

def sym {A : Type} {x y : A} : Equal x y → Equal y x
  | .refl => .refl

def trans {A : Type} {x y z : A} : Equal x y → Equal y z → Equal x z
  | .refl, .refl => .refl

-- Addition properties
def plusZeroLeft (n : MyNat) : Equal (plus .zero n) n := .refl

def plusZeroRight : (n : MyNat) → Equal (plus n .zero) n
  | .zero   => .refl
  | .succ n => congSucc (plusZeroRight n)

def plusSuccRight : (n m : MyNat) → Equal (plus n (.succ m)) (.succ (plus n m))
  | .zero,   _ => .refl
  | .succ n, m => congSucc (plusSuccRight n m)

def plusAssoc : (n m p : MyNat) → Equal (plus (plus n m) p) (plus n (plus m p))
  | .zero,   _, _ => .refl
  | .succ n, m, p => congSucc (plusAssoc n m p)

def plusComm : (n m : MyNat) → Equal (plus n m) (plus m n)
  | .zero,   m => sym (plusZeroRight m)
  | .succ n, m => trans (congSucc (plusComm n m)) (sym (plusSuccRight m n))

def congPlusLeft {n m : MyNat} (p : MyNat) : Equal n m → Equal (plus n p) (plus m p)
  | .refl => .refl

def congPlusRight {n m : MyNat} : (p : MyNat) → Equal n m → Equal (plus p n) (plus p m)
  | .zero,   eq => eq
  | .succ p, eq => congSucc (congPlusRight p eq)

-- Multiplication properties
def mulZeroLeft (n : MyNat) : Equal (mul .zero n) .zero := .refl

def mulZeroRight : (n : MyNat) → Equal (mul n .zero) .zero
  | .zero   => .refl
  | .succ n => mulZeroRight n

def mulSuccRight : (n m : MyNat) → Equal (mul n (.succ m)) (plus n (mul n m))
  | .zero,   _ => .refl
  | .succ n, m =>
      congSucc
        (trans (congPlusRight m (mulSuccRight n m))
          (trans (sym (plusAssoc m n (mul n m)))
            (trans (congPlusLeft (mul n m) (plusComm m n))
              (plusAssoc n m (mul n m)))))

def mulComm : (n m : MyNat) → Equal (mul n m) (mul m n)
  | .zero,   m => sym (mulZeroRight m)
  | .succ n, m => trans (congPlusRight m (mulComm n m)) (sym (mulSuccRight m n))

-- Distributivity
def mulDistribRight : (n m p : MyNat) → Equal (mul (plus n m) p) (plus (mul n p) (mul m p))
  | .zero,   _, _ => .refl
  | .succ n, m, p =>
      trans (congPlusRight p (mulDistribRight n m p))
        (sym (plusAssoc p (mul n p) (mul m p)))

#check plusComm
#check mulComm
#check mulDistribRight
`;

// Ported from the TT "Nat Math (Tactics)" preset. A tactics showcase over the
// builtin Nat (so real Lean tactics — simp, omega, induction…with, rw, exact —
// shine), keeping the original theorem names + a custom Leq inductive. Verified.
const NAT_MATH_TACTICS = `-- Nat Math (Tactics): arithmetic over the builtin Nat, proved with real Lean tactics.

theorem plusZeroLeft : (n : Nat) → 0 + n = n := by
  intro n; simp

theorem plusZeroRight : (n : Nat) → n + 0 = n := by
  intro n; simp

theorem plusSuccRight : (n m : Nat) → n + (m + 1) = (n + m) + 1 := by
  intro n m; omega

theorem plusAssoc : (n m p : Nat) → (n + m) + p = n + (m + p) := by
  intro n m p; omega

theorem plusComm : (n m : Nat) → n + m = m + n := by
  intro n m; omega

theorem plusLeftComm : (m n p : Nat) → m + (n + p) = n + (m + p) := by
  intro m n p; omega

theorem mulZeroLeft : (n : Nat) → 0 * n = 0 := by
  intro n; simp

theorem mulZeroRight : (n : Nat) → n * 0 = 0 := by
  intro n; simp

theorem mulOneLeft : (n : Nat) → 1 * n = n := by
  intro n; simp

theorem mulOneRight : (n : Nat) → n * 1 = n := by
  intro n; simp

theorem mulComm : (n m : Nat) → n * m = m * n := by
  intro n m; exact Nat.mul_comm n m

theorem mulDistribRight : (n m p : Nat) → (n + m) * p = n * p + m * p := by
  intro n m p; exact Nat.add_mul n m p

theorem mulAssoc : (n m p : Nat) → (n * m) * p = n * (m * p) := by
  intro n m p; exact Nat.mul_assoc n m p

theorem mulDistribLeft : (n m p : Nat) → n * (m + p) = n * m + n * p := by
  intro n m p; exact Nat.mul_add n m p

-- Triangle Sum: 2 * sum(1..n) = n * (n + 1)
def sum : Nat → Nat
  | 0     => 0
  | n + 1 => (n + 1) + sum n

theorem doubleSum : (n : Nat) → sum n + sum n = n * (n + 1) := by
  intro n
  induction n with
  | zero => rfl
  | succ k ih =>
    show ((k + 1) + sum k) + ((k + 1) + sum k) = (k + 1) * ((k + 1) + 1)
    have e : (k + 1) * ((k + 1) + 1) = k * (k + 1) + (k + 1) + (k + 1) := by
      rw [Nat.mul_add, Nat.succ_mul, Nat.mul_one]
    rw [e, ← ih]; omega

-- Leq: ordering on Nat (custom inductive, mirrors the original)
inductive Leq : Nat → Nat → Type where
  | LeqZero : {n : Nat} → Leq 0 n
  | LeqSucc : {n m : Nat} → Leq n m → Leq (n + 1) (m + 1)

def leqRefl : (n : Nat) → Leq n n := by
  intro n
  induction n with
  | zero => exact .LeqZero
  | succ k ih => exact .LeqSucc ih

def leqTrans : {a b c : Nat} → Leq a b → Leq b c → Leq a c := by
  intro a b c hab hbc
  cases hab with
  | LeqZero => exact .LeqZero
  | LeqSucc p =>
    cases hbc with
    | LeqSucc q => exact .LeqSucc (leqTrans p q)

theorem leqAntisym : {a b : Nat} → Leq a b → Leq b a → a = b := by
  intro a b hab hba
  cases hab with
  | LeqZero =>
    cases hba with
    | LeqZero => rfl
  | LeqSucc p =>
    cases hba with
    | LeqSucc q =>
      have := leqAntisym p q
      omega
`;

// Ported from the TT "Peano Arithmetic" preset: a PeanoNat *record* with its own
// induction eliminator (ind/indZero/indSucc), and plus/comm/assoc derived purely
// through the eliminator — universe-polymorphic Equal, no Mathlib. Verified.
const PEANO = `-- Peano (record): a carrier with zero/succ and an induction eliminator,
-- with addition + its laws derived entirely through the eliminator.

universe u v

inductive Equal {A : Type u} : A → A → Type u where
  | refl : {a : A} → Equal a a

def eqSym {A : Type u} {x y : A} : Equal x y → Equal y x
  | .refl => .refl

def eqTrans {A : Type u} {x y z : A} : Equal x y → Equal y z → Equal x z
  | .refl, .refl => .refl

def eqCong {A : Type u} {B : Type v} (f : A → B) {x y : A} : Equal x y → Equal (f x) (f y)
  | .refl => .refl

inductive MyVoid : Type where

def MyNot (A : Type u) : Type u := A → MyVoid

structure PeanoNat where
  carrier : Type
  zero : carrier
  succ : carrier → carrier
  zeroNeqSucc : {n : carrier} → MyNot (Equal zero (succ n))
  succInj : {m n : carrier} → Equal (succ m) (succ n) → Equal m n
  ind : {P : carrier → Type} → P zero → ({n : carrier} → P n → P (succ n)) → (n : carrier) → P n
  indZero : {P : carrier → Type} → (base : P zero) → (step : {n : carrier} → P n → P (succ n)) →
    Equal (ind base step zero) base
  indSucc : {P : carrier → Type} → (base : P zero) → (step : {n : carrier} → P n → P (succ n)) →
    (n : carrier) → Equal (ind base step (succ n)) (step (ind base step n))

@[reducible] def plus (N : PeanoNat) (n m : N.carrier) : N.carrier :=
  N.ind m (fun ih => N.succ ih) n

def plusZeroEq (N : PeanoNat) (m : N.carrier) : Equal (plus N N.zero m) m :=
  N.indZero m (fun ih => N.succ ih)

def plusSuccEq (N : PeanoNat) (k m : N.carrier) :
    Equal (plus N (N.succ k) m) (N.succ (plus N k m)) :=
  N.indSucc m (fun ih => N.succ ih) k

def plusZeroRight (N : PeanoNat) (n : N.carrier) : Equal (plus N n N.zero) n :=
  N.ind (P := fun k => Equal (plus N k N.zero) k)
    (plusZeroEq N N.zero)
    (fun {k} ih => eqTrans (plusSuccEq N k N.zero) (eqCong N.succ ih))
    n

def plusSuccRight (N : PeanoNat) (n m : N.carrier) :
    Equal (plus N n (N.succ m)) (N.succ (plus N n m)) :=
  N.ind (P := fun k => Equal (plus N k (N.succ m)) (N.succ (plus N k m)))
    (eqTrans (plusZeroEq N (N.succ m)) (eqSym (eqCong N.succ (plusZeroEq N m))))
    (fun {k} ih =>
      eqTrans (eqTrans (plusSuccEq N k (N.succ m)) (eqCong N.succ ih))
            (eqSym (eqCong N.succ (plusSuccEq N k m))))
    n

def plusComm (N : PeanoNat) (n m : N.carrier) : Equal (plus N n m) (plus N m n) :=
  N.ind (P := fun k => Equal (plus N k m) (plus N m k))
    (eqTrans (plusZeroEq N m) (eqSym (plusZeroRight N m)))
    (fun {k} ih =>
      eqTrans (eqTrans (plusSuccEq N k m) (eqCong N.succ ih)) (eqSym (plusSuccRight N m k)))
    n

def plusAssoc (N : PeanoNat) (a b c : N.carrier) :
    Equal (plus N (plus N a b) c) (plus N a (plus N b c)) :=
  N.ind (P := fun k => Equal (plus N (plus N k b) c) (plus N k (plus N b c)))
    (eqTrans (eqCong (fun x => plus N x c) (plusZeroEq N b)) (eqSym (plusZeroEq N (plus N b c))))
    (fun {k} ih =>
      eqTrans
        (eqTrans
          (eqTrans (eqCong (fun x => plus N x c) (plusSuccEq N k b))
                   (plusSuccEq N (plus N k b) c))
          (eqCong N.succ ih))
        (eqSym (plusSuccEq N k (plus N b c))))
    a
`;

const MATHLIB = `import Mathlib

-- Requires the Mathlib toggle (first build is slow).
example (a b : ℝ) : a + b = b + a := by ring

example (n : ℕ) : ∑ i ∈ Finset.range n, (i : ℚ) = n * (n - 1) / 2 := by
  induction n with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih]; push_cast; ring
`;

export const LEAN_PRESETS: LeanPreset[] = [
  { name: 'Basics', code: BASICS },
  { name: 'Induction', code: INDUCTION },
  { name: 'Inductive type', code: INDUCTIVE },
  { name: 'Lists', code: LISTS },
  { name: 'Nat Math (from scratch)', code: NAT_MATH },
  { name: 'Nat Math (tactics)', code: NAT_MATH_TACTICS },
  { name: 'Peano (record)', code: PEANO },
  { name: 'Mathlib (∑, ring)', code: MATHLIB, mathlib: true },
];

export const DEFAULT_LEAN_SOURCE = BASICS;
