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
const NAT_MATH = `-- Nat Math (from scratch): the full TT development ported to core Lean.
-- A hand-rolled MyNat with its own Equal, plus, mul, one; the 12 semiring laws
-- + a Semiring record/instance; Leq ordering; subtraction lemmas; summation;
-- and the triangle-sum statement (left as sorry, as in the original).

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

-- Equality helpers (named to avoid clashing with Lean's Trans/_root_.trans)
def congSucc {n m : MyNat} : Equal n m → Equal (MyNat.succ n) (MyNat.succ m)
  | .refl => .refl

def succInj {n m : MyNat} : Equal (MyNat.succ n) (.succ m) → Equal n m
  | .refl => .refl

def eqSym {A : Type} {x y : A} : Equal x y → Equal y x
  | .refl => .refl

def eqTrans {A : Type} {x y z : A} : Equal x y → Equal y z → Equal x z
  | .refl, .refl => .refl

def eqCong {A B : Type} {x y : A} (f : A → B) : Equal x y → Equal (f x) (f y)
  | .refl => .refl

def replace {A : Type} {x y : A} (P : A → Type) : Equal x y → P x → P y
  | .refl, px => px

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
  | .zero,   m => eqSym (plusZeroRight m)
  | .succ n, m => eqTrans (congSucc (plusComm n m)) (eqSym (plusSuccRight m n))

def congPlusLeft {n m : MyNat} (p : MyNat) : Equal n m → Equal (plus n p) (plus m p)
  | .refl => .refl

def congPlusRight {n m : MyNat} : (p : MyNat) → Equal n m → Equal (plus p n) (plus p m)
  | .zero,   eq => eq
  | .succ p, eq => congSucc (congPlusRight p eq)

def plusLeftComm (m n p : MyNat) : Equal (plus m (plus n p)) (plus n (plus m p)) :=
  eqTrans (eqSym (plusAssoc m n p)) (eqTrans (congPlusLeft p (plusComm m n)) (plusAssoc n m p))

-- Multiplication properties
def mulZeroLeft (n : MyNat) : Equal (mul .zero n) .zero := .refl

def mulZeroRight : (n : MyNat) → Equal (mul n .zero) .zero
  | .zero   => .refl
  | .succ n => mulZeroRight n

def mulOneLeft (n : MyNat) : Equal (mul one n) n := plusZeroRight n

def mulOneRight : (n : MyNat) → Equal (mul n one) n
  | .zero   => .refl
  | .succ n => congSucc (mulOneRight n)

def mulSuccRight : (n m : MyNat) → Equal (mul n (.succ m)) (plus n (mul n m))
  | .zero,   _ => .refl
  | .succ n, m =>
      congSucc (eqTrans (congPlusRight m (mulSuccRight n m)) (plusLeftComm m n (mul n m)))

def mulComm : (n m : MyNat) → Equal (mul n m) (mul m n)
  | .zero,   m => eqSym (mulZeroRight m)
  | .succ n, m => eqTrans (congPlusRight m (mulComm n m)) (eqSym (mulSuccRight m n))

def mulDistribRight : (n m p : MyNat) → Equal (mul (plus n m) p) (plus (mul n p) (mul m p))
  | .zero,   _, _ => .refl
  | .succ n, m, p =>
      eqTrans (congPlusRight p (mulDistribRight n m p)) (eqSym (plusAssoc p (mul n p) (mul m p)))

def mulAssoc : (n m p : MyNat) → Equal (mul (mul n m) p) (mul n (mul m p))
  | .zero,   _, _ => .refl
  | .succ n, m, p =>
      eqTrans (mulDistribRight m (mul n m) p) (congPlusRight (mul m p) (mulAssoc n m p))

def mulDistribLeft : (n m p : MyNat) → Equal (mul n (plus m p)) (plus (mul n m) (mul n p))
  | .zero,   _, _ => .refl
  | .succ n, m, p =>
      eqTrans (congPlusRight (plus m p) (mulDistribLeft n m p))
        (eqTrans (plusAssoc m p (plus (mul n m) (mul n p)))
          (eqTrans (congPlusRight m (plusLeftComm p (mul n m) (mul n p)))
            (eqSym (plusAssoc m (mul n m) (plus p (mul n p))))))

-- Semiring record and instance
structure Semiring (A : Type) where
  add : A → A → A
  mulS : A → A → A
  zero : A
  oneS : A
  addZeroLeft : (a : A) → Equal (add zero a) a
  addZeroRight : (a : A) → Equal (add a zero) a
  addComm : (a b : A) → Equal (add a b) (add b a)
  addAssoc : (a b c : A) → Equal (add (add a b) c) (add a (add b c))
  mulZeroL : (a : A) → Equal (mulS zero a) zero
  mulZeroR : (a : A) → Equal (mulS a zero) zero
  mulOneL : (a : A) → Equal (mulS oneS a) a
  mulOneR : (a : A) → Equal (mulS a oneS) a
  mulCommS : (a b : A) → Equal (mulS a b) (mulS b a)
  mulAssocS : (a b c : A) → Equal (mulS (mulS a b) c) (mulS a (mulS b c))
  distribL : (a b c : A) → Equal (mulS a (add b c)) (add (mulS a b) (mulS a c))
  distribR : (a b c : A) → Equal (mulS (add a b) c) (add (mulS a c) (mulS b c))

def natSemiring : Semiring MyNat where
  add := plus
  mulS := mul
  zero := .zero
  oneS := one
  addZeroLeft := plusZeroLeft
  addZeroRight := plusZeroRight
  addComm := plusComm
  addAssoc := plusAssoc
  mulZeroL := mulZeroLeft
  mulZeroR := mulZeroRight
  mulOneL := mulOneLeft
  mulOneR := mulOneRight
  mulCommS := mulComm
  mulAssocS := mulAssoc
  distribL := mulDistribLeft
  distribR := mulDistribRight

-- Leq: ordering on MyNat
inductive Leq : MyNat → MyNat → Type where
  | LeqZero : {n : MyNat} → Leq .zero n
  | LeqSucc : {n m : MyNat} → Leq n m → Leq (.succ n) (.succ m)

def leqRefl : (n : MyNat) → Leq n n
  | .zero   => .LeqZero
  | .succ n => .LeqSucc (leqRefl n)

def leqTrans : {a b c : MyNat} → Leq a b → Leq b c → Leq a c
  | _, _, _, .LeqZero,   _          => .LeqZero
  | _, _, _, .LeqSucc p, .LeqSucc q => .LeqSucc (leqTrans p q)

def leqAntisym : {a b : MyNat} → Leq a b → Leq b a → Equal a b
  | _, _, .LeqZero,   .LeqZero   => .refl
  | _, _, .LeqSucc p, .LeqSucc q => congSucc (leqAntisym p q)

def leqSuccRight : {i n : MyNat} → Leq i n → Leq i (.succ n)
  | _, _, .LeqZero   => .LeqZero
  | _, _, .LeqSucc l => .LeqSucc (leqSuccRight l)

-- Subtraction and minus lemmas
def minus : MyNat → MyNat → MyNat
  | .zero,   _       => .zero
  | .succ a, .zero   => .succ a
  | .succ a, .succ b => minus a b

-- minus n zero = n doesn't hold definitionally for a variable n under Lean's
-- compiled recursion, so prove it (and use it where the TT preset relied on the
-- minus a Zero = a equation reducing).
def minusZeroR : (n : MyNat) → Equal (minus n .zero) n
  | .zero   => .refl
  | .succ _ => .refl

def minusSucc : {i n : MyNat} → Leq i n → Equal (minus (.succ n) i) (.succ (minus n i))
  | _, _, @Leq.LeqZero n => eqCong MyNat.succ (eqSym (minusZeroR n))
  | _, _, @Leq.LeqSucc i' n' l => @minusSucc i' n' l

def plusMinusCancel : {i n : MyNat} → Leq i n → Equal (plus i (minus n i)) n
  | _, _, @Leq.LeqZero n => minusZeroR n
  | _, _, .LeqSucc l => congSucc (plusMinusCancel l)

def minusSelf : (n : MyNat) → Equal (minus n n) .zero
  | .zero   => .refl
  | .succ n => minusSelf n

def plusMinusSucc : {i n : MyNat} → Leq i n → Equal (plus i (minus (.succ n) i)) (.succ n)
  | .zero,   _, .LeqZero   => .refl
  | .succ _, _, .LeqSucc l => congSucc (plusMinusSucc l)

-- Summation
def sumStartCount : (start count : MyNat) → (MyNat → MyNat) → MyNat
  | _,     .zero,   _ => .zero
  | start, .succ k, f => plus (sumStartCount start k f) (f (plus start k))

def sumStartCountZero (s : MyNat) (f : MyNat → MyNat) : Equal (sumStartCount s .zero f) .zero := .refl

def sumStartCountOne (s : MyNat) (f : MyNat → MyNat) : Equal (sumStartCount s (.succ .zero) f) (f s) :=
  eqCong f (plusZeroRight s)

def sum (start stop : MyNat) (f : MyNat → MyNat) : MyNat :=
  sumStartCount start (minus (.succ stop) start) f

def two : MyNat := .succ (.succ .zero)

-- Triangle sum: 2 * (0 + 1 + ... + n) = (n + 1) * n.
-- Left as sorry, exactly as the original TT preset left it (?TODO).
-- (def, not theorem: this custom Equal lives in Type, not Prop.)
def triangleSum (n : MyNat) :
    Equal (mul two (sum .zero n (fun i => i))) (mul (plus n one) n) := sorry

#check natSemiring
#check leqAntisym
#check triangleSum
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
