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
-- A hand-rolled MyNat with plus, mul, one; the 12 semiring laws
-- + a Semiring record/instance; Leq ordering; subtraction lemmas; summation;
-- and the triangle-sum statement (left as sorry, as in the original).
-- Equality is Lean's native = (Eq), so rw/simp/rfl and rewrite suggestions work.

inductive MyNat where
  | zero : MyNat
  | succ : MyNat → MyNat

def plus : MyNat → MyNat → MyNat
  | .zero,   m => m
  | .succ n, m => .succ (plus n m)

def mul : MyNat → MyNat → MyNat
  | .zero,   _ => .zero
  | .succ n, m => plus m (mul n m)

def one : MyNat := .succ .zero

-- Notation so the structured editor renders real math (a + b, a * b, a = b,
-- a ≤ b) instead of plus a b / a = b. Lean's delaborator applies these
-- to the function-form proofs below automatically.
infixl:65 " + " => plus
infixl:70 " * " => mul
instance : OfNat MyNat 0 := ⟨MyNat.zero⟩
instance : OfNat MyNat 1 := ⟨one⟩

-- Render the bare constructor MyNat.zero as the literal 0. After induction,
-- goals substitute the raw constructor (not the OfNat literal), so without this
-- the base case shows MyNat.zero instead of 0.
@[app_unexpander MyNat.zero] def unexpMyNatZero : Lean.PrettyPrinter.Unexpander
  | \`($_) => \`(0)

-- Equality helpers (named to avoid clashing with Lean's Trans/_root_.trans)
def congSucc {n m : MyNat} : n = m → (MyNat.succ n) = (MyNat.succ m)
  | rfl => rfl

def succInj {n m : MyNat} : (MyNat.succ n) = (.succ m) → n = m
  | rfl => rfl

def eqSym {A : Type} {x y : A} : x = y → y = x
  | rfl => rfl

def eqTrans {A : Type} {x y z : A} : x = y → y = z → x = z
  | rfl, rfl => rfl

def eqCong {A B : Type} {x y : A} (f : A → B) : x = y → (f x) = (f y)
  | rfl => rfl

def replace {A : Type} {x y : A} (P : A → Type) : x = y → P x → P y
  | rfl, px => px

-- Addition properties
def plusZeroLeft (n : MyNat) : (plus .zero n) = n := rfl

def plusZeroRight : (n : MyNat) → (plus n .zero) = n
  | .zero   => rfl
  | .succ n => congSucc (plusZeroRight n)

def plusSuccRight : (n m : MyNat) → (plus n (.succ m)) = (.succ (plus n m))
  | .zero,   _ => rfl
  | .succ n, m => congSucc (plusSuccRight n m)

def plusAssoc : (n m p : MyNat) → (plus (plus n m) p) = (plus n (plus m p))
  | .zero,   _, _ => rfl
  | .succ n, m, p => congSucc (plusAssoc n m p)

def plusComm : (n m : MyNat) → (plus n m) = (plus m n)
  | .zero,   m => eqSym (plusZeroRight m)
  | .succ n, m => eqTrans (congSucc (plusComm n m)) (eqSym (plusSuccRight m n))

def congPlusLeft {n m : MyNat} (p : MyNat) : n = m → (plus n p) = (plus m p)
  | rfl => rfl

def congPlusRight {n m : MyNat} : (p : MyNat) → n = m → (plus p n) = (plus p m)
  | .zero,   eq => eq
  | .succ p, eq => congSucc (congPlusRight p eq)

def plusLeftComm (m n p : MyNat) : (plus m (plus n p)) = (plus n (plus m p)) :=
  eqTrans (eqSym (plusAssoc m n p)) (eqTrans (congPlusLeft p (plusComm m n)) (plusAssoc n m p))

-- Multiplication properties
def mulZeroLeft (n : MyNat) : (mul .zero n) = .zero := rfl

def mulZeroRight : (n : MyNat) → (mul n .zero) = .zero
  | .zero   => rfl
  | .succ n => mulZeroRight n

def mulOneLeft (n : MyNat) : (mul one n) = n := plusZeroRight n

def mulOneRight : (n : MyNat) → (mul n one) = n
  | .zero   => rfl
  | .succ n => congSucc (mulOneRight n)

def mulSuccRight : (n m : MyNat) → (mul n (.succ m)) = (plus n (mul n m))
  | .zero,   _ => rfl
  | .succ n, m =>
      congSucc (eqTrans (congPlusRight m (mulSuccRight n m)) (plusLeftComm m n (mul n m)))

def mulComm : (n m : MyNat) → (mul n m) = (mul m n)
  | .zero,   m => eqSym (mulZeroRight m)
  | .succ n, m => eqTrans (congPlusRight m (mulComm n m)) (eqSym (mulSuccRight m n))

def mulDistribRight : (n m p : MyNat) → (mul (plus n m) p) = (plus (mul n p) (mul m p))
  | .zero,   _, _ => rfl
  | .succ n, m, p =>
      eqTrans (congPlusRight p (mulDistribRight n m p)) (eqSym (plusAssoc p (mul n p) (mul m p)))

def mulAssoc : (n m p : MyNat) → (mul (mul n m) p) = (mul n (mul m p))
  | .zero,   _, _ => rfl
  | .succ n, m, p =>
      eqTrans (mulDistribRight m (mul n m) p) (congPlusRight (mul m p) (mulAssoc n m p))

def mulDistribLeft : (n m p : MyNat) → (mul n (plus m p)) = (plus (mul n m) (mul n p))
  | .zero,   _, _ => rfl
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
  addZeroLeft : (a : A) → (add zero a) = a
  addZeroRight : (a : A) → (add a zero) = a
  addComm : (a b : A) → (add a b) = (add b a)
  addAssoc : (a b c : A) → (add (add a b) c) = (add a (add b c))
  mulZeroL : (a : A) → (mulS zero a) = zero
  mulZeroR : (a : A) → (mulS a zero) = zero
  mulOneL : (a : A) → (mulS oneS a) = a
  mulOneR : (a : A) → (mulS a oneS) = a
  mulCommS : (a b : A) → (mulS a b) = (mulS b a)
  mulAssocS : (a b c : A) → (mulS (mulS a b) c) = (mulS a (mulS b c))
  distribL : (a b c : A) → (mulS a (add b c)) = (add (mulS a b) (mulS a c))
  distribR : (a b c : A) → (mulS (add a b) c) = (add (mulS a c) (mulS b c))

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
inductive Leq : MyNat → MyNat → Prop where
  | LeqZero : {n : MyNat} → Leq .zero n
  | LeqSucc : {n m : MyNat} → Leq n m → Leq (.succ n) (.succ m)

infix:50 " ≤ " => Leq

def leqRefl : (n : MyNat) → Leq n n
  | .zero   => .LeqZero
  | .succ n => .LeqSucc (leqRefl n)

def leqTrans : {a b c : MyNat} → Leq a b → Leq b c → Leq a c
  | _, _, _, .LeqZero,   _          => .LeqZero
  | _, _, _, .LeqSucc p, .LeqSucc q => .LeqSucc (leqTrans p q)

def leqAntisym : {a b : MyNat} → Leq a b → Leq b a → a = b
  | _, _, .LeqZero,   .LeqZero   => rfl
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
def minusZeroR : (n : MyNat) → (minus n .zero) = n
  | .zero   => rfl
  | .succ _ => rfl

def minusSucc : {i n : MyNat} → Leq i n → (minus (.succ n) i) = (.succ (minus n i))
  | _, _, @Leq.LeqZero n => eqCong MyNat.succ (eqSym (minusZeroR n))
  | _, _, @Leq.LeqSucc i' n' l => @minusSucc i' n' l

def plusMinusCancel : {i n : MyNat} → Leq i n → (plus i (minus n i)) = n
  | _, _, @Leq.LeqZero n => minusZeroR n
  | _, _, .LeqSucc l => congSucc (plusMinusCancel l)

def minusSelf : (n : MyNat) → (minus n n) = .zero
  | .zero   => rfl
  | .succ n => minusSelf n

def plusMinusSucc : {i n : MyNat} → Leq i n → (plus i (minus (.succ n) i)) = (.succ n)
  | .zero,   _, .LeqZero   => rfl
  | .succ _, _, .LeqSucc l => congSucc (plusMinusSucc l)

-- Summation
def sumStartCount : (start count : MyNat) → (MyNat → MyNat) → MyNat
  | _,     .zero,   _ => .zero
  | start, .succ k, f => plus (sumStartCount start k f) (f (plus start k))

def sumStartCountZero (s : MyNat) (f : MyNat → MyNat) : (sumStartCount s .zero f) = .zero := rfl

def sumStartCountOne (s : MyNat) (f : MyNat → MyNat) : (sumStartCount s (.succ .zero) f) = (f s) :=
  eqCong f (plusZeroRight s)

def sum (start stop : MyNat) (f : MyNat → MyNat) : MyNat :=
  sumStartCount start (minus (.succ stop) start) f

def two : MyNat := .succ (.succ .zero)
instance : OfNat MyNat 2 := ⟨two⟩
notation:max "∑[" i "," lo "," hi "] " f:67 => sum lo hi (fun i => f)

-- sumStartCount splits off its last term definitionally.
def sumStartCountSplit (s k : MyNat) (f : MyNat → MyNat) :
    (sumStartCount s (.succ k) f) = (plus (sumStartCount s k f) (f (plus s k))) := rfl

-- Summation splitting: sum from i to (n+1) = (sum from i to n) + f(n+1).
def summationSplit (i n : MyNat) (l : Leq i n) (f : MyNat → MyNat) :
    (sum i (.succ n) f) = (plus (sum i n f) (f (.succ n))) :=
  eqTrans
    (eqCong (fun k => sumStartCount i k f) (minusSucc (leqSuccRight l)))
    (congPlusRight (sum i n f) (eqCong f (plusMinusSucc l)))

-- Bridge the successor constructor to +1 (they're equal but not definitionally,
-- since plus recurses on its first arg). Lets you rewrite n.succ to n + 1
-- so the arithmetic lemmas can normalize it.
def succAddOne (n : MyNat) : (MyNat.succ n) = (plus n 1) :=
  eqSym (eqTrans (plusComm n 1) rfl)

-- 2 = 1 + 1 (definitionally). With succAddOne this lets the arithmetic lemmas
-- expand the numeral 2 the same way successors expand, so ring-style goals like
-- the triangle-sum step normalize to a common form and close.
def twoEqAddOne : (2 : MyNat) = (plus 1 1) := rfl

-- Triangle sum: 2 * (0 + 1 + ... + n) = (n + 1) * n.
-- Left as sorry, exactly as the original TT preset left it (?TODO).
-- (def, not theorem: this custom lives = in Type, not Prop.)
def triangleSum (n : MyNat) :
    (mul 2 (∑[i,0,n] i)) = (mul (plus n 1) n) := sorry

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
-- Equality is Lean's native = (Eq). The eliminator comes in two forms:
-- ind into Type (so plus computes a carrier value) and indProp into Prop
-- (so the equational proofs can do induction).

universe u v

def eqSym {A : Type u} {x y : A} : x = y → y = x
  | rfl => rfl

def eqTrans {A : Type u} {x y z : A} : x = y → y = z → x = z
  | rfl, rfl => rfl

def eqCong {A : Type u} {B : Type v} (f : A → B) {x y : A} : x = y → (f x) = (f y)
  | rfl => rfl

inductive MyVoid : Prop where

def MyNot (A : Prop) : Prop := A → MyVoid

structure PeanoNat where
  carrier : Type
  zero : carrier
  succ : carrier → carrier
  zeroNeqSucc : {n : carrier} → MyNot (zero = succ n)
  succInj : {m n : carrier} → succ m = succ n → m = n
  ind : {P : carrier → Type} → P zero → ({n : carrier} → P n → P (succ n)) → (n : carrier) → P n
  indProp : {P : carrier → Prop} → P zero → ({n : carrier} → P n → P (succ n)) → (n : carrier) → P n
  indZero : {P : carrier → Type} → (base : P zero) → (step : {n : carrier} → P n → P (succ n)) →
    (ind base step zero) = base
  indSucc : {P : carrier → Type} → (base : P zero) → (step : {n : carrier} → P n → P (succ n)) →
    (n : carrier) → (ind base step (succ n)) = (step (ind base step n))

@[reducible] def plus (N : PeanoNat) (n m : N.carrier) : N.carrier :=
  N.ind m (fun ih => N.succ ih) n

def plusZeroEq (N : PeanoNat) (m : N.carrier) : (plus N N.zero m) = m :=
  N.indZero m (fun ih => N.succ ih)

def plusSuccEq (N : PeanoNat) (k m : N.carrier) :
    (plus N (N.succ k) m) = (N.succ (plus N k m)) :=
  N.indSucc m (fun ih => N.succ ih) k

def plusZeroRight (N : PeanoNat) (n : N.carrier) : (plus N n N.zero) = n :=
  N.indProp (P := fun k => (plus N k N.zero) = k)
    (plusZeroEq N N.zero)
    (fun {k} ih => eqTrans (plusSuccEq N k N.zero) (eqCong N.succ ih))
    n

def plusSuccRight (N : PeanoNat) (n m : N.carrier) :
    (plus N n (N.succ m)) = (N.succ (plus N n m)) :=
  N.indProp (P := fun k => (plus N k (N.succ m)) = (N.succ (plus N k m)))
    (eqTrans (plusZeroEq N (N.succ m)) (eqSym (eqCong N.succ (plusZeroEq N m))))
    (fun {k} ih =>
      eqTrans (eqTrans (plusSuccEq N k (N.succ m)) (eqCong N.succ ih))
            (eqSym (eqCong N.succ (plusSuccEq N k m))))
    n

def plusComm (N : PeanoNat) (n m : N.carrier) : (plus N n m) = (plus N m n) :=
  N.indProp (P := fun k => (plus N k m) = (plus N m k))
    (eqTrans (plusZeroEq N m) (eqSym (plusZeroRight N m)))
    (fun {k} ih =>
      eqTrans (eqTrans (plusSuccEq N k m) (eqCong N.succ ih)) (eqSym (plusSuccRight N m k)))
    n

def plusAssoc (N : PeanoNat) (a b c : N.carrier) :
    (plus N (plus N a b) c) = (plus N a (plus N b c)) :=
  N.indProp (P := fun k => (plus N (plus N k b) c) = (plus N k (plus N b c)))
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

// Ported from the TT "Real Analysis" preset: a from-scratch algebraic hierarchy
// (AbelianGroup to Ring to Field to OrderedField to CompleteOrderedField), the
// reals, limits, and derivatives, culminating in the sum/scalar/chain rules.
// Core Lean, no Mathlib. Faithful statements; hard tactic-mode proofs are sorry.
const REAL_ANALYSIS = `-- Real Analysis: algebraic hierarchy, ordered fields, limits, and derivatives
-- Proves (f+g)' = f' + g', (c*f)' = c*f', and the chain rule (g.f)'=g'(f(x0))*f'(x0)
-- Translated from the leanUI TT/TTK "real-analysis" preset to core Lean 4 (no Mathlib).

------------------------------------------------------------
-- Foundation: basic types and equality
------------------------------------------------------------

universe u v w

inductive MyVoid : Type where

def myAbsurd {A : Type} : MyVoid → A := fun v => nomatch v



def eqSym {A : Type} {x y : A} : x = y → y = x
  | rfl => rfl

def eqTrans {A : Type} {x y z : A} : x = y → y = z → x = z
  | rfl, rfl => rfl

def eqCong {A B : Type} {x y : A} (f : A → B) : x = y → (f x) = (f y)
  | rfl => rfl

-- Transport: rewrite along an equality proof
def replace {A : Type} {x y : A} (P : A → Sort w) : x = y → P x → P y
  | rfl, px => px

inductive Either (A : Sort u) (B : Sort v) where
  | left : A → Either A B
  | right : B → Either A B

def eitherElim {A : Sort u} {B : Sort v} {C : Sort w} (f : A → C) (g : B → C) : Either A B → C
  | .left a => f a
  | .right b => g b

def eitherElimDep {A : Sort u} {B : Sort v} (C : Either A B → Sort w)
    (f : (a : A) → C (.left a)) (g : (b : B) → C (.right b)) : (e : Either A B) → C e
  | .left a => f a
  | .right b => g b

structure Pair (A B : Type) where
  fst : A
  snd : B

structure DPair (A : Type u) (B : A → Type v) : Type (max u v) where
  fst : A
  snd : B fst

------------------------------------------------------------
-- Order Hierarchy: Preorder -> PartialOrder -> TotalOrder
------------------------------------------------------------

structure Preorder (A : Type) where
  le : A → A → Type
  leRefl : (a : A) → le a a
  leTrans : (a b c : A) → le a b → le b c → le a c

structure PartialOrder (A : Type) extends Preorder A where
  leAntisym : (a b : A) → le a b → le b a → a = b

structure TotalOrder (A : Type) extends PartialOrder A where
  leTotal : (a b : A) → Either (le a b) (le b a)

------------------------------------------------------------
-- Algebraic Hierarchy
------------------------------------------------------------

structure AbelianGroup (A : Type) where
  add : A → A → A
  zero : A
  neg : A → A
  addAssoc : (a b c : A) → (add (add a b) c) = (add a (add b c))
  addComm : (a b : A) → (add a b) = (add b a)
  addZeroRight : (a : A) → (add a zero) = a
  negRight : (a : A) → (add a (neg a)) = zero

structure Ring (A : Type) extends AbelianGroup A where
  mul : A → A → A
  one : A
  mulAssoc : (a b c : A) → (mul (mul a b) c) = (mul a (mul b c))
  mulOneLeft : (a : A) → (mul one a) = a
  mulOneRight : (a : A) → (mul a one) = a
  distribLeft : (a b c : A) → (mul a (add b c)) = (add (mul a b) (mul a c))
  distribRight : (a b c : A) → (mul (add a b) c) = (add (mul a c) (mul b c))

structure CommRing (A : Type) extends Ring A where
  mulComm : (a b : A) → (mul a b) = (mul b a)

structure Field (A : Type) extends CommRing A where
  inv : A → A
  mulInvRight : (a : A) → (a = zero → MyVoid) → (mul a (inv a)) = one

------------------------------------------------------------
-- Ordered Field: Field + Total Order + Compatibility
------------------------------------------------------------

structure OrderedField (A : Type) : Type 1 extends Field A where
  le : A → A → Type
  leRefl : (a : A) → le a a
  leAntisym : (a b : A) → le a b → le b a → a = b
  leTrans : (a b c : A) → le a b → le b c → le a c
  leTotal : (a b : A) → Either (le a b) (le b a)
  addLeLeft : (a b c : A) → le a b → le (add c a) (add c b)
  mulNonneg : (a b : A) → le zero a → le zero b → le zero (mul a b)
  zeroLeOne : le zero one
  zeroNeOne : zero = one → MyVoid
  invPos : (a : A) → le zero a → (a = zero → MyVoid) → le zero (inv a)
  leToEqOrLt : (a b : A) → le a b → Either (a = b) (Pair (le a b) (a = b → MyVoid))

------------------------------------------------------------
-- Complete Ordered Field: the Dedekind completeness axiom
------------------------------------------------------------

structure CompleteOrderedField (A : Type) : Type 1 extends OrderedField A where
  sup : (A → Type) → A
  supUpperBound : (P : A → Type) → (x : A) → P x → le x (sup P)
  supLeast : (P : A → Type) → (b : A) → ((x : A) → P x → le x b) → le (sup P) b

------------------------------------------------------------
-- The Real Numbers
------------------------------------------------------------

-- leanUI's Real = (A : Type ** CompleteOrderedField A). We model it as a DPair
-- whose first component is the carrier Type and whose second is the field structure.
-- (In core Lean the resulting universe is Type 2, not Type 1, because
-- CompleteOrderedField A : Type 1; the original : Type 1 ascription is dropped.)
@[reducible] def Real := DPair Type CompleteOrderedField

@[reducible] def Carrier (R : Real) : Type := DPair.fst R

@[reducible] def fieldOf (R : Real) : CompleteOrderedField (Carrier R) := DPair.snd R

------------------------------------------------------------
-- Field operations, parametric over any Real
------------------------------------------------------------

def radd {R : Real} : Carrier R → Carrier R → Carrier R := (fieldOf R).add

def rmul {R : Real} : Carrier R → Carrier R → Carrier R := (fieldOf R).mul

def rzero (R : Real) : Carrier R := (fieldOf R).zero

def rone (R : Real) : Carrier R := (fieldOf R).one

------------------------------------------------------------
-- Natural numbers + numeric literal coercion to Carrier R
------------------------------------------------------------

inductive MyNat : Type where
  | zero : MyNat
  | succ : MyNat → MyNat

def realOfNat (R : Real) : MyNat → Carrier R
  | .zero => rzero R
  | .succ n => radd (rone R) (realOfNat R n)

def plus : MyNat → MyNat → MyNat
  | .zero, m => m
  | .succ n, m => .succ (plus n m)

def mult : MyNat → MyNat → MyNat
  | .zero, _ => .zero
  | .succ n, m => plus m (mult n m)

------------------------------------------------------------
-- Integers (Lean-style two-constructor representation)
------------------------------------------------------------

inductive MyInt : Type where
  | intOfNat : MyNat → MyInt
  | intNegSucc : MyNat → MyInt

def negOfNat : MyNat → MyInt
  | .zero => .intOfNat .zero
  | .succ n => .intNegSucc n

def intZero : MyInt := .intOfNat .zero

def intOne : MyInt := .intOfNat (.succ .zero)

def intNeg : MyInt → MyInt
  | .intOfNat .zero => .intOfNat .zero
  | .intOfNat (.succ n) => .intNegSucc n
  | .intNegSucc n => .intOfNat (.succ n)

def subNatNat : MyNat → MyNat → MyInt
  | .zero, .zero => .intOfNat .zero
  | .succ m, .zero => .intOfNat (.succ m)
  | .zero, .succ n => .intNegSucc n
  | .succ m, .succ n => subNatNat m n

def intAdd : MyInt → MyInt → MyInt
  | .intOfNat m, .intOfNat n => .intOfNat (plus m n)
  | .intOfNat m, .intNegSucc n => subNatNat m (.succ n)
  | .intNegSucc m, .intOfNat n => subNatNat n (.succ m)
  | .intNegSucc m, .intNegSucc n => .intNegSucc (.succ (plus m n))

def intMul : MyInt → MyInt → MyInt
  | .intOfNat m, .intOfNat n => .intOfNat (mult m n)
  | .intOfNat m, .intNegSucc n => negOfNat (mult m (.succ n))
  | .intNegSucc m, .intOfNat n => negOfNat (mult (.succ m) n)
  | .intNegSucc m, .intNegSucc n => .intOfNat (mult (.succ m) (.succ n))

def intSub : MyInt → MyInt → MyInt
  | a, b => intAdd a (intNeg b)

-- NotZero — proof-bundled positivity predicate.
inductive NotZero : MyNat → Type where
  | isSucc : (n : MyNat) → NotZero (.succ n)

def mulSuccSuccNotZero (m n : MyNat) : NotZero (mult (.succ m) (.succ n)) :=
  .isSucc (plus n (mult m (.succ n)))

def mulNotZero : (d1 d2 : MyNat) → NotZero d1 → NotZero d2 → NotZero (mult d1 d2)
  | .succ k1, .succ k2, .isSucc _, .isSucc _ => mulSuccSuccNotZero k1 k2

-- MyRat — Lean-style proof-bundled rational.
inductive MyRat : Type where
  | mkRat : MyInt → (d : MyNat) → NotZero d → MyRat

def ratPlus : MyRat → MyRat → MyRat
  | .mkRat a b pb, .mkRat c d pd =>
      .mkRat (intAdd (intMul a (.intOfNat d)) (intMul c (.intOfNat b))) (mult b d) (mulNotZero b d pb pd)

def ratMult : MyRat → MyRat → MyRat
  | .mkRat a b pb, .mkRat c d pd =>
      .mkRat (intMul a c) (mult b d) (mulNotZero b d pb pd)

def minus : MyNat → MyNat → MyNat
  | n, .zero => n
  | .zero, .succ _ => .zero
  | .succ n, .succ m => minus n m

def ratSub : MyRat → MyRat → MyRat
  | .mkRat a b pb, .mkRat c d pd =>
      .mkRat (intSub (intMul a (.intOfNat d)) (intMul c (.intOfNat b))) (mult b d) (mulNotZero b d pb pd)

def rneg {R : Real} : Carrier R → Carrier R := (fieldOf R).neg

def realOfInt (R : Real) : MyInt → Carrier R
  | .intOfNat n => realOfNat R n
  | .intNegSucc n => rneg (radd (rone R) (realOfNat R n))

def rinv {R : Real} : Carrier R → Carrier R := (fieldOf R).inv

def rle {R : Real} : Carrier R → Carrier R → Type := (fieldOf R).le

-- Subtraction: a - b = a + (-b)
def rsub {R : Real} (a b : Carrier R) : Carrier R := radd a (rneg b)

-- Division: a / b = a * inv(b)
def rdiv {R : Real} (a b : Carrier R) : Carrier R := rmul a (rinv b)

-- Strict ordering: a < b iff a <= b and a /= b
def rlt {R : Real} (a b : Carrier R) : Type := Pair (rle a b) (a = b → MyVoid)

-- Notation so the editor renders real-number expressions as math.
infixl:65 " + " => radd
infixl:70 " * " => rmul
infixl:65 " - " => rsub
infixl:70 " / " => rdiv
infix:50 " ≤ " => rle
infix:50 " < " => rlt
prefix:75 "-" => rneg

-- Absolute value (defined from leTotal via eitherElim, not axiomatized)
def rabs {R : Real} (a : Carrier R) : Carrier R :=
  eitherElim (fun _ => a) (fun _ => rneg a) ((fieldOf R).leTotal (rzero R) a)

def absElim {R : Real} (a : Carrier R) (C : Carrier R → Sort w)
    (pos : rle (rzero R) a → C a) (neg : rle a (rzero R) → C (rneg a)) : C (rabs a) :=
  eitherElimDep (fun e => C (eitherElim (fun _ => a) (fun _ => rneg a) e))
    (fun h => pos h) (fun h => neg h)
    ((fieldOf R).leTotal (rzero R) a)

def realOfRat (R : Real) : MyRat → Carrier R
  | .mkRat n (.succ .zero) _ => realOfInt R n
  | .mkRat n d _ => rdiv (realOfInt R n) (realOfNat R d)

------------------------------------------------------------
-- Limits: the epsilon-delta definition
------------------------------------------------------------

@[reducible] def EpsDeltaWitness {R : Real} (f : Carrier R → Carrier R)
    (x0 L epsilon delta : Carrier R) : Type :=
  Pair (rlt (rzero R) delta)
    ((x : Carrier R) → rlt (rzero R) (rabs (rsub x x0)) → rlt (rabs (rsub x x0)) delta →
      rlt (rabs (rsub (f x) L)) epsilon)

structure Limit {R : Real} (f : Carrier R → Carrier R) (x0 L : Carrier R) where
  eps_delta : (epsilon : Carrier R) → rlt (rzero R) epsilon →
              DPair (Carrier R)
                (fun delta => EpsDeltaWitness f x0 L epsilon delta)

-- NOTE: leanUI used a dependent-pair existential (δ : Carrier R ** EpsDeltaWitness ...).
-- In core Lean we model it with DPair; the first component family is the carrier itself.
-- (See uses of DPair.fst / DPair.snd below.)

------------------------------------------------------------
-- Algebraic lemmas
------------------------------------------------------------

-- TACTIC-MODE in source (erw); kept faithful as statement, body sorried.
def addZeroLeft {R : Real} (a : Carrier R) : (radd (rzero R) a) = a := sorry

def addRealOfNat (R : Real) : (n m : MyNat) →
    (radd (realOfNat R n) (realOfNat R m)) = (realOfNat R (plus n m))
  | .zero, m => addZeroLeft (realOfNat R m)
  | .succ n, m =>
      eqTrans ((fieldOf R).addAssoc (rone R) (realOfNat R n) (realOfNat R m))
        (eqCong (fun z => radd (rone R) z) (addRealOfNat R n m))

-- TACTIC-MODE in source (erw).
def negLeft {R : Real} (a : Carrier R) : (radd (rneg a) a) = (rzero R) := sorry

def addNegRight {R : Real} (a : Carrier R) : (radd a (rneg a)) = (rzero R) :=
  (fieldOf R).negRight a

def addLeRight {R : Real} (a b c : Carrier R) (h : rle a b) : rle (radd a c) (radd b c) :=
  replace (fun z => rle z (radd b c)) ((fieldOf R).addComm c a)
    (replace (fun z => rle (radd c a) z) ((fieldOf R).addComm c b)
      ((fieldOf R).addLeLeft a b c h))

def addLeBoth {R : Real} (a b c d : Carrier R) (hab : rle a b) (hcd : rle c d) :
    rle (radd a c) (radd b d) :=
  (fieldOf R).leTrans (radd a c) (radd b c) (radd b d)
    (addLeRight a b c hab) ((fieldOf R).addLeLeft c d b hcd)

-- TACTIC-MODE in source (erw).
def negZero (R : Real) : (rneg (rzero R)) = (rzero R) := sorry

def leNegNonneg {R : Real} (a : Carrier R) (h : rle a (rzero R)) : rle (rzero R) (rneg a) :=
  replace (fun z => rle z (rneg a)) ((fieldOf R).negRight a)
    (replace (fun z => rle (radd a (rneg a)) z) (addZeroLeft (rneg a))
      (addLeRight a (rzero R) (rneg a) h))

def negNonpos {R : Real} (a : Carrier R) (h : rle (rzero R) a) : rle (rneg a) (rzero R) :=
  replace (fun z => rle (rneg a) z) ((fieldOf R).negRight a)
    (replace (fun z => rle z (radd a (rneg a))) (addZeroLeft (rneg a))
      (addLeRight (rzero R) a (rneg a) h))

def leLtTransLe {R : Real} (a b c : Carrier R) (hab : rle a b) (hbc : rle b c) : rle a c :=
  (fieldOf R).leTrans a b c hab hbc

def leLtTransNe {R : Real} (a b c : Carrier R) (hab : rle a b) (hbc : rle b c)
    (nebc : b = c → MyVoid) (eq : a = c) : MyVoid :=
  nebc ((fieldOf R).leAntisym b c hbc (replace (fun z => rle z b) eq hab))

def leLtTrans {R : Real} (a b c : Carrier R) (hab : rle a b) (hbc : rlt b c) : rlt a c :=
  Pair.mk (leLtTransLe a b c hab (Pair.fst hbc)) (leLtTransNe a b c hab (Pair.fst hbc) (Pair.snd hbc))

def ltLeTransLe {R : Real} (a b c : Carrier R) (hab : rle a b) (hbc : rle b c) : rle a c :=
  (fieldOf R).leTrans a b c hab hbc

def ltLeTransNe {R : Real} (a b c : Carrier R) (hab : rle a b) (neab : a = b → MyVoid)
    (hbc : rle b c) (eq : a = c) : MyVoid :=
  neab ((fieldOf R).leAntisym a b hab
    ((fieldOf R).leTrans b c a hbc
      (replace (fun z => rle z a) eq ((fieldOf R).leRefl a))))

def ltLeTrans {R : Real} (a b c : Carrier R) (hab : rlt a b) (hbc : rle b c) : rlt a c :=
  Pair.mk (ltLeTransLe a b c (Pair.fst hab) hbc) (ltLeTransNe a b c (Pair.fst hab) (Pair.snd hab) hbc)

-- TACTIC-MODE in source (erw).
def addCancelRightHelper {R : Real} (x c : Carrier R) :
    (radd (radd x c) (rneg c)) = x := sorry

-- TACTIC-MODE in source (erw).
def addCancelRight {R : Real} (a b c : Carrier R) (h : (radd a c) = (radd b c)) :
    a = b := sorry

def addLeRightCancel {R : Real} (a b c : Carrier R) (h : rle (radd a c) (radd b c)) : rle a b :=
  replace (fun z => rle z b) (addCancelRightHelper a c)
    (replace (fun z => rle (radd (radd a c) (rneg c)) z) (addCancelRightHelper b c)
      (addLeRight (radd a c) (radd b c) (rneg c) h))

def addLeLeftCancel {R : Real} (a b c : Carrier R) (h : rle (radd c a) (radd c b)) : rle a b :=
  addLeRightCancel a b c
    (replace (fun z => rle (radd a c) z) ((fieldOf R).addComm c b)
      (replace (fun z => rle z (radd c b)) ((fieldOf R).addComm c a) h))

def addLtBothNe {R : Real} (a b c d : Carrier R) (leab : rle a b) (neab : a = b → MyVoid)
    (lecd : rle c d) (eq : (radd a c) = (radd b d)) : MyVoid :=
  neab (addCancelRight a b c
    ((fieldOf R).leAntisym (radd a c) (radd b c)
      (addLeRight a b c leab)
      ((fieldOf R).leTrans (radd b c) (radd b d) (radd a c)
        ((fieldOf R).addLeLeft c d b lecd)
        (replace (fun z => rle (radd b d) z) (eqSym eq)
          ((fieldOf R).leRefl (radd b d))))))

def addLtBoth {R : Real} (a b c d : Carrier R) (hab : rlt a b) (hcd : rlt c d) :
    rlt (radd a c) (radd b d) :=
  Pair.mk (addLeBoth a b c d (Pair.fst hab) (Pair.fst hcd))
    (addLtBothNe a b c d (Pair.fst hab) (Pair.snd hab) (Pair.fst hcd))

------------------------------------------------------------
-- Halving: 1/2 * eps + 1/2 * eps = eps
------------------------------------------------------------

def rtwo (R : Real) : Carrier R := radd (rone R) (rone R)

-- Render the carrier constants rzero/rone/rtwo R as the literals 0/1/2 in the
-- structured editor (display only — like MyNat.zero's unexpander).
@[app_unexpander rzero] def unexpRZero : Lean.PrettyPrinter.Unexpander
  | \`($_ $_) => \`(0)
  | _ => throw ()
@[app_unexpander rone] def unexpROne : Lean.PrettyPrinter.Unexpander
  | \`($_ $_) => \`(1)
  | _ => throw ()
@[app_unexpander rtwo] def unexpRTwo : Lean.PrettyPrinter.Unexpander
  | \`($_ $_) => \`(2)
  | _ => throw ()

def rhalf (R : Real) : Carrier R := rinv (rtwo R)

def oneLeTwo (R : Real) : rle (rone R) (rtwo R) :=
  replace (fun z => rle z (rtwo R)) (addZeroLeft (rone R))
    (addLeRight (rzero R) (rone R) (rone R) ((fieldOf R).zeroLeOne))

def twoNeZero (R : Real) (eq : (rtwo R) = (rzero R)) : MyVoid :=
  (fieldOf R).zeroNeOne
    ((fieldOf R).leAntisym (rzero R) (rone R)
      ((fieldOf R).zeroLeOne)
      (replace (fun z => rle (rone R) z) eq (oneLeTwo R)))

-- TACTIC-MODE in source (erw).
def halfPlusHalf (R : Real) : (radd (rhalf R) (rhalf R)) = (rone R) := sorry

-- TACTIC-MODE in source (erw).
def halfMulEps {R : Real} (e : Carrier R) :
    (radd (rmul (rhalf R) e) (rmul (rhalf R) e)) = e := sorry

def zeroLeTwo (R : Real) : rle (rzero R) (rtwo R) :=
  (fieldOf R).leTrans (rzero R) (rone R) (rtwo R)
    ((fieldOf R).zeroLeOne) (oneLeTwo R)

def halfPos (R : Real) : rle (rzero R) (rhalf R) :=
  (fieldOf R).invPos (rtwo R) (zeroLeTwo R) (twoNeZero R)

def halfMulEpsLe {R : Real} (e : Carrier R) (hle : rle (rzero R) e) :
    rle (rzero R) (rmul (rhalf R) e) :=
  (fieldOf R).mulNonneg (rhalf R) e (halfPos R) hle

def halfMulEpsNe {R : Real} (e : Carrier R) (hle : rle (rzero R) e)
    (hne : (rzero R) = e → MyVoid) (heq : (rzero R) = (rmul (rhalf R) e)) : MyVoid :=
  hne (eqTrans (eqSym (addZeroLeft (rzero R)))
    (eqTrans (eqCong (fun z => radd z z) heq) (halfMulEps e)))

-- TACTIC-MODE in source (constructor).
def halfMulEpsPos {R : Real} (e : Carrier R) (hlt : rlt (rzero R) e) :
    rlt (rzero R) (rmul (rhalf R) e) := sorry

------------------------------------------------------------
-- Negation distributes over addition: -(a+b) = (-a)+(-b)
------------------------------------------------------------

-- TACTIC-MODE in source (erw).
def addSumNeg {R : Real} (a b : Carrier R) : (radd (radd a b) (rneg a)) = b := sorry

-- TACTIC-MODE in source (erw).
def negAddCancel {R : Real} (a b : Carrier R) :
    (radd (radd a b) (radd (rneg a) (rneg b))) = (rzero R) := sorry

-- TACTIC-MODE in source (erw).
def negUnique {R : Real} (a b : Carrier R) (h : (radd a b) = (rzero R)) :
    b = (rneg a) := sorry

-- TACTIC-MODE in source (erw).
def negAdd {R : Real} (a b : Carrier R) :
    (rneg (radd a b)) = (radd (rneg a) (rneg b)) := sorry

def negNeg {R : Real} (a : Carrier R) : (rneg (rneg a)) = a :=
  eqSym (negUnique (rneg a) a (negLeft a))

def negRealOfInt (R : Real) : (a : MyInt) →
    (rneg (realOfInt R a)) = (realOfInt R (intNeg a))
  | .intOfNat .zero => negZero R
  | .intOfNat (.succ _) => rfl
  | .intNegSucc n => negNeg (radd (rone R) (realOfNat R n))

def plusSuccRight : (m n : MyNat) → (plus m (.succ n)) = (.succ (plus m n))
  | .zero, _ => rfl
  | .succ m, n => eqCong MyNat.succ (plusSuccRight m n)

-- TACTIC-MODE in source (erw).
def addOnePlusOneShuffle (R : Real) (m n : MyNat) :
    (radd (radd (rone R) (realOfNat R m)) (radd (rone R) (realOfNat R n))) = (radd (rone R) (radd (rone R) (realOfNat R (plus m n)))) := sorry

------------------------------------------------------------
-- (a+b)-(c+d) = (a-c)+(b-d)
------------------------------------------------------------

-- TACTIC-MODE in source (erw).
def fourTermRearrange {R : Real} (a b c d : Carrier R) :
    (radd (radd a b) (radd c d)) = (radd (radd a c) (radd b d)) := sorry

-- TACTIC-MODE in source (erw).
def subAddSub {R : Real} (a b c d : Carrier R) :
    (rsub (radd a b) (radd c d)) = (radd (rsub a c) (rsub b d)) := sorry

------------------------------------------------------------
-- Multiplication-negation lemmas (needed for abs properties)
------------------------------------------------------------

def mulZeroLeft {R : Real} (a : Carrier R) : (rmul (rzero R) a) = (rzero R) :=
  addCancelRight (rmul (rzero R) a) (rzero R) (rmul (rzero R) a)
    (eqTrans (eqSym ((fieldOf R).distribRight (rzero R) (rzero R) a))
      (eqTrans (eqCong (fun z => rmul z a) (addZeroLeft (rzero R)))
        (eqSym (addZeroLeft (rmul (rzero R) a)))))

-- TACTIC-MODE in source (erw).
def mulZeroRight {R : Real} (c : Carrier R) : (rmul c (rzero R)) = (rzero R) := sorry

def mulRealOfNat (R : Real) : (n m : MyNat) →
    (rmul (realOfNat R n) (realOfNat R m)) = (realOfNat R (mult n m))
  | .zero, m => mulZeroLeft (realOfNat R m)
  | .succ n, m =>
      eqTrans ((fieldOf R).distribRight (rone R) (realOfNat R n) (realOfNat R m))
        (eqTrans (eqCong (fun z => radd z (rmul (realOfNat R n) (realOfNat R m)))
            ((fieldOf R).mulOneLeft (realOfNat R m)))
          (eqTrans (eqCong (fun z => radd (realOfNat R m) z) (mulRealOfNat R n m))
            (addRealOfNat R m (mult n m))))

def oneNeZero (R : Real) (eq : (rone R) = (rzero R)) : MyVoid :=
  (fieldOf R).zeroNeOne (eqSym eq)

def invOne (R : Real) : (rinv (rone R)) = (rone R) :=
  eqTrans (eqSym ((fieldOf R).mulOneLeft (rinv (rone R))))
    ((fieldOf R).mulInvRight (rone R) (oneNeZero R))

def divOne {R : Real} (a : Carrier R) : (rdiv a (rone R)) = a :=
  eqTrans (eqCong (fun z => rmul a z) (invOne R)) ((fieldOf R).mulOneRight a)

def mulDivAssoc {R : Real} (a b c : Carrier R) :
    (rmul a (rdiv b c)) = (rdiv (rmul a b) c) :=
  eqSym ((fieldOf R).mulAssoc a b (rinv c))

def divMulRight {R : Real} (a b c : Carrier R) :
    (rmul (rdiv a b) c) = (rdiv (rmul a c) b) :=
  eqTrans ((fieldOf R).mulAssoc a (rinv b) c)
    (eqTrans (eqCong (fun z => rmul a z) ((fieldOf R).mulComm (rinv b) c))
      (eqSym ((fieldOf R).mulAssoc a c (rinv b))))

def realOfNatOne (R : Real) : (realOfNat R (.succ .zero)) = (rone R) :=
  (fieldOf R).addZeroRight (rone R)

def realOfIntOne (R : Real) : (realOfInt R (.intOfNat (.succ .zero))) = (rone R) :=
  realOfNatOne R

def realOfRatOne (R : Real) :
    (realOfRat R (.mkRat (.intOfNat (.succ .zero)) (.succ .zero) (.isSucc .zero))) = (rone R) :=
  realOfNatOne R

def realOfNatZero (R : Real) : (realOfNat R .zero) = (rzero R) := rfl

def realOfIntZero (R : Real) : (realOfInt R (.intOfNat .zero)) = (rzero R) := rfl

def realOfRatZero (R : Real) :
    (realOfRat R (.mkRat (.intOfNat .zero) (.succ .zero) (.isSucc .zero))) = (rzero R) := rfl

def rtwoAsRealOfRat (R : Real) :
    (rtwo R) = (realOfRat R (.mkRat (.intOfNat (.succ (.succ .zero))) (.succ .zero) (.isSucc .zero))) :=
  eqCong (fun z => radd (rone R) z) (eqSym ((fieldOf R).addZeroRight (rone R)))

def roneAsRealOfRat (R : Real) :
    (rone R) = (realOfRat R (.mkRat (.intOfNat (.succ .zero)) (.succ .zero) (.isSucc .zero))) :=
  eqSym (realOfRatOne R)

def rzeroAsRealOfRat (R : Real) :
    (rzero R) = (realOfRat R (.mkRat (.intOfNat .zero) (.succ .zero) (.isSucc .zero))) := rfl

-- TACTIC-MODE in source (constructor).
def zeroLtOne (R : Real) : rlt (rzero R) (rone R) := sorry

def realOfNatNonneg (R : Real) : (n : MyNat) → rle (rzero R) (realOfNat R n)
  | .zero => (fieldOf R).leRefl (rzero R)
  | .succ n =>
      replace (fun z => rle z (radd (rone R) (realOfNat R n)))
        ((fieldOf R).addZeroRight (rzero R))
        (addLeBoth (rzero R) (rone R) (rzero R) (realOfNat R n)
          ((fieldOf R).zeroLeOne) (realOfNatNonneg R n))

def oneLeRealOfNatSucc (R : Real) (n : MyNat) : rle (rone R) (realOfNat R (.succ n)) :=
  replace (fun z => rle z (radd (rone R) (realOfNat R n)))
    ((fieldOf R).addZeroRight (rone R))
    ((fieldOf R).addLeLeft (rzero R) (realOfNat R n) (rone R)
      (realOfNatNonneg R n))

def realOfNatSuccPos (R : Real) (n : MyNat) : rlt (rzero R) (realOfNat R (.succ n)) :=
  ltLeTrans (rzero R) (rone R) (realOfNat R (.succ n)) (zeroLtOne R) (oneLeRealOfNatSucc R n)

def realOfNatSuccNeZero (R : Real) (n : MyNat) (eq : (realOfNat R (.succ n)) = (rzero R)) :
    MyVoid :=
  Pair.snd (realOfNatSuccPos R n) (eqSym eq)

-- TACTIC-MODE in source (apply / erw).
def mulNeZero {R : Real} (a b : Carrier R) (ane : a = (rzero R) → MyVoid)
    (bne : b = (rzero R) → MyVoid) (eq : (rmul a b) = (rzero R)) : MyVoid := sorry

-- TACTIC-MODE in source (erw).
def mulInvMulInv {R : Real} (a b : Carrier R) (ane : a = (rzero R) → MyVoid)
    (bne : b = (rzero R) → MyVoid) :
    (rmul (rmul a b) (rmul (rinv a) (rinv b))) = (rone R) := sorry

-- TACTIC-MODE in source (erw).
def invMul {R : Real} (a b : Carrier R) (ane : a = (rzero R) → MyVoid)
    (bne : b = (rzero R) → MyVoid) :
    (rinv (rmul a b)) = (rmul (rinv a) (rinv b)) := sorry

-- TACTIC-MODE in source (erw).
def mulDivDiv {R : Real} (a b c d : Carrier R) (bne : b = (rzero R) → MyVoid)
    (dne : d = (rzero R) → MyVoid) :
    (rmul (rdiv a b) (rdiv c d)) = (rdiv (rmul a c) (rmul b d)) := sorry

def divCancel {R : Real} (a e : Carrier R) (ene : e = (rzero R) → MyVoid) :
    (rdiv (rmul a e) e) = a :=
  eqTrans ((fieldOf R).mulAssoc a e (rinv e))
    (eqTrans (eqCong (fun z => rmul a z) ((fieldOf R).mulInvRight e ene))
      ((fieldOf R).mulOneRight a))

def addDivSame {R : Real} (x y e : Carrier R) :
    (radd (rdiv x e) (rdiv y e)) = (rdiv (radd x y) e) :=
  eqSym ((fieldOf R).distribRight x y (rinv e))

def divDenomExpand {R : Real} (x b d : Carrier R) (bne : b = (rzero R) → MyVoid)
    (dne : d = (rzero R) → MyVoid) :
    (rdiv x b) = (rdiv (rmul x d) (rmul b d)) :=
  eqTrans (eqSym ((fieldOf R).mulOneRight (rdiv x b)))
    (eqTrans (eqCong (fun z => rmul (rdiv x b) z)
        (eqSym ((fieldOf R).mulInvRight d dne)))
      (mulDivDiv x b d d bne dne))

def addDivDiv {R : Real} (x b y d : Carrier R) (bne : b = (rzero R) → MyVoid)
    (dne : d = (rzero R) → MyVoid) :
    (radd (rdiv x b) (rdiv y d)) = (rdiv (radd (rmul x d) (rmul y b)) (rmul b d)) :=
  eqTrans (eqCong (fun z => radd z (rdiv y d)) (divDenomExpand x b d bne dne))
    (eqTrans (eqCong (fun z => radd (rdiv (rmul x d) (rmul b d)) z)
        (eqTrans (divDenomExpand y d b dne bne)
          (eqCong (fun w => rdiv (rmul y b) w) ((fieldOf R).mulComm d b))))
      (addDivSame (rmul x d) (rmul y b) (rmul b d)))

def addCommonDenom {R : Real} (a c e : Carrier R) (ene : e = (rzero R) → MyVoid) :
    (radd a (rdiv c e)) = (rdiv (radd (rmul a e) c) e) :=
  eqTrans (eqCong (fun z => radd z (rdiv c e)) (eqSym (divCancel a e ene)))
    (addDivSame (rmul a e) c e)

def addCommonDenomLeft {R : Real} (a c e : Carrier R) (ene : e = (rzero R) → MyVoid) :
    (radd (rdiv a e) c) = (rdiv (radd a (rmul c e)) e) :=
  eqTrans (eqCong (fun z => radd (rdiv a e) z) (eqSym (divCancel c e ene)))
    (addDivSame a (rmul c e) e)

def mulNegRight {R : Real} (c b : Carrier R) : (rmul c (rneg b)) = (rneg (rmul c b)) :=
  negUnique (rmul c b) (rmul c (rneg b))
    (eqTrans (eqSym ((fieldOf R).distribLeft c b (rneg b)))
      (eqTrans (eqCong (fun z => rmul c z) ((fieldOf R).negRight b))
        (mulZeroRight c)))

-- TACTIC-MODE in source (erw).
def mulNegLeft {R : Real} (a b : Carrier R) : (rmul (rneg a) b) = (rneg (rmul a b)) := sorry

def negDivLeft {R : Real} (y e : Carrier R) : (rneg (rdiv y e)) = (rdiv (rneg y) e) :=
  eqSym (mulNegLeft y (rinv e))

def subDivSame {R : Real} (x y e : Carrier R) :
    (rsub (rdiv x e) (rdiv y e)) = (rdiv (rsub x y) e) :=
  eqTrans (eqCong (fun z => radd (rdiv x e) z) (negDivLeft y e)) (addDivSame x (rneg y) e)

def subCommonDenom {R : Real} (a c e : Carrier R) (ene : e = (rzero R) → MyVoid) :
    (rsub a (rdiv c e)) = (rdiv (rsub (rmul a e) c) e) :=
  eqTrans (eqCong (fun z => radd a z) (negDivLeft c e)) (addCommonDenom a (rneg c) e ene)

def subCommonDenomLeft {R : Real} (a c e : Carrier R) (ene : e = (rzero R) → MyVoid) :
    (rsub (rdiv a e) c) = (rdiv (rsub a (rmul c e)) e) :=
  eqTrans (addCommonDenomLeft a (rneg c) e ene)
    (eqCong (fun z => rdiv (radd a z) e) (mulNegLeft c e))

def subDivDiv {R : Real} (x b y d : Carrier R) (bne : b = (rzero R) → MyVoid)
    (dne : d = (rzero R) → MyVoid) :
    (rsub (rdiv x b) (rdiv y d)) = (rdiv (rsub (rmul x d) (rmul y b)) (rmul b d)) :=
  eqTrans (eqCong (fun z => radd (rdiv x b) z) (negDivLeft y d))
    (eqTrans (addDivDiv x b (rneg y) d bne dne)
      (eqCong (fun z => rdiv (radd (rmul x d) z) (rmul b d)) (mulNegLeft y b)))

------------------------------------------------------------
-- Absolute value properties (derived from leTotal)
------------------------------------------------------------

def absNonneg {R : Real} (a : Carrier R) : rle (rzero R) (rabs a) :=
  absElim a (fun x => rle (rzero R) x) (fun h => h) (fun h => leNegNonneg a h)

def absZero (R : Real) : (rabs (rzero R)) = (rzero R) :=
  absElim (rzero R) (fun x => x = (rzero R)) (fun _ => rfl) (fun _ => negZero R)

def absEqZero {R : Real} (a : Carrier R) (h : (rabs a) = (rzero R)) : a = (rzero R) :=
  absElim a (fun x => x = (rzero R) → a = (rzero R))
    (fun _ eq => eq)
    (fun _ eq => eqTrans (eqSym (negNeg a))
      (eqTrans (eqCong (fun z => rneg z) eq) (negZero R))) h

def leAbs {R : Real} (a : Carrier R) : rle a (rabs a) :=
  absElim a (fun x => rle a x) (fun _ => (fieldOf R).leRefl a)
    (fun h => (fieldOf R).leTrans a (rzero R) (rneg a) h (leNegNonneg a h))

def leAbsNeg {R : Real} (a : Carrier R) : rle (rneg a) (rabs a) :=
  absElim a (fun x => rle (rneg a) x)
    (fun h => (fieldOf R).leTrans (rneg a) (rzero R) a (negNonpos a h) h)
    (fun _ => (fieldOf R).leRefl (rneg a))

def absTriangle {R : Real} (a b : Carrier R) :
    rle (rabs (radd a b)) (radd (rabs a) (rabs b)) :=
  absElim (radd a b) (fun x => rle x (radd (rabs a) (rabs b)))
    (fun _ => addLeBoth a (rabs a) b (rabs b) (leAbs a) (leAbs b))
    (fun _ => replace (fun z => rle z (radd (rabs a) (rabs b))) (eqSym (negAdd a b))
      (addLeBoth (rneg a) (rabs a) (rneg b) (rabs b) (leAbsNeg a) (leAbsNeg b)))

def absOfNonneg {R : Real} (a : Carrier R) (h : rle (rzero R) a) : (rabs a) = a :=
  absElim a (fun x => x = a) (fun _ => rfl)
    (fun h2 => eqTrans (eqCong (fun z => rneg z)
        (eqSym ((fieldOf R).leAntisym (rzero R) a h h2)))
      (eqTrans (negZero R) ((fieldOf R).leAntisym (rzero R) a h h2)))

def absOfNonpos {R : Real} (a : Carrier R) (h : rle a (rzero R)) : (rabs a) = (rneg a) := sorry

def negMulNeg {R : Real} (a b : Carrier R) : (rmul (rneg a) (rneg b)) = (rmul a b) :=
  eqTrans (mulNegLeft a (rneg b))
    (eqTrans (eqCong (fun z => rneg z) (mulNegRight a b)) (negNeg (rmul a b)))

def mulNonnegNonpos {R : Real} (a b : Carrier R) (ha : rle (rzero R) a) (hb : rle b (rzero R)) :
    rle (rmul a b) (rzero R) :=
  replace (fun z => rle z (rzero R)) (negNeg (rmul a b))
    (negNonpos (rneg (rmul a b))
      (replace (fun z => rle (rzero R) z) (mulNegRight a b)
        ((fieldOf R).mulNonneg a (rneg b) ha (leNegNonneg b hb))))

def mulNegNeg {R : Real} (a b : Carrier R) (ha : rle a (rzero R)) (hb : rle b (rzero R)) :
    rle (rzero R) (rmul a b) :=
  replace (fun z => rle (rzero R) z) (negMulNeg a b)
    ((fieldOf R).mulNonneg (rneg a) (rneg b)
      (leNegNonneg a ha) (leNegNonneg b hb))

def absMul {R : Real} (a b : Carrier R) :
    (rabs (rmul a b)) = (rmul (rabs a) (rabs b)) :=
  absElim a (fun va => (rabs (rmul a b)) = (rmul va (rabs b)))
    (fun ha => absElim b (fun vb => (rabs (rmul a b)) = (rmul a vb))
      (fun hb => absOfNonneg (rmul a b) ((fieldOf R).mulNonneg a b ha hb))
      (fun hb => eqTrans (absOfNonpos (rmul a b) (mulNonnegNonpos a b ha hb))
        (eqSym (mulNegRight a b))))
    (fun ha => absElim b (fun vb => (rabs (rmul a b)) = (rmul (rneg a) vb))
      (fun hb => eqTrans (absOfNonpos (rmul a b)
          (replace (fun z => rle z (rzero R)) ((fieldOf R).mulComm b a)
            (mulNonnegNonpos b a hb ha)))
        (eqSym (mulNegLeft a b)))
      (fun hb => eqTrans (absOfNonneg (rmul a b) (mulNegNeg a b ha hb))
        (eqSym (negMulNeg a b))))

------------------------------------------------------------
-- THE THEOREM: lim(f) + lim(g) = lim(f + g)
------------------------------------------------------------

def coreEstimate {R : Real} (f g : Carrier R → Carrier R) (x0 L M he x : Carrier R)
    (hfx : rlt (rabs (rsub (f x) L)) he) (hgx : rlt (rabs (rsub (g x) M)) he) :
    rlt (rabs (rsub (radd (f x) (g x)) (radd L M))) (radd he he) :=
  leLtTrans (rabs (rsub (radd (f x) (g x)) (radd L M)))
    (radd (rabs (rsub (f x) L)) (rabs (rsub (g x) M))) (radd he he)
    (replace (fun z => rle (rabs z) (radd (rabs (rsub (f x) L)) (rabs (rsub (g x) M))))
      (eqSym (subAddSub (f x) (g x) L M))
      (absTriangle (rsub (f x) L) (rsub (g x) M)))
    (addLtBoth (rabs (rsub (f x) L)) he (rabs (rsub (g x) M)) he hfx hgx)

def halfEqDiv {R : Real} (e : Carrier R) : (rmul (rhalf R) e) = (rdiv e (rtwo R)) :=
  (fieldOf R).mulComm (rhalf R) e

def divTwoPos {R : Real} (e : Carrier R) (hlt : rlt (rzero R) e) :
    rlt (rzero R) (rdiv e (rtwo R)) :=
  replace (fun z => rlt (rzero R) z) (halfEqDiv e) (halfMulEpsPos e hlt)

def divTwoAddEq {R : Real} (e : Carrier R) :
    (radd (rdiv e (rtwo R)) (rdiv e (rtwo R))) = e :=
  replace (fun z => (radd z z) = e) (halfEqDiv e) (halfMulEps e)

def convertEps {R : Real} (epsilon v : Carrier R)
    (hlt : rlt v (radd (rdiv epsilon (rtwo R)) (rdiv epsilon (rtwo R)))) : rlt v epsilon :=
  replace (fun z => rlt v z) (divTwoAddEq epsilon) hlt

-- TACTIC-MODE in source (constructor / intros / cases). Statement kept faithful.
def limitAdd {R : Real} (f g : Carrier R → Carrier R) (x0 L M : Carrier R)
    (limF : Limit f x0 L) (limG : Limit g x0 M) :
    Limit (fun x => radd (f x) (g x)) x0 (radd L M) := sorry

def limitAdd3 {R : Real} (f g h : Carrier R → Carrier R) (x0 L M N : Carrier R)
    (limF : Limit f x0 L) (limG : Limit g x0 M) (limH : Limit h x0 N) :
    Limit (fun x => radd (radd (f x) (g x)) (h x)) x0 (radd (radd L M) N) :=
  limitAdd (fun x => radd (f x) (g x)) h x0 (radd L M) N (limitAdd f g x0 L M limF limG) limH

------------------------------------------------------------
-- The lim operator: projecting the limit value
------------------------------------------------------------

def subSelf {R : Real} (a : Carrier R) : (rsub a a) = (rzero R) :=
  (fieldOf R).negRight a

-- TACTIC-MODE in source (constructor). Statement kept faithful.
def limitConst {R : Real} (k x0 : Carrier R) : Limit (fun _ => k) x0 k := sorry

@[reducible] def lim {R : Real} {L : Carrier R} (_f : Carrier R → Carrier R)
    (_x0 : Carrier R) (_pf : Limit _f _x0 L) : Carrier R := L

def limit_pull_radd {R : Real} (f g : Carrier R → Carrier R) (x0 Lf Lg : Carrier R)
    (limF : Limit f x0 Lf) (limG : Limit g x0 Lg) :
    (radd (lim f x0 limF) (lim g x0 limG)) = (lim (fun x => radd (f x) (g x)) x0 (limitAdd f g x0 Lf Lg limF limG)) := rfl

def limit_pull_radd3 {R : Real} (f g h : Carrier R → Carrier R) (x0 Lf Lg Lh : Carrier R)
    (limF : Limit f x0 Lf) (limG : Limit g x0 Lg) (limH : Limit h x0 Lh) :
    (radd (radd (lim f x0 limF) (lim g x0 limG)) (lim h x0 limH)) = (lim (fun x => radd (radd (f x) (g x)) (h x)) x0
        (limitAdd3 f g h x0 Lf Lg Lh limF limG limH)) := rfl

def lim_const {R : Real} (k x0 : Carrier R) :
    k = (lim (fun _ => k) x0 (limitConst k x0)) := rfl

def limit_pull_const_add {R : Real} (k : Carrier R) (f : Carrier R → Carrier R)
    (x0 Lf : Carrier R) (limF : Limit f x0 Lf) :
    (radd k (lim f x0 limF)) = (lim (fun x => radd k (f x)) x0 (limitAdd (fun _ => k) f x0 k Lf (limitConst k x0) limF)) :=
  rfl

------------------------------------------------------------
-- DERIVATIVES
------------------------------------------------------------

def diffQuot {R : Real} (f : Carrier R → Carrier R) (x0 x : Carrier R) : Carrier R :=
  rmul (rsub (f x) (f x0)) (rinv (rsub x x0))

@[reducible] def HasDerivative {R : Real} (f : Carrier R → Carrier R) (x0 L : Carrier R) : Type :=
  Limit (diffQuot f x0) x0 L

@[reducible] def deriv {R : Real} {L : Carrier R} (_f : Carrier R → Carrier R)
    (_x0 : Carrier R) (_hf : HasDerivative _f _x0 L) : Carrier R := L

-- TACTIC-MODE in source (constructor). Statement kept faithful.
def limitExt {R : Real} (f g : Carrier R → Carrier R) (x0 L : Carrier R)
    (ext : (x : Carrier R) → (f x) = (g x)) (limF : Limit f x0 L) : Limit g x0 L := sorry

-- TACTIC-MODE in source (erw). Statement kept faithful.
def diffQuotAddEq {R : Real} (f g : Carrier R → Carrier R) (x0 x : Carrier R) :
    (radd (diffQuot f x0 x) (diffQuot g x0 x)) = (diffQuot (fun y => radd (f y) (g y)) x0 x) := sorry

def derivAdd {R : Real} (f g : Carrier R → Carrier R) (x0 L M : Carrier R)
    (hf : HasDerivative f x0 L) (hg : HasDerivative g x0 M) :
    HasDerivative (fun x => radd (f x) (g x)) x0 (radd L M) :=
  limitExt (fun x => radd (diffQuot f x0 x) (diffQuot g x0 x))
    (diffQuot (fun y => radd (f y) (g y)) x0) x0 (radd L M)
    (diffQuotAddEq f g x0)
    (limitAdd (diffQuot f x0) (diffQuot g x0) x0 L M hf hg)

------------------------------------------------------------
-- SCALAR MULTIPLICATION OF LIMITS AND DERIVATIVES
------------------------------------------------------------

-- TACTIC-MODE in source (erw).
def mulSubDistrib {R : Real} (c a b : Carrier R) :
    (rmul c (rsub a b)) = (rsub (rmul c a) (rmul c b)) := sorry

-- TACTIC-MODE in source (erw).
def diffQuotScalarEq {R : Real} (c : Carrier R) (f : Carrier R → Carrier R) (x0 x : Carrier R) :
    (rmul c (diffQuot f x0 x)) = (diffQuot (fun y => rmul c (f y)) x0 x) := sorry

------------------------------------------------------------
-- Infrastructure: abs, ordering, and multiplication lemmas
------------------------------------------------------------

-- TACTIC-MODE in source (erw).
def subCancel {R : Real} (a b : Carrier R) : (radd (rsub a b) b) = a := sorry

-- TACTIC-MODE in source (constructor).
def absPos {R : Real} (c : Carrier R) (hne : c = (rzero R) → MyVoid) :
    rlt (rzero R) (rabs c) := sorry

-- TACTIC-MODE in source (rewrite). Statement kept faithful.
def leToSubNonneg {R : Real} (a b : Carrier R) (hab : rle a b) : rle (rzero R) (rsub b a) := sorry

def mulLeLeft {R : Real} (c a b : Carrier R) (hc : rle (rzero R) c) (hab : rle a b) :
    rle (rmul c a) (rmul c b) :=
  replace (fun z => rle (rmul c a) z) (subCancel (rmul c b) (rmul c a))
    (replace (fun z => rle (rmul c a) (radd z (rmul c a))) (mulSubDistrib c b a)
      (replace (fun z => rle z (radd (rmul c (rsub b a)) (rmul c a))) (addZeroLeft (rmul c a))
        (addLeRight (rzero R) (rmul c (rsub b a)) (rmul c a)
          ((fieldOf R).mulNonneg c (rsub b a) hc (leToSubNonneg a b hab)))))

def oneLeAbsPlusOne {R : Real} (c : Carrier R) :
    rle (rone R) (radd (rabs c) (rone R)) :=
  replace (fun z => rle (rone R) z) ((fieldOf R).addComm (rone R) (rabs c))
    (replace (fun z => rle z (radd (rone R) (rabs c)))
      ((fieldOf R).addZeroRight (rone R))
      ((fieldOf R).addLeLeft (rzero R) (rabs c) (rone R) (absNonneg c)))

def absPlusOnePos {R : Real} (c : Carrier R) : rlt (rzero R) (radd (rabs c) (rone R)) :=
  ltLeTrans (rzero R) (rone R) (radd (rabs c) (rone R)) (zeroLtOne R) (oneLeAbsPlusOne c)

def absPlusOneNe {R : Real} (c : Carrier R) (heq : (radd (rabs c) (rone R)) = (rzero R)) :
    MyVoid :=
  Pair.snd (absPlusOnePos c) (eqSym heq)

-- TACTIC-MODE in source (erw).
def mulLtLeftNe {R : Real} (c a b : Carrier R) (hc : rle (rzero R) c)
    (hcne : c = (rzero R) → MyVoid) (hab : rle a b) (heq : (rmul c a) = (rmul c b)) :
    a = b := sorry

-- TACTIC-MODE in source (constructor).
def mulLtLeft {R : Real} (c a b : Carrier R) (hc : rlt (rzero R) c) (hab : rlt a b) :
    rlt (rmul c a) (rmul c b) := sorry

def mulLeRight {R : Real} (a b c : Carrier R) (hab : rle a b) (hc : rle (rzero R) c) :
    rle (rmul a c) (rmul b c) :=
  replace (fun z => rle z (rmul b c)) ((fieldOf R).mulComm c a)
    (replace (fun z => rle (rmul c a) z) ((fieldOf R).mulComm c b)
      (mulLeLeft c a b hc hab))

def absLeAbsPlusOne {R : Real} (c : Carrier R) : rle (rabs c) (radd (rabs c) (rone R)) :=
  replace (fun z => rle z (radd (rabs c) (rone R)))
    ((fieldOf R).addZeroRight (rabs c))
    ((fieldOf R).addLeLeft (rzero R) (rone R) (rabs c)
      ((fieldOf R).zeroLeOne))

-- TACTIC-MODE in source (erw).
def mulInvCancel {R : Real} (M a : Carrier R) (hne : M = (rzero R) → MyVoid) :
    (rmul M (rmul a (rinv M))) = a := sorry

-- TACTIC-MODE in source (constructor).
def epsOverMPos {R : Real} (eps M : Carrier R) (heps : rlt (rzero R) eps)
    (hM : rlt (rzero R) M) : rlt (rzero R) (rmul eps (rinv M)) := sorry

------------------------------------------------------------
-- Scalar multiplication of limits (proved)
------------------------------------------------------------

def scalarAbsBound {R : Real} (c a b : Carrier R) :
    rle (rabs (rsub (rmul c a) (rmul c b))) (rmul (radd (rabs c) (rone R)) (rabs (rsub a b))) :=
  replace (fun z => rle (rabs z) (rmul (radd (rabs c) (rone R)) (rabs (rsub a b))))
    (mulSubDistrib c a b)
    (replace (fun z => rle z (rmul (radd (rabs c) (rone R)) (rabs (rsub a b))))
      (eqSym (absMul c (rsub a b)))
      (mulLeRight (rabs c) (radd (rabs c) (rone R)) (rabs (rsub a b))
        (absLeAbsPlusOne c) (absNonneg (rsub a b))))

-- TACTIC-MODE in source (constructor). Statement kept faithful.
def limitScalarAll {R : Real} (c : Carrier R) (h : Carrier R → Carrier R) (x0 L : Carrier R)
    (limH : Limit h x0 L) : Limit (fun x => rmul c (h x)) x0 (rmul c L) := sorry

def limitScalar {R : Real} (c : Carrier R) (_hcnz : c = (rzero R) → MyVoid)
    (f : Carrier R → Carrier R) (x0 L : Carrier R) (limF : Limit f x0 L) :
    Limit (fun x => rmul c (f x)) x0 (rmul c L) :=
  limitScalarAll c f x0 L limF

def derivScalar {R : Real} (c : Carrier R) (hcnz : c = (rzero R) → MyVoid)
    (f : Carrier R → Carrier R) (x0 L : Carrier R) (hf : HasDerivative f x0 L) :
    HasDerivative (fun x => rmul c (f x)) x0 (rmul c L) :=
  limitExt (fun x => rmul c (diffQuot f x0 x)) (diffQuot (fun y => rmul c (f y)) x0) x0 (rmul c L)
    (diffQuotScalarEq c f x0) (limitScalar c hcnz (diffQuot f x0) x0 L hf)

------------------------------------------------------------
-- Infrastructure for the chain rule
------------------------------------------------------------

-- TACTIC-MODE in source (erw).
def subZeroRight {R : Real} (a : Carrier R) : (rsub a (rzero R)) = a := sorry

------------------------------------------------------------
-- Int -> Real arithmetic homomorphisms
------------------------------------------------------------

-- TACTIC-MODE in source (erw).
def subSuccSucc {R : Real} (a b : Carrier R) :
    (rsub a b) = (rsub (radd (rone R) a) (radd (rone R) b)) := sorry

def subNatNatLemma (R : Real) : (m n : MyNat) →
    (realOfInt R (subNatNat m n)) = (rsub (realOfNat R m) (realOfNat R n))
  | .zero, .zero => eqSym (subZeroRight (rzero R))
  | .succ m, .zero => eqSym (subZeroRight (realOfNat R (.succ m)))
  | .zero, .succ n => eqSym (addZeroLeft (rneg (radd (rone R) (realOfNat R n))))
  | .succ m, .succ n =>
      eqTrans (subNatNatLemma R m n) (subSuccSucc (realOfNat R m) (realOfNat R n))

def addRealOfInt (R : Real) : (a b : MyInt) →
    (radd (realOfInt R a) (realOfInt R b)) = (realOfInt R (intAdd a b))
  | .intOfNat m, .intOfNat n => addRealOfNat R m n
  | .intOfNat m, .intNegSucc n => eqSym (subNatNatLemma R m (.succ n))
  | .intNegSucc m, .intOfNat n =>
      eqTrans ((fieldOf R).addComm
          (rneg (radd (rone R) (realOfNat R m))) (realOfNat R n))
        (eqSym (subNatNatLemma R n (.succ m)))
  | .intNegSucc m, .intNegSucc n =>
      eqTrans (eqSym (negAdd (radd (rone R) (realOfNat R m)) (radd (rone R) (realOfNat R n))))
        (eqCong rneg (addOnePlusOneShuffle R m n))

def subRealOfInt (R : Real) (a c : MyInt) :
    (rsub (realOfInt R a) (realOfInt R c)) = (realOfInt R (intSub a c)) :=
  eqTrans (eqCong (fun z => radd (realOfInt R a) z) (negRealOfInt R c))
    (addRealOfInt R a (intNeg c))

def negOfNatLemma (R : Real) : (k : MyNat) →
    (rneg (realOfNat R k)) = (realOfInt R (negOfNat k))
  | .zero => negZero R
  | .succ _ => rfl

def mulRealOfInt (R : Real) : (a b : MyInt) →
    (rmul (realOfInt R a) (realOfInt R b)) = (realOfInt R (intMul a b))
  | .intOfNat m, .intOfNat n => mulRealOfNat R m n
  | .intOfNat m, .intNegSucc n =>
      eqTrans (mulNegRight (realOfNat R m) (radd (rone R) (realOfNat R n)))
        (eqTrans (eqCong rneg (mulRealOfNat R m (.succ n)))
          (negOfNatLemma R (mult m (.succ n))))
  | .intNegSucc m, .intOfNat n =>
      eqTrans (mulNegLeft (radd (rone R) (realOfNat R m)) (realOfNat R n))
        (eqTrans (eqCong rneg (mulRealOfNat R (.succ m) n))
          (negOfNatLemma R (mult (.succ m) n)))
  | .intNegSucc m, .intNegSucc n =>
      eqTrans (negMulNeg (radd (rone R) (realOfNat R m)) (radd (rone R) (realOfNat R n)))
        (mulRealOfNat R (.succ m) (.succ n))

def plusZeroRight : (n : MyNat) → (plus n .zero) = n
  | .zero => rfl
  | .succ k => eqCong MyNat.succ (plusZeroRight k)

def multOneRight : (n : MyNat) → (mult n (.succ .zero)) = n
  | .zero => rfl
  | .succ k => eqCong MyNat.succ (multOneRight k)

def intMulOneRight : (a : MyInt) → (intMul a (.intOfNat (.succ .zero))) = a
  | .intOfNat m => eqCong MyInt.intOfNat (multOneRight m)
  | .intNegSucc m => eqCong MyInt.intNegSucc (multOneRight m)

def mulRealOfRat (R : Real) : (a b : MyRat) →
    (rmul (realOfRat R a) (realOfRat R b)) = (realOfRat R (ratMult a b))
  | .mkRat a (.succ .zero) _, .mkRat c (.succ .zero) _ => mulRealOfInt R a c
  | .mkRat a (.succ .zero) _, .mkRat c (.succ (.succ d1)) _ =>
      eqTrans (mulDivAssoc (realOfInt R a) (realOfInt R c) (realOfNat R (.succ (.succ d1))))
        (eqTrans (eqCong (fun z => rdiv z (realOfNat R (.succ (.succ d1)))) (mulRealOfInt R a c))
          (eqCong (fun z => rdiv (realOfInt R (intMul a c)) (realOfNat R (.succ (.succ z))))
            (eqSym (plusZeroRight d1))))
  | .mkRat a (.succ (.succ b1)) _, .mkRat c (.succ .zero) _ =>
      eqTrans (divMulRight (realOfInt R a) (realOfNat R (.succ (.succ b1))) (realOfInt R c))
        (eqTrans (eqCong (fun z => rdiv z (realOfNat R (.succ (.succ b1)))) (mulRealOfInt R a c))
          (eqCong (fun z => rdiv (realOfInt R (intMul a c)) (realOfNat R (.succ (.succ z))))
            (eqSym (multOneRight b1))))
  | .mkRat a (.succ (.succ b1)) _, .mkRat c (.succ (.succ d1)) _ =>
      eqTrans (mulDivDiv (realOfInt R a) (realOfNat R (.succ (.succ b1))) (realOfInt R c)
          (realOfNat R (.succ (.succ d1)))
          (realOfNatSuccNeZero R (.succ b1)) (realOfNatSuccNeZero R (.succ d1)))
        (eqTrans (eqCong (fun z => rdiv z (rmul (realOfNat R (.succ (.succ b1)))
              (realOfNat R (.succ (.succ d1))))) (mulRealOfInt R a c))
          (eqCong (fun z => rdiv (realOfInt R (intMul a c)) z)
            (mulRealOfNat R (.succ (.succ b1)) (.succ (.succ d1)))))

def addRealOfRat (R : Real) : (a b : MyRat) →
    (radd (realOfRat R a) (realOfRat R b)) = (realOfRat R (ratPlus a b))
  | .mkRat a (.succ .zero) _, .mkRat c (.succ .zero) _ =>
      eqTrans (addRealOfInt R a c)
        (eqCong (realOfInt R)
          (eqTrans (eqCong (fun z => intAdd z c) (eqSym (intMulOneRight a)))
            (eqCong (fun z => intAdd (intMul a (.intOfNat (.succ .zero))) z)
              (eqSym (intMulOneRight c)))))
  | .mkRat a (.succ .zero) _, .mkRat c (.succ (.succ d1)) _ =>
      eqTrans (addCommonDenom (realOfInt R a) (realOfInt R c) (realOfNat R (.succ (.succ d1)))
          (realOfNatSuccNeZero R (.succ d1)))
        (eqTrans (eqCong (fun z => rdiv z (realOfNat R (.succ (.succ d1))))
            (eqTrans (eqCong (fun z => radd z (realOfInt R c))
                (mulRealOfInt R a (.intOfNat (.succ (.succ d1)))))
              (eqTrans (addRealOfInt R (intMul a (.intOfNat (.succ (.succ d1)))) c)
                (eqCong (fun z => realOfInt R (intAdd (intMul a (.intOfNat (.succ (.succ d1)))) z))
                  (eqSym (intMulOneRight c))))))
          (eqCong (fun z => rdiv (realOfInt R (intAdd (intMul a (.intOfNat (.succ (.succ d1))))
              (intMul c (.intOfNat (.succ .zero))))) (realOfNat R (.succ (.succ z))))
            (eqSym (plusZeroRight d1))))
  | .mkRat a (.succ (.succ b1)) _, .mkRat c (.succ .zero) _ =>
      eqTrans (addCommonDenomLeft (realOfInt R a) (realOfInt R c) (realOfNat R (.succ (.succ b1)))
          (realOfNatSuccNeZero R (.succ b1)))
        (eqTrans (eqCong (fun z => rdiv z (realOfNat R (.succ (.succ b1))))
            (eqTrans (eqCong (fun z => radd (realOfInt R a) z)
                (mulRealOfInt R c (.intOfNat (.succ (.succ b1)))))
              (eqTrans (addRealOfInt R a (intMul c (.intOfNat (.succ (.succ b1)))))
                (eqCong (fun z => realOfInt R (intAdd z (intMul c (.intOfNat (.succ (.succ b1))))))
                  (eqSym (intMulOneRight a))))))
          (eqCong (fun z => rdiv (realOfInt R (intAdd (intMul a (.intOfNat (.succ .zero)))
              (intMul c (.intOfNat (.succ (.succ b1)))))) (realOfNat R (.succ (.succ z))))
            (eqSym (multOneRight b1))))
  | .mkRat a (.succ (.succ b1)) _, .mkRat c (.succ (.succ d1)) _ =>
      eqTrans (addDivDiv (realOfInt R a) (realOfNat R (.succ (.succ b1))) (realOfInt R c)
          (realOfNat R (.succ (.succ d1)))
          (realOfNatSuccNeZero R (.succ b1)) (realOfNatSuccNeZero R (.succ d1)))
        (eqTrans (eqCong (fun z => rdiv z (rmul (realOfNat R (.succ (.succ b1)))
              (realOfNat R (.succ (.succ d1)))))
            (eqTrans (eqCong (fun z => radd z (rmul (realOfInt R c) (realOfNat R (.succ (.succ b1)))))
                (mulRealOfInt R a (.intOfNat (.succ (.succ d1)))))
              (eqTrans (eqCong (fun z => radd (realOfInt R (intMul a (.intOfNat (.succ (.succ d1)))))
                    z) (mulRealOfInt R c (.intOfNat (.succ (.succ b1)))))
                (addRealOfInt R (intMul a (.intOfNat (.succ (.succ d1))))
                  (intMul c (.intOfNat (.succ (.succ b1))))))))
          (eqCong (fun z => rdiv (realOfInt R (intAdd (intMul a (.intOfNat (.succ (.succ d1))))
              (intMul c (.intOfNat (.succ (.succ b1)))))) z)
            (mulRealOfNat R (.succ (.succ b1)) (.succ (.succ d1)))))

def subRealOfRat (R : Real) : (a b : MyRat) →
    (rsub (realOfRat R a) (realOfRat R b)) = (realOfRat R (ratSub a b))
  | .mkRat a (.succ .zero) _, .mkRat c (.succ .zero) _ =>
      eqTrans (subRealOfInt R a c)
        (eqCong (realOfInt R)
          (eqTrans (eqCong (fun z => intSub z c) (eqSym (intMulOneRight a)))
            (eqCong (fun z => intSub (intMul a (.intOfNat (.succ .zero))) z)
              (eqSym (intMulOneRight c)))))
  | .mkRat a (.succ .zero) _, .mkRat c (.succ (.succ d1)) _ =>
      eqTrans (subCommonDenom (realOfInt R a) (realOfInt R c) (realOfNat R (.succ (.succ d1)))
          (realOfNatSuccNeZero R (.succ d1)))
        (eqTrans (eqCong (fun z => rdiv z (realOfNat R (.succ (.succ d1))))
            (eqTrans (eqCong (fun z => rsub z (realOfInt R c))
                (mulRealOfInt R a (.intOfNat (.succ (.succ d1)))))
              (eqTrans (subRealOfInt R (intMul a (.intOfNat (.succ (.succ d1)))) c)
                (eqCong (fun z => realOfInt R (intSub (intMul a (.intOfNat (.succ (.succ d1)))) z))
                  (eqSym (intMulOneRight c))))))
          (eqCong (fun z => rdiv (realOfInt R (intSub (intMul a (.intOfNat (.succ (.succ d1))))
              (intMul c (.intOfNat (.succ .zero))))) (realOfNat R (.succ (.succ z))))
            (eqSym (plusZeroRight d1))))
  | .mkRat a (.succ (.succ b1)) _, .mkRat c (.succ .zero) _ =>
      eqTrans (subCommonDenomLeft (realOfInt R a) (realOfInt R c) (realOfNat R (.succ (.succ b1)))
          (realOfNatSuccNeZero R (.succ b1)))
        (eqTrans (eqCong (fun z => rdiv z (realOfNat R (.succ (.succ b1))))
            (eqTrans (eqCong (fun z => rsub (realOfInt R a) z)
                (mulRealOfInt R c (.intOfNat (.succ (.succ b1)))))
              (eqTrans (subRealOfInt R a (intMul c (.intOfNat (.succ (.succ b1)))))
                (eqCong (fun z => realOfInt R (intSub z (intMul c (.intOfNat (.succ (.succ b1))))))
                  (eqSym (intMulOneRight a))))))
          (eqCong (fun z => rdiv (realOfInt R (intSub (intMul a (.intOfNat (.succ .zero)))
              (intMul c (.intOfNat (.succ (.succ b1)))))) (realOfNat R (.succ (.succ z))))
            (eqSym (multOneRight b1))))
  | .mkRat a (.succ (.succ b1)) _, .mkRat c (.succ (.succ d1)) _ =>
      eqTrans (subDivDiv (realOfInt R a) (realOfNat R (.succ (.succ b1))) (realOfInt R c)
          (realOfNat R (.succ (.succ d1)))
          (realOfNatSuccNeZero R (.succ b1)) (realOfNatSuccNeZero R (.succ d1)))
        (eqTrans (eqCong (fun z => rdiv z (rmul (realOfNat R (.succ (.succ b1)))
              (realOfNat R (.succ (.succ d1)))))
            (eqTrans (eqCong (fun z => rsub z (rmul (realOfInt R c) (realOfNat R (.succ (.succ b1)))))
                (mulRealOfInt R a (.intOfNat (.succ (.succ d1)))))
              (eqTrans (eqCong (fun z => rsub (realOfInt R (intMul a (.intOfNat (.succ (.succ d1)))))
                    z) (mulRealOfInt R c (.intOfNat (.succ (.succ b1)))))
                (subRealOfInt R (intMul a (.intOfNat (.succ (.succ d1))))
                  (intMul c (.intOfNat (.succ (.succ b1))))))))
          (eqCong (fun z => rdiv (realOfInt R (intSub (intMul a (.intOfNat (.succ (.succ d1))))
              (intMul c (.intOfNat (.succ (.succ b1)))))) z)
            (mulRealOfNat R (.succ (.succ b1)) (.succ (.succ d1)))))

def absOfMul {R : Real} (a b : Carrier R) :
    (rabs (rmul a b)) = (rmul (rabs a) (rabs b)) := absMul a b

def absOfZero (R : Real) : (rabs (rzero R)) = (rzero R) := absZero R

def mulZeroBoth {R : Real} (a b : Carrier R) :
    (rmul (rzero R) a) = (rmul (rzero R) b) :=
  eqTrans (mulZeroLeft a) (eqSym (mulZeroLeft b))

def ltToLe {R : Real} (a b : Carrier R) (h : rlt a b) : rle a b := Pair.fst h

def absLtToLe {R : Real} (a b : Carrier R) (h : rlt (rabs a) b) : rle (rabs a) b := Pair.fst h

-- TACTIC-MODE in source (erw).
def subSplit {R : Real} (a b c : Carrier R) :
    (radd (rsub a c) (rsub c b)) = (rsub a b) := sorry

def subTriangle {R : Real} (a b c : Carrier R) :
    rle (rabs (rsub a b)) (radd (rabs (rsub a c)) (rabs (rsub c b))) :=
  replace (fun z => rle (rabs z) (radd (rabs (rsub a c)) (rabs (rsub c b))))
    (subSplit a b c) (absTriangle (rsub a c) (rsub c b))

-- TACTIC-MODE in source (erw).
def mulSubDistribRight {R : Real} (a b c : Carrier R) :
    (rmul (rsub a b) c) = (rsub (rmul a c) (rmul b c)) := sorry

-- TACTIC-MODE in source (erw).
def mulInvLeftCancel {R : Real} (a b : Carrier R) (hne : a = (rzero R) → MyVoid) :
    (rmul a (rmul (rinv a) b)) = b := sorry

-- TACTIC-MODE in source (erw).
def diffQuotSubMulEq {R : Real} (a b c : Carrier R) (hne : b = (rzero R) → MyVoid) :
    (rmul (rsub (rmul a (rinv b)) c) b) = (rsub a (rmul c b)) := sorry

def eqOrNeZeroLeft {R : Real} (a : Carrier R) (h : (rzero R) = (rabs a)) :
    a = (rzero R) :=
  absEqZero a (eqSym h)

def eqOrNeZeroRight {R : Real} (a : Carrier R) (hne : (rzero R) = (rabs a) → MyVoid)
    (heq : a = (rzero R)) : MyVoid :=
  hne (eqSym (eqTrans (eqCong (fun z => rabs z) heq) (absOfZero R)))

def eqOrNeZero {R : Real} (a : Carrier R) :
    Either (a = (rzero R)) (a = (rzero R) → MyVoid) :=
  eitherElim (fun h => Either.left (eqOrNeZeroLeft a h))
    (fun h => Either.right (eqOrNeZeroRight a (Pair.snd h)))
    ((fieldOf R).leToEqOrLt (rzero R) (rabs a) (absNonneg a))

def derivBoundZero (R : Real) (g : Carrier R → Carrier R) (y0 Lg eta : Carrier R) :
    rle (rabs (rsub (rsub (g y0) (g y0)) (rmul Lg (rzero R)))) (rmul eta (rabs (rzero R))) :=
  replace (fun z => rle z (rmul eta (rabs (rzero R))))
    (eqSym (eqTrans (eqCong (fun z => rabs (rsub (rsub (g y0) (g y0)) z)) (mulZeroRight Lg))
      (eqTrans (eqCong (fun z => rabs z) (subZeroRight (rsub (g y0) (g y0))))
        (eqTrans (eqCong (fun z => rabs z) (subSelf (g y0))) (absOfZero R)))))
    (replace (fun z => rle (rzero R) z)
      (eqSym (eqTrans (eqCong (fun z => rmul eta z) (absOfZero R)) (mulZeroRight eta)))
      ((fieldOf R).leRefl (rzero R)))

-- TACTIC-MODE in source (erw).
def subEqZeroToEq {R : Real} (a b : Carrier R) (h : (rsub a b) = (rzero R)) :
    a = b := sorry

def derivBoundNonzero (R : Real) (g : Carrier R → Carrier R) (y0 Lg eta y : Carrier R)
    (hne : (rsub y y0) = (rzero R) → MyVoid)
    (hle : rle (rabs (rsub (diffQuot g y0 y) Lg)) eta) :
    rle (rabs (rsub (rsub (g y) (g y0)) (rmul Lg (rsub y y0)))) (rmul eta (rabs (rsub y y0))) :=
  replace (fun z => rle (rabs z) (rmul eta (rabs (rsub y y0))))
    (diffQuotSubMulEq (rsub (g y) (g y0)) (rsub y y0) Lg hne)
    (replace (fun z => rle z (rmul eta (rabs (rsub y y0))))
      (eqSym (absOfMul (rsub (diffQuot g y0 y) Lg) (rsub y y0)))
      (mulLeRight (rabs (rsub (diffQuot g y0 y) Lg)) eta (rabs (rsub y y0)) hle
        (absNonneg (rsub y y0))))

@[reducible] def DerivBoundWitness (R : Real) (g : Carrier R → Carrier R)
    (y0 Lg eta dg : Carrier R) : Type :=
  Pair (rlt (rzero R) dg)
    ((y : Carrier R) → rlt (rabs (rsub y y0)) dg →
      rle (rabs (rsub (rsub (g y) (g y0)) (rmul Lg (rsub y y0)))) (rmul eta (rabs (rsub y y0))))

-- TACTIC-MODE in source (constructor). Statement kept faithful.
def derivBound {R : Real} (g : Carrier R → Carrier R) (y0 Lg : Carrier R)
    (hg : HasDerivative g y0 Lg) (eta : Carrier R) (heta : rlt (rzero R) eta) :
    DPair (Carrier R)
      (fun delta => DerivBoundWitness R g y0 Lg eta delta) := sorry

-- TACTIC-MODE in source (constructor).
def addLtRight {R : Real} (a b c : Carrier R) (h : rlt a b) :
    rlt (radd a c) (radd b c) := sorry

def absSubAdd {R : Real} (a b : Carrier R) :
    rle (rabs a) (radd (rabs (rsub a b)) (rabs b)) :=
  replace (fun z => rle (rabs z) (radd (rabs (rsub a b)) (rabs b)))
    (subCancel a b) (absTriangle (rsub a b) b)

@[reducible] def DiffQuotBoundWitness (R : Real) (f : Carrier R → Carrier R)
    (x0 Lf df : Carrier R) : Type :=
  Pair (rlt (rzero R) df)
    ((x : Carrier R) → rlt (rzero R) (rabs (rsub x x0)) → rlt (rabs (rsub x x0)) df →
      rlt (rabs (diffQuot f x0 x)) (radd (rabs Lf) (rone R)))

-- TACTIC-MODE in source (constructor). Statement kept faithful.
def diffQuotBounded {R : Real} (f : Carrier R → Carrier R) (x0 Lf : Carrier R)
    (hf : HasDerivative f x0 Lf) :
    DPair (Carrier R)
      (fun delta => DiffQuotBoundWitness R f x0 Lf delta) := sorry

-- TACTIC-MODE in source (erw).
def diffQuotTimesH {R : Real} (f : Carrier R → Carrier R) (x0 x : Carrier R)
    (hne : (rsub x x0) = (rzero R) → MyVoid) :
    (rmul (diffQuot f x0 x) (rsub x x0)) = (rsub (f x) (f x0)) := sorry

def absDiffQuotTimesH {R : Real} (f : Carrier R → Carrier R) (x0 x : Carrier R)
    (hne : (rsub x x0) = (rzero R) → MyVoid) :
    (rmul (rabs (diffQuot f x0 x)) (rabs (rsub x x0))) = (rabs (rsub (f x) (f x0))) :=
  eqTrans (eqSym (absOfMul (diffQuot f x0 x) (rsub x x0)))
    (eqCong (fun z => rabs z) (diffQuotTimesH f x0 x hne))

@[reducible] def ContinuousWitness {R : Real} (f : Carrier R → Carrier R)
    (x0 target dc : Carrier R) : Type :=
  Pair (rlt (rzero R) dc)
    ((x : Carrier R) → rlt (rzero R) (rabs (rsub x x0)) → rlt (rabs (rsub x x0)) dc →
      rlt (rabs (rsub (f x) (f x0))) target)

def absMulBound {R : Real} (a b M eps : Carrier R) (hle : rle (rabs a) M)
    (hlt : rlt (rabs b) eps) (hM : rlt (rzero R) M) :
    rlt (rmul (rabs a) (rabs b)) (rmul M eps) :=
  leLtTrans (rmul (rabs a) (rabs b)) (rmul M (rabs b)) (rmul M eps)
    (mulLeRight (rabs a) M (rabs b) hle (absNonneg b))
    (mulLtLeft M (rabs b) eps hM hlt)

def continuityBound {R : Real} (f : Carrier R → Carrier R) (x0 x lf target : Carrier R)
    (hdq : rle (rabs (diffQuot f x0 x)) (radd (rabs lf) (rone R)))
    (hdelta : rlt (rabs (rsub x x0)) (rmul target (rinv (radd (rabs lf) (rone R)))))
    (hne : (rsub x x0) = (rzero R) → MyVoid) :
    rlt (rabs (rsub (f x) (f x0))) target :=
  replace (fun z => rlt z target) (absDiffQuotTimesH f x0 x hne)
    (replace (fun z => rlt (rmul (rabs (diffQuot f x0 x)) (rabs (rsub x x0))) z)
      (mulInvCancel (radd (rabs lf) (rone R)) target (absPlusOneNe lf))
      (absMulBound (diffQuot f x0 x) (rsub x x0) (radd (rabs lf) (rone R))
        (rmul target (rinv (radd (rabs lf) (rone R)))) hdq hdelta (absPlusOnePos lf)))

-- TACTIC-MODE in source (have / cases). Statement kept faithful.
def continuousFromDeriv {R : Real} (f : Carrier R → Carrier R) (x0 Lf : Carrier R)
    (hf : HasDerivative f x0 Lf) (target : Carrier R) (htarget : rlt (rzero R) target) :
    DPair (Carrier R)
      (fun dc => ContinuousWitness f x0 target dc) := sorry

------------------------------------------------------------
-- THE CHAIN RULE: (g . f)'(x0) = g'(f(x0)) . f'(x0)
------------------------------------------------------------

def chainTermA {R : Real} (g f : Carrier R → Carrier R) (x0 Lg x : Carrier R) : Carrier R :=
  rmul (rsub (rsub (g (f x)) (g (f x0))) (rmul Lg (rsub (f x) (f x0)))) (rinv (rsub x x0))

-- TACTIC-MODE in source (erw). Statement kept faithful.
def chainAlgId {R : Real} (g f : Carrier R → Carrier R) (x0 Lg : Carrier R) (x : Carrier R) :
    (radd (chainTermA g f x0 Lg x) (rmul Lg (diffQuot f x0 x))) = (diffQuot (fun y => g (f y)) x0 x) := sorry

-- TACTIC-MODE in source (erw). Statement kept faithful.
def mulAssocAbs {R : Real} (eta a b : Carrier R) :
    (rmul (rmul eta (rabs a)) (rabs b)) = (rmul eta (rabs (rmul a b))) := sorry

def chainBound {R : Real} (num fxfx0 h eta M eps : Carrier R)
    (hdb : rle (rabs num) (rmul eta (rabs fxfx0)))
    (hdq : rlt (rabs (rmul fxfx0 (rinv h))) M)
    (heta : rlt (rzero R) eta) (hmul : (rmul eta M) = eps) :
    rlt (rabs (rmul num (rinv h))) eps :=
  replace (fun z => rlt (rabs (rmul num (rinv h))) z) hmul
    (leLtTrans (rabs (rmul num (rinv h))) (rmul eta (rabs (rmul fxfx0 (rinv h)))) (rmul eta M)
      (replace (fun z => rle z (rmul eta (rabs (rmul fxfx0 (rinv h)))))
        (eqSym (absOfMul num (rinv h)))
        (replace (fun z => rle (rmul (rabs num) (rabs (rinv h))) z)
          (mulAssocAbs eta fxfx0 (rinv h))
          (mulLeRight (rabs num) (rmul eta (rabs fxfx0)) (rabs (rinv h)) hdb (absNonneg (rinv h)))))
      (mulLtLeft eta (rabs (rmul fxfx0 (rinv h))) M heta hdq))

-- TACTIC-MODE in source (have / cases). Statement kept faithful.
def chainTermALimit {R : Real} (g f : Carrier R → Carrier R) (x0 Lg Lf : Carrier R)
    (hf : HasDerivative f x0 Lf) (hg : HasDerivative g (f x0) Lg) :
    Limit (chainTermA g f x0 Lg) x0 (rzero R) := sorry

-- TACTIC-MODE in source (suffices / have). Statement kept faithful.
def derivChain {R : Real} (g f : Carrier R → Carrier R) (x0 Lf Lg : Carrier R)
    (hf : HasDerivative f x0 Lf) (hg : HasDerivative g (f x0) Lg) :
    HasDerivative (fun x => g (f x)) x0 (rmul Lg Lf) := sorry

def derivChainEq {R : Real} (g f : Carrier R → Carrier R) (x0 Lf Lg : Carrier R)
    (hf : HasDerivative f x0 Lf) (hg : HasDerivative g (f x0) Lg) :
    (deriv (fun x => g (f x)) x0 (derivChain g f x0 Lf Lg hf hg)) = (rmul (deriv g (f x0) hg) (deriv f x0 hf)) := rfl

------------------------------------------------------------
-- Demo / scratch goal
------------------------------------------------------------

def demoTestLiterals (R : Real) :
    rle (realOfNat R (.succ .zero)) (realOfNat R (.succ (.succ .zero))) := sorry
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
  { name: 'Real Analysis (chain rule)', code: REAL_ANALYSIS },
  { name: 'Mathlib (∑, ring)', code: MATHLIB, mathlib: true },
];

export const DEFAULT_LEAN_SOURCE = BASICS;
