/**
 * Lean-native example programs for the editor preset picker.
 *
 * These replace the old TT/TTK presets (which used the now-superseded surface
 * syntax). Core-mode friendly: none require Mathlib. The Mathlib toggle unlocks
 * the richer examples that import it.
 *
 * DOC-COMMENT STYLE: a lemma's doc comment is its CITATION — the prose says
 * "by <doc>" ("This holds by transitivity.", "Observe … by the triangle
 * inequality."). Write docs as short noun phrases that read after "by":
 * "totality of ≤", "positivity of halving", "adding the two estimates".
 * No sentences, no internal commas, no colons.
 *
 * NO BACKTICKS anywhere in this file's Lean code or comments — the presets are
 * TS template literals and a backtick terminates them mid-file.
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

-- Render succ a as a + 1 — a paper never writes a.succ. Display-only: the
-- constructor spelling still parses, and case labels keep their own path.
@[app_unexpander MyNat.succ] def unexpMyNatSucc : Lean.PrettyPrinter.Unexpander
  | \`($_ $n) => \`($n + 1)
  | _ => throw ()

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

/-- commutativity of multiplication -/
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

/-- distributivity -/
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
/-- splitting off the last summand -/
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
-- Proven by induction: the zero case holds by rfl; the succ case peels the last
-- term off the sum via summationSplit (whose i <= n premise is the trivial side
-- goal 0 <= a, closed by the LeqZero constructor), folds in the induction
-- hypothesis, and normalizes both sides with the arithmetic lemmas.
-- (def, not theorem: this custom lives = in Type, not Prop.)
def triangleSum (n : MyNat) :
    (mul 2 (∑[i,0,n] i)) = (mul (plus n 1) n) := by
  induction n with
  | zero =>
    rfl
  | succ a a_ih =>
    rw [summationSplit]
    ·
      rw [mulDistribLeft]
      rw [a_ih]
      simp [mulComm, mulDistribLeft, twoEqAddOne, succAddOne, plusLeftComm, plusComm]
    ·
      constructor

-- ============ Fubini for finite double sums ============

-- (a+b)+(c+d) = (a+c)+(b+d)
/-- the middle-four exchange -/
def plusSwap (a b c d : MyNat) :
    (plus (plus a b) (plus c d)) = (plus (plus a c) (plus b d)) :=
  eqTrans (plusAssoc a b (plus c d))
    (eqTrans (congPlusRight a (plusLeftComm b c d))
      (eqSym (plusAssoc a c (plus b d))))

def sumStartCountCongr (s : MyNat) {f g : MyNat → MyNat} (h : ∀ k, (f k) = (g k)) :
    (c : MyNat) → (sumStartCount s c f) = (sumStartCount s c g)
  | .zero => rfl
  | .succ c =>
    eqTrans (congPlusLeft (f (plus s c)) (sumStartCountCongr s h c))
      (congPlusRight (sumStartCount s c g) (h (plus s c)))

/-- sums of pointwise-equal functions agree -/
def sumCongr (lo hi : MyNat) {f g : MyNat → MyNat} (h : ∀ k, (f k) = (g k)) :
    (sum lo hi f) = (sum lo hi g) :=
  sumStartCountCongr lo h (minus (.succ hi) lo)

def sumStartCountAdd (s : MyNat) (f g : MyNat → MyNat) :
    (c : MyNat) → (sumStartCount s c (fun k => plus (f k) (g k)))
      = (plus (sumStartCount s c f) (sumStartCount s c g))
  | .zero => rfl
  | .succ c =>
    eqTrans (congPlusLeft _ (sumStartCountAdd s f g c))
      (plusSwap (sumStartCount s c f) (sumStartCount s c g) (f (plus s c)) (g (plus s c)))

/-- a sum of pointwise sums splits into two sums -/
def sumAdd (lo hi : MyNat) (f g : MyNat → MyNat) :
    (sum lo hi (fun k => plus (f k) (g k))) = (plus (sum lo hi f) (sum lo hi g)) :=
  sumStartCountAdd lo f g (minus (.succ hi) lo)

-- FUBINI (finite form): the two orders of a double sum agree. Induct on the
-- outer bound; split off its last row, swap the smaller double sum by the
-- induction hypothesis, absorb the split row back inside with sumAdd.
def fubini (m : MyNat) (f : MyNat → MyNat → MyNat) :
    (n : MyNat) → (∑[i,0,n] (∑[j,0,m] f i j)) = (∑[j,0,m] (∑[i,0,n] f i j)) := by
  intro n
  induction n with
  | zero =>
    rfl
  | succ a ih =>
    rw [summationSplit]
    ·
      rw [ih]
      rw [← sumAdd]
      exact sumCongr 0 m (fun j => eqSym (summationSplit 0 a .LeqZero (fun i => f i j)))
    ·
      constructor

-- ============ rearrangement (finite form) ============

def sumList : List MyNat → MyNat
  | [] => .zero
  | x :: xs => plus x (sumList xs)

-- REARRANGEMENT (finite form): a finite sum may be reorganized freely — the
-- sum of a list is invariant under any permutation of its terms. (The
-- infinite statement needs absolute convergence and the limit framework;
-- this is its finite heart.) Induct on the permutation derivation: nothing
-- to show for [], a shared head passes through, a swap is commutativity two
-- terms deep, and two permutations in sequence chain.
def rearrangement (l1 l2 : List MyNat) (hp : l1.Perm l2) :
    (sumList l1) = (sumList l2) := by
  induction hp with
  | nil =>
    rfl
  | cons x _ ih =>
    exact congPlusRight _ ih
  | swap x y l =>
    exact plusLeftComm y x (sumList l)
  | trans _ _ ih1 ih2 =>
    exact eqTrans ih1 ih2

#check natSemiring
#check leqAntisym
#check triangleSum
#check fubini
#check rearrangement
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
// The tower every analysis preset shares: Peano → integers → rationals →
// the axiomatized complete ordered field, notation, abs/min, limits.
const RA_TOWER = `-- Real Analysis: algebraic hierarchy, ordered fields, limits, and derivatives
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

-- DPair IS the data existential: display (and allow writing) it as
-- exists-prime x in A, P x. The prime keeps it distinct from core's
-- Prop-valued exists; the math renderer shows a plain exists-quantifier.
notation:30 "∃' " x:51 " ∈ " A:51 ", " P => DPair A (fun x => P)
@[app_unexpander DPair] def unexpDPair : Lean.PrettyPrinter.Unexpander
  | \`($_ $A fun $x:ident => $P) => \`(∃' $x:ident ∈ $A, $P)
  | _ => throw ()

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

-- Display the carrier as ℝ (display only, like rzero/rone's 0/1 unexpanders).
-- Every signature in this preset is parametric over the ONE bundled R, so
-- eliding it is unambiguous; the math renderer maps ℝ to \\mathbb{R}.
-- mkIdent (not a quoted ident) keeps it hygiene-free — no ✝ dagger in the pp.
@[app_unexpander Carrier] def unexpCarrier : Lean.PrettyPrinter.Unexpander
  | \`($_ $_) => pure (Lean.mkIdent \`ℝ)
  | _ => throw ()

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
-- (priority := high): these coexist with core's +/*/-// (HAdd/HDiv…); without
-- an explicit priority, a term like eps / 2 is AMBIGUOUS between rdiv and
-- HDiv.hDiv — high priority makes the carrier operators win outright.
infixl:65 (priority := high) " + " => radd
infixl:70 (priority := high) " * " => rmul
infixl:65 (priority := high) " - " => rsub
infixl:70 (priority := high) " / " => rdiv
infix:50 (priority := high) " ≤ " => rle
infix:50 (priority := high) " < " => rlt
prefix:75 (priority := high) "-" => rneg

-- Absolute value (defined from leTotal via eitherElim, not axiomatized)
def rabs {R : Real} (a : Carrier R) : Carrier R :=
  eitherElim (fun _ => a) (fun _ => rneg a) ((fieldOf R).leTotal (rzero R) a)

-- |a| for absolute value, in both directions: the macro lets you WRITE it, the
-- unexpander makes Lean PRINT it, so a goal reads |f x - L| < ε instead of
-- rabs (f x - L) < ε. \`noWs\` (no whitespace inside the bars) is how Mathlib
-- spells this too — it keeps the bars from being confused with the \`|\` that
-- separates match alternatives.
macro:max atomic("|" noWs) a:term noWs "|" : term => \`(rabs $a)
@[app_unexpander rabs] def unexpRabs : Lean.PrettyPrinter.Unexpander
  | \`($_ $a) => \`(|$a|)
  | _ => throw ()

def absElim {R : Real} (a : Carrier R) (C : Carrier R → Sort w)
    (pos : rle (rzero R) a → C a) (neg : rle a (rzero R) → C (rneg a)) : C (rabs a) :=
  eitherElimDep (fun e => C (eitherElim (fun _ => a) (fun _ => rneg a) e))
    (fun h => pos h) (fun h => neg h)
    ((fieldOf R).leTotal (rzero R) a)

-- Minimum (defined from leTotal via eitherElim, like rabs — not axiomatized).
-- The ε-δ workhorse: two deltas become one via δ := min δ₁ δ₂.
def rmin {R : Real} (a b : Carrier R) : Carrier R :=
  eitherElim (fun _ => a) (fun _ => b) ((fieldOf R).leTotal a b)

-- min is what a paper writes; rmin is our internal spelling. The display is
-- NOTATION rather than the identifier min, which resolves to Lean's own and
-- came back hygiene-daggered as min-dagger.
notation:max "min(" a ", " b ")" => rmin a b
@[app_unexpander rmin] def unexpRmin : Lean.PrettyPrinter.Unexpander
  | \`($_ $a $b) => \`(min($a, $b))
  | _ => throw ()

def minElim {R : Real} (a b : Carrier R) (C : Carrier R → Sort w)
    (left : rle a b → C a) (right : rle b a → C b) : C (rmin a b) :=
  eitherElimDep (fun e => C (eitherElim (fun _ => a) (fun _ => b) e))
    (fun h => left h) (fun h => right h)
    ((fieldOf R).leTotal a b)

-- The minimum IS one of its two arguments — the fact a reader quotes, and
-- the elementary reason anything true of both is true of it. (Mathlib spells
-- this min_choice.)
/-- the minimum being one of its two arguments -/
def minChoice {R : Real} (a b : Carrier R) :
    Either ((rmin a b) = a) ((rmin a b) = b) :=
  minElim a b (fun z => Either (z = a) (z = b)) (fun _ => .left rfl) (fun _ => .right rfl)

/-- min bounding its left argument -/
def minLeLeft {R : Real} (a b : Carrier R) : rle (rmin a b) a :=
  minElim a b (fun z => rle z a) (fun _ => (fieldOf R).leRefl a) (fun h => h)

/-- min bounding its right argument -/
def minLeRight {R : Real} (a b : Carrier R) : rle (rmin a b) b :=
  minElim a b (fun z => rle z b) (fun h => h) (fun _ => (fieldOf R).leRefl b)

def ltMin {R : Real} (c a b : Carrier R) (ha : rlt c a) (hb : rlt c b) :
    rlt c (rmin a b) :=
  minElim a b (fun z => rlt c z) (fun _ => ha) (fun _ => hb)

-- Positivity is not a special property of min: the minimum is one of the two
-- arguments, and BOTH are positive, so whichever it is, it is positive. The
-- case split lives here, in the two-line lemma, rather than in the ε-δ proof.
/-- positivity of the minimum -/
def minPos {R : Real} (a b : Carrier R) (ha : rlt (rzero R) a) (hb : rlt (rzero R) b) :
    rlt (rzero R) (rmin a b) := by
  cases minChoice a b with
  | left h => rw [h]; exact ha
  | right h => rw [h]; exact hb

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

-- Display EpsDeltaWitness as WHAT IT SAYS — a paper never names this bundle,
-- it writes the estimate: "0 < δ and for all x, 0 < |x−x₀| < δ implies
-- |f(x)−L| < ε". Display-only (the unexpander emits syntax, nothing is
-- re-elaborated); the input spelling EpsDeltaWitness f x0 L ε δ still works.
@[app_unexpander EpsDeltaWitness] def unexpEpsDeltaWitness : Lean.PrettyPrinter.Unexpander
  | \`($_ $f $x0 $L $ε $δ) => do
    match f with
    -- A lambda reuses ITS OWN binder as the ∀ variable — no hygiene dagger,
    -- and |(fun x => f x + g x) x| beta-reads as |f x + g x| for free.
    | \`(fun $y:ident => $body) =>
      \`(0 < $δ ∧ ∀ $y:ident, 0 < |$y - $x0| → |$y - $x0| < $δ → |$body - $L| < $ε)
    | _ =>
      let x := Lean.mkIdent \`x
      \`(0 < $δ ∧ ∀ $x:ident, 0 < |$x - $x0| → |$x - $x0| < $δ → |$f $x - $L| < $ε)
  | _ => throw ()

structure Limit {R : Real} (f : Carrier R → Carrier R) (x0 L : Carrier R) where
  eps_delta : (epsilon : Carrier R) → rlt (rzero R) epsilon →
              DPair (Carrier R)
                (fun delta => EpsDeltaWitness f x0 L epsilon delta)

-- Display notation: the math renderer recognizes the lim marker and shows
-- Limit f x0 L as the limit  lim_{x → x0} f(x) = L  (a lambda f shows its bound
-- variable / body). Pure display + parse sugar; Limit f x0 L still works directly.
notation:50 "lim⟦" x0 "⟧ " f " = " L => Limit f x0 L

-- NOTE: leanUI used a dependent-pair existential (δ : Carrier R ** EpsDeltaWitness ...).
-- In core Lean we model it with DPair; the first component family is the carrier itself.
-- (See uses of DPair.fst / DPair.snd below.)

------------------------------------------------------------
-- Algebraic lemmas
------------------------------------------------------------

-- TACTIC-MODE in source (erw); kept faithful as statement, body sorried.
------------------------------------------------------------
-- The order axioms, usable BY NAME
--
-- The axioms live inside the CompleteOrderedField structure, where they read
-- as "self.le self.zero self.one" — raw projections, in terms of the structure
-- fields rather than this file's notation. That makes them invisible to anyone
-- (human or suggestion engine) looking for something shaped like 0 ≤ 1.
-- These wrappers restate each one in the notation the goals actually use, so
-- an ordered-field axiom is reachable exactly like any other lemma here.
------------------------------------------------------------

def zeroLeOne (R : Real) : rle (rzero R) (rone R) := (fieldOf R).zeroLeOne

def zeroNeOne (R : Real) : (rzero R) = (rone R) → MyVoid := (fieldOf R).zeroNeOne

def leRefl {R : Real} (a : Carrier R) : rle a a := (fieldOf R).leRefl a

def leTrans {R : Real} (a b c : Carrier R) (hab : rle a b) (hbc : rle b c) : rle a c :=
  (fieldOf R).leTrans a b c hab hbc

def leAntisym {R : Real} (a b : Carrier R) (hab : rle a b) (hba : rle b a) : a = b :=
  (fieldOf R).leAntisym a b hab hba

/-- totality of ≤ -/
def leTotal {R : Real} (a b : Carrier R) : Either (rle a b) (rle b a) :=
  (fieldOf R).leTotal a b

def addLeLeft {R : Real} (a b c : Carrier R) (h : rle a b) : rle (radd c a) (radd c b) :=
  (fieldOf R).addLeLeft a b c h

def mulNonneg {R : Real} (a b : Carrier R) (ha : rle (rzero R) a) (hb : rle (rzero R) b) :
    rle (rzero R) (rmul a b) :=
  (fieldOf R).mulNonneg a b ha hb

def invNonneg {R : Real} (a : Carrier R) (ha : rle (rzero R) a)
    (hne : a = (rzero R) → MyVoid) : rle (rzero R) (rinv a) :=
  (fieldOf R).invPos a ha hne

def addZeroLeft {R : Real} (a : Carrier R) : (radd (rzero R) a) = a :=
  eqTrans ((fieldOf R).addComm (rzero R) a) ((fieldOf R).addZeroRight a)

def addRealOfNat (R : Real) : (n m : MyNat) →
    (radd (realOfNat R n) (realOfNat R m)) = (realOfNat R (plus n m))
  | .zero, m => addZeroLeft (realOfNat R m)
  | .succ n, m =>
      eqTrans ((fieldOf R).addAssoc (rone R) (realOfNat R n) (realOfNat R m))
        (eqCong (fun z => radd (rone R) z) (addRealOfNat R n m))

def negLeft {R : Real} (a : Carrier R) : (radd (rneg a) a) = (rzero R) :=
  eqTrans ((fieldOf R).addComm (rneg a) a) ((fieldOf R).negRight a)

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
def negZero (R : Real) : (rneg (rzero R)) = (rzero R) :=
  eqTrans (eqSym (addZeroLeft (rneg (rzero R)))) ((fieldOf R).negRight (rzero R))

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

/-- transitivity -/
def leLtTrans {R : Real} (a b c : Carrier R) (hab : rle a b) (hbc : rlt b c) : rlt a c :=
  Pair.mk (leLtTransLe a b c hab (Pair.fst hbc)) (leLtTransNe a b c hab (Pair.fst hbc) (Pair.snd hbc))

def ltLeTransLe {R : Real} (a b c : Carrier R) (hab : rle a b) (hbc : rle b c) : rle a c :=
  (fieldOf R).leTrans a b c hab hbc

def ltLeTransNe {R : Real} (a b c : Carrier R) (hab : rle a b) (neab : a = b → MyVoid)
    (hbc : rle b c) (eq : a = c) : MyVoid :=
  neab ((fieldOf R).leAntisym a b hab
    ((fieldOf R).leTrans b c a hbc
      (replace (fun z => rle z a) eq ((fieldOf R).leRefl a))))

/-- transitivity -/
def ltLeTrans {R : Real} (a b c : Carrier R) (hab : rlt a b) (hbc : rle b c) : rlt a c :=
  Pair.mk (ltLeTransLe a b c (Pair.fst hab) hbc) (ltLeTransNe a b c (Pair.fst hab) (Pair.snd hab) hbc)

-- calc chains need Trans instances to link mixed relations — the transitivity
-- lemmas above are exactly the content, these just register them so a reader
-- can write  a = b ... _ <= c ... _ < d  as one derivation.
instance {R : Real} : Trans (α := Carrier R) (β := Carrier R) (γ := Carrier R) rle rle rle where
  trans h1 h2 := (fieldOf R).leTrans _ _ _ h1 h2
instance {R : Real} : Trans (α := Carrier R) (β := Carrier R) (γ := Carrier R) rle rlt rlt where
  trans h1 h2 := leLtTrans _ _ _ h1 h2
instance {R : Real} : Trans (α := Carrier R) (β := Carrier R) (γ := Carrier R) rlt rle rlt where
  trans h1 h2 := ltLeTrans _ _ _ h1 h2


-- TACTIC-MODE in source (erw).
def addCancelRightHelper {R : Real} (x c : Carrier R) :
    (radd (radd x c) (rneg c)) = x :=
  eqTrans ((fieldOf R).addAssoc x c (rneg c))
    (eqTrans (eqCong (fun z => radd x z) ((fieldOf R).negRight c))
      ((fieldOf R).addZeroRight x))

def addCancelRight {R : Real} (a b c : Carrier R) (h : (radd a c) = (radd b c)) :
    a = b :=
  eqTrans (eqSym (addCancelRightHelper a c))
    (eqTrans (eqCong (fun z => radd z (rneg c)) h) (addCancelRightHelper b c))

def addLeRightCancel {R : Real} (a b c : Carrier R) (h : rle (radd a c) (radd b c)) : rle a b :=
  replace (fun z => rle z b) (addCancelRightHelper a c)
    (replace (fun z => rle (radd (radd a c) (rneg c)) z) (addCancelRightHelper b c)
      (addLeRight (radd a c) (radd b c) (rneg c) h))

def addLeLeftCancel {R : Real} (a b c : Carrier R) (h : rle (radd c a) (radd c b)) : rle a b :=
  addLeRightCancel a b c
    (replace (fun z => rle (radd a c) z) ((fieldOf R).addComm c b)
      (replace (fun z => rle z (radd c b)) ((fieldOf R).addComm c a) h))

-- Cancellation, the STRICT version. a < b is (a ≤ b) paired with (a ≠ b), so
-- both halves come straight from the ≤ version and congruence.
--
-- Read BACKWARDS this is the "add the same thing to both sides" move: applying
-- it to a goal like 1 < 2 asks you to choose a shift c and then show
-- 1 + c < 2 + c. The ≤-only cancellation couldn't express that on a < goal.
def addLtRightCancel {R : Real} (a b c : Carrier R) (h : rlt (radd a c) (radd b c)) : rlt a b :=
  Pair.mk (addLeRightCancel a b c (Pair.fst h))
    (fun e => Pair.snd h (eqCong (fun z => radd z c) e))

def addLtLeftCancel {R : Real} (a b c : Carrier R) (h : rlt (radd c a) (radd c b)) : rlt a b :=
  Pair.mk (addLeLeftCancel a b c (Pair.fst h))
    (fun e => Pair.snd h (eqCong (fun z => radd c z) e))

-- The forward direction on the left, to match addLtRight.
def addLtLeft {R : Real} (a b c : Carrier R) (h : rlt a b) : rlt (radd c a) (radd c b) :=
  Pair.mk ((fieldOf R).addLeLeft a b c (Pair.fst h))
    (fun e => Pair.snd h (addCancelRight a b c
      (replace (fun z => (radd a c) = z) ((fieldOf R).addComm c b)
        (replace (fun z => z = (radd c b)) ((fieldOf R).addComm c a) e))))

def addLtBothNe {R : Real} (a b c d : Carrier R) (leab : rle a b) (neab : a = b → MyVoid)
    (lecd : rle c d) (eq : (radd a c) = (radd b d)) : MyVoid :=
  neab (addCancelRight a b c
    ((fieldOf R).leAntisym (radd a c) (radd b c)
      (addLeRight a b c leab)
      ((fieldOf R).leTrans (radd b c) (radd b d) (radd a c)
        ((fieldOf R).addLeLeft c d b lecd)
        (replace (fun z => rle (radd b d) z) (eqSym eq)
          ((fieldOf R).leRefl (radd b d))))))

/-- adding the two estimates -/
def addLtBoth {R : Real} (a b c d : Carrier R) (hab : rlt a b) (hcd : rlt c d) :
    rlt (radd a c) (radd b d) :=
  Pair.mk (addLeBoth a b c d (Pair.fst hab) (Pair.fst hcd))
    (addLtBothNe a b c d (Pair.fst hab) (Pair.snd hab) (Pair.fst hcd))

------------------------------------------------------------
-- Halving: 1/2 * eps + 1/2 * eps = eps
------------------------------------------------------------

def rtwo (R : Real) : Carrier R := radd (rone R) (rone R)

-- Numeric literals AT the carrier: 0/1/2 elaborate to rzero/rone/rtwo, so a
-- user can WRITE what the goals display (eps / 2, 0 < eps). Display of
-- those constants as literals is the unexpanders' job below; these instances
-- are the PARSING direction.
instance {R : Real} : OfNat (Carrier R) 0 := ⟨rzero R⟩
instance {R : Real} : OfNat (Carrier R) 1 := ⟨rone R⟩
instance {R : Real} : OfNat (Carrier R) 2 := ⟨rtwo R⟩

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

-- The instances above mean every goal holds numerals in ONE of two forms: a
-- user-typed literal is \`OfNat.ofNat 2\` while a lemma-substituted one is
-- \`rtwo R\` — same display, DIFFERENT terms, and simp/rw matching is syntactic.
-- A lemma stated about \`rtwo R\` silently misses literal goals (and vice
-- versa). These @[simp] bridges normalize literals to the constants, so plain
-- \`simp\` — the editor's "Compute" move — sees one representation. rfl-true:
-- the instances ARE the constants.
@[simp] def litZero {R : Real} : (0 : Carrier R) = rzero R := rfl
@[simp] def litOne {R : Real} : (1 : Carrier R) = rone R := rfl
@[simp] def litTwo {R : Real} : (2 : Carrier R) = rtwo R := rfl

def rhalf (R : Real) : Carrier R := rinv (rtwo R)

def oneLeTwo (R : Real) : rle (rone R) (rtwo R) :=
  replace (fun z => rle z (rtwo R)) (addZeroLeft (rone R))
    (addLeRight (rzero R) (rone R) (rone R) ((fieldOf R).zeroLeOne))

def twoNeZero (R : Real) (eq : (rtwo R) = (rzero R)) : MyVoid :=
  (fieldOf R).zeroNeOne
    ((fieldOf R).leAntisym (rzero R) (rone R)
      ((fieldOf R).zeroLeOne)
      (replace (fun z => rle (rone R) z) eq (oneLeTwo R)))

-- ½ + ½ = ½·1 + ½·1 = ½·(1+1) = ½·2 = 1 (the last step is inv·a = 1, with
-- ½·2 ≡ (inv 2)·2 and 1+1 ≡ 2 definitionally).
def halfPlusHalf (R : Real) : (radd (rhalf R) (rhalf R)) = (rone R) :=
  eqTrans (eqCong (fun z => radd z (rhalf R)) (eqSym ((fieldOf R).mulOneRight (rhalf R))))
    (eqTrans (eqCong (fun z => radd (rmul (rhalf R) (rone R)) z)
        (eqSym ((fieldOf R).mulOneRight (rhalf R))))
      (eqTrans (eqSym ((fieldOf R).distribLeft (rhalf R) (rone R) (rone R)))
        (eqTrans (eqSym ((fieldOf R).mulComm (rtwo R) (rinv (rtwo R))))
          ((fieldOf R).mulInvRight (rtwo R) (twoNeZero R)))))

def halfMulEps {R : Real} (e : Carrier R) :
    (radd (rmul (rhalf R) e) (rmul (rhalf R) e)) = e :=
  eqTrans (eqSym ((fieldOf R).distribRight (rhalf R) (rhalf R) e))
    (eqTrans (eqCong (fun z => rmul z e) (halfPlusHalf R))
      ((fieldOf R).mulOneLeft e))

def zeroLeTwo (R : Real) : rle (rzero R) (rtwo R) :=
  (fieldOf R).leTrans (rzero R) (rone R) (rtwo R)
    ((fieldOf R).zeroLeOne) (oneLeTwo R)

-- 1 ≠ 2. Since 2 is 1 + 1, "1 = 2" says "0 + 1 = 1 + 1"; cancelling the 1 on
-- the right leaves "0 = 1", which the ordered field forbids.
def oneNeTwo (R : Real) (eq : (rone R) = (rtwo R)) : MyVoid :=
  (fieldOf R).zeroNeOne
    (addCancelRight (rzero R) (rone R) (rone R)
      (eqTrans (addZeroLeft (rone R)) eq))

-- The strict versions: a < b is (a ≤ b) paired with (a ≠ b), and both halves
-- are right above.
def oneLtTwo (R : Real) : rlt (rone R) (rtwo R) :=
  Pair.mk (oneLeTwo R) (oneNeTwo R)

def zeroLtTwo (R : Real) : rlt (rzero R) (rtwo R) :=
  Pair.mk (zeroLeTwo R) (fun eq => twoNeZero R (eqSym eq))

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
------------------------------------------------------------
-- STRICT POSITIVITY: products, inverses, quotients
--
-- Everything here reduces to two ordered-field facts — mulNonneg (a product of
-- nonnegatives is nonnegative) and invPos (the inverse of a nonnegative nonzero
-- is nonnegative) — plus the observation that a < b is (a ≤ b) paired with
-- (a ≠ b). The ≠ halves are where the field structure does the work: in a
-- field, a product of nonzeros is nonzero, because you can multiply by an
-- inverse and cancel.
------------------------------------------------------------

-- c * 0 = 0. Not an axiom: distributivity gives c*0 = c*0 + c*0, and
-- cancelling one copy leaves 0.
def mulZeroRight {R : Real} (c : Carrier R) : (rmul c (rzero R)) = (rzero R) :=
  eqSym (addCancelRight (rzero R) (rmul c (rzero R)) (rmul c (rzero R))
    (eqTrans (addZeroLeft (rmul c (rzero R)))
      (eqTrans (eqSym (eqCong (fun z => rmul c z) ((fieldOf R).addZeroRight (rzero R))))
        ((fieldOf R).distribLeft c (rzero R) (rzero R)))))

-- 1/a * a = 1 (the field axiom is stated the other way round).
def mulInvLeft {R : Real} (a : Carrier R) (ane : a = (rzero R) → MyVoid) :
    (rmul (rinv a) a) = (rone R) :=
  eqTrans (eqSym ((fieldOf R).mulComm a (rinv a))) ((fieldOf R).mulInvRight a ane)

-- A product of nonzeros is nonzero: if a * b = 0 then multiplying by 1/a and
-- cancelling gives b = 0.
def mulNeZero {R : Real} (a b : Carrier R) (ane : a = (rzero R) → MyVoid)
    (bne : b = (rzero R) → MyVoid) (eq : (rmul a b) = (rzero R)) : MyVoid :=
  bne
    (eqTrans (eqSym ((fieldOf R).mulOneLeft b))
      (eqTrans (eqCong (fun z => rmul z b) (eqSym (mulInvLeft a ane)))
        (eqTrans ((fieldOf R).mulAssoc (rinv a) a b)
          (eqTrans (eqCong (fun z => rmul (rinv a) z) eq) (mulZeroRight (rinv a))))))

-- 1/b is nonzero: if it were 0 then b * (1/b) = 0, but that product is 1.
def invNeZero {R : Real} (b : Carrier R) (bne : b = (rzero R) → MyVoid)
    (eq : (rinv b) = (rzero R)) : MyVoid :=
  (fieldOf R).zeroNeOne
    (eqSym (eqTrans (eqSym ((fieldOf R).mulInvRight b bne))
      (eqTrans (eqCong (fun z => rmul b z) eq) (mulZeroRight b))))

-- The nonzero half of a strict positivity, the way round the field wants it.
def posNeZero {R : Real} (a : Carrier R) (ha : rlt (rzero R) a) :
    a = (rzero R) → MyVoid :=
  fun z => Pair.snd ha (eqSym z)

-- 0 < a and 0 < b give 0 < a * b.
def mulPos {R : Real} (a b : Carrier R) (ha : rlt (rzero R) a) (hb : rlt (rzero R) b) :
    rlt (rzero R) (rmul a b) :=
  Pair.mk ((fieldOf R).mulNonneg a b (Pair.fst ha) (Pair.fst hb))
    (fun eq => mulNeZero a b (posNeZero a ha) (posNeZero b hb) (eqSym eq))

-- 0 < b gives 0 < 1/b.
def invPosStrict {R : Real} (b : Carrier R) (hb : rlt (rzero R) b) :
    rlt (rzero R) (rinv b) :=
  Pair.mk ((fieldOf R).invPos b (Pair.fst hb) (posNeZero b hb))
    (fun eq => invNeZero b (posNeZero b hb) (eqSym eq))

def halfPosStrict (R : Real) : rlt (rzero R) (rhalf R) :=
  invPosStrict (rtwo R) (zeroLtTwo R)

def halfMulEpsPos {R : Real} (e : Carrier R) (hlt : rlt (rzero R) e) :
    rlt (rzero R) (rmul (rhalf R) e) :=
  mulPos (rhalf R) e (halfPosStrict R) hlt

------------------------------------------------------------
-- Negation distributes over addition: -(a+b) = (-a)+(-b)
------------------------------------------------------------

-- (a + b) + -a = b: commute the inner sum, reassociate, cancel, drop the zero.
@[simp] def addSumNeg {R : Real} (a b : Carrier R) : (radd (radd a b) (rneg a)) = b :=
  eqTrans (eqCong (fun z => radd z (rneg a)) ((fieldOf R).addComm a b))
    (eqTrans ((fieldOf R).addAssoc b a (rneg a))
      (eqTrans (eqCong (fun z => radd b z) ((fieldOf R).negRight a))
        ((fieldOf R).addZeroRight b)))

-- 2 + -1 computes to 1 (2 is DEFINED as 1 + 1, so this is addSumNeg at 1 1).
-- @[simp] so the editor's "Compute" move reduces displayed arithmetic; stated
-- on the constants, with the literal forms reached via the lit* bridges.
@[simp] def twoAddNegOne {R : Real} : (radd (rtwo R) (rneg (rone R))) = (rone R) :=
  addSumNeg (rone R) (rone R)

def negAddCancel {R : Real} (a b : Carrier R) :
    (radd (radd a b) (radd (rneg a) (rneg b))) = (rzero R) :=
  eqTrans (eqSym ((fieldOf R).addAssoc (radd a b) (rneg a) (rneg b)))
    (eqTrans (eqCong (fun z => radd z (rneg b)) (addSumNeg a b))
      ((fieldOf R).negRight b))

-- b is THE additive inverse of a: anything that sums to zero with a is -a.
def negUnique {R : Real} (a b : Carrier R) (h : (radd a b) = (rzero R)) :
    b = (rneg a) :=
  eqTrans (eqSym (addZeroLeft b))
    (eqTrans (eqCong (fun z => radd z b) (eqSym (negLeft a)))
      (eqTrans ((fieldOf R).addAssoc (rneg a) a b)
        (eqTrans (eqCong (fun z => radd (rneg a) z) h)
          ((fieldOf R).addZeroRight (rneg a)))))

def negAdd {R : Real} (a b : Carrier R) :
    (rneg (radd a b)) = (radd (rneg a) (rneg b)) :=
  eqSym (negUnique (radd a b) (radd (rneg a) (rneg b)) (negAddCancel a b))

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

-- Middle-four exchange: (a+b)+(c+d) = (a+c)+(b+d).
def addAddSwap {R : Real} (a b c d : Carrier R) :
    (radd (radd a b) (radd c d)) = (radd (radd a c) (radd b d)) :=
  eqTrans ((fieldOf R).addAssoc a b (radd c d))
    (eqTrans (eqCong (fun z => radd a z) (eqSym ((fieldOf R).addAssoc b c d)))
      (eqTrans (eqCong (fun z => radd a (radd z d)) ((fieldOf R).addComm b c))
        (eqTrans (eqCong (fun z => radd a z) ((fieldOf R).addAssoc c b d))
          (eqSym ((fieldOf R).addAssoc a c (radd b d))))))

/-- regrouping the difference of sums -/
def subAddSub {R : Real} (a b c d : Carrier R) :
    (rsub (radd a b) (radd c d)) = (radd (rsub a c) (rsub b d)) :=
  eqTrans (eqCong (fun z => radd (radd a b) z) (negAdd c d))
    (addAddSwap a b (rneg c) (rneg d))

------------------------------------------------------------
-- Multiplication-negation lemmas (needed for abs properties)
------------------------------------------------------------

def mulZeroLeft {R : Real} (a : Carrier R) : (rmul (rzero R) a) = (rzero R) :=
  addCancelRight (rmul (rzero R) a) (rzero R) (rmul (rzero R) a)
    (eqTrans (eqSym ((fieldOf R).distribRight (rzero R) (rzero R) a))
      (eqTrans (eqCong (fun z => rmul z a) (addZeroLeft (rzero R)))
        (eqSym (addZeroLeft (rmul (rzero R) a)))))

-- TACTIC-MODE in source (erw).
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
-- Not an extra axiom: an ordered field already asserts 0 ≤ 1 (zeroLeOne) and
-- 0 ≠ 1 (zeroNeOne), and a < b is defined as exactly that pair. So strict
-- positivity of 1 is just those two axioms put together.
def zeroLtOne (R : Real) : rlt (rzero R) (rone R) :=
  Pair.mk ((fieldOf R).zeroLeOne) ((fieldOf R).zeroNeOne)

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

def mulNegLeft {R : Real} (a b : Carrier R) : (rmul (rneg a) b) = (rneg (rmul a b)) :=
  eqTrans ((fieldOf R).mulComm (rneg a) b)
    (eqTrans (mulNegRight b a) (eqCong (fun z => rneg z) ((fieldOf R).mulComm b a)))

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

/-- the triangle inequality -/
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

def absOfNonpos {R : Real} (a : Carrier R) (h : rle a (rzero R)) : (rabs a) = (rneg a) :=
  absElim a (fun x => x = (rneg a))
    (fun h2 => eqTrans (eqSym ((fieldOf R).leAntisym (rzero R) a h2 h))
      (eqTrans (eqSym (negZero R)) (eqCong (fun z => rneg z) ((fieldOf R).leAntisym (rzero R) a h2 h))))
    (fun _ => rfl)

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

/-- positivity of halving -/
def divTwoPos {R : Real} (e : Carrier R) (hlt : rlt (rzero R) e) :
    rlt (rzero R) (rdiv e (rtwo R)) :=
  replace (fun z => rlt (rzero R) z) (halfEqDiv e) (halfMulEpsPos e hlt)

-- General positivity of quotients: 0 < a and 0 < b give 0 < a / b. The ε-δ
-- proofs mostly need the divTwoPos special case above, but the general form
-- belongs in the toolkit (statement faithful; body sorried like the other
-- ports of TT tactic proofs — the sorry surfaces as a warning, not an error).
/-- positivity of quotients -/
def divPos {R : Real} (a b : Carrier R) (ha : rlt (rzero R) a) (hb : rlt (rzero R) b) :
    rlt (rzero R) (rdiv a b) :=
  mulPos a (rinv b) ha (invPosStrict b hb)

def divTwoAddEq {R : Real} (e : Carrier R) :
    (radd (rdiv e (rtwo R)) (rdiv e (rtwo R))) = e :=
  replace (fun z => (radd z z) = e) (halfEqDiv e) (halfMulEps e)

/-- the halves adding up to ε -/
def convertEps {R : Real} (epsilon v : Carrier R)
    (hlt : rlt v (radd (rdiv epsilon (rtwo R)) (rdiv epsilon (rtwo R)))) : rlt v epsilon :=
  replace (fun z => rlt v z) (divTwoAddEq epsilon) hlt

`;

const REAL_ANALYSIS = RA_TOWER + `-- THE milestone: lim f + lim g = lim (f + g), the way a textbook writes it.
--
-- Take δ to be the SMALLER of the two deltas. min is below both, so one δ
-- serves both estimates and there is nothing to case-split on — compare the
-- earlier seeding of this proof, which split on which delta was smaller and
-- then repeated the whole ε/2 + ε/2 argument in each branch.
--
-- Write δ for that minimum; minPos gives 0 < δ, and minLeLeft/minLeRight
-- carry |x − x₀| < δ down
-- to each delta; then subAddSub → absTriangle → convertEps → addLtBoth.
-- limitAddFromScratch below is the blank slate to build it in yourself.
def limitAdd {R : Real} (f g : Carrier R → Carrier R) (x0 L M : Carrier R)
    (limF : Limit f x0 L) (limG : Limit g x0 M) :
    Limit (fun x => radd (f x) (g x)) x0 (radd L M) := by
  constructor
  intro ε epsPos
  have h2 : 0 < ε / 2 := divTwoPos ε epsPos
  have hF := limF.eps_delta (ε / 2) h2
  obtain ⟨deltaF, fProof⟩ := hF
  have hG := limG.eps_delta (ε / 2) h2
  obtain ⟨deltaG, gProof⟩ := hG
  obtain ⟨dfPos, fFn⟩ := fProof
  obtain ⟨dgPos, gFn⟩ := gProof
  let delta := min(deltaF, deltaG)
  constructor
  case eps_delta.fst =>
    exact delta
  case eps_delta.snd =>
    constructor
    case fst =>
      exact minPos deltaF deltaG dfPos dgPos
    case snd =>
      intro x h h1
      have hxF := ltLeTrans |x - x0| delta deltaF h1 (minLeLeft deltaF deltaG)
      have hxG := ltLeTrans |x - x0| delta deltaG h1 (minLeRight deltaF deltaG)
      have fHalfEps := fFn x h hxF
      have gHalfEps := gFn x h hxG
      apply leLtTrans
      case b =>
        exact |f x - L| + |g x - M|
      case hab =>
        rw [subAddSub]
        exact absTriangle (f x - L) (g x - M)
      case hbc =>
        apply convertEps
        exact addLtBoth |f x - L| (ε / 2) |g x - M| (ε / 2) fHalfEps gHalfEps

-- The same exercise with nothing filled in — for building the whole thing from
-- the first click (and for the tests that check each of those clicks works).

def limitAddFromScratch {R : Real} (f g : Carrier R → Carrier R) (x0 L M : Carrier R)
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

-- Translation invariance, the STRICT version. The ordered field gives it for ≤
-- (addLeLeft); a < b is (a ≤ b) paired with (a ≠ b), and the ≠ half is exactly
-- right-cancellation.
def addLtRight {R : Real} (a b c : Carrier R) (h : rlt a b) :
    rlt (radd a c) (radd b c) :=
  Pair.mk (addLeRight a b c (Pair.fst h))
    (fun eq => Pair.snd h (addCancelRight a b c eq))

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

const VECTOR_SPACE = `-- Linear algebra from scratch: vector spaces, span, independence, basis.
-- THE exercise: every finite (list-spanned) vector space has a basis.
-- Fresh preset, so it uses core Prop connectives (∃, ∧, ∨) throughout —
-- goals and hypotheses read as ordinary logic.

structure Field' where
  F : Type
  zero : F
  one : F
  add : F → F → F
  mul : F → F → F
  neg : F → F
  inv : F → F  -- total; inv zero unspecified
  add_comm : ∀ a b, add a b = add b a
  add_assoc : ∀ a b c, add (add a b) c = add a (add b c)
  add_zero : ∀ a, add a zero = a
  add_neg : ∀ a, add a (neg a) = zero
  mul_comm : ∀ a b, mul a b = mul b a
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  mul_one : ∀ a, mul a one = a
  mul_inv : ∀ a, a ≠ zero → mul a (inv a) = one
  distrib : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c)
  zero_ne_one : zero ≠ one

-- Display: a VECTOR SPACE stands for its own carrier (the mathematician's
-- abuse of notation — "vs ∈ List(W)", not "List(W.V)"), and a list's length
-- is |vs|. Display-only unexpanders; the source spellings still work.
structure VectorSpace (K : Field') where
  V : Type
  zero : V
  add : V → V → V
  neg : V → V
  smul : K.F → V → V
  add_comm : ∀ u v, add u v = add v u
  add_assoc : ∀ u v w, add (add u v) w = add u (add v w)
  add_zero : ∀ v, add v zero = v
  add_neg : ∀ v, add v (neg v) = zero
  smul_one : ∀ v, smul K.one v = v
  smul_assoc : ∀ a b v, smul (K.mul a b) v = smul a (smul b v)
  smul_add : ∀ a u v, smul a (add u v) = add (smul a u) (smul a v)
  add_smul : ∀ a b v, smul (K.add a b) v = add (smul a v) (smul b v)

@[app_unexpander VectorSpace.V] def unexpVSCarrier : Lean.PrettyPrinter.Unexpander
  | \`($_ $W) => pure W
  | _ => throw ()

-- |vs| for list length. The atomic/noWs macro form (same trick as the
-- real-analysis |a| for rabs) keeps the bars away from an inductive's own
-- alternative bars; the unexpander gives the display direction.
macro:max atomic("|" noWs) l:term noWs "|" : term => \`(List.length $l)
@[app_unexpander List.length] def unexpListLength : Lean.PrettyPrinter.Unexpander
  | \`($_ $l) => \`(|$l|)
  | _ => throw ()

-- K and W are bound EXPLICITLY on every declaration (no section variable):
-- a section-included implicit that the statement never names shows up in the
-- goal context under Lean's inaccessible dagger (K✝), which is an internal
-- encoding no reader should see.

-- Membership in the span, as an inductive: the zero vector is in it, and it
-- is closed under adding a scaled generator. (An inductive beats the
-- ∃-of-coefficient-lists form: every span lemma becomes an induction on the
-- derivation instead of coefficient-list surgery.)
inductive InSpan {K : Field'} (W : VectorSpace K) (vs : List W.V) : W.V → Prop where
  | zero : InSpan W vs W.zero
  | step (c : K.F) (v : W.V) (hv : v ∈ vs) {u : W.V} (hu : InSpan W vs u) :
      InSpan W vs (W.add (W.smul c v) u)

-- vs spans the whole space.
def Spans {K : Field'} (W : VectorSpace K) (vs : List W.V) : Prop :=
  ∀ v, InSpan W vs v

-- No vector of vs is in the span of the OTHERS.
def Independent {K : Field'} (W : VectorSpace K) (vs : List W.V) : Prop :=
  ∀ v pre post, vs = pre ++ v :: post → ¬ InSpan W (pre ++ post) v

def Basis {K : Field'} (W : VectorSpace K) (vs : List W.V) : Prop :=
  Spans W vs ∧ Independent W vs

-- Prose notation: goals READ AS SENTENCES — "vs spans W", "bs is a basis
-- of W". Ordinary Lean notation, so display and input both work, defined
-- exactly where the domain lives: in the preset.
notation:50 vs:51 " spans " W:51 => Spans W vs
notation:50 bs:51 " is\u00a0a\u00a0basis\u00a0of " W:51 => Basis W bs
-- "v \u2208 span vs" \u2014 the operator reading of InSpan. The NBSP keeps "span" from
-- becoming a reserved keyword (same trick as the basis notation above); the
-- vector space is inferred from the list.
notation:50 v:51 " \u2208\u00a0span " vs:max => InSpan _ vs v
-- The wildcard in the expansion blocks the auto-generated delaborator, so
-- displays kept printing raw InSpan applications; say it explicitly.
@[app_unexpander InSpan] def unexpInSpan : Lean.PrettyPrinter.Unexpander
  | \`($_ $W $vs $v) => \`($v \u2208\u00a0span $vs)
  | _ => throw ()

-- Some vector is in the span of the OTHERS. (Reducible so obtain unpacks it.)
@[reducible] def Dependent {K : Field'} (W : VectorSpace K) (vs : List W.V) : Prop :=
  ∃ v pre post, vs = pre ++ v :: post ∧ InSpan W (pre ++ post) v

-- Scaling zero gives zero: not an axiom, but forced by distributivity plus
-- cancellation (s = s + s only for s = 0).
theorem smulZero {K : Field'} {W : VectorSpace K} (c : K.F) : W.smul c W.zero = W.zero := by
  have h : W.smul c W.zero = W.add (W.smul c W.zero) (W.smul c W.zero) := by
    rw [← W.smul_add, W.add_zero]
  have h2 := congrArg (fun x => W.add x (W.neg (W.smul c W.zero))) h
  simp only [W.add_assoc, W.add_neg] at h2
  rw [W.add_zero] at h2
  exact h2.symm

-- The span is closed under addition: induct on the left derivation.
theorem spanAdd {K : Field'} {W : VectorSpace K} (ws : List W.V) {a b : W.V}
    (ha : InSpan W ws a) (hb : InSpan W ws b) : InSpan W ws (W.add a b) := by
  induction ha with
  | zero => rw [W.add_comm, W.add_zero]; exact hb
  | step c v hv hu ih => rw [W.add_assoc]; exact InSpan.step c v hv ih

-- The span is closed under scaling: scale each step of the derivation.
theorem spanSmul {K : Field'} {W : VectorSpace K} (ws : List W.V) (c : K.F) {a : W.V}
    (ha : InSpan W ws a) : InSpan W ws (W.smul c a) := by
  induction ha with
  | zero => rw [smulZero]; exact InSpan.zero
  | step c' v hv hu ih =>
    rw [W.smul_add, ← W.smul_assoc]
    exact InSpan.step (K.mul c c') v hv ih

-- Anything in the span of vs is in the span of ws, provided every GENERATOR
-- of vs is: induct on the derivation, rebuilding each step with the two
-- closure lemmas.
/-- monotonicity of span -/
theorem spanMono {K : Field'} {W : VectorSpace K} (vs ws : List W.V)
    (hgen : ∀ v, v ∈ vs → InSpan W ws v) {u : W.V}
    (hu : InSpan W vs u) : InSpan W ws u := by
  induction hu with
  | zero => exact InSpan.zero
  | step c v hv hu ih => exact spanAdd ws (spanSmul ws c (hgen v hv)) ih

-- Every generator is in the span: c := one, rest := zero.
/-- generators lying in their own span -/
theorem generatorInSpan {K : Field'} {W : VectorSpace K} (vs : List W.V) (v : W.V) (hv : v ∈ vs) :
    InSpan W vs v := by
  have h := InSpan.step K.one v hv InSpan.zero
  rw [W.add_zero, W.smul_one] at h
  exact h

-- Removing a vector that the rest already spans keeps the span — the heart
-- of basis extraction. Every generator of vs is in the span of pre ++ post
-- (v by hv, the others by membership), so spanMono carries every derivation
-- across.
/-- redundancy of a vector the rest already spans -/
theorem spanDrop {K : Field'} {W : VectorSpace K} (vs pre post : List W.V) (v : W.V)
    (hvs : vs = pre ++ v :: post)
    (hv : InSpan W (pre ++ post) v)
    (hs : Spans W vs) : Spans W (pre ++ post) := by
  intro u
  apply spanMono vs (pre ++ post)
  · intro w hw
    rw [hvs] at hw
    rcases List.mem_append.mp hw with hpre | hcons
    · exact generatorInSpan _ w (List.mem_append.mpr (Or.inl hpre))
    · rcases List.mem_cons.mp hcons with rfl | hpost
      · exact hv
      · exact generatorInSpan _ w (List.mem_append.mpr (Or.inr hpost))
  · exact hs u

-- The empty list is trivially independent.
/-- vacuous independence of the empty list -/
theorem nilIndependent {K : Field'} {W : VectorSpace K} : Independent W [] := by
  intro v pre post h
  cases pre <;> simp_all

-- Classically, a list is independent or some vector lies in the span of the
-- others. (The negation-pushing lives HERE, once, so the main proof below
-- reads as a clean case split.)
/-- the independence dichotomy -/
theorem independentOrDependent {K : Field'} {W : VectorSpace K} (vs : List W.V) :
    Independent W vs ∨ Dependent W vs := by
  cases Classical.em (Independent W vs) with
  | inl h => exact Or.inl h
  | inr h =>
    right
    simp only [Independent, Classical.not_forall, Classical.not_imp, Classical.not_not] at h
    obtain ⟨v, pre, post, h1, h2⟩ := h
    exact ⟨v, pre, post, h1, h2⟩

-- THE theorem: a space spanned by SOME list has a basis. Extraction, by
-- induction on a length bound: either vs is independent — it IS a basis — or
-- some vector lies in the span of the others; drop it (the span survives, by
-- spanDrop) and continue with the strictly shorter list.
-- Dropping one vector strictly shrinks the list — the bound for the
-- recursion. (Library lemma: tactic machinery like simp-at/omega lives here,
-- so the MAIN proof below stays within the editor's renderable subset.)
/-- strong induction on the length of a list -/
theorem lengthStrongInduction {α : Type u} {P : List α → Prop}
    (step : ∀ vs : List α, (∀ ws : List α, ws.length < vs.length → P ws) → P vs) :
    ∀ vs : List α, P vs := by
  have aux : ∀ n (vs : List α), vs.length ≤ n → P vs := by
    intro n
    induction n with
    | zero =>
      intro vs hle
      exact step vs (fun ws hw => absurd (Nat.lt_of_lt_of_le hw hle) (Nat.not_lt_zero _))
    | succ n ih =>
      intro vs hle
      exact step vs (fun ws hw => ih ws (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hw hle)))
  intro vs
  exact aux vs.length vs (Nat.le_refl _)

/-- the length decrease from dropping a vector -/
theorem lengthDropLt {K : Field'} {W : VectorSpace K} (v : W.V) (pre post vs : List W.V)
    (hvs : vs = pre ++ v :: post) : (pre ++ post).length < vs.length := by
  subst hvs
  simp [List.length_append]

theorem basisExistsAux {K : Field'} {W : VectorSpace K} : ∀ vs : List W.V, Spans W vs →
    ∃ bs : List W.V, Basis W bs := by
  apply lengthStrongInduction
  intro vs ih h
  cases independentOrDependent vs with
  | inl hind => exact ⟨vs, h, hind⟩
  | inr hdep =>
    obtain ⟨v, pre, post, hvs, hspan⟩ := hdep
    exact ih (pre ++ post) (lengthDropLt v pre post vs hvs) (spanDrop vs pre post v hvs hspan h)

theorem basisExists {K : Field'} {W : VectorSpace K} (vs : List W.V) (h : Spans W vs) :
    ∃ bs : List W.V, Basis W bs :=
  basisExistsAux vs h
`;

const MATHLIB = `import Mathlib

-- Requires the Mathlib toggle (first build is slow).
example (a b : ℝ) : a + b = b + a := by ring

example (n : ℕ) : ∑ i ∈ Finset.range n, (i : ℚ) = n * (n - 1) / 2 := by
  induction n with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

-- The SAME obligation the from-scratch Real Analysis preset needs, where it
-- costs a chain of ~20 hand-proved lemmas up from the ordered-field axioms.
-- Here it is one suggestion, and the editor finds it without being told Mathlib
-- is loaded: "positivity" is offered on every goal and simply fails to validate
-- where it doesn't exist.
theorem halfPos (ε : ℝ) (hε : 0 < ε) : 0 < ε / 2 := by
  sorry

-- Likewise "linarith" for the arithmetic the from-scratch preset had to build
-- translation-invariance lemmas for.
theorem shiftLt (a b c : ℝ) (h : a < b) : a + c < b + c := by
  sorry
`;

const MULTIVAR = RA_TOWER + `
------------------------------------------------------------
-- Multivariable: R^m, matrices, and the total derivative
------------------------------------------------------------

-- R^m as functions from Fin m; a matrix as its rows.
@[reducible] def Vec (R : Real) (m : Nat) : Type := Fin m → Carrier R
@[reducible] def Mat (R : Real) (n m : Nat) : Type := Fin n → Fin m → Carrier R

def vadd {R : Real} {m : Nat} (u v : Vec R m) : Vec R m := fun i => radd (u i) (v i)
def vsub {R : Real} {m : Nat} (u v : Vec R m) : Vec R m := fun i => rsub (u i) (v i)
def smulV {R : Real} {m : Nat} (t : Carrier R) (v : Vec R m) : Vec R m := fun i => rmul t (v i)

-- The j-th standard basis vector.
def basis {R : Real} {m : Nat} (j : Fin m) : Vec R m :=
  fun i => if i = j then rone R else rzero R

-- Finite sums over Fin k, peeling the LAST index.
def finSum {R : Real} : (k : Nat) → (Fin k → Carrier R) → Carrier R
  | .zero, _ => rzero R
  | .succ k, f => radd (finSum k (fun i => f i.castSucc)) (f (Fin.last k))

def finSumCongr {R : Real} : (k : Nat) → {f g : Fin k → Carrier R} →
    ((i : Fin k) → (f i) = (g i)) → (finSum k f) = (finSum k g)
  | .zero, _, _, _ => rfl
  | .succ k, f, g, h =>
    eqTrans (eqCong (fun z => radd z (f (Fin.last k))) (finSumCongr k (fun i => h i.castSucc)))
      (eqCong (fun z => radd (finSum k (fun i => g i.castSucc)) z) (h (Fin.last k)))

def finSumZero {R : Real} : (k : Nat) → (finSum (R := R) k (fun _ => rzero R)) = (rzero R)
  | .zero => rfl
  | .succ k =>
    eqTrans (eqCong (fun z => radd z (rzero R)) (finSumZero k)) ((fieldOf R).addZeroRight (rzero R))

-- A sum with a single nonzero entry is that entry.
def finSumSingle {R : Real} : (k : Nat) → (j : Fin k) → (c : Carrier R) →
    (finSum k (fun i => if i = j then c else rzero R)) = c
  | .succ k, j, c => by
    induction j using Fin.lastCases with
    | last =>
      show (radd (finSum k fun i => if i.castSucc = Fin.last k then c else rzero R)
        (if (Fin.last k) = (Fin.last k) then c else rzero R)) = c
      rw [if_pos rfl]
      have he : ∀ i : Fin k, (if i.castSucc = Fin.last k then c else rzero R) = rzero R := by
        intro i
        rw [if_neg (Fin.ne_of_lt (Fin.castSucc_lt_last i))]
      rw [finSumCongr k he, finSumZero k]
      exact addZeroLeft c
    | cast j' =>
      show (radd (finSum k fun i => if i.castSucc = j'.castSucc then c else rzero R)
        (if (Fin.last k) = j'.castSucc then c else rzero R)) = c
      rw [if_neg (Ne.symm (Fin.ne_of_lt (Fin.castSucc_lt_last j')))]
      have he : ∀ i : Fin k, (if i.castSucc = j'.castSucc then c else rzero R)
          = (if i = j' then c else rzero R) := by
        intro i
        by_cases hij : i = j'
        · rw [if_pos hij, if_pos (by rw [hij])]
        · rw [if_neg hij, if_neg (fun he => hij (Fin.castSucc_inj.1 he))]
      rw [finSumCongr k he, finSumSingle k j' c]
      exact (fieldOf R).addZeroRight c

-- The (sum) norm on R^m.
def vnorm {R : Real} {m : Nat} (v : Vec R m) : Carrier R :=
  finSum m (fun i => rabs (v i))

def mulVec {R : Real} {n m : Nat} (A : Mat R n m) (v : Vec R m) : Vec R n :=
  fun i => finSum m (fun j => rmul (A i j) (v j))

-- Prose notation for the vector layer: goals read as mathematics (u + v,
-- t • v, ‖v‖, A ⬝ v, ℝ^m) instead of as calls. The tower already claims
-- + - * for the CARRIER at high priority; these are overloads, and Lean
-- picks whichever elaborates. Display comes from the unexpanders.
infixl:65 " + " => vadd
infixl:65 " - " => vsub
infixr:73 " • " => smulV
infixl:74 " ⬝ " => mulVec
notation:max "‖" v "‖" => vnorm v
notation:max "e_" j:max => basis j
notation:max "ℝ^" m:max => Vec _ m

@[app_unexpander vadd] def unexpVadd : Lean.PrettyPrinter.Unexpander
  | \`($_ $u $v) => \`($u + $v)
  | _ => throw ()
@[app_unexpander vsub] def unexpVsub : Lean.PrettyPrinter.Unexpander
  | \`($_ $u $v) => \`($u - $v)
  | _ => throw ()
@[app_unexpander smulV] def unexpSmulV : Lean.PrettyPrinter.Unexpander
  | \`($_ $t $v) => \`($t • $v)
  | _ => throw ()
@[app_unexpander mulVec] def unexpMulVec : Lean.PrettyPrinter.Unexpander
  | \`($_ $A $v) => \`($A ⬝ $v)
  | _ => throw ()
@[app_unexpander vnorm] def unexpVnorm : Lean.PrettyPrinter.Unexpander
  | \`($_ $v) => \`(‖$v‖)
  | _ => throw ()
@[app_unexpander basis] def unexpBasis : Lean.PrettyPrinter.Unexpander
  | \`($_ $j) => \`(e_ $j)
  | _ => throw ()
@[app_unexpander Vec] def unexpVec : Lean.PrettyPrinter.Unexpander
  | \`($_ $_R $m) => \`(ℝ^$m)
  | _ => throw ()
@[app_unexpander Mat] def unexpMat : Lean.PrettyPrinter.Unexpander
  | \`($_ $_R $n $m) => \`(ℝ^$n×$m)
  | _ => throw ()

-- Matrix times a scaled basis vector picks out one column, scaled:
-- (A · (t e_j))_i = t * A_ij.
def mulVecBasis {R : Real} {n m : Nat} (A : Mat R n m) (t : Carrier R)
    (j : Fin m) (i : Fin n) :
    ((mulVec A (smulV t (basis j))) i) = (rmul t (A i j)) := by
  show (finSum m fun l => rmul (A i l) (rmul t (basis j l))) = rmul t (A i j)
  have he : ∀ l : Fin m, (rmul (A i l) (rmul t (basis j l)))
      = (if l = j then rmul t (A i j) else rzero R) := by
    intro l
    by_cases hlj : l = j
    · rw [if_pos hlj, hlj]
      have hb : (basis (R := R) j j) = rone R := by
        show (if j = j then rone R else rzero R) = rone R
        rw [if_pos rfl]
      rw [hb]
      exact eqTrans (eqCong (fun z => rmul (A i j) z) ((fieldOf R).mulOneRight t))
        ((fieldOf R).mulComm (A i j) t)
    · rw [if_neg hlj]
      have hb : (basis (R := R) j l) = rzero R := by
        show (if l = j then rone R else rzero R) = rzero R
        rw [if_neg hlj]
      rw [hb]
      exact eqTrans (eqCong (fun z => rmul (A i l) z) (mulZeroRight t)) (mulZeroRight (A i l))
  rw [finSumCongr m he, finSumSingle m j (rmul t (A i j))]

-- The norm of a scaled basis vector is |t|.
def vnormBasis {R : Real} {m : Nat} (t : Carrier R) (j : Fin m) :
    (vnorm (smulV t (basis j))) = (rabs t) := by
  show (finSum m fun i => rabs (rmul t (basis j i))) = rabs t
  have he : ∀ i : Fin m, (rabs (rmul t (basis j i))) = (if i = j then rabs t else rzero R) := by
    intro i
    by_cases hij : i = j
    · rw [if_pos hij, hij]
      have hb : (basis (R := R) j j) = rone R := by
        show (if j = j then rone R else rzero R) = rone R
        rw [if_pos rfl]
      rw [hb]
      exact eqCong (fun z => rabs z) ((fieldOf R).mulOneRight t)
    · rw [if_neg hij]
      have hb : (basis (R := R) j i) = rzero R := by
        show (if i = j then rone R else rzero R) = rzero R
        rw [if_neg hij]
      rw [hb, mulZeroRight t, absZero]
  rw [finSumCongr m he, finSumSingle m j (rabs t)]

-- A sum of nonnegative terms is nonnegative.
def finSumNonneg {R : Real} : (k : Nat) → (f : Fin k → Carrier R) →
    ((l : Fin k) → rle (rzero R) (f l)) → rle (rzero R) (finSum k f)
  | .zero, _, _ => (fieldOf R).leRefl (rzero R)
  | .succ k, f, h =>
    replace (fun z => rle z (radd (finSum k fun l => f l.castSucc) (f (Fin.last k))))
      (addZeroLeft (rzero R))
      (addLeBoth (rzero R) (finSum k fun l => f l.castSucc) (rzero R) (f (Fin.last k))
        (finSumNonneg k _ (fun l => h l.castSucc)) (h (Fin.last k)))

-- Any single nonnegative term is at most the whole sum.
def termLeSum {R : Real} : (k : Nat) → (f : Fin k → Carrier R) →
    ((l : Fin k) → rle (rzero R) (f l)) → (j : Fin k) → rle (f j) (finSum k f)
  | .succ k, f, h, j => by
    induction j using Fin.lastCases with
    | last =>
      show rle (f (Fin.last k)) (radd (finSum k fun l => f l.castSucc) (f (Fin.last k)))
      exact replace (fun z => rle z (radd (finSum k fun l => f l.castSucc) (f (Fin.last k))))
        (addZeroLeft (f (Fin.last k)))
        (addLeRight (rzero R) (finSum k fun l => f l.castSucc) (f (Fin.last k))
          (finSumNonneg k _ (fun l => h l.castSucc)))
    | cast j' =>
      show rle (f j'.castSucc) (radd (finSum k fun l => f l.castSucc) (f (Fin.last k)))
      exact (fieldOf R).leTrans (f j'.castSucc) (finSum k fun l => f l.castSucc)
        (radd (finSum k fun l => f l.castSucc) (f (Fin.last k)))
        (termLeSum k _ (fun l => h l.castSucc) j')
        (replace (fun z => rle z (radd (finSum k fun l => f l.castSucc) (f (Fin.last k))))
          ((fieldOf R).addZeroRight (finSum k fun l => f l.castSucc))
          ((fieldOf R).addLeLeft (rzero R) (f (Fin.last k)) (finSum k fun l => f l.castSucc)
            (h (Fin.last k))))

-- Every component is bounded by the norm.
def componentLeNorm {R : Real} {m : Nat} (v : Vec R m) (i : Fin m) :
    rle (rabs (v i)) (vnorm v) :=
  termLeSum m (fun l => rabs (v l)) (fun l => absNonneg (v l)) i

-- THE definition: A is the derivative of f at x when the linear approximation
-- error vanishes faster than the displacement — for every ε > 0 there is a
-- δ > 0 with ‖f(x+h) − f(x) − A·h‖ ≤ ε‖h‖ whenever 0 < ‖h‖ < δ.
@[reducible] def HasDerivAt {R : Real} {m n : Nat}
    (f : Vec R m → Vec R n) (x : Vec R m) (A : Mat R n m) : Type :=
  (epsilon : Carrier R) → rlt (rzero R) epsilon →
    DPair (Carrier R) (fun delta => Pair (rlt (rzero R) delta)
      ((h : Vec R m) → rlt (rzero R) (vnorm h) → rlt (vnorm h) delta →
        rle (vnorm (vsub (f (vadd x h)) (vadd (f x) (mulVec A h)))) (rmul epsilon (vnorm h))))

-- ============ the order/division helpers for the estimate ============

-- 0 ≤ x − y exactly captures y ≤ x, in the direction we need.
def subNonnegOfLe {R : Real} (b c : Carrier R) (h : rle b c) : rle (rzero R) (rsub c b) :=
  replace (fun z => rle z (rsub c b)) (addNegRight b)
    (addLeRight b c (rneg b) h)

def leOfSubNonneg {R : Real} (x y : Carrier R) (h : rle (rzero R) (rsub x y)) : rle y x :=
  replace (fun z => rle z x) (addZeroLeft y)
    (replace (fun z => rle (radd (rzero R) y) z)
      (eqTrans ((fieldOf R).addAssoc x (rneg y) y)
        (eqTrans (eqCong (fun z => radd x z) (negLeft y)) ((fieldOf R).addZeroRight x)))
      (addLeRight (rzero R) (rsub x y) y h))

-- Multiplying an inequality by a nonnegative factor on the right.
def mulLeMonoRight {R : Real} (a b c : Carrier R) (hab : rle a b) (hc : rle (rzero R) c) :
    rle (rmul a c) (rmul b c) := by
  apply leOfSubNonneg
  have hd : (rsub (rmul b c) (rmul a c)) = (rmul (rsub b a) c) :=
    eqSym (eqTrans ((fieldOf R).distribRight b (rneg a) c)
      (eqCong (fun z => radd (rmul b c) z) (mulNegLeft a c)))
  rw [hd]
  exact (fieldOf R).mulNonneg (rsub b a) c (subNonnegOfLe a b hab) hc

-- Subtraction distributes over a common denominator (no side condition:
-- division IS multiplication by the inverse).
def divSubLeft {R : Real} (u w t : Carrier R) :
    (rsub (rdiv u t) (rdiv w t)) = (rdiv (rsub u w) t) :=
  eqSym (eqTrans ((fieldOf R).distribRight u (rneg w) (rinv t))
    (eqCong (fun z => radd (rdiv u t) z) (mulNegLeft w (rinv t))))

-- (t·c)/t = c for t ≠ 0.
def mulDivCancelLeft {R : Real} (t c : Carrier R) (tne : t = (rzero R) → MyVoid) :
    (rdiv (rmul t c) t) = c :=
  eqTrans (eqCong (fun z => rmul z (rinv t)) ((fieldOf R).mulComm t c))
    (eqTrans ((fieldOf R).mulAssoc c t (rinv t))
      (eqTrans (eqCong (fun z => rmul c z) ((fieldOf R).mulInvRight t tne))
        ((fieldOf R).mulOneRight c)))

-- |t| of a nonzero t is nonzero, and t − 0 = t.
def subZero {R : Real} (t : Carrier R) : (rsub t (rzero R)) = t :=
  eqTrans (eqCong (fun z => radd t z) (negZero R)) ((fieldOf R).addZeroRight t)

def neZeroOfAbsPos {R : Real} (t : Carrier R) (h : rlt (rzero R) (rabs t)) :
    t = (rzero R) → MyVoid :=
  fun he => Pair.snd h (eqSym (eqTrans (eqCong (fun z => rabs z) he) (absZero R)))

-- |t|·|1/t| = 1 for t ≠ 0.
def absMulAbsInv {R : Real} (t : Carrier R) (tne : t = (rzero R) → MyVoid) :
    (rmul (rabs t) (rabs (rinv t))) = (rone R) :=
  eqTrans (eqSym (absMul t (rinv t)))
    (eqTrans (eqCong (fun z => rabs z) ((fieldOf R).mulInvRight t tne))
      (absOfNonneg (rone R) (zeroLeOne R)))

-- Half of a positive is strictly below it.
def halfLtSelf {R : Real} (e : Carrier R) (he : rlt (rzero R) e) :
    rlt (rdiv e (rtwo R)) e :=
  replace (fun z => rlt z e) ((fieldOf R).addZeroRight (rdiv e (rtwo R)))
    (replace (fun z => rlt (radd (rdiv e (rtwo R)) (rzero R)) z) (divTwoAddEq e)
      (addLtLeft (rzero R) (rdiv e (rtwo R)) (rdiv e (rtwo R)) (divTwoPos e he)))


-- a − (b+c) = (a − b) − c.
def subSubOfSubAdd {R : Real} (a b c : Carrier R) :
    (rsub a (radd b c)) = (rsub (rsub a b) c) :=
  eqTrans (eqCong (fun z => radd a z) (negAdd b c))
    (eqSym ((fieldOf R).addAssoc a (rneg b) (rneg c)))

-- ============ THE JACOBIAN THEOREM ============

-- JACOBIAN: the best linear approximation, when it exists, has the partial
-- derivatives as entries. Fix a row i and a column j; the difference quotient
-- of component i along direction e_j converges to A_ij. The proof: feed ε/2
-- to differentiability, keep its δ. For 0 < |t| < δ the displacement h = t·e_j
-- has norm |t|, so the approximation error is at most (ε/2)|t|; its i-th
-- component says |f(x+te_j)_i − f(x)_i − t·A_ij| ≤ (ε/2)|t|, and dividing by
-- |t| bounds the quotient's distance from A_ij by ε/2 < ε.
def jacobianEntries {R : Real} {m n : Nat}
    (f : Vec R m → Vec R n) (x : Vec R m) (A : Mat R n m)
    (hA : HasDerivAt f x A) (i : Fin n) (j : Fin m) :
    Limit (fun t => rdiv (rsub ((f (vadd x (smulV t (basis j)))) i) ((f x) i)) t)
      (rzero R) (A i j) := by
  constructor
  intro epsilon epsPos
  have hde := hA (rdiv epsilon (rtwo R)) (divTwoPos epsilon epsPos)
  obtain ⟨delta, dProof⟩ := hde
  obtain ⟨dPos, dBound⟩ := dProof
  constructor
  case snd =>
    constructor
    case fst =>
      exact dPos
    case snd =>
      intro t htPos htLt
      have tne : t = (rzero R) → MyVoid := neZeroOfAbsPos t (replace (fun z => rlt (rzero R) (rabs z)) (subZero t) htPos)
      have hnPos : rlt (rzero R) (vnorm (smulV t (basis j))) := replace (fun z => rlt (rzero R) z) (eqSym (vnormBasis t j)) (replace (fun z => rlt (rzero R) (rabs z)) (subZero t) htPos)
      have hnLt : rlt (vnorm (smulV t (basis j))) delta := replace (fun z => rlt z delta) (eqSym (vnormBasis t j)) (replace (fun z => rlt (rabs z) delta) (subZero t) htLt)
      have hbound := dBound (smulV t (basis j)) hnPos hnLt
      have hcomp : rle (rabs ((vsub (f (vadd x (smulV t (basis j)))) (vadd (f x) (mulVec A (smulV t (basis j))))) i)) (rmul (rdiv epsilon (rtwo R)) (rabs t)) := leLtTransLe (rabs ((vsub (f (vadd x (smulV t (basis j)))) (vadd (f x) (mulVec A (smulV t (basis j))))) i)) (vnorm (vsub (f (vadd x (smulV t (basis j)))) (vadd (f x) (mulVec A (smulV t (basis j)))))) (rmul (rdiv epsilon (rtwo R)) (rabs t)) (componentLeNorm (vsub (f (vadd x (smulV t (basis j)))) (vadd (f x) (mulVec A (smulV t (basis j))))) i) (replace (fun z => rle (vnorm (vsub (f (vadd x (smulV t (basis j)))) (vadd (f x) (mulVec A (smulV t (basis j)))))) (rmul (rdiv epsilon (rtwo R)) z)) (vnormBasis t j) hbound)
      have hshape : ((vsub (f (vadd x (smulV t (basis j)))) (vadd (f x) (mulVec A (smulV t (basis j))))) i) = (rsub (rsub ((f (vadd x (smulV t (basis j)))) i) ((f x) i)) (rmul t (A i j))) := eqTrans (eqCong (fun z => rsub ((f (vadd x (smulV t (basis j)))) i) (radd ((f x) i) z)) (mulVecBasis A t j i)) (subSubOfSubAdd ((f (vadd x (smulV t (basis j)))) i) ((f x) i) (rmul t (A i j)))
      have hnum : rle (rabs (rsub (rsub ((f (vadd x (smulV t (basis j)))) i) ((f x) i)) (rmul t (A i j)))) (rmul (rdiv epsilon (rtwo R)) (rabs t)) := replace (fun z => rle (rabs z) (rmul (rdiv epsilon (rtwo R)) (rabs t))) hshape hcomp
      have hsplit : (rsub (rdiv (rsub ((f (vadd x (smulV t (basis j)))) i) ((f x) i)) t) (A i j)) = (rdiv (rsub (rsub ((f (vadd x (smulV t (basis j)))) i) ((f x) i)) (rmul t (A i j))) t) := eqTrans (eqCong (fun z => rsub (rdiv (rsub ((f (vadd x (smulV t (basis j)))) i) ((f x) i)) t) z) (eqSym (mulDivCancelLeft t (A i j) tne))) (divSubLeft (rsub ((f (vadd x (smulV t (basis j)))) i) ((f x) i)) (rmul t (A i j)) t)
      have habs : (rabs (rsub (rdiv (rsub ((f (vadd x (smulV t (basis j)))) i) ((f x) i)) t) (A i j))) = (rmul (rabs (rsub (rsub ((f (vadd x (smulV t (basis j)))) i) ((f x) i)) (rmul t (A i j)))) (rabs (rinv t))) := eqTrans (eqCong (fun z => rabs z) hsplit) (absMul (rsub (rsub ((f (vadd x (smulV t (basis j)))) i) ((f x) i)) (rmul t (A i j))) (rinv t))
      rw [habs]
      have hchain : rle (rmul (rabs (rsub (rsub ((f (vadd x (smulV t (basis j)))) i) ((f x) i)) (rmul t (A i j)))) (rabs (rinv t))) (rmul (rmul (rdiv epsilon (rtwo R)) (rabs t)) (rabs (rinv t))) := mulLeMonoRight (rabs (rsub (rsub ((f (vadd x (smulV t (basis j)))) i) ((f x) i)) (rmul t (A i j)))) (rmul (rdiv epsilon (rtwo R)) (rabs t)) (rabs (rinv t)) hnum (absNonneg (rinv t))
      have he : (rmul (rmul (rdiv epsilon (rtwo R)) (rabs t)) (rabs (rinv t))) = (rdiv epsilon (rtwo R)) := eqTrans ((fieldOf R).mulAssoc (rdiv epsilon (rtwo R)) (rabs t) (rabs (rinv t))) (eqTrans (eqCong (fun z => rmul (rdiv epsilon (rtwo R)) z) (absMulAbsInv t tne)) ((fieldOf R).mulOneRight (rdiv epsilon (rtwo R))))
      exact leLtTrans (rmul (rabs (rsub (rsub ((f (vadd x (smulV t (basis j)))) i) ((f x) i)) (rmul t (A i j)))) (rabs (rinv t))) (rdiv epsilon (rtwo R)) epsilon (leLtTransLe (rmul (rabs (rsub (rsub ((f (vadd x (smulV t (basis j)))) i) ((f x) i)) (rmul t (A i j)))) (rabs (rinv t))) (rmul (rmul (rdiv epsilon (rtwo R)) (rabs t)) (rabs (rinv t))) (rdiv epsilon (rtwo R)) hchain (replace (fun z => rle z (rdiv epsilon (rtwo R))) (eqSym he) ((fieldOf R).leRefl (rdiv epsilon (rtwo R))))) (halfLtSelf epsilon epsPos)

#check @jacobianEntries
`;

const VANDERMONDE = MULTIVAR + `
------------------------------------------------------------
-- Determinants: first-row Laplace expansion
------------------------------------------------------------
-- (The tower binds + * - / to the carrier, so Nat index arithmetic is
-- spelled n.succ / Fin.succ throughout.)

-- Powers, for the Vandermonde entries.
def rpow {R : Real} (a : Carrier R) : Nat → Carrier R
  | .zero => rone R
  | .succ k => rmul a (rpow a k)

-- The first index of a nonempty Fin range.
def fin0 {k : Nat} : Fin k.succ := ⟨0, Nat.succ_pos k⟩

-- Alternating sum over Fin k: f 0 − f 1 + f 2 − …
def altSum {R : Real} : (k : Nat) → (Fin k → Carrier R) → Carrier R
  | .zero, _ => rzero R
  | .succ k, f => rsub (f fin0) (altSum k (fun j => f j.succ))

-- The k-th index of Fin n.succ with position j skipped: the columns of a
-- minor, renumbered. (Core Lean has no Fin.succAbove; this is it.)
def skip {n : Nat} (j : Fin n.succ) (k : Fin n) : Fin n.succ :=
  if Nat.blt k.val j.val then k.castSucc else k.succ

-- Delete row 0 and column j.
def minor {R : Real} {n : Nat} (A : Mat R n.succ n.succ) (j : Fin n.succ) : Mat R n n :=
  fun i k => A i.succ (skip j k)

-- The determinant, by expansion along the first row.
def det {R : Real} : (n : Nat) → Mat R n n → Carrier R
  | .zero, _ => rone R
  | .succ n, A => altSum n.succ (fun j => rmul (A fin0 j) (det n (minor A j)))

-- Replace one column.
def updateCol {R : Real} {n m : Nat} (A : Mat R n m) (j : Fin m) (u : Fin n → Carrier R) : Mat R n m :=
  fun i k => if k = j then u i else A i k

-- Scale one row.
def scaleRow {R : Real} {n m : Nat} (A : Mat R n m) (i0 : Fin n) (c : Carrier R) : Mat R n m :=
  fun i k => if i = i0 then rmul c (A i k) else A i k

#check @det
#check @minor

-- c(a − b) = ca − cb.
def mulSubRight {R : Real} (c a b : Carrier R) :
    (rmul c (rsub a b)) = (rsub (rmul c a) (rmul c b)) :=
  eqTrans ((fieldOf R).distribLeft c a (rneg b))
    (eqCong (fun z => radd (rmul c a) z) (mulNegRight c b))

def altSumCongr {R : Real} : (k : Nat) → {f g : Fin k → Carrier R} →
    ((j : Fin k) → (f j) = (g j)) → (altSum k f) = (altSum k g)
  | .zero, _, _, _ => rfl
  | .succ k, f, g, h =>
    eqTrans (eqCong (fun z => rsub z (altSum k (fun j => f j.succ))) (h fin0))
      (eqCong (fun z => rsub (g fin0) z) (altSumCongr k (fun j => h j.succ)))

def altSumZero {R : Real} : (k : Nat) → (altSum (R := R) k (fun _ => rzero R)) = (rzero R)
  | .zero => rfl
  | .succ k =>
    eqTrans (eqCong (fun z => rsub (rzero R) z) (altSumZero k)) (subZero (rzero R))

-- When every term past the head vanishes, the alternating sum IS the head.
/-- an alternating sum collapsing to its head -/
def altSumHead {R : Real} {k : Nat} (f : Fin k.succ → Carrier R)
    (h : (j : Fin k) → (f j.succ) = (rzero R)) : (altSum k.succ f) = (f fin0) :=
  eqTrans (eqCong (fun z => rsub (f fin0) z)
      (eqTrans (altSumCongr k h) (altSumZero k)))
    (subZero (f fin0))

-- Alternating sums scale.
/-- scaling an alternating sum -/
def altSumMul {R : Real} (c : Carrier R) : (k : Nat) → (f : Fin k → Carrier R) →
    (altSum k (fun j => rmul c (f j))) = (rmul c (altSum k f))
  | .zero, _ => eqSym (mulZeroRight c)
  | .succ k, f =>
    eqTrans (eqCong (fun z => rsub (rmul c (f fin0)) z) (altSumMul c k (fun j => f j.succ)))
      (eqSym (mulSubRight c (f fin0) (altSum k (fun j => f j.succ))))

/-- scaling a later row commuting with the minor -/
def minorScaleRow {R : Real} {n : Nat} (A : Mat R n.succ n.succ) (i0 : Fin n) (c : Carrier R)
    (j : Fin n.succ) :
    (minor (scaleRow A i0.succ c) j) = (scaleRow (minor A j) i0 c) := by
  funext i k
  show (scaleRow A i0.succ c) i.succ (skip j k) = (scaleRow (minor A j) i0 c) i k
  by_cases hi : i = i0
  · rw [hi]
    show (if i0.succ = i0.succ then rmul c (A i0.succ (skip j k)) else A i0.succ (skip j k))
      = (if i0 = i0 then rmul c ((minor A j) i0 k) else (minor A j) i0 k)
    rw [if_pos rfl, if_pos rfl]
    rfl
  · have his : i.succ = i0.succ → False := fun he => hi (Fin.succ_inj.mp he)
    show (if i.succ = i0.succ then rmul c (A i.succ (skip j k)) else A i.succ (skip j k))
      = (if i = i0 then rmul c ((minor A j) i k) else (minor A j) i k)
    rw [if_neg his, if_neg hi]
    rfl

/-- homogeneity of the determinant in each row -/
def detScaleRow {R : Real} : (n : Nat) → (A : Mat R n n) → (i0 : Fin n) → (c : Carrier R) →
    (det n (scaleRow A i0 c)) = (rmul c (det n A))
  | .succ n, A, i0, c => by
    induction i0 using Fin.cases with
    | zero =>
      show (altSum n.succ fun j => rmul ((scaleRow A fin0 c) fin0 j) (det n (minor (scaleRow A fin0 c) j)))
        = rmul c (altSum n.succ fun j => rmul (A fin0 j) (det n (minor A j)))
      rw [← altSumMul c n.succ (fun j => rmul (A fin0 j) (det n (minor A j)))]
      apply altSumCongr n.succ
      intro j
      have h1 : (scaleRow A fin0 c) fin0 j = rmul c (A fin0 j) := by
        show (if (fin0 : Fin n.succ) = fin0 then rmul c (A fin0 j) else A fin0 j) = rmul c (A fin0 j)
        rw [if_pos rfl]
      have h2 : (minor (scaleRow A fin0 c) j) = (minor A j) := by
        funext i k
        show (if i.succ = fin0 then rmul c (A i.succ (skip j k)) else A i.succ (skip j k))
          = A i.succ (skip j k)
        rw [if_neg (fun he => Nat.succ_ne_zero i.val (congrArg Fin.val he))]
      rw [h1, h2]
      exact (fieldOf R).mulAssoc c (A fin0 j) (det n (minor A j))
    | succ i0' =>
      show (altSum n.succ fun j => rmul ((scaleRow A i0'.succ c) fin0 j) (det n (minor (scaleRow A i0'.succ c) j)))
        = rmul c (altSum n.succ fun j => rmul (A fin0 j) (det n (minor A j)))
      rw [← altSumMul c n.succ (fun j => rmul (A fin0 j) (det n (minor A j)))]
      apply altSumCongr n.succ
      intro j
      have h1 : (scaleRow A i0'.succ c) fin0 j = A fin0 j := by
        show (if (fin0 : Fin n.succ) = i0'.succ then rmul c (A fin0 j) else A fin0 j) = A fin0 j
        rw [if_neg (fun he => Nat.succ_ne_zero i0'.val (congrArg Fin.val he).symm)]
      rw [h1, minorScaleRow A i0' c j, detScaleRow n (minor A j) i0' c]
      exact eqTrans (eqSym ((fieldOf R).mulAssoc (A fin0 j) c (det n (minor A j))))
        (eqTrans (eqCong (fun z => rmul z (det n (minor A j))) ((fieldOf R).mulComm (A fin0 j) c))
          ((fieldOf R).mulAssoc c (A fin0 j) (det n (minor A j))))

#check @detScaleRow

-- ============ index bookkeeping for minors ============
-- (Pure term proofs: omega cannot see this file's Nat.lt hypotheses.)

theorem skipOfLt {n : Nat} (j : Fin n.succ) (k : Fin n) (h : Nat.lt k.val j.val) :
    (skip j k) = k.castSucc := by
  unfold skip
  rw [if_pos (by rw [Nat.blt_eq]; exact h)]

theorem skipOfGe {n : Nat} (j : Fin n.succ) (k : Fin n) (h : Nat.le j.val k.val) :
    (skip j k) = k.succ := by
  unfold skip
  rw [if_neg (by rw [Nat.blt_eq]; exact Nat.not_lt.mpr h)]

theorem skipValLt {n : Nat} (j : Fin n.succ) (k : Fin n) (h : Nat.lt k.val j.val) :
    (skip j k).val = k.val := by
  rw [skipOfLt j k h]
  rfl

theorem skipValGe {n : Nat} (j : Fin n.succ) (k : Fin n) (h : Nat.le j.val k.val) :
    (skip j k).val = Nat.succ k.val := by
  rw [skipOfGe j k h]
  rfl

theorem skipNe {n : Nat} (j : Fin n.succ) (k : Fin n) : (skip j k) = j → False := by
  intro he
  have hv := congrArg Fin.val he
  by_cases h : Nat.lt k.val j.val
  · rw [skipValLt j k h] at hv
    exact Nat.lt_irrefl j.val (hv ▸ h)
  · have h2 := Nat.le_of_not_lt h
    rw [skipValGe j k h2] at hv
    exact Nat.not_succ_le_self k.val (by rw [hv]; exact h2)

theorem skipInj {n : Nat} (j : Fin n.succ) (k1 k2 : Fin n) (he : (skip j k1) = (skip j k2)) :
    k1 = k2 := by
  have hv := congrArg Fin.val he
  apply Fin.ext
  by_cases h1 : Nat.lt k1.val j.val
  · rw [skipValLt j k1 h1] at hv
    by_cases h2 : Nat.lt k2.val j.val
    · rw [skipValLt j k2 h2] at hv
      exact hv
    · rw [skipValGe j k2 (Nat.le_of_not_lt h2)] at hv
      exact absurd hv (Nat.ne_of_lt (Nat.lt_succ_of_le (Nat.le_of_lt (Nat.lt_of_lt_of_le h1 (Nat.le_of_not_lt h2)))))
  · rw [skipValGe j k1 (Nat.le_of_not_lt h1)] at hv
    by_cases h2 : Nat.lt k2.val j.val
    · rw [skipValLt j k2 h2] at hv
      exact absurd hv (Ne.symm (Nat.ne_of_lt (Nat.lt_succ_of_le (Nat.le_of_lt (Nat.lt_of_lt_of_le h2 (Nat.le_of_not_lt h1))))))
    · rw [skipValGe j k2 (Nat.le_of_not_lt h2)] at hv
      exact Nat.succ.inj hv

-- The position of column j inside the minor that skips column j2 (j ≠ j2).
def unskip {n : Nat} (j2 j : Fin n.succ) (hne : j.val = j2.val → False) : Fin n :=
  if h : Nat.blt j.val j2.val then
    ⟨j.val, Nat.lt_of_lt_of_le (Nat.blt_eq ▸ h) (Nat.le_of_lt_succ j2.isLt)⟩
  else
    ⟨Nat.pred j.val,
      Nat.lt_of_lt_of_le
        (Nat.pred_lt (fun h0 => Nat.not_lt_zero j2.val (h0 ▸
          (Nat.lt_of_le_of_ne (Nat.le_of_not_lt (fun hl => h ((Nat.blt_eq (x := j.val) (y := j2.val)).symm ▸ hl)))
            (fun he => hne he.symm)))))
        (Nat.le_of_lt_succ j.isLt)⟩

/-- the column-index round trip through a minor -/
theorem skipUnskip {n : Nat} (j2 j : Fin n.succ) (hne : j.val = j2.val → False) :
    (skip j2 (unskip j2 j hne)) = j := by
  apply Fin.ext
  unfold unskip
  by_cases h : Nat.blt j.val j2.val
  · rw [dif_pos h]
    rw [Nat.blt_eq] at h
    exact skipValLt j2 _ h
  · rw [dif_neg h]
    rw [Nat.blt_eq] at h
    have hlt : Nat.lt j2.val j.val :=
      Nat.lt_of_le_of_ne (Nat.le_of_not_lt h) (fun he => hne he.symm)
    have hpos : Nat.lt 0 j.val := Nat.lt_of_le_of_lt (Nat.zero_le j2.val) hlt
    have h3 : Nat.le j2.val (Nat.pred j.val) := Nat.le_pred_of_lt hlt
    rw [skipValGe j2 _ h3]
    show Nat.succ (Nat.pred j.val) = j.val
    exact Nat.succ_pred_eq_of_pos hpos

#check @skipUnskip

-- ============ columns: update, minors, multilinearity ============

theorem updateColSame {R : Real} {n m : Nat} (A : Mat R n m) (j : Fin m)
    (u : Fin n → Carrier R) (i : Fin n) : (updateCol A j u) i j = u i := by
  show (if j = j then u i else A i j) = u i
  rw [if_pos rfl]

theorem updateColOther {R : Real} {n m : Nat} (A : Mat R n m) (j : Fin m)
    (u : Fin n → Carrier R) (i : Fin n) (j2 : Fin m) (hne : j2 = j → False) :
    (updateCol A j u) i j2 = A i j2 := by
  show (if j2 = j then u i else A i j2) = A i j2
  rw [if_neg hne]

-- Replacing a column and then DELETING it changes nothing.
theorem minorUpdateColSame {R : Real} {n : Nat} (A : Mat R n.succ n.succ) (j : Fin n.succ)
    (u : Fin n.succ → Carrier R) : (minor (updateCol A j u) j) = (minor A j) := by
  funext i k
  exact updateColOther A j u i.succ (skip j k) (skipNe j k)

theorem skipEqIff {n : Nat} (j2 j : Fin n.succ) (hne : j.val = j2.val → False) (k : Fin n) :
    ((skip j2 k) = j) ↔ (k = unskip j2 j hne) := by
  constructor
  · intro h
    exact skipInj j2 k (unskip j2 j hne) (eqTrans h (eqSym (skipUnskip j2 j hne)))
  · intro h
    rw [h]
    exact skipUnskip j2 j hne

-- Replacing column j and then deleting a DIFFERENT column j2 leaves the
-- replacement in place, at the position column j occupies inside the minor.
theorem minorUpdateColOther {R : Real} {n : Nat} (A : Mat R n.succ n.succ)
    (j2 j : Fin n.succ) (hne : j.val = j2.val → False) (u : Fin n.succ → Carrier R) :
    (minor (updateCol A j u) j2)
      = (updateCol (minor A j2) (unskip j2 j hne) (fun i => u i.succ)) := by
  funext i k
  by_cases hk : k = unskip j2 j hne
  · have h1 : (skip j2 k) = j := (skipEqIff j2 j hne k).2 hk
    show (updateCol A j u) i.succ (skip j2 k) = (updateCol (minor A j2) (unskip j2 j hne) (fun i => u i.succ)) i k
    rw [h1, updateColSame A j u i.succ, hk, updateColSame (minor A j2) (unskip j2 j hne) _ i]
  · have h1 : (skip j2 k) = j → False := fun he => hk ((skipEqIff j2 j hne k).1 he)
    show (updateCol A j u) i.succ (skip j2 k) = (updateCol (minor A j2) (unskip j2 j hne) (fun i => u i.succ)) i k
    rw [updateColOther A j u i.succ (skip j2 k) h1,
        updateColOther (minor A j2) (unskip j2 j hne) _ i k hk]
    rfl

/-- additivity of alternating sums -/
def altSumAdd {R : Real} : (k : Nat) → (f g : Fin k → Carrier R) →
    (altSum k (fun j => radd (f j) (g j))) = (radd (altSum k f) (altSum k g))
  | .zero, _, _ => eqSym (addZeroLeft (rzero R))
  | .succ k, f, g =>
    eqTrans (eqCong (fun z => rsub (radd (f fin0) (g fin0)) z)
        (altSumAdd k (fun j => f j.succ) (fun j => g j.succ)))
      (subAddSub (f fin0) (g fin0)
        (altSum k (fun j => f j.succ)) (altSum k (fun j => g j.succ)))

/-- additivity of the determinant in any one column -/
def detColAdd {R : Real} : (n : Nat) → (A : Mat R n n) → (j : Fin n) → (u v : Fin n → Carrier R) →
    (det n (updateCol A j (fun i => radd (u i) (v i))))
      = (radd (det n (updateCol A j u)) (det n (updateCol A j v)))
  | .zero, _, j, _, _ => j.elim0
  | .succ n, A, j, u, v => by
    show (altSum n.succ fun j2 => rmul ((updateCol A j (fun i => radd (u i) (v i))) fin0 j2)
        (det n (minor (updateCol A j (fun i => radd (u i) (v i))) j2)))
      = radd (altSum n.succ fun j2 => rmul ((updateCol A j u) fin0 j2) (det n (minor (updateCol A j u) j2)))
          (altSum n.succ fun j2 => rmul ((updateCol A j v) fin0 j2) (det n (minor (updateCol A j v) j2)))
    rw [← altSumAdd n.succ
      (fun j2 => rmul ((updateCol A j u) fin0 j2) (det n (minor (updateCol A j u) j2)))
      (fun j2 => rmul ((updateCol A j v) fin0 j2) (det n (minor (updateCol A j v) j2)))]
    apply altSumCongr n.succ
    intro j2
    by_cases hj : j = j2
    · -- the replaced column is the one being deleted: the minors coincide
      rw [← hj, updateColSame A j _ fin0, updateColSame A j u fin0, updateColSame A j v fin0,
          minorUpdateColSame A j, minorUpdateColSame A j u, minorUpdateColSame A j v]
      exact (fieldOf R).distribRight (u fin0) (v fin0) (det n (minor A j))
    · -- a different column is deleted: the replacement survives inside the minor
      have hne : j.val = j2.val → False := fun he => hj (Fin.ext he)
      have hne2 : j = j2 → False := hj
      rw [updateColOther A j _ fin0 j2 (fun he => hne2 (eqSym he)),
          updateColOther A j u fin0 j2 (fun he => hne2 (eqSym he)),
          updateColOther A j v fin0 j2 (fun he => hne2 (eqSym he)),
          minorUpdateColOther A j2 j hne _, minorUpdateColOther A j2 j hne u,
          minorUpdateColOther A j2 j hne v,
          detColAdd n (minor A j2) (unskip j2 j hne) (fun i => u i.succ) (fun i => v i.succ)]
      exact (fieldOf R).distribLeft (A fin0 j2)
        (det n (updateCol (minor A j2) (unskip j2 j hne) fun i => u i.succ))
        (det n (updateCol (minor A j2) (unskip j2 j hne) fun i => v i.succ))

#check @detColAdd

/-- homogeneity of the determinant in any one column -/
def detColSmul {R : Real} : (n : Nat) → (A : Mat R n n) → (j : Fin n) → (c : Carrier R) →
    (u : Fin n → Carrier R) →
    (det n (updateCol A j (fun i => rmul c (u i)))) = (rmul c (det n (updateCol A j u)))
  | .zero, _, j, _, _ => j.elim0
  | .succ n, A, j, c, u => by
    show (altSum n.succ fun j2 => rmul ((updateCol A j (fun i => rmul c (u i))) fin0 j2)
        (det n (minor (updateCol A j (fun i => rmul c (u i))) j2)))
      = rmul c (altSum n.succ fun j2 => rmul ((updateCol A j u) fin0 j2) (det n (minor (updateCol A j u) j2)))
    rw [← altSumMul c n.succ
      (fun j2 => rmul ((updateCol A j u) fin0 j2) (det n (minor (updateCol A j u) j2)))]
    apply altSumCongr n.succ
    intro j2
    by_cases hj : j = j2
    · rw [← hj, updateColSame A j _ fin0, updateColSame A j u fin0,
          minorUpdateColSame A j, minorUpdateColSame A j u]
      exact (fieldOf R).mulAssoc c (u fin0) (det n (minor A j))
    · have hne : j.val = j2.val → False := fun he => hj (Fin.ext he)
      rw [updateColOther A j _ fin0 j2 (fun he => hj (eqSym he)),
          updateColOther A j u fin0 j2 (fun he => hj (eqSym he)),
          minorUpdateColOther A j2 j hne _, minorUpdateColOther A j2 j hne u,
          detColSmul n (minor A j2) (unskip j2 j hne) c (fun i => u i.succ)]
      exact eqTrans (eqSym ((fieldOf R).mulAssoc (A fin0 j2) c
          (det n (updateCol (minor A j2) (unskip j2 j hne) fun i => u i.succ))))
        (eqTrans (eqCong (fun z => rmul z (det n (updateCol (minor A j2) (unskip j2 j hne) fun i => u i.succ)))
            ((fieldOf R).mulComm (A fin0 j2) c))
          ((fieldOf R).mulAssoc c (A fin0 j2)
            (det n (updateCol (minor A j2) (unskip j2 j hne) fun i => u i.succ))))

-- a − a = 0.
def subSelf {R : Real} (a : Carrier R) : (rsub a a) = (rzero R) := addNegRight a

-- An alternating sum in which only two ADJACENT terms survive, and they are
-- equal, is zero: consecutive terms always carry opposite signs. (Induct on
-- the position of the pair; the head case is "f 0 − f 1", the step drops a
-- vanishing head.)
/-- cancellation of equal adjacent terms -/
def altSumPairCancel {R : Real} : (p : Nat) → (k : Nat) → (f : Fin k → Carrier R) →
    (hp : Nat.lt (Nat.succ p) k) →
    (hz : (j : Fin k) → (j.val = p → False) → (j.val = Nat.succ p → False) → (f j) = (rzero R)) →
    (heq : (j1 : Fin k) → (j2 : Fin k) → j1.val = p → j2.val = Nat.succ p → (f j1) = (f j2)) →
    (altSum k f) = (rzero R)
  | .zero, .succ (.succ k), f, _, hz, heq => by
    have htail : (altSum k.succ (fun j => f j.succ)) = f (Fin.succ fin0) := by
      apply altSumHead (fun j => f j.succ)
      intro j
      exact hz j.succ.succ (fun he => Nat.succ_ne_zero j.val.succ he)
        (fun he => Nat.succ_ne_zero j.val (Nat.succ.inj he))
    show (rsub (f fin0) (altSum k.succ (fun j => f j.succ))) = rzero R
    rw [htail, ← heq fin0 (Fin.succ fin0) rfl rfl]
    exact subSelf (f fin0)
  | .zero, .succ .zero, _, hp, _, _ => absurd hp (Nat.lt_irrefl 1)
  | .succ p, .succ k, f, hp, hz, heq => by
    have hhead : (f fin0) = rzero R :=
      hz fin0 (fun he => Nat.succ_ne_zero p (eqSym he)) (fun he => Nat.succ_ne_zero p.succ (eqSym he))
    have htail : (altSum k (fun j => f j.succ)) = rzero R := by
      apply altSumPairCancel p k (fun j => f j.succ) (Nat.lt_of_succ_lt_succ hp)
      · intro j h1 h2
        exact hz j.succ (fun he => h1 (Nat.succ.inj he)) (fun he => h2 (Nat.succ.inj he))
      · intro j1 j2 h1 h2
        exact heq j1.succ j2.succ (congrArg Nat.succ h1) (congrArg Nat.succ h2)
    show (rsub (f fin0) (altSum k (fun j => f j.succ))) = rzero R
    rw [hhead, htail]
    exact subSelf (rzero R)

#check @detColSmul

theorem unskipValLt {n : Nat} (j0 j : Fin n.succ) (hne : j.val = j0.val → False)
    (h : Nat.lt j.val j0.val) : (unskip j0 j hne).val = j.val := by
  unfold unskip
  rw [dif_pos (by rw [Nat.blt_eq]; exact h)]

theorem unskipValGt {n : Nat} (j0 j : Fin n.succ) (hne : j.val = j0.val → False)
    (h : Nat.lt j0.val j.val) : (unskip j0 j hne).val = Nat.pred j.val := by
  unfold unskip
  rw [dif_neg (by rw [Nat.blt_eq]; exact Nat.not_lt.mpr (Nat.le_of_lt h))]

-- Deleting a column OUTSIDE an adjacent pair keeps the pair adjacent.
/-- a deleted column outside a pair keeping the pair adjacent -/
theorem unskipAdj {n : Nat} (j0 j1 j2 : Fin n.succ)
    (h1 : j1.val = j0.val → False) (h2 : j2.val = j0.val → False)
    (hadj : j2.val = Nat.succ j1.val) :
    (unskip j0 j2 h2).val = Nat.succ (unskip j0 j1 h1).val := by
  by_cases hlt : Nat.lt j1.val j0.val
  · -- j0 is to the RIGHT of the pair: is it right of j2 too?
    have h2lt : Nat.lt j2.val j0.val :=
      Nat.lt_of_le_of_ne (by rw [hadj]; exact hlt) h2
    rw [unskipValLt j0 j1 h1 hlt, unskipValLt j0 j2 h2 h2lt, hadj]
  · -- j0 is to the LEFT of the pair (it cannot be inside it)
    have hgt1 : Nat.lt j0.val j1.val :=
      Nat.lt_of_le_of_ne (Nat.le_of_not_lt hlt) (fun he => h1 (eqSym he))
    have hgt2 : Nat.lt j0.val j2.val := by
      rw [hadj]; exact Nat.lt_succ_of_lt hgt1
    rw [unskipValGt j0 j1 h1 hgt1, unskipValGt j0 j2 h2 hgt2, hadj]
    show Nat.pred (Nat.succ j1.val) = Nat.succ (Nat.pred j1.val)
    rw [Nat.succ_pred_eq_of_pos (Nat.lt_of_le_of_lt (Nat.zero_le j0.val) hgt1)]
    exact Nat.pred_succ j1.val

-- Deleting EITHER of two equal adjacent columns leaves the same matrix.
/-- deleting either of two equal adjacent columns -/
theorem minorEqAdj {R : Real} {n : Nat} (A : Mat R n.succ n.succ) (j1 j2 : Fin n.succ)
    (hadj : j2.val = Nat.succ j1.val) (heq : (i : Fin n.succ) → (A i j1) = (A i j2)) :
    (minor A j1) = (minor A j2) := by
  funext i k
  show A i.succ (skip j1 k) = A i.succ (skip j2 k)
  by_cases hk : Nat.lt k.val j1.val
  · rw [skipOfLt j1 k hk, skipOfLt j2 k (by rw [hadj]; exact Nat.lt_succ_of_lt hk)]
  · by_cases hk2 : k.val = j1.val
    · -- the two skips land on the two EQUAL columns, opposite ways round
      have e1 : (skip j1 k) = j2 := by
        apply Fin.ext
        rw [skipValGe j1 k (Nat.le_of_eq (eqSym hk2)), hadj, hk2]
      have e2 : (skip j2 k) = j1 := by
        apply Fin.ext
        rw [skipValLt j2 k (by rw [hadj, hk2]; exact Nat.lt_succ_self j1.val), hk2]
      rw [e1, e2]
      exact eqSym (heq i.succ)
    · have hge : Nat.le j2.val k.val := by
        rw [hadj]
        exact Nat.succ_le_of_lt (Nat.lt_of_le_of_ne (Nat.le_of_not_lt hk) (fun he => hk2 (eqSym he)))
      rw [skipOfGe j1 k (Nat.le_of_not_lt hk), skipOfGe j2 k hge]

/-- a determinant with two equal adjacent columns vanishes -/
def detColEqAdjZero {R : Real} : (n : Nat) → (A : Mat R n n) → (j1 : Fin n) → (j2 : Fin n) →
    (hadj : j2.val = Nat.succ j1.val) → ((i : Fin n) → (A i j1) = (A i j2)) →
    (det n A) = (rzero R)
  | .zero, _, j1, _, _, _ => j1.elim0
  | .succ n, A, j1, j2, hadj, heq => by
    show (altSum n.succ fun j0 => rmul (A fin0 j0) (det n (minor A j0))) = rzero R
    apply altSumPairCancel j1.val n.succ _ (by rw [← hadj]; exact j2.isLt)
    · -- every OTHER expansion term drops: its minor still has the equal pair
      intro j0 hz1 hz2
      have h1 : j1.val = j0.val → False := fun he => hz1 (eqSym he)
      have h2 : j2.val = j0.val → False := fun he => hz2 (eqSym (eqTrans (eqSym hadj) he))
      have hminor : (det n (minor A j0)) = rzero R := by
        apply detColEqAdjZero n (minor A j0) (unskip j0 j1 h1) (unskip j0 j2 h2)
          (unskipAdj j0 j1 j2 h1 h2 hadj)
        intro i
        show A i.succ (skip j0 (unskip j0 j1 h1)) = A i.succ (skip j0 (unskip j0 j2 h2))
        rw [skipUnskip j0 j1 h1, skipUnskip j0 j2 h2]
        exact heq i.succ
      rw [hminor]
      exact mulZeroRight (A fin0 j0)
    · -- the two surviving terms are equal, and adjacent terms cancel
      intro k1 k2 hk1 hk2
      have e1 : k1 = j1 := Fin.ext hk1
      have e2 : k2 = j2 := Fin.ext (eqTrans hk2 (eqSym hadj))
      rw [e1, e2, heq fin0, minorEqAdj A j1 j2 hadj heq]

#check @detColEqAdjZero

theorem updateColSelf {R : Real} {n m : Nat} (A : Mat R n m) (j : Fin m) :
    (updateCol A j (fun i => A i j)) = A := by
  funext i k
  by_cases hk : k = j
  · rw [hk]
    exact updateColSame A j (fun i => A i j) i
  · exact updateColOther A j (fun i => A i j) i k hk

-- subtracting a multiple of the neighbouring column
/-- invariance under a column operation -/
def detColOpAdj {R : Real} (n : Nat) (A : Mat R n n) (j1 j2 : Fin n)
    (hadj : j2.val = Nat.succ j1.val) (c : Carrier R) :
    (det n (updateCol A j2 (fun i => rsub (A i j2) (rmul c (A i j1))))) = (det n A) := by
  have hne : j1 = j2 → False := fun he => Nat.succ_ne_self j1.val
    (eqTrans (eqSym hadj) (congrArg Fin.val (eqSym he)))
  -- rewrite the subtraction as an addition of a scaled column
  have hform : (fun i => rsub (A i j2) (rmul c (A i j1)))
      = (fun i => radd (A i j2) (rmul (rneg c) (A i j1))) := by
    funext i
    show radd (A i j2) (rneg (rmul c (A i j1))) = radd (A i j2) (rmul (rneg c) (A i j1))
    rw [mulNegLeft c (A i j1)]
  rw [hform,
      detColAdd n A j2 (fun i => A i j2) (fun i => rmul (rneg c) (A i j1)),
      updateColSelf A j2,
      detColSmul n A j2 (rneg c) (fun i => A i j1)]
  -- the second determinant has two equal adjacent columns
  have hzero : (det n (updateCol A j2 (fun i => A i j1))) = rzero R := by
    apply detColEqAdjZero n (updateCol A j2 (fun i => A i j1)) j1 j2 hadj
    intro i
    rw [updateColOther A j2 (fun i => A i j1) i j1 hne,
        updateColSame A j2 (fun i => A i j1) i]
  rw [hzero, mulZeroRight (rneg c)]
  exact (fieldOf R).addZeroRight (det n A)

#check @detColOpAdj

-- ============ the Vandermonde matrix ============

-- The tower's lemmas are stated on the field RECORD; these restate the two
-- unit laws on the rmul/rone spellings the goals actually contain, so \`rw\`
-- can match them syntactically.
def rmulOneRight {R : Real} (a : Carrier R) : (rmul a (rone R)) = a := (fieldOf R).mulOneRight a
def rmulOneLeft {R : Real} (a : Carrier R) : (rmul (rone R) a) = a := (fieldOf R).mulOneLeft a
def rmulComm {R : Real} (a b : Carrier R) : (rmul a b) = (rmul b a) := (fieldOf R).mulComm a b

-- V_ij = x_i^j: a total function of (i, j) on the rectangle, which is why the
-- grid display is DERIVED (1, x_i, x_i^2, …, x_i^{n-1}) rather than authored.
def vandermonde {R : Real} {n : Nat} (x : Fin n → Carrier R) : Mat R n n :=
  fun i j => rpow (x i) j.val

/-- the 1x1 Vandermonde determinant -/
def vandermonde1 {R : Real} (x : Fin 1 → Carrier R) :
    (det 1 (vandermonde x)) = (rone R) :=
  eqTrans (subZero (rmul (rone R) (rone R))) (rmulOneRight (rone R))

/-- the 2x2 Vandermonde determinant -/
def vandermonde2 {R : Real} (x : Fin 2 → Carrier R) :
    (det 2 (vandermonde x)) = (rsub (x (Fin.succ fin0)) (x fin0)) := by
  -- the expansion, written out: 1·(x_2·1·1 − 0) − ((x_1·1)·(1·1 − 0) − 0)
  show rsub (rmul (rone R) (rsub (rmul (rmul (x (Fin.succ fin0)) (rone R)) (rone R)) (rzero R)))
      (rsub (rmul (rmul (x fin0) (rone R)) (rsub (rmul (rone R) (rone R)) (rzero R))) (rzero R))
    = rsub (x (Fin.succ fin0)) (x fin0)
  simp only [subZero, rmulOneRight, rmulOneLeft]

#check @vandermonde
#check @vandermonde2

-- when the top row is (1, 0, …, 0) the determinant IS the first minor's
/-- expansion along a cleared first row -/
def detFirstRowUnit {R : Real} (n : Nat) (A : Mat R n.succ n.succ)
    (h0 : (A fin0 fin0) = (rone R))
    (hz : (j : Fin n) → (A fin0 j.succ) = (rzero R)) :
    (det n.succ A) = (det n (minor A fin0)) := by
  show (altSum n.succ fun j => rmul (A fin0 j) (det n (minor A j))) = det n (minor A fin0)
  rw [altSumHead (fun j => rmul (A fin0 j) (det n (minor A j)))
    (fun j => by
      show rmul (A fin0 j.succ) (det n (minor A j.succ)) = rzero R
      rw [hz j]
      exact mulZeroLeft (det n (minor A j.succ)))]
  rw [h0]
  exact rmulOneLeft (det n (minor A fin0))

#check @detFirstRowUnit

-- ============ factoring a scalar out of EVERY row ============

-- (ab)(pq) = (ap)(bq)
/-- the middle-four exchange for products -/
def mulSwap {R : Real} (a b p q : Carrier R) :
    (rmul (rmul a b) (rmul p q)) = (rmul (rmul a p) (rmul b q)) :=
  eqTrans ((fieldOf R).mulAssoc a b (rmul p q))
    (eqTrans (eqCong (fun z => rmul a z)
        (eqTrans (eqSym ((fieldOf R).mulAssoc b p q))
          (eqTrans (eqCong (fun z => rmul z q) ((fieldOf R).mulComm b p))
            ((fieldOf R).mulAssoc p b q))))
      (eqSym ((fieldOf R).mulAssoc a p (rmul b q))))

def finProd {R : Real} : (k : Nat) → (Fin k → Carrier R) → Carrier R
  | .zero, _ => rone R
  | .succ k, f => rmul (f fin0) (finProd k (fun j => f j.succ))

-- Scale row i by c i, for every row at once.
def scaleRows {R : Real} {n m : Nat} (A : Mat R n m) (c : Fin n → Carrier R) : Mat R n m :=
  fun i k => rmul (c i) (A i k)

theorem minorScaleRows {R : Real} {n : Nat} (A : Mat R n.succ n.succ)
    (c : Fin n.succ → Carrier R) (j : Fin n.succ) :
    (minor (scaleRows A c) j) = (scaleRows (minor A j) (fun i => c i.succ)) := rfl

-- the determinant picks up the product of the scalars
/-- factoring a scalar out of every row -/
def detScaleRows {R : Real} : (n : Nat) → (A : Mat R n n) → (c : Fin n → Carrier R) →
    (det n (scaleRows A c)) = (rmul (finProd n c) (det n A))
  | .zero, _, _ => eqSym (rmulOneLeft (rone R))
  | .succ n, A, c => by
    show (altSum n.succ fun j => rmul (rmul (c fin0) (A fin0 j)) (det n (minor (scaleRows A c) j)))
      = rmul (rmul (c fin0) (finProd n (fun i => c i.succ)))
          (altSum n.succ fun j => rmul (A fin0 j) (det n (minor A j)))
    rw [← altSumMul (rmul (c fin0) (finProd n (fun i => c i.succ))) n.succ
      (fun j => rmul (A fin0 j) (det n (minor A j)))]
    apply altSumCongr n.succ
    intro j
    rw [minorScaleRows A c j, detScaleRows n (minor A j) (fun i => c i.succ)]
    exact mulSwap (c fin0) (A fin0 j) (finProd n (fun i => c i.succ)) (det n (minor A j))

#check @detScaleRows

-- ============ the column operations, applied one at a time ============

-- The matrix partway through the reduction: columns 0..k still hold the
-- original powers, every column ABOVE k has already had its neighbour
-- subtracted and so carries the common factor (x_i - x_1).
-- k = n-1 is the Vandermonde matrix itself; k = 0 is the fully reduced one.
def vandStep {R : Real} {n : Nat} (x : Fin n.succ → Carrier R) (k : Nat) : Mat R n.succ n.succ :=
  fun i j => if Nat.ble j.val k = true then rpow (x i) j.val
             else rmul (rpow (x i) (Nat.pred j.val)) (rsub (x i) (x fin0))

/-- one step of the column reduction -/
def detVandStep {R : Real} {n : Nat} (x : Fin n.succ → Carrier R) (k : Nat)
    (hk : Nat.lt (Nat.succ k) (Nat.succ n)) :
    (det n.succ (vandStep x (Nat.succ k))) = (det n.succ (vandStep x k)) := by
  have key : (updateCol (vandStep x (Nat.succ k)) ⟨Nat.succ k, hk⟩
      (fun i => rsub ((vandStep x (Nat.succ k)) i ⟨Nat.succ k, hk⟩)
        (rmul (x fin0) ((vandStep x (Nat.succ k)) i ⟨k, Nat.lt_of_succ_lt hk⟩))))
      = vandStep x k := by
    funext i j
    by_cases hj : j = (⟨Nat.succ k, hk⟩ : Fin n.succ)
    · -- the operated column: x^{k+1} - x_1 x^k = x^k (x - x_1)
      rw [hj, updateColSame]
      show rsub (if Nat.ble (Nat.succ k) (Nat.succ k) = true then rpow (x i) (Nat.succ k) else
              rmul (rpow (x i) (Nat.pred (Nat.succ k))) (rsub (x i) (x fin0)))
          (rmul (x fin0) (if Nat.ble k (Nat.succ k) = true then rpow (x i) k else
              rmul (rpow (x i) (Nat.pred k)) (rsub (x i) (x fin0))))
        = (if Nat.ble (Nat.succ k) k = true then rpow (x i) (Nat.succ k) else
            rmul (rpow (x i) (Nat.pred (Nat.succ k))) (rsub (x i) (x fin0)))
      rw [if_pos (by rw [Nat.ble_eq]; exact Nat.le_refl (Nat.succ k)), if_pos (by rw [Nat.ble_eq]; exact Nat.le_succ k),
          if_neg (by rw [Nat.ble_eq]; exact fun hle => Nat.not_succ_le_self k hle)]
      show rsub (rmul (x i) (rpow (x i) k)) (rmul (x fin0) (rpow (x i) k))
        = rmul (rpow (x i) k) (rsub (x i) (x fin0))
      rw [mulSubRight (rpow (x i) k) (x i) (x fin0),
          rmulComm (rpow (x i) k) (x i),
          rmulComm (rpow (x i) k) (x fin0)]
    · -- every other column: untouched on both sides, or already operated
      rw [updateColOther _ _ _ i j hj]
      show (if Nat.ble j.val (Nat.succ k) = true then rpow (x i) j.val else
              rmul (rpow (x i) (Nat.pred j.val)) (rsub (x i) (x fin0)))
        = (if Nat.ble j.val k = true then rpow (x i) j.val else
              rmul (rpow (x i) (Nat.pred j.val)) (rsub (x i) (x fin0)))
      by_cases hle : Nat.ble j.val k = true
      · rw [if_pos hle, if_pos (by rw [Nat.ble_eq] at hle ⊢; exact Nat.le_succ_of_le hle)]
      · have hgt : Nat.lt k j.val := by
          rw [Nat.ble_eq] at hle
          exact Nat.lt_of_not_le hle
        have hne : j.val = Nat.succ k → False := fun he => hj (Fin.ext he)
        rw [if_neg hle, if_neg (by
          rw [Nat.ble_eq]
          exact fun hle2 => hne (Nat.le_antisymm hle2 (Nat.succ_le_of_lt hgt)))]
  rw [← key]
  exact eqSym (detColOpAdj n.succ (vandStep x (Nat.succ k)) ⟨k, Nat.lt_of_succ_lt hk⟩
    ⟨Nat.succ k, hk⟩ rfl (x fin0))

/-- the whole column reduction -/
def detVandSteps {R : Real} {n : Nat} (x : Fin n.succ → Carrier R) :
    (k : Nat) → (hk : Nat.lt k (Nat.succ n)) →
    (det n.succ (vandStep x k)) = (det n.succ (vandStep x 0))
  | .zero, _ => rfl
  | .succ k, hk => eqTrans (detVandStep x k hk) (detVandSteps x k (Nat.lt_of_succ_lt hk))

#check @detVandSteps

-- ============ THE VANDERMONDE IDENTITY ============

-- the first variable factors out, leaving the Vandermonde determinant of
-- the remaining ones
/-- the Vandermonde recursion -/
def vandermondeRecursion {R : Real} {n : Nat} (x : Fin n.succ → Carrier R) :
    (det n.succ (vandermonde x))
      = (rmul (finProd n (fun i => rsub (x i.succ) (x fin0)))
          (det n (vandermonde (fun i => x i.succ)))) := by
  -- nothing has been operated on yet
  have htop : (vandermonde x) = (vandStep x n) := by
    funext i j
    show rpow (x i) j.val = (if Nat.ble j.val n = true then rpow (x i) j.val else
      rmul (rpow (x i) (Nat.pred j.val)) (rsub (x i) (x fin0)))
    rw [if_pos (by rw [Nat.ble_eq]; exact Nat.le_of_lt_succ j.isLt)]
  -- after every operation the first row is (1, 0, …, 0)
  have h0 : ((vandStep x 0) fin0 fin0) = rone R := by
    show (if Nat.ble 0 0 = true then rpow (x fin0) 0 else
      rmul (rpow (x fin0) (Nat.pred 0)) (rsub (x fin0) (x fin0))) = rone R
    rfl
  have hz : (j : Fin n) → ((vandStep x 0) fin0 j.succ) = rzero R := by
    intro j
    show (if Nat.ble (Nat.succ j.val) 0 = true then rpow (x fin0) (Nat.succ j.val) else
      rmul (rpow (x fin0) (Nat.pred (Nat.succ j.val))) (rsub (x fin0) (x fin0))) = rzero R
    rw [if_neg (by rw [Nat.ble_eq]; exact fun h => Nat.not_succ_le_zero j.val h),
        subSelf (x fin0)]
    exact mulZeroRight (rpow (x fin0) j.val)
  -- and the surviving minor is the smaller Vandermonde, row i scaled by (x_i − x_1)
  have hminor : (minor (vandStep x 0) fin0)
      = (scaleRows (vandermonde (fun i => x i.succ)) (fun i => rsub (x i.succ) (x fin0))) := by
    funext i k
    show (vandStep x 0) i.succ (skip fin0 k)
      = rmul (rsub (x i.succ) (x fin0)) (rpow (x i.succ) k.val)
    rw [skipOfGe fin0 k (Nat.zero_le k.val)]
    show (if Nat.ble (Nat.succ k.val) 0 = true then rpow (x i.succ) (Nat.succ k.val) else
      rmul (rpow (x i.succ) (Nat.pred (Nat.succ k.val))) (rsub (x i.succ) (x fin0)))
      = rmul (rsub (x i.succ) (x fin0)) (rpow (x i.succ) k.val)
    rw [if_neg (by rw [Nat.ble_eq]; exact fun h => Nat.not_succ_le_zero k.val h)]
    exact rmulComm (rpow (x i.succ) k.val) (rsub (x i.succ) (x fin0))
  rw [htop, detVandSteps x n (Nat.lt_succ_self n), detFirstRowUnit n (vandStep x 0) h0 hz,
      hminor, detScaleRows n (vandermonde (fun i => x i.succ)) (fun i => rsub (x i.succ) (x fin0))]

-- The product over all pairs i < j, written the way the recursion produces it:
-- (x_2 − x_1)(x_3 − x_1)…(x_n − x_1) times the same for the remaining variables.
def vandProd {R : Real} : (n : Nat) → (x : Fin n → Carrier R) → Carrier R
  | .zero, _ => rone R
  | .succ n, x => rmul (finProd n (fun i => rsub (x i.succ) (x fin0)))
      (vandProd n (fun i => x i.succ))

-- VANDERMONDE: det V = ∏_{i<j} (x_j − x_i)
/-- Vandermonde's identity -/
theorem vandermondeIdentity {R : Real} : ∀ (n : Nat) (x : Fin n → Carrier R),
    (det n (vandermonde x)) = (vandProd n x) := by
  intro n
  induction n with
  | zero =>
    intro x
    rfl
  | succ n ih =>
    intro x
    rw [vandermondeRecursion x, ih (fun i => x i.succ)]
    rfl

#check @vandermondeIdentity

-- SANITY: the product really is (x_2 - x_1) at n = 2, so the identity's
-- right-hand side is the product a paper writes.
def vandProd2Check {R : Real} (x : Fin 2 → Carrier R) :
    (vandProd 2 x) = (rsub (x (Fin.succ fin0)) (x fin0)) := by
  show rmul (rmul (rsub (x (Fin.succ fin0)) (x fin0)) (rone R)) (rmul (rone R) (rone R))
    = rsub (x (Fin.succ fin0)) (x fin0)
  rw [rmulOneRight, rmulOneRight, rmulOneRight]

-- and it agrees with the directly-computed 2x2 determinant
def vandermondeAgrees {R : Real} (x : Fin 2 → Carrier R) :
    (vandProd 2 x) = (det 2 (vandermonde x)) :=
  eqTrans (vandProd2Check x) (eqSym (vandermonde2 x))

#check @vandermondeIdentity
#check @vandermondeAgrees
`;

const GROUP_THEORY = `-- Group Theory (from scratch): finite groups as element lists, subgroups,
-- cosets, and Lagrange's theorem — the order of a subgroup divides the order
-- of the group. NO Mathlib; the counting arguments live in library lemmas so
-- the MAIN proofs stay in the renderable subset.

-- ============ groups ============

structure MyGroup where
  carrier : Type
  mul : carrier → carrier → carrier
  one : carrier
  inv : carrier → carrier
  mulAssoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  oneMul : ∀ a, mul one a = a
  invMul : ∀ a, mul (inv a) a = one

namespace MyGroup

variable {G : MyGroup}

-- Derived one-sided identities/inverses (the usual exercises).
theorem mulInv (a : G.carrier) : G.mul a (G.inv a) = G.one := by
  have hx : G.mul (G.mul a (G.inv a)) (G.mul a (G.inv a)) = G.mul a (G.inv a) := by
    rw [G.mulAssoc, ← G.mulAssoc (G.inv a), G.invMul, G.oneMul]
  have h := congrArg (G.mul (G.inv (G.mul a (G.inv a)))) hx
  rw [← G.mulAssoc, G.invMul, G.oneMul] at h
  exact h

theorem mulOne (a : G.carrier) : G.mul a G.one = a := by
  rw [← G.invMul a, ← G.mulAssoc, mulInv, G.oneMul]

theorem mulLeftCancel {a b c : G.carrier} (h : G.mul a b = G.mul a c) : b = c := by
  have h2 := congrArg (G.mul (G.inv a)) h
  rw [← G.mulAssoc, ← G.mulAssoc, G.invMul, G.oneMul, G.oneMul] at h2
  exact h2

theorem invInv (a : G.carrier) : G.inv (G.inv a) = a := by
  apply mulLeftCancel (a := G.inv a)
  rw [mulInv, G.invMul]

theorem invMulRev (a b : G.carrier) :
    G.inv (G.mul a b) = G.mul (G.inv b) (G.inv a) := by
  apply mulLeftCancel (a := G.mul a b)
  rw [mulInv, G.mulAssoc, ← G.mulAssoc b, mulInv, G.oneMul, mulInv]

end MyGroup

-- Prose notation: group elements read as mathematics — a * b, a⁻¹, 1 — while
-- Nat's own * stays untouched (instances are per-carrier, not global syntax).
instance {G : MyGroup} : Mul G.carrier := ⟨G.mul⟩
instance {G : MyGroup} : OfNat G.carrier 1 := ⟨G.one⟩
@[reducible] def ginv {G : MyGroup} (a : G.carrier) : G.carrier := G.inv a
postfix:max "⁻¹" => ginv

@[app_unexpander MyGroup.mul] def unexpGroupMul : Lean.PrettyPrinter.Unexpander
  | \`($_ $_G $a $b) => \`($a * $b)
  | _ => throw ()
@[app_unexpander MyGroup.inv] def unexpGroupInv : Lean.PrettyPrinter.Unexpander
  | \`($_ $_G $a) => \`($a⁻¹)
  | _ => throw ()
@[app_unexpander MyGroup.one] def unexpGroupOne : Lean.PrettyPrinter.Unexpander
  | \`($_ $_G) => \`(1)
  | _ => throw ()

-- ============ list library (what Finset would give us) ============

-- Counting distinct elements: a list with no duplicates. (Core Lean has
-- List.Nodup but few lemmas about it without Mathlib — we prove what we use.)

/-- injectivity keeping an absent element absent -/
theorem notMemMap {α β : Type} {f : α → β}
    (inj : ∀ x y, f x = f y → x = y) {a : α} {l : List α}
    (h : a ∉ l) : f a ∉ l.map f := by
  intro hmem
  rw [List.mem_map] at hmem
  obtain ⟨b, hb, hfb⟩ := hmem
  have hba := inj b a hfb
  rw [hba] at hb
  exact h hb

/-- an injective map preserving distinctness -/
theorem nodupMap {α β : Type} {f : α → β}
    (inj : ∀ x y, f x = f y → x = y) :
    ∀ {l : List α}, l.Nodup → (l.map f).Nodup := by
  intro l
  induction l with
  | nil => intro _; exact List.nodup_nil
  | cons a t ih =>
    intro h
    rw [List.nodup_cons] at h
    rw [List.map_cons, List.nodup_cons]
    exact ⟨notMemMap inj h.1, ih h.2⟩

-- Two nodup lists with the same members have the same length: the bijection
-- a paper would not even bother to mention. Proved by induction with erase.
/-- equal length from equal membership -/
theorem lengthEqOfSameMem {α : Type} [DecidableEq α] :
    ∀ (l1 l2 : List α), l1.Nodup → l2.Nodup → (∀ x, x ∈ l1 ↔ x ∈ l2) →
      l1.length = l2.length := by
  intro l1
  induction l1 with
  | nil =>
    intro l2 _ _ hiff
    cases l2 with
    | nil => rfl
    | cons b t =>
      exact absurd ((hiff b).2 (List.mem_cons_self)) (List.not_mem_nil)
  | cons a t ih =>
    intro l2 h1 h2 hiff
    rw [List.nodup_cons] at h1
    have ha2 : a ∈ l2 := (hiff a).1 (List.mem_cons_self)
    have herase : (l2.erase a).length = l2.length - 1 := List.length_erase_of_mem ha2
    have hlen2 : l2.length = (l2.erase a).length + 1 := by
      rw [herase]
      have hpos : 0 < l2.length := List.length_pos_of_mem ha2
      omega
    rw [List.length_cons, hlen2]
    have ht : t.length = (l2.erase a).length := by
      apply ih (l2.erase a) h1.2 (h2.erase a)
      intro x
      constructor
      · intro hx
        have hxl2 : x ∈ l2 := (hiff x).1 (List.mem_cons_of_mem a hx)
        have hxa : x ≠ a := fun he => h1.1 (he ▸ hx)
        exact (List.mem_erase_of_ne hxa).2 hxl2
      · intro hx
        have hxl2 : x ∈ l2 := List.mem_of_mem_erase hx
        have hxa : x ≠ a := (List.Nodup.mem_erase_iff h2).1 hx |>.1
        have := (hiff x).2 hxl2
        cases this with
        | head => exact absurd rfl hxa
        | tail _ hxt => exact hxt
    omega

/-- filtering preserving distinctness -/
theorem nodupFilter {α : Type} (p : α → Bool) :
    ∀ {l : List α}, l.Nodup → (l.filter p).Nodup := by
  intro l
  induction l with
  | nil => intro _; exact List.nodup_nil
  | cons a t ih =>
    intro h
    rw [List.nodup_cons] at h
    cases hpa : p a with
    | false => rw [List.filter_cons_of_neg (by simp [hpa])]; exact ih h.2
    | true =>
      rw [List.filter_cons_of_pos hpa, List.nodup_cons]
      exact ⟨fun hm => h.1 (List.mem_filter.1 hm).1, ih h.2⟩

/-- a filter and its complement splitting the count -/
theorem lengthFilterSplit {α : Type} (p : α → Bool) :
    ∀ (l : List α), (l.filter p).length + (l.filter (fun a => !p a)).length = l.length := by
  intro l
  induction l with
  | nil => rfl
  | cons a t ih =>
    cases hpa : p a with
    | true =>
      rw [List.filter_cons_of_pos hpa, List.filter_cons_of_neg (by simp [hpa])]
      simp only [List.length_cons]
      omega
    | false =>
      rw [List.filter_cons_of_neg (by simp [hpa]), List.filter_cons_of_pos (by simp [hpa])]
      simp only [List.length_cons]
      omega

/-- strong induction on the length of a list -/
theorem lengthStrongInduction {α : Type u} {P : List α → Prop}
    (step : ∀ vs : List α, (∀ ws : List α, ws.length < vs.length → P ws) → P vs) :
    ∀ vs : List α, P vs := by
  have aux : ∀ n (vs : List α), vs.length ≤ n → P vs := by
    intro n
    induction n with
    | zero =>
      intro vs hle
      exact step vs (fun ws hw => absurd (Nat.lt_of_lt_of_le hw hle) (Nat.not_lt_zero _))
    | succ n ih =>
      intro vs hle
      exact step vs (fun ws hw => ih ws (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hw hle)))
  intro vs
  exact aux vs.length vs (Nat.le_refl _)

-- ============ finite groups, subgroups, cosets ============

structure FiniteGroup extends MyGroup where
  deq : DecidableEq carrier
  elems : List carrier
  elemsNodup : elems.Nodup
  elemsComplete : ∀ x, x ∈ elems

instance (G : FiniteGroup) : DecidableEq G.carrier := G.deq

/-- the order of a finite group -/
def FiniteGroup.order (G : FiniteGroup) : Nat := G.elems.length

structure Subgroup (G : FiniteGroup) where
  members : List G.carrier
  membersNodup : members.Nodup
  oneMem : G.one ∈ members
  mulMem : ∀ a, a ∈ members → ∀ b, b ∈ members → G.mul a b ∈ members
  invMem : ∀ a, a ∈ members → G.inv a ∈ members

/-- the order of a subgroup -/
def Subgroup.order {G : FiniteGroup} (H : Subgroup G) : Nat := H.members.length

-- Prose notation for the COUNTING layer. \`r.Nodup\` and \`r.length\` are how
-- Lean spells "a set, not a multiset" and "how many" — implementation
-- vocabulary that a paper never prints. The NBSP keeps each multi-word
-- phrase a SINGLE token, so its words are not reserved as keywords (a
-- chained spelling would make \`for\` unusable as a binder name).
notation:50 r:51 " has distinct elements" => List.Nodup r

-- |G|, |H|, |r| — the order of a group, of a subgroup, and the size of a
-- finite set, all written the way mathematics writes them. Overloaded on
-- the three types; Lean picks by elaboration.
macro:max atomic("|" noWs) g:term noWs "|" : term => \`(FiniteGroup.order $g)
macro:max atomic("|" noWs) h:term noWs "|" : term => \`(Subgroup.order $h)
macro:max atomic("|" noWs) l:term noWs "|" : term => \`(List.length $l)

@[app_unexpander FiniteGroup.order] def unexpGOrder : Lean.PrettyPrinter.Unexpander
  | \`($_ $g) => \`(|$g|)
  | _ => throw ()
@[app_unexpander Subgroup.order] def unexpHOrder : Lean.PrettyPrinter.Unexpander
  | \`($_ $h) => \`(|$h|)
  | _ => throw ()
@[app_unexpander List.length] def unexpLen : Lean.PrettyPrinter.Unexpander
  | \`($_ $l) => \`(|$l|)
  | _ => throw ()
@[app_unexpander List.Nodup] def unexpNodup : Lean.PrettyPrinter.Unexpander
  | \`($_ $r) => \`($r has distinct elements)
  | _ => throw ()
-- A group displays as its own carrier — the abuse of notation every paper
-- uses. FiniteGroup EXTENDS MyGroup, so the projection to the parent
-- structure has to disappear too, or \`G.carrier\` reads \`G.toMyGroup\`.
@[app_unexpander MyGroup.carrier] def unexpCarrier : Lean.PrettyPrinter.Unexpander
  | \`($_ $G) => \`($G)
  | _ => throw ()
@[app_unexpander FiniteGroup.toMyGroup] def unexpToMyGroup : Lean.PrettyPrinter.Unexpander
  | \`($_ $G) => \`($G)
  | _ => throw ()

-- every element of H translated by g
/-- the left coset gH -/
def coset {G : FiniteGroup} (g : G.carrier) (H : Subgroup G) : List G.carrier :=
  H.members.map (G.mul g)

-- translation is injective, so a coset has exactly the subgroup's order
/-- the order of a coset -/
theorem cosetOrder {G : FiniteGroup} (g : G.carrier) (H : Subgroup G) :
    (coset g H).length = H.order := List.length_map ..

theorem cosetNodup {G : FiniteGroup} (g : G.carrier) (H : Subgroup G) :
    (coset g H).Nodup :=
  nodupMap (fun _ _ h => MyGroup.mulLeftCancel h) H.membersNodup

/-- x lies in gH exactly when g⁻¹x lies in H -/
theorem memCoset {G : FiniteGroup} {g x : G.carrier} {H : Subgroup G} :
    x ∈ coset g H ↔ G.mul (G.inv g) x ∈ H.members := by
  constructor
  · intro hx
    rw [coset, List.mem_map] at hx
    obtain ⟨h, hh, hgh⟩ := hx
    rw [← hgh, ← G.mulAssoc, G.invMul, G.oneMul]
    exact hh
  · intro hx
    rw [coset, List.mem_map]
    refine ⟨G.mul (G.inv g) x, hx, ?_⟩
    rw [← G.mulAssoc, MyGroup.mulInv, G.oneMul]

-- ============ the counting argument ============

-- A set of elements is SATURATED for H when it contains whole cosets: if it
-- holds x, it holds everything in xH. The group itself is saturated, and
-- removing one coset keeps the rest saturated — that is the whole of
-- Lagrange's theorem.
def Saturated {G : FiniteGroup} (H : Subgroup G) (r : List G.carrier) : Prop :=
  ∀ x, x ∈ r → ∀ y, G.mul (G.inv x) y ∈ H.members → y ∈ r

notation:50 r:51 " saturated for " H:51 => Saturated H r
@[app_unexpander Saturated] def unexpSaturated : Lean.PrettyPrinter.Unexpander
  | \`($_ $H $r) => \`($r saturated for $H)
  | _ => throw ()

/-- the part of r lying in the coset gH -/
def cosetPart {G : FiniteGroup} (H : Subgroup G) (g : G.carrier) (r : List G.carrier) : List G.carrier :=
  r.filter (fun x => decide (G.mul (G.inv g) x ∈ H.members))

/-- the remainder after removing a coset -/
def rest {G : FiniteGroup} (H : Subgroup G) (g : G.carrier) (r : List G.carrier) : List G.carrier :=
  r.filter (fun x => !decide (G.mul (G.inv g) x ∈ H.members))

/-- removing a coset splits the count -/
theorem cosetSplit {G : FiniteGroup} (H : Subgroup G) (g : G.carrier) (r : List G.carrier) :
    r.length = (cosetPart H g r).length + (rest H g r).length :=
  (lengthFilterSplit _ r).symm

-- in a saturated set the part lying in gH is ALL of gH: order H many
/-- the order of a coset inside a saturated set -/
theorem cosetPartOrder {G : FiniteGroup} (H : Subgroup G) {g : G.carrier} {r : List G.carrier}
    (hnd : r.Nodup) (hg : g ∈ r) (hsat : Saturated H r) :
    (cosetPart H g r).length = H.order := by
  rw [← cosetOrder g H]
  apply lengthEqOfSameMem _ _ (nodupFilter _ hnd) (cosetNodup g H)
  intro x
  rw [memCoset]
  rw [List.mem_filter]
  constructor
  · intro ⟨_, hx⟩
    exact of_decide_eq_true hx
  · intro hx
    exact ⟨hsat g hg x hx, decide_eq_true hx⟩

/-- distinctness surviving the removal -/
theorem restNodup {G : FiniteGroup} (H : Subgroup G) (g : G.carrier) {r : List G.carrier}
    (hnd : r.Nodup) : (rest H g r).Nodup := nodupFilter _ hnd

/-- membership in the remainder -/
theorem memRest {G : FiniteGroup} {H : Subgroup G} {g x : G.carrier} {r : List G.carrier} :
    x ∈ rest H g r ↔ x ∈ r ∧ ¬ G.mul (G.inv g) x ∈ H.members := by
  unfold rest
  rw [List.mem_filter]
  constructor
  · intro ⟨hr, hx⟩
    refine ⟨hr, ?_⟩
    intro hmem
    simp [decide_eq_true hmem] at hx
  · intro ⟨hr, hx⟩
    refine ⟨hr, ?_⟩
    simp [decide_eq_false hx]

-- two elements of one coset see the same cosets
/-- saturation surviving the removal of a coset -/
theorem restSaturated {G : FiniteGroup} (H : Subgroup G) (g : G.carrier) {r : List G.carrier}
    (hsat : Saturated H r) : Saturated H (rest H g r) := by
  intro x hx y hy
  rw [memRest] at hx
  rw [memRest]
  refine ⟨hsat x hx.1 y hy, ?_⟩
  intro hgy
  apply hx.2
  -- g⁻¹x = (g⁻¹y)(y⁻¹x), both factors in H
  have hyx : G.mul (G.inv y) x ∈ H.members := by
    have := H.invMem _ hy
    rw [MyGroup.invMulRev, MyGroup.invInv] at this
    exact this
  have hprod := H.mulMem _ hgy _ hyx
  rw [G.mulAssoc, ← G.mulAssoc y (G.inv y) x, MyGroup.mulInv, G.oneMul] at hprod
  exact hprod

-- g itself lies in the coset removed, so something really went
/-- the strict decrease from removing a nonempty coset -/
theorem restShorter {G : FiniteGroup} (H : Subgroup G) {g : G.carrier} {r : List G.carrier}
    (hg : g ∈ r) : (rest H g r).length < r.length := by
  have hsplit := cosetSplit H g r
  have hgpart : g ∈ cosetPart H g r := by
    rw [cosetPart, List.mem_filter]
    refine ⟨hg, decide_eq_true ?_⟩
    rw [G.invMul]
    exact H.oneMem
  have hpos : 0 < (cosetPart H g r).length := List.length_pos_of_mem hgpart
  omega

/-- the empty-or-inhabited dichotomy -/
theorem emptyOrMem {α : Type} : ∀ l : List α, l = [] ∨ ∃ x, x ∈ l := by
  intro l
  cases l with
  | nil => exact Or.inl rfl
  | cons a t => exact Or.inr ⟨a, List.mem_cons_self⟩

-- ============ Lagrange ============

/-- saturated sets counting in multiples of the order of H -/
theorem lagrangeAux {G : FiniteGroup} (H : Subgroup G) :
    ∀ r : List G.carrier, r.Nodup → Saturated H r → ∃ k, r.length = k * H.order := by
  apply lengthStrongInduction
  intro r ih hnd hsat
  cases emptyOrMem r with
  | inl hempty =>
    exact ⟨0, by rw [hempty, Nat.zero_mul]; rfl⟩
  | inr hmem =>
    obtain ⟨g, hg⟩ := hmem
    obtain ⟨k, hk⟩ := ih (rest H g r) (restShorter H hg) (restNodup H g hnd) (restSaturated H g hsat)
    have hsplit : r.length = (cosetPart H g r).length + (rest H g r).length := cosetSplit H g r
    have hpart : (cosetPart H g r).length = H.order := cosetPartOrder H hnd hg hsat
    exact ⟨k + 1, by rw [hsplit, hpart, hk, Nat.succ_mul, Nat.add_comm]⟩

-- the group contains everything, so it is saturated for any H
/-- the whole group being saturated -/
theorem fullSaturated {G : FiniteGroup} (H : Subgroup G) : Saturated H G.elems :=
  fun _ _ y _ => G.elemsComplete y

-- LAGRANGE: the order of a subgroup divides the order of the group
/-- Lagrange's theorem -/
theorem lagrange {G : FiniteGroup} (H : Subgroup G) : H.order ∣ G.order := by
  obtain ⟨k, hk⟩ := lagrangeAux H G.elems G.elemsNodup (fullSaturated H)
  exact ⟨k, by show G.elems.length = H.order * k; rw [hk, Nat.mul_comm]⟩

-- ============ quotient groups ============

-- N is NORMAL when conjugation never leaves it: g n g⁻¹ ∈ N.
def Normal {G : FiniteGroup} (N : Subgroup G) : Prop :=
  ∀ g n, n ∈ N.members → G.mul g (G.mul n (G.inv g)) ∈ N.members

/-- conjugation by an inverse staying inside a normal subgroup -/
theorem conjMem {G : FiniteGroup} {N : Subgroup G} (hN : Normal N) (g : G.carrier)
    {n : G.carrier} (hn : n ∈ N.members) :
    G.mul (G.inv g) (G.mul n g) ∈ N.members := by
  have h := hN (G.inv g) n hn
  rw [MyGroup.invInv] at h
  exact h

-- Two elements are congruent mod N when they lie in the same left coset.
def CosetEq {G : FiniteGroup} (N : Subgroup G) (a b : G.carrier) : Prop :=
  G.mul (G.inv a) b ∈ N.members

-- Congruence reads the way number theory writes it: a ≡ b (mod N).
notation:50 a:51 " ≡ " b:51 " (mod " N:51 ")" => CosetEq N a b

/-- reflexivity of congruence mod N -/
theorem cosetEqRefl {G : FiniteGroup} (N : Subgroup G) (a : G.carrier) : CosetEq N a a := by
  unfold CosetEq
  rw [G.invMul]
  exact N.oneMem

-- invert the witness
/-- symmetry of congruence mod N -/
theorem cosetEqSymm {G : FiniteGroup} {N : Subgroup G} {a b : G.carrier}
    (h : CosetEq N a b) : CosetEq N b a := by
  unfold CosetEq
  have hi := N.invMem _ h
  rw [MyGroup.invMulRev, MyGroup.invInv] at hi
  exact hi

-- multiply the witnesses
/-- transitivity of congruence mod N -/
theorem cosetEqTrans {G : FiniteGroup} {N : Subgroup G} {a b c : G.carrier}
    (hab : CosetEq N a b) (hbc : CosetEq N b c) : CosetEq N a c := by
  unfold CosetEq
  have hprod := N.mulMem _ hab _ hbc
  rw [G.mulAssoc, ← G.mulAssoc b (G.inv b) c, MyGroup.mulInv, G.oneMul] at hprod
  exact hprod

-- (ac)⁻¹(bd) = [c⁻¹(a⁻¹b)c]·[c⁻¹d]
/-- the regrouping behind well-definedness -/
theorem quotRegroup {G : FiniteGroup} (a b c d : G.carrier) :
    G.mul (G.inv (G.mul a c)) (G.mul b d) =
      G.mul (G.mul (G.inv c) (G.mul (G.mul (G.inv a) b) c)) (G.mul (G.inv c) d) := by
  rw [MyGroup.invMulRev]
  rw [G.mulAssoc (G.inv c) (G.mul (G.mul (G.inv a) b) c) (G.mul (G.inv c) d)]
  rw [G.mulAssoc (G.mul (G.inv a) b) c (G.mul (G.inv c) d)]
  rw [← G.mulAssoc c (G.inv c) d]
  rw [MyGroup.mulInv, G.oneMul]
  rw [G.mulAssoc (G.inv c) (G.inv a) (G.mul b d)]
  rw [G.mulAssoc (G.inv a) b d]

/-- multiplication descending to the cosets -/
theorem quotMulDescends {G : FiniteGroup} {N : Subgroup G} (hN : Normal N)
    {a b c d : G.carrier} (hab : CosetEq N a b) (hcd : CosetEq N c d) :
    CosetEq N (G.mul a c) (G.mul b d) := by
  unfold CosetEq
  have hconj : G.mul (G.inv c) (G.mul (G.mul (G.inv a) b) c) ∈ N.members := conjMem hN c hab
  have hprod : G.mul (G.mul (G.inv c) (G.mul (G.mul (G.inv a) b) c)) (G.mul (G.inv c) d) ∈ N.members :=
    N.mulMem _ hconj _ hcd
  rw [quotRegroup]
  exact hprod

-- a·(b⁻¹a)·a⁻¹ = a·b⁻¹
/-- conjugation collapsing onto the witness -/
theorem conjCollapse {G : FiniteGroup} (a b : G.carrier) :
    G.mul a (G.mul (G.mul (G.inv b) a) (G.inv a)) = G.mul a (G.inv b) := by
  rw [G.mulAssoc (G.inv b) a (G.inv a), MyGroup.mulInv, MyGroup.mulOne]

/-- inversion descending to the cosets -/
theorem quotInvDescends {G : FiniteGroup} {N : Subgroup G} (hN : Normal N)
    {a b : G.carrier} (hab : CosetEq N a b) :
    CosetEq N (G.inv a) (G.inv b) := by
  unfold CosetEq
  have hsym := cosetEqSymm hab
  have hconj : G.mul a (G.mul (G.mul (G.inv b) a) (G.inv a)) ∈ N.members := hN a _ hsym
  rw [MyGroup.invInv, ← conjCollapse a b]
  exact hconj

-- congruence mod N as a Setoid, so Lean's Quotient can carry the cosets
def cosetSetoid {G : FiniteGroup} (N : Subgroup G) : Setoid G.carrier :=
  ⟨CosetEq N, fun a => cosetEqRefl N a, cosetEqSymm, cosetEqTrans⟩

/-- the quotient group induced by a normal subgroup -/
def QuotientGroup {G : FiniteGroup} (N : Subgroup G) (hN : Normal N) : MyGroup where
  carrier := Quotient (cosetSetoid N)
  mul := Quotient.lift₂ (fun a b => Quotient.mk (cosetSetoid N) (G.mul a b))
    (fun _ _ _ _ hab hcd => Quot.sound (quotMulDescends hN hab hcd))
  one := Quotient.mk (cosetSetoid N) G.one
  inv := Quotient.lift (fun a => Quotient.mk (cosetSetoid N) (G.inv a))
    (fun _ _ hab => Quot.sound (quotInvDescends hN hab))
  mulAssoc := by
    intro a b c
    induction a using Quotient.ind
    induction b using Quotient.ind
    induction c using Quotient.ind
    exact congrArg (Quotient.mk _) (G.mulAssoc _ _ _)
  oneMul := by
    intro a
    induction a using Quotient.ind
    exact congrArg (Quotient.mk _) (G.oneMul _)
  invMul := by
    intro a
    induction a using Quotient.ind
    exact congrArg (Quotient.mk _) (G.invMul _)
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
  { name: 'Vector Spaces (basis)', code: VECTOR_SPACE },
  { name: 'Group Theory (Lagrange)', code: GROUP_THEORY },
  { name: 'Multivariable (Jacobian)', code: MULTIVAR },
  { name: 'Determinants (Vandermonde)', code: VANDERMONDE },
  { name: 'Mathlib (∑, ring)', code: MATHLIB, mathlib: true },
];

export const DEFAULT_LEAN_SOURCE = BASICS;
