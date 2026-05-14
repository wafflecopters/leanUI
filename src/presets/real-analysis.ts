export const REAL_ANALYSIS_CODE = `-- Real Analysis: algebraic hierarchy, ordered fields, limits, and derivatives
-- Proves (f+g)' = f' + g', (c*f)' = c*f', and the chain rule (g.f)' = g'(f(x0)) * f'(x0)

------------------------------------------------------------
-- Foundation: basic types and equality
------------------------------------------------------------

inductive Void : Type where

absurd : {A : Type} -> Void -> A

@syntax $0 =_{$A} $1 @becomes Equal $$0 $$1
inductive Equal : {A : Type} -> A -> A -> Type where
  refl : {A : Type} -> {a : A} -> Equal a a

sym : {A : Type} -> {x y : A} -> Equal x y -> Equal y x
sym refl = refl

trans : {A : Type} -> {x y z : A} -> Equal x y -> Equal y z -> Equal x z
trans refl refl = refl

cong : {A B : Type} -> {x y : A} -> (f : A -> B) -> Equal x y -> Equal (f x) (f y)
cong f refl = refl

-- Transport: rewrite along an equality proof
replace : {A : Type} -> {x y : A} -> (P : A -> Type) -> Equal x y -> P x -> P y
replace P refl px = px

@syntax $0 \\vee $1 @becomes Either $$0 $$1
inductive Either : Type -> Type -> Type where
  Left : {A B : Type} -> A -> Either A B
  Right : {A B : Type} -> B -> Either A B

eitherElim : {A B C : Type} -> (A -> C) -> (B -> C) -> Either A B -> C
eitherElim f g (Left a) = f a
eitherElim f g (Right b) = g b

eitherElimDep : {A B : Type} -> (C : Either A B -> Type) -> ((a : A) -> C (Left a)) -> ((b : B) -> C (Right b)) -> (e : Either A B) -> C e
eitherElimDep C f g (Left a) = f a
eitherElimDep C f g (Right b) = g b

@syntax $0 \\wedge $1 @becomes Pair $$0 $$1
record Pair (A B : Type) where
  constructor MkPair
  fst : A
  snd : B

@syntax \\exists $x \\in $A , $P @becomes DPair {u} {v} $$A (\\$x => $P)
record DPair {u v : ULevel} (A : Type u) (B : A -> Type v) : Type (UMax u v) where
  @syntax \\text{witness} $x, \\text{and} $y @becomes MkDPair $x $y
  constructor MkDPair
  fst : A
  snd : B fst

infixr 40 ** := DPair binding

------------------------------------------------------------
-- Order Hierarchy: Preorder -> PartialOrder -> TotalOrder
------------------------------------------------------------

record Preorder (A : Type) where
  le : A -> A -> Type
  leRefl : (a : A) -> le a a
  leTrans : (a b c : A) -> le a b -> le b c -> le a c

record PartialOrder (A : Type) extends Preorder A where
  leAntisym : (a b : A) -> le a b -> le b a -> Equal a b

record TotalOrder (A : Type) extends PartialOrder A where
  leTotal : (a b : A) -> Either (le a b) (le b a)

------------------------------------------------------------
-- Algebraic Hierarchy
------------------------------------------------------------

-- An abelian (commutative) group: the additive foundation
record AbelianGroup (A : Type) where
  add : A -> A -> A
  zero : A
  neg : A -> A
  addAssoc : (a b c : A) -> Equal (add (add a b) c) (add a (add b c))
  addComm : (a b : A) -> Equal (add a b) (add b a)
  addZeroRight : (a : A) -> Equal (add a zero) a
  negRight : (a : A) -> Equal (add a (neg a)) zero

-- A ring: abelian group + multiplication with identity and distributivity
record Ring (A : Type) extends AbelianGroup A where
  mul : A -> A -> A
  one : A
  mulAssoc : (a b c : A) -> Equal (mul (mul a b) c) (mul a (mul b c))
  mulOneLeft : (a : A) -> Equal (mul one a) a
  mulOneRight : (a : A) -> Equal (mul a one) a
  distribLeft : (a b c : A) -> Equal (mul a (add b c)) (add (mul a b) (mul a c))
  distribRight : (a b c : A) -> Equal (mul (add a b) c) (add (mul a c) (mul b c))

-- A commutative ring: ring with commutative multiplication
record CommRing (A : Type) extends Ring A where
  mulComm : (a b : A) -> Equal (mul a b) (mul b a)

-- A field: commutative ring with multiplicative inverses (for nonzero elements)
-- Convention: inv(0) can be anything; the axiom only holds for a /= 0
record Field (A : Type) extends CommRing A where
  inv : A -> A
  mulInvRight : (a : A) -> (Equal a zero -> Void) -> Equal (mul a (inv a)) one

------------------------------------------------------------
-- Ordered Field: Field + Total Order + Compatibility
------------------------------------------------------------

-- An ordered field extends Field with a total order compatible with the algebra.
-- Includes abs with triangle inequality, and basic positivity facts.
record OrderedField (A : Type) : Type 1 extends Field A where
  le : A -> A -> Type
  leRefl : (a : A) -> le a a
  leAntisym : (a b : A) -> le a b -> le b a -> Equal a b
  leTrans : (a b c : A) -> le a b -> le b c -> le a c
  leTotal : (a b : A) -> Either (le a b) (le b a)
  -- Compatibility: adding preserves order, product of nonneg is nonneg
  addLeLeft : (a b c : A) -> le a b -> le (add c a) (add c b)
  mulNonneg : (a b : A) -> le zero a -> le zero b -> le zero (mul a b)
  -- Positivity axioms
  zeroLeOne : le zero one
  zeroNeOne : Equal zero one -> Void
  invPos : (a : A) -> le zero a -> (Equal a zero -> Void) -> le zero (inv a)
  -- Decidable refinement of le: a <= b implies a = b or a < b
  leToEqOrLt : (a b : A) -> le a b -> Either (Equal a b) (Pair (le a b) (Equal a b -> Void))

------------------------------------------------------------
-- Complete Ordered Field: the Dedekind completeness axiom
------------------------------------------------------------

record CompleteOrderedField (A : Type) : Type 1 extends OrderedField A where
  sup : (A -> Type) -> A
  supUpperBound : (P : A -> Type) -> (x : A) -> P x -> le x (sup P)
  supLeast : (P : A -> Type) -> (b : A) -> ((x : A) -> P x -> le x b) -> le (sup P) b

------------------------------------------------------------
-- The Real Numbers
------------------------------------------------------------

-- A "Real" is any type bundled with a complete ordered field structure.
-- No postulate needed — we just pass the instance around.
Real : Type 1
Real = (A : Type ** CompleteOrderedField A)

-- Convenience: extract carrier type and field structure
Carrier : Real -> Type
Carrier R = DPair.fst R

field : (R : Real) -> CompleteOrderedField (Carrier R)
field R = DPair.snd R

------------------------------------------------------------
-- Field operations, parametric over any Real
------------------------------------------------------------

radd : {R : Real} -> Carrier R -> Carrier R -> Carrier R
radd {R} = CompleteOrderedField.add (field R)

rmul : {R : Real} -> Carrier R -> Carrier R -> Carrier R
rmul {R} = CompleteOrderedField.mul (field R)

rzero : (R : Real) -> Carrier R
rzero R = CompleteOrderedField.zero (field R)

rone : (R : Real) -> Carrier R
rone R = CompleteOrderedField.one (field R)

------------------------------------------------------------
-- Natural numbers + numeric literal coercion to Carrier R
------------------------------------------------------------

@syntax @impl=nat
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

-- Coercion: any natural literal becomes a Carrier R value.
-- realOfNat R 0 = rzero R; realOfNat R (n+1) = rone R + realOfNat R n
-- This makes \`1 : Carrier R\`, \`2 : Carrier R\` work via @ofNat dispatch.
@syntax @ofNat
realOfNat : (R : Real) -> Nat -> Carrier R
realOfNat R Zero = rzero R
realOfNat R (Succ n) = radd (rone R) (realOfNat R n)

-- Nat addition. The recursive definition is the source of truth; the
-- @natAdd annotation gives WHNF a BigInt fast-path so closed NatLit args
-- compute in O(log N) machine ops instead of O(N) reduction steps.
@syntax @natAdd
plus : Nat -> Nat -> Nat
plus Zero m = m
plus (Succ n) m = Succ (plus n m)

-- Nat multiplication. Same pattern as plus: recursive definition + BigInt
-- fast-path for closed args. Together with plus, makes 'mult 100 100'
-- O(log N) instead of O(N²).
@syntax @natMul
mult : Nat -> Nat -> Nat
mult Zero m = Zero
mult (Succ n) m = plus m (mult n m)

------------------------------------------------------------
-- Integers (Lean-style two-constructor representation)
------------------------------------------------------------
-- Int avoids the dual-zero problem of (sign, magnitude) by using:
--   IntOfNat n   represents  n     (n >= 0)
--   IntNegSucc n represents  -(n+1)   (strictly negative)
-- So 0 is uniquely IntOfNat Zero, and -1 = IntNegSucc Zero.
@syntax @impl=int
inductive Int : Type where
  IntOfNat : Nat -> Int
  IntNegSucc : Nat -> Int

-- Smart constructor: -n as an Int. Handles n=0 specially (-0 = 0).
negOfNat : Nat -> Int
negOfNat Zero = IntOfNat Zero
negOfNat (Succ n) = IntNegSucc n

intZero : Int
intZero = IntOfNat Zero

intOne : Int
intOne = IntOfNat (Succ Zero)

-- Negation: total, no edge cases (0 negates to 0).
intNeg : Int -> Int
intNeg (IntOfNat Zero) = IntOfNat Zero
intNeg (IntOfNat (Succ n)) = IntNegSucc n
intNeg (IntNegSucc n) = IntOfNat (Succ n)

-- subNatNat m n represents m - n as a signed Int. Recursive on both
-- args; no conditionals needed.
subNatNat : Nat -> Nat -> Int
subNatNat Zero Zero = IntOfNat Zero
subNatNat (Succ m) Zero = IntOfNat (Succ m)
subNatNat Zero (Succ n) = IntNegSucc n
subNatNat (Succ m) (Succ n) = subNatNat m n

-- Int addition: case-split on signs, use subNatNat for mixed.
intAdd : Int -> Int -> Int
intAdd (IntOfNat m) (IntOfNat n) = IntOfNat (plus m n)
intAdd (IntOfNat m) (IntNegSucc n) = subNatNat m (Succ n)
intAdd (IntNegSucc m) (IntOfNat n) = subNatNat n (Succ m)
intAdd (IntNegSucc m) (IntNegSucc n) = IntNegSucc (Succ (plus m n))

-- Int multiplication: case-split, use negOfNat to handle the (zero,
-- negative) case correctly (0 * -k = 0, not "negative zero").
intMul : Int -> Int -> Int
intMul (IntOfNat m) (IntOfNat n) = IntOfNat (mult m n)
intMul (IntOfNat m) (IntNegSucc n) = negOfNat (mult m (Succ n))
intMul (IntNegSucc m) (IntOfNat n) = negOfNat (mult (Succ m) n)
intMul (IntNegSucc m) (IntNegSucc n) = IntOfNat (mult (Succ m) (Succ n))

intSub : Int -> Int -> Int
intSub a b = intAdd a (intNeg b)

-- realOfInt is defined after rneg comes into scope (search "realOfInt :")

-- NotZero — the proof-bundled positivity predicate. NotZero (Succ k) has
-- the canonical inhabitant IsSucc k; NotZero Zero is uninhabited (no
-- pattern matches). Foundation for the upcoming Rat refactor: when we
-- change MkRat to take a (d : Nat) and a NotZero d proof, the kernel
-- can pattern-match away the d=0 case automatically.
inductive NotZero : Nat -> Type where
  IsSucc : (n : Nat) -> NotZero (Succ n)

-- (Succ m) * (Succ n) is always Succ-shaped (mult's Succ case +
-- plus's Succ case). The Succ-of-something gives the NotZero proof.
mulSuccSuccNotZero : (m n : Nat) -> NotZero (mult (Succ m) (Succ n))
mulSuccSuccNotZero m n = IsSucc (plus n (mult m (Succ n)))

-- Given NotZero d1 and NotZero d2, mult d1 d2 is also non-zero. The
-- pattern match forces both inputs to have shape (Succ k), reducing
-- to mulSuccSuccNotZero. The d=Zero case is RULED OUT structurally —
-- no IsSucc constructor matches NotZero Zero.
mulNotZero : (d1 d2 : Nat) -> NotZero d1 -> NotZero d2 -> NotZero (mult d1 d2)
mulNotZero (Succ k1) (Succ k2) (IsSucc _) (IsSucc _) = mulSuccSuccNotZero k1 k2

-- Rat — Lean-style proof-bundled rational. The numerator is a signed
-- Int (so subtraction is total), the denominator is a Nat with a bundled
-- NotZero proof. This rules out 1/0 structurally and lets pattern
-- matching auto-discharge the d ≠ 0 hypothesis everywhere div appears.
@syntax @impl=rat
inductive Rat : Type where
  MkRat : Int -> (d : Nat) -> NotZero d -> Rat

-- Rat arithmetic. Recursive definitions are the source of truth (so
-- proofs by induction work); the @ratAdd/@ratMul/@ratSub annotations
-- give WHNF a BigInt fast-path for closed RatLit args.
--   a/b + c/d = (a*d + c*b) / (b*d)
@syntax @ratAdd
ratPlus : Rat -> Rat -> Rat
ratPlus (MkRat a b pb) (MkRat c d pd) = MkRat (intAdd (intMul a (IntOfNat d)) (intMul c (IntOfNat b))) (mult b d) (mulNotZero b d pb pd)

--   a/b * c/d = (a*c) / (b*d)
@syntax @ratMul
ratMult : Rat -> Rat -> Rat
ratMult (MkRat a b pb) (MkRat c d pd) = MkRat (intMul a c) (mult b d) (mulNotZero b d pb pd)

-- minus: truncated nat subtraction (returns Zero when b > a). Kept for
-- generic Nat code; ratSub uses intSub on signed Int numerators instead.
minus : Nat -> Nat -> Nat
minus n Zero = n
minus Zero (Succ _) = Zero
minus (Succ n) (Succ m) = minus n m

-- Rat subtraction. With signed Int numerators, this is total — the
-- result can be a negative rational. The @ratSub primitive computes
-- via BigInt; the iota-view canonicalizes the kernel form.
--   a/b - c/d = (a*d - c*b) / (b*d)
@syntax @ratSub
ratSub : Rat -> Rat -> Rat
ratSub (MkRat a b pb) (MkRat c d pd) = MkRat (intSub (intMul a (IntOfNat d)) (intMul c (IntOfNat b))) (mult b d) (mulNotZero b d pb pd)

rneg : {R : Real} -> Carrier R -> Carrier R
rneg {R} = CompleteOrderedField.neg (field R)

-- Coercion: Int -> Carrier R. Mirrors realOfNat, with the negative case
-- using rneg on the abstract field. \`IntNegSucc n\` represents -(n+1), so
-- it maps to -(1 + realOfNat n) = -(realOfNat (Succ n)). Registered as
-- @ofInt so signed integer literals (e.g. \`-1 : Carrier R\` in tactic
-- input) elaborate through this function instead of a hardcoded \`rneg\`.
@syntax @ofInt
realOfInt : (R : Real) -> Int -> Carrier R
realOfInt R (IntOfNat n) = realOfNat R n
realOfInt R (IntNegSucc n) = rneg (radd (rone R) (realOfNat R n))

-- negRealOfInt is defined further down, once negZero and negNeg are in scope.

rinv : {R : Real} -> Carrier R -> Carrier R
rinv {R} = CompleteOrderedField.inv (field R)

rle : {R : Real} -> Carrier R -> Carrier R -> Type
rle {R} = CompleteOrderedField.le (field R)

-- Subtraction: a - b = a + (-b)
rsub : {R : Real} -> Carrier R -> Carrier R -> Carrier R
rsub {R} a b = radd a (rneg b)

-- Division: a / b = a * inv(b)
rdiv : {R : Real} -> Carrier R -> Carrier R -> Carrier R
rdiv {R} a b = rmul a (rinv b)

infixl 70 / := rdiv

-- Strict ordering: a < b iff a <= b and a /= b
rlt : {R : Real} -> Carrier R -> Carrier R -> Type
rlt {R} a b = Pair (rle a b) (Equal a b -> Void)

-- Absolute value (defined from leTotal via eitherElim, not axiomatized)
rabs : {R : Real} -> Carrier R -> Carrier R
rabs {R} a = eitherElim (\\_ => a) (\\_ => rneg a) (CompleteOrderedField.leTotal (field R) (rzero R) a)

-- Dependent elimination for abs: to prove C(|a|), prove C(a) when 0<=a and C(-a) when a<=0
absElim : {R : Real} -> (a : Carrier R) -> (C : Carrier R -> Type) -> (rle (rzero R) a -> C a) -> (rle a (rzero R) -> C (rneg a)) -> C (rabs a)
absElim {R} a C pos neg = eitherElimDep (\\e => C (eitherElim (\\_ => a) (\\_ => rneg a) e)) (\\h => pos h) (\\h => neg h) (CompleteOrderedField.leTotal (field R) (rzero R) a)

-- Coercion: a decimal literal in a 'Carrier R' position elaborates to
-- realOfRat R (MkRat num den), which is (realOfNat R num) / (realOfNat R den).
-- So '1.5 : Carrier R' becomes '(realOfNat R 3) / (realOfNat R 2)'.
-- The structural definition lets the kernel reduce all the way to
-- abstract field axioms; homomorphism lemmas (below) build on this.
-- The d=1 case must come first so realOfRat produces the SAME kernel term
-- as @ofNat for integer-valued literals: \`realOfRat R (MkRat n 1)\` reduces
-- to \`realOfNat R n\`, matching what \`realOfNat\` would produce directly.
-- Without this, mixing integer literals (\`2.0\` → NatLit → @ofNat path) with
-- decimals (\`1.5\` → RatLit → @ofRat path) would create incompatible kernel
-- forms (\`realOfNat n\` vs \`rdiv (realOfNat n) (realOfNat 1)\`) that can't be
-- bridged structurally.
@syntax @ofRat
-- NOTE: use named pattern vars (\`p\`) for the NotZero proof instead of \`_\`.
-- The kernel's PWild handling has a known bug (substPatternBindings counts
-- only PVar bindings, but the compiled RHS uses indices counting both).
-- With \`p\`, indices line up correctly.
realOfRat : (R : Real) -> Rat -> Carrier R
realOfRat R (MkRat n (Succ Zero) p) = realOfInt R n
realOfRat R (MkRat n d p) = rdiv (realOfInt R n) (realOfNat R d)

-- Rat homomorphism lemmas (addRealOfRat, mulRealOfRat, subRealOfRat) are
-- defined further down — they need addRealOfNat and mulRealOfNat to be in
-- scope first.

------------------------------------------------------------
-- Limits: the epsilon-delta definition
------------------------------------------------------------

-- Epsilon-delta witness: given δ, prove δ > 0
-- and the epsilon-delta condition
@syntax @unfold
EpsDeltaWitness : {R : Real} -> (f : Carrier R -> Carrier R) -> (x0 : Carrier R) -> (L : Carrier R) -> (ε : Carrier R) -> Carrier R -> Type
EpsDeltaWitness {R} f x0 L ε δ = Pair (rlt (rzero R) δ) ((x : Carrier R) -> rlt (rzero R) (rabs (rsub x x0)) -> rlt (rabs (rsub x x0)) δ -> rlt (rabs (rsub (f x) L)) ε)

-- A proof that lim_{x -> x0} f(x) = L.
-- For every ε > 0, there exists δ > 0 such that
-- for all x, |x - x0| < δ implies |f(x) - L| < ε.
record Limit {R : Real} (f : Carrier R -> Carrier R) (x0 : Carrier R) (L : Carrier R) where
  eps_delta : (ε : Carrier R) -> rlt (rzero R) ε ->
              (δ : Carrier R ** EpsDeltaWitness f x0 L ε δ)

------------------------------------------------------------
-- Algebraic lemmas
------------------------------------------------------------

addZeroLeft : {R : Real} -> (a : Carrier R) -> Equal (radd (rzero R) a) a := by
  intros R a
  erw (CompleteOrderedField.addComm (field R) (rzero R) a), (CompleteOrderedField.addZeroRight (field R) a)

-- nat→Real homomorphism: realOfNat distributes over plus.
-- THIS is the bridge that lets numeric literal arithmetic work on abstract Real.
-- Proof sketch (induction on n):
--   Zero: rzero + realOfNat m = realOfNat m  by addZeroLeft
--   Succ: ((rone + realOfNat n) + realOfNat m)
--       = rone + (realOfNat n + realOfNat m)  by addAssoc
--       = rone + realOfNat (plus n m)         by IH
--       = realOfNat (Succ (plus n m))         by realOfNat (def-equal)
--       = realOfNat (plus (Succ n) m)         by plus (def-equal)
-- Applying \`addRealOfNat R 170 34\` proves \`Equal (radd 170 34) 204\` on Carrier R
-- because plus 170 34 reduces to NatLit 204 by primitive arithmetic.
addRealOfNat : (R : Real) -> (n m : Nat) -> Equal (radd (realOfNat R n) (realOfNat R m)) (realOfNat R (plus n m))
addRealOfNat R Zero m = addZeroLeft (realOfNat R m)
addRealOfNat R (Succ n) m = trans (CompleteOrderedField.addAssoc (field R) (rone R) (realOfNat R n) (realOfNat R m)) (cong (\\z => radd (rone R) z) (addRealOfNat R n m))

@syntax @simp
negLeft : {R : Real} -> (a : Carrier R) -> Equal (radd (rneg a) a) (rzero R) := by
  intros R a
  erw (CompleteOrderedField.addComm (field R) (rneg a) a), (CompleteOrderedField.negRight (field R) a)

-- a + (-a) = 0. The CompleteOrderedField axiom exposed as a top-level
-- lemma so the suggestion strip can offer it as a one-click @simp on
-- patterns like \`1 + (-1)\` (which match \`radd a (rneg a)\`).
@syntax @simp
addNegRight : {R : Real} -> (a : Carrier R) -> Equal (radd a (rneg a)) (rzero R)
addNegRight {R} a = CompleteOrderedField.negRight (field R) a

addLeRight : {R : Real} -> (a b c : Carrier R) -> rle a b -> rle (radd a c) (radd b c)
addLeRight {R} a b c h = (replace (\\z => rle z (radd b c)) (CompleteOrderedField.addComm (field R) c a) (replace (\\z => rle (radd c a) z) (CompleteOrderedField.addComm (field R) c b) (CompleteOrderedField.addLeLeft (field R) a b c h)))

addLeBoth : {R : Real} -> (a b c d : Carrier R) -> rle a b -> rle c d -> rle (radd a c) (radd b d)
addLeBoth {R} a b c d hab hcd = (CompleteOrderedField.leTrans (field R) (radd a c) (radd b c) (radd b d) (addLeRight a b c hab) (CompleteOrderedField.addLeLeft (field R) c d b hcd))

-- neg(0) = 0
negZero : (R : Real) -> Equal (rneg (rzero R)) (rzero R) := by
  intros R
  erw (sym (addZeroLeft (rneg (rzero R)))), (CompleteOrderedField.negRight (field R) (rzero R))

-- a <= 0 implies 0 <= -a
leNegNonneg : {R : Real} -> (a : Carrier R) -> rle a (rzero R) -> rle (rzero R) (rneg a)
leNegNonneg {R} a h = replace (\\z => rle z (rneg a)) (CompleteOrderedField.negRight (field R) a) (replace (\\z => rle (radd a (rneg a)) z) (addZeroLeft (rneg a)) (addLeRight a (rzero R) (rneg a) h))

-- 0 <= a implies -a <= 0
negNonpos : {R : Real} -> (a : Carrier R) -> rle (rzero R) a -> rle (rneg a) (rzero R)
negNonpos {R} a h = replace (\\z => rle (rneg a) z) (CompleteOrderedField.negRight (field R) a) (replace (\\z => rle z (radd a (rneg a))) (addZeroLeft (rneg a)) (addLeRight (rzero R) a (rneg a) h))

-- leLtTrans: a <= b, b < c => a < c
leLtTransLe : {R : Real} -> (a b c : Carrier R) -> rle a b -> rle b c -> rle a c
leLtTransLe {R} a b c hab hbc = CompleteOrderedField.leTrans (field R) a b c hab hbc

leLtTransNe : {R : Real} -> (a b c : Carrier R) -> rle a b -> rle b c -> (Equal b c -> Void) -> Equal a c -> Void
leLtTransNe {R} a b c hab hbc nebc eq = nebc (CompleteOrderedField.leAntisym (field R) b c hbc (replace (\\z => rle z b) eq hab))

leLtTrans : {R : Real} -> (a b c : Carrier R) -> rle a b -> rlt b c -> rlt a c
leLtTrans {R} a b c hab hbc = MkPair (leLtTransLe a b c hab (Pair.fst hbc)) (leLtTransNe a b c hab (Pair.fst hbc) (Pair.snd hbc))

-- ltLeTrans: a < b, b <= c => a < c
ltLeTransLe : {R : Real} -> (a b c : Carrier R) -> rle a b -> rle b c -> rle a c
ltLeTransLe {R} a b c hab hbc = CompleteOrderedField.leTrans (field R) a b c hab hbc

ltLeTransNe : {R : Real} -> (a b c : Carrier R) -> rle a b -> (Equal a b -> Void) -> rle b c -> Equal a c -> Void
ltLeTransNe {R} a b c hab neab hbc eq = neab (CompleteOrderedField.leAntisym (field R) a b hab (CompleteOrderedField.leTrans (field R) b c a hbc (replace (\\z => rle z a) eq (CompleteOrderedField.leRefl (field R) a))))

ltLeTrans : {R : Real} -> (a b c : Carrier R) -> rlt a b -> rle b c -> rlt a c
ltLeTrans {R} a b c hab hbc = MkPair (ltLeTransLe a b c (Pair.fst hab) hbc) (ltLeTransNe a b c (Pair.fst hab) (Pair.snd hab) hbc)

-- Cancellation: a + c = b + c => a = b
addCancelRightHelper : {R : Real} -> (x c : Carrier R) -> Equal (radd (radd x c) (rneg c)) x := by
  intros R x c
  erw (CompleteOrderedField.addAssoc (field R) x c (rneg c)), (CompleteOrderedField.negRight (field R) c), (CompleteOrderedField.addZeroRight (field R) x)

addCancelRight : {R : Real} -> (a b c : Carrier R) -> Equal (radd a c) (radd b c) -> Equal a b := by
  intros R a b c h
  erw (sym (addCancelRightHelper a c)), h, (addCancelRightHelper b c)

-- Cancellation forms for ordering (for backward reasoning via apply):
-- "a <= b" goal can be reduced to "a + c <= b + c" by applying these.
addLeRightCancel : {R : Real} -> (a b c : Carrier R) -> rle (radd a c) (radd b c) -> rle a b
addLeRightCancel {R} a b c h = (replace (\\z => rle z b) (addCancelRightHelper a c) (replace (\\z => rle (radd (radd a c) (rneg c)) z) (addCancelRightHelper b c) (addLeRight (radd a c) (radd b c) (rneg c) h)))

addLeLeftCancel : {R : Real} -> (a b c : Carrier R) -> rle (radd c a) (radd c b) -> rle a b
addLeLeftCancel {R} a b c h = (addLeRightCancel a b c (replace (\\z => rle (radd a c) z) (CompleteOrderedField.addComm (field R) c b) (replace (\\z => rle z (radd c b)) (CompleteOrderedField.addComm (field R) c a) h)))


-- Strict addition: a < b, c < d => a + c < b + d
addLtBothNe : {R : Real} -> (a b c d : Carrier R) -> rle a b -> (Equal a b -> Void) -> rle c d -> Equal (radd a c) (radd b d) -> Void
addLtBothNe {R} a b c d leab neab lecd eq = (neab (addCancelRight a b c (CompleteOrderedField.leAntisym (field R) (radd a c) (radd b c) (addLeRight a b c leab) (CompleteOrderedField.leTrans (field R) (radd b c) (radd b d) (radd a c) (CompleteOrderedField.addLeLeft (field R) c d b lecd) (replace (\\z => rle (radd b d) z) (sym eq) (CompleteOrderedField.leRefl (field R) (radd b d)))))))

addLtBoth : {R : Real} -> (a b c d : Carrier R) -> rlt a b -> rlt c d -> rlt (radd a c) (radd b d)
addLtBoth {R} a b c d hab hcd = MkPair (addLeBoth a b c d (Pair.fst hab) (Pair.fst hcd)) (addLtBothNe a b c d (Pair.fst hab) (Pair.snd hab) (Pair.fst hcd))

------------------------------------------------------------
-- Halving: 1/2 * eps + 1/2 * eps = eps
------------------------------------------------------------

@syntax 2
rtwo : (R : Real) -> Carrier R
rtwo R = radd (rone R) (rone R)

rhalf : (R : Real) -> Carrier R
rhalf R = rinv (rtwo R)

oneLeTwo : (R : Real) -> rle (rone R) (rtwo R)
oneLeTwo R = (replace (\\z => rle z (rtwo R)) (addZeroLeft (rone R)) (addLeRight (rzero R) (rone R) (rone R) (CompleteOrderedField.zeroLeOne (field R))))

twoNeZero : (R : Real) -> Equal (rtwo R) (rzero R) -> Void
twoNeZero R eq = (CompleteOrderedField.zeroNeOne (field R) (CompleteOrderedField.leAntisym (field R) (rzero R) (rone R) (CompleteOrderedField.zeroLeOne (field R)) (replace (\\z => rle (rone R) z) eq (oneLeTwo R))))

-- 1/2 + 1/2 = 1
halfPlusHalf : (R : Real) -> Equal (radd (rhalf R) (rhalf R)) (rone R) := by
  intros R
  erw (cong (\\z => radd z z) (sym (CompleteOrderedField.mulOneLeft (field R) (rhalf R)))), (sym (CompleteOrderedField.distribRight (field R) (rone R) (rone R) (rhalf R))), (CompleteOrderedField.mulInvRight (field R) (rtwo R) (twoNeZero R))

-- (1/2)*e + (1/2)*e = e
halfMulEps : {R : Real} -> (e : Carrier R) -> Equal (radd (rmul (rhalf R) e) (rmul (rhalf R) e)) e := by
  intros R e
  erw (sym (CompleteOrderedField.distribRight (field R) (rhalf R) (rhalf R) e)), (halfPlusHalf R), (CompleteOrderedField.mulOneLeft (field R) e)

zeroLeTwo : (R : Real) -> rle (rzero R) (rtwo R)
zeroLeTwo R = CompleteOrderedField.leTrans (field R) (rzero R) (rone R) (rtwo R) (CompleteOrderedField.zeroLeOne (field R)) (oneLeTwo R)

halfPos : (R : Real) -> rle (rzero R) (rhalf R)
halfPos R = CompleteOrderedField.invPos (field R) (rtwo R) (zeroLeTwo R) (twoNeZero R)

halfMulEpsLe : {R : Real} -> (e : Carrier R) -> rle (rzero R) e -> rle (rzero R) (rmul (rhalf R) e)
halfMulEpsLe {R} e hle = CompleteOrderedField.mulNonneg (field R) (rhalf R) e (halfPos R) hle

halfMulEpsNe : {R : Real} -> (e : Carrier R) -> rle (rzero R) e -> (Equal (rzero R) e -> Void) -> Equal (rzero R) (rmul (rhalf R) e) -> Void
halfMulEpsNe {R} e hle hne heq = hne (trans (sym (addZeroLeft (rzero R))) (trans (cong (\\z => radd z z) heq) (halfMulEps e)))

-- 0 < e => 0 < (1/2)*e
halfMulEpsPos : {R : Real} -> (e : Carrier R) -> rlt (rzero R) e -> rlt (rzero R) (rmul (rhalf R) e) := by
  intros R e hlt
  constructor
  · exact (halfMulEpsLe e (Pair.fst hlt))
  · exact (halfMulEpsNe e (Pair.fst hlt) (Pair.snd hlt))

------------------------------------------------------------
-- Negation distributes over addition: -(a+b) = (-a)+(-b)
------------------------------------------------------------

addSumNeg : {R : Real} -> (a b : Carrier R) -> Equal (radd (radd a b) (rneg a)) b := by
  intros R a b
  erw (CompleteOrderedField.addComm (field R) (radd a b) (rneg a)), (sym (CompleteOrderedField.addAssoc (field R) (rneg a) a b)), (negLeft a), (addZeroLeft b)

negAddCancel : {R : Real} -> (a b : Carrier R) -> Equal (radd (radd a b) (radd (rneg a) (rneg b))) (rzero R) := by
  intros R a b
  erw (sym (CompleteOrderedField.addAssoc (field R) (radd a b) (rneg a) (rneg b))), (addSumNeg a b), (CompleteOrderedField.negRight (field R) b)

negUnique : {R : Real} -> (a b : Carrier R) -> Equal (radd a b) (rzero R) -> Equal b (rneg a) := by
  intros R a b h
  erw (sym (addZeroLeft b)), (sym (negLeft a)), (CompleteOrderedField.addAssoc (field R) (rneg a) a b), h, (CompleteOrderedField.addZeroRight (field R) (rneg a))

negAdd : {R : Real} -> (a b : Carrier R) -> Equal (rneg (radd a b)) (radd (rneg a) (rneg b)) := by
  intros R a b
  erw (sym (negUnique (radd a b) (radd (rneg a) (rneg b)) (negAddCancel a b)))

-- --a = a
negNeg : {R : Real} -> (a : Carrier R) -> Equal (rneg (rneg a)) a
negNeg {R} a = sym (negUnique (rneg a) a (negLeft a))

-- Int -> Real negation homomorphism. Three pattern cases (the two Int
-- ctors plus IntOfNat split by Zero/Succ for the (-0 = 0) edge):
--   IntOfNat 0      ->  neg(0) = 0       via negZero
--   IntOfNat (S n)  ->  rfl              definitionally equal
--   IntNegSucc n    ->  neg(neg x) = x   via negNeg
negRealOfInt : (R : Real) -> (a : Int) -> Equal (rneg (realOfInt R a)) (realOfInt R (intNeg a))
negRealOfInt R (IntOfNat Zero) = negZero R
negRealOfInt R (IntOfNat (Succ n)) = refl
negRealOfInt R (IntNegSucc n) = negNeg (radd (rone R) (realOfNat R n))

-- Nat lemma: plus m (Succ n) = Succ (plus m n). Standard, induction on m.
plusSuccRight : (m n : Nat) -> Equal {A := Nat} (plus m (Succ n)) (Succ (plus m n))
plusSuccRight Zero n = refl
plusSuccRight (Succ m) n = cong Succ (plusSuccRight m n)

-- Field-algebra: (1+a) + (1+b) = 1 + (1 + realOfNat (plus m n)) when
-- a = realOfNat m, b = realOfNat n. Five assoc/comm/addRealOfNat shuffles.
-- Helper for the (IntNegSucc m, IntNegSucc n) case of addRealOfInt.
addOnePlusOneShuffle : (R : Real) -> (m n : Nat) -> Equal (radd (radd (rone R) (realOfNat R m)) (radd (rone R) (realOfNat R n))) (radd (rone R) (radd (rone R) (realOfNat R (plus m n)))) := by
  intros R m n
  erw (CompleteOrderedField.addAssoc (field R) (rone R) (realOfNat R m) (radd (rone R) (realOfNat R n))), (cong (\\z => radd (rone R) z) (sym (CompleteOrderedField.addAssoc (field R) (realOfNat R m) (rone R) (realOfNat R n)))), (cong (\\z => radd (rone R) (radd z (realOfNat R n))) (CompleteOrderedField.addComm (field R) (realOfNat R m) (rone R))), (cong (\\z => radd (rone R) z) (CompleteOrderedField.addAssoc (field R) (rone R) (realOfNat R m) (realOfNat R n))), (cong (\\z => radd (rone R) (radd (rone R) z)) (addRealOfNat R m n))

-- subSuccSucc, subNatNatLemma, addRealOfInt: defined further down,
-- after subAddSub / subSelf / subZeroRight are in scope.

------------------------------------------------------------
-- (a+b)-(c+d) = (a-c)+(b-d)
------------------------------------------------------------

fourTermRearrange : {R : Real} -> (a b c d : Carrier R) -> Equal (radd (radd a b) (radd c d)) (radd (radd a c) (radd b d)) := by
  intros R a b c d
  erw (CompleteOrderedField.addAssoc (field R) a b (radd c d)), (cong (\\z => radd a z) (trans (CompleteOrderedField.addComm (field R) b (radd c d)) (trans (CompleteOrderedField.addAssoc (field R) c d b) (cong (\\z => radd c z) (CompleteOrderedField.addComm (field R) d b))))), (sym (CompleteOrderedField.addAssoc (field R) a c (radd b d)))

subAddSub : {R : Real} -> (a b c d : Carrier R) -> Equal (rsub (radd a b) (radd c d)) (radd (rsub a c) (rsub b d)) := by
  intros R a b c d
  erw (cong (\\z => radd (radd a b) z) (negAdd c d)), (fourTermRearrange a b (rneg c) (rneg d))

------------------------------------------------------------
-- Multiplication-negation lemmas (needed for abs properties)
------------------------------------------------------------

-- 0*a = 0
mulZeroLeft : {R : Real} -> (a : Carrier R) -> Equal (rmul (rzero R) a) (rzero R)
mulZeroLeft {R} a = addCancelRight (rmul (rzero R) a) (rzero R) (rmul (rzero R) a) (trans (sym (CompleteOrderedField.distribRight (field R) (rzero R) (rzero R) a)) (trans (cong (\\z => rmul z a) (addZeroLeft (rzero R))) (sym (addZeroLeft (rmul (rzero R) a)))))

-- c*0 = 0
mulZeroRight : {R : Real} -> (c : Carrier R) -> Equal (rmul c (rzero R)) (rzero R) := by
  intros R c
  erw (CompleteOrderedField.mulComm (field R) c (rzero R)), (mulZeroLeft c)

-- nat→Real multiplication homomorphism: realOfNat distributes over mult.
-- The mul analog of addRealOfNat. Together they bridge any concrete nat
-- polynomial expression to abstract Real.
-- Proof (induction on n):
--   Zero: rmul (rzero R) (realOfNat R m) = rzero R = realOfNat R 0
--         which is def-equal to realOfNat R (mult 0 m).
--   Succ: rmul (radd 1 (realOfNat R n)) (realOfNat R m)
--       = rmul 1 m + rmul (realOfNat R n) (realOfNat R m)        [distribRight]
--       = realOfNat R m + rmul (realOfNat R n) (realOfNat R m)   [mulOneLeft]
--       = realOfNat R m + realOfNat R (mult n m)                 [IH/cong]
--       = realOfNat R (plus m (mult n m))                        [addRealOfNat]
--       = realOfNat R (mult (Succ n) m)                          [def-equal]
-- NOTE: type-checking USES of this lemma is currently slow for n*m > ~25
-- (kernel defeq fully unfolds realOfNat at each step). Soundness is fine;
-- perf optimization is a separate workstream.
mulRealOfNat : (R : Real) -> (n m : Nat) -> Equal (rmul (realOfNat R n) (realOfNat R m)) (realOfNat R (mult n m))
mulRealOfNat R Zero m = mulZeroLeft (realOfNat R m)
mulRealOfNat R (Succ n) m = trans (CompleteOrderedField.distribRight (field R) (rone R) (realOfNat R n) (realOfNat R m)) (trans (cong (\\z => radd z (rmul (realOfNat R n) (realOfNat R m))) (CompleteOrderedField.mulOneLeft (field R) (realOfNat R m))) (trans (cong (\\z => radd (realOfNat R m) z) (mulRealOfNat R n m)) (addRealOfNat R m (mult n m))))

-- Foundational field-algebra lemmas. Building blocks for the Rat
-- homomorphisms below — derived from CompleteOrderedField axioms, no
-- postulates.

-- 1 != 0 (flip of zeroNeOne)
oneNeZero : (R : Real) -> Equal (rone R) (rzero R) -> Void
oneNeZero R eq = CompleteOrderedField.zeroNeOne (field R) (sym eq)

-- 1/1 = 1: the multiplicative inverse of one is one.
-- Proof: 1 = 1*(1/1) by mulOneLeft^{-1}, and 1*(1/1) = 1 by mulInvRight.
invOne : (R : Real) -> Equal (rinv (rone R)) (rone R)
invOne R = trans (sym (CompleteOrderedField.mulOneLeft (field R) (rinv (rone R)))) (CompleteOrderedField.mulInvRight (field R) (rone R) (oneNeZero R))

-- a/1 = a: dividing by one is the identity.
divOne : {R : Real} -> (a : Carrier R) -> Equal (rdiv a (rone R)) a
divOne {R} a = trans (cong (\\z => rmul a z) (invOne R)) (CompleteOrderedField.mulOneRight (field R) a)

-- a * (b/c) = (a*b)/c — multiplication absorbs into the numerator
-- (just associativity unfolded; no non-zero needed).
mulDivAssoc : {R : Real} -> (a b c : Carrier R) -> Equal (rmul a (rdiv b c)) (rdiv (rmul a b) c)
mulDivAssoc {R} a b c = sym (CompleteOrderedField.mulAssoc (field R) a b (rinv c))

-- (a/b) * c = (a*c)/b — symmetric to mulDivAssoc.
divMulRight : {R : Real} -> (a b c : Carrier R) -> Equal (rmul (rdiv a b) c) (rdiv (rmul a c) b)
divMulRight {R} a b c = trans (CompleteOrderedField.mulAssoc (field R) a (rinv b) c) (trans (cong (\\z => rmul a z) (CompleteOrderedField.mulComm (field R) (rinv b) c)) (sym (CompleteOrderedField.mulAssoc (field R) a c (rinv b))))

@syntax @simp
-- realOfNat R 1 = 1: in any field, "one" as a Nat coerces to the
-- field's multiplicative identity. Reduces via realOfNat's Succ case:
-- realOfNat 1 = 1 + realOfNat 0 = 1 + 0, then addZeroRight closes it.
realOfNatOne : (R : Real) -> Equal (realOfNat R 1) (rone R)
realOfNatOne R = CompleteOrderedField.addZeroRight (field R) (rone R)

-- Bridge lemmas: the @ofRat / @ofInt elaboration ladders wrap an integer
-- literal \`1 : Carrier R\` as \`realOfRat R (MkRat (IntOfNat 1) 1 _)\` or
-- \`realOfInt R (IntOfNat 1)\` — both of which are definitionally equal to
-- \`rone R\` but structurally distinct, so simp lemmas keyed on \`rone R\`
-- (like addNegRight) don't fire. Tagging these as @simp lets the
-- suggestion strip canonicalize them to bare \`rone R\` in one click,
-- after which the structural simp lemmas line up.
@syntax @simp
realOfIntOne : (R : Real) -> Equal (realOfInt R (IntOfNat 1)) (rone R)
realOfIntOne R = realOfNatOne R

@syntax @simp
realOfRatOne : (R : Real) -> Equal (realOfRat R (MkRat (IntOfNat 1) 1 (IsSucc 0))) (rone R)
realOfRatOne R = realOfNatOne R

-- Zero-side bridge lemmas, parallel to the One-side ones. Tagged @simp so
-- \`0 : Carrier R\` literal-coerced through @ofNat / @ofInt / @ofRat
-- collapses to \`rzero R\` and field axioms like
-- \`CompleteOrderedField.zeroLeOne : rle (rzero R) (rone R)\` can apply.
@syntax @simp
realOfNatZero : (R : Real) -> Equal (realOfNat R 0) (rzero R)
realOfNatZero R = refl

@syntax @simp
realOfIntZero : (R : Real) -> Equal (realOfInt R (IntOfNat 0)) (rzero R)
realOfIntZero R = refl

@syntax @simp
realOfRatZero : (R : Real) -> Equal (realOfRat R (MkRat (IntOfNat 0) 1 (IsSucc 0))) (rzero R)
realOfRatZero R = refl

-- 0 < 1: the field's foundational positivity. Used by realOfNatSuccPos
-- (below) and the limit/derivative proofs (further down).
zeroLtOne : (R : Real) -> rlt (rzero R) (rone R) := by
  intros R
  constructor
  · exact (CompleteOrderedField.zeroLeOne (field R))
  · exact (CompleteOrderedField.zeroNeOne (field R))

-- realOfNat R n is non-negative for every Nat n. Induction on n:
-- base (Zero): 0 ≤ 0 by reflexivity. Step (Succ): 0 + 0 ≤ 1 + n by
-- addLeBoth(zeroLeOne, IH); rewrite 0+0 to 0 via addZeroRight.
realOfNatNonneg : (R : Real) -> (n : Nat) -> rle (rzero R) (realOfNat R n)
realOfNatNonneg R Zero = CompleteOrderedField.leRefl (field R) (rzero R)
realOfNatNonneg R (Succ n) = replace (\\z => rle z (radd (rone R) (realOfNat R n))) (CompleteOrderedField.addZeroRight (field R) (rzero R)) (addLeBoth (rzero R) (rone R) (rzero R) (realOfNat R n) (CompleteOrderedField.zeroLeOne (field R)) (realOfNatNonneg R n))

-- 1 ≤ realOfNat R (Succ n) for every Nat n. Follows from realOfNatNonneg:
-- 1+0 ≤ 1+n by addLeLeft(realOfNatNonneg); rewrite 1+0 to 1 via addZeroRight.
oneLeRealOfNatSucc : (R : Real) -> (n : Nat) -> rle (rone R) (realOfNat R (Succ n))
oneLeRealOfNatSucc R n = replace (\\z => rle z (radd (rone R) (realOfNat R n))) (CompleteOrderedField.addZeroRight (field R) (rone R)) (CompleteOrderedField.addLeLeft (field R) (rzero R) (realOfNat R n) (rone R) (realOfNatNonneg R n))

-- 0 < realOfNat R (Succ n): transitivity of 0 < 1 ≤ realOfNat (Succ n).
realOfNatSuccPos : (R : Real) -> (n : Nat) -> rlt (rzero R) (realOfNat R (Succ n))
realOfNatSuccPos R n = ltLeTrans (rzero R) (rone R) (realOfNat R (Succ n)) (zeroLtOne R) (oneLeRealOfNatSucc R n)

-- realOfNat R (Succ n) ≠ 0: the load-bearing non-zero proof for canonical
-- Rat denominators. From realOfNatSuccPos = Pair (0 ≤ x) (0 ≠ x); take
-- the second arg and flip via sym.
realOfNatSuccNeZero : (R : Real) -> (n : Nat) -> Equal (realOfNat R (Succ n)) (rzero R) -> Void
realOfNatSuccNeZero R n eq = Pair.snd (realOfNatSuccPos R n) (sym eq)

-- a≠0 ∧ b≠0 → a*b ≠ 0. By contradiction: if a*b = 0 and a ≠ 0, then
-- b = 1*b = (1/a · a)*b = 1/a · (a*b) = 1/a · 0 = 0 — contradicting b ≠ 0.
-- (Same shape as the existing mulLtLeftNe cancellation proof.)
mulNeZero : {R : Real} -> (a b : Carrier R) -> (Equal a (rzero R) -> Void) -> (Equal b (rzero R) -> Void) -> Equal (rmul a b) (rzero R) -> Void := by
  intros R a b ane bne eq
  apply bne
  erw (sym (CompleteOrderedField.mulOneLeft (field R) b)), (cong (\\z => rmul z b) (sym (trans (CompleteOrderedField.mulComm (field R) (rinv a) a) (CompleteOrderedField.mulInvRight (field R) a ane)))), (CompleteOrderedField.mulAssoc (field R) (rinv a) a b), (cong (\\z => rmul (rinv a) z) eq), (mulZeroRight (rinv a))

-- (a*b) * (inv a * inv b) = 1. Five associativity/commutativity shuffles
-- bring matched a/inv-a and b/inv-b adjacent, then mulInvRight closes each.
-- Building block for invMul.
mulInvMulInv : {R : Real} -> (a b : Carrier R) -> (Equal a (rzero R) -> Void) -> (Equal b (rzero R) -> Void) -> Equal (rmul (rmul a b) (rmul (rinv a) (rinv b))) (rone R) := by
  intros R a b ane bne
  erw (CompleteOrderedField.mulAssoc (field R) a b (rmul (rinv a) (rinv b))), (sym (CompleteOrderedField.mulAssoc (field R) b (rinv a) (rinv b))), (CompleteOrderedField.mulComm (field R) b (rinv a)), (CompleteOrderedField.mulAssoc (field R) (rinv a) b (rinv b)), (CompleteOrderedField.mulInvRight (field R) b bne), (CompleteOrderedField.mulOneRight (field R) (rinv a)), (CompleteOrderedField.mulInvRight (field R) a ane)

-- 1/(a*b) = (1/a)*(1/b). By uniqueness of inverse: both sides are the
-- multiplicative inverse of (a*b). Specifically:
--   1/(a*b) = 1/(a*b) * 1
--          = 1/(a*b) * ((a*b) * (1/a * 1/b))     [via mulInvMulInv]
--          = (1/(a*b) * (a*b)) * (1/a * 1/b)     [mulAssoc]
--          = 1 * (1/a * 1/b)                     [mulInvRight, needs a*b ≠ 0]
--          = 1/a * 1/b                           [mulOneLeft]
invMul : {R : Real} -> (a b : Carrier R) -> (Equal a (rzero R) -> Void) -> (Equal b (rzero R) -> Void) -> Equal (rinv (rmul a b)) (rmul (rinv a) (rinv b)) := by
  intros R a b ane bne
  erw (sym (CompleteOrderedField.mulOneRight (field R) (rinv (rmul a b)))), (cong (\\z => rmul (rinv (rmul a b)) z) (sym (mulInvMulInv a b ane bne))), (sym (CompleteOrderedField.mulAssoc (field R) (rinv (rmul a b)) (rmul a b) (rmul (rinv a) (rinv b)))), (CompleteOrderedField.mulComm (field R) (rinv (rmul a b)) (rmul a b)), (CompleteOrderedField.mulInvRight (field R) (rmul a b) (mulNeZero a b ane bne)), (CompleteOrderedField.mulOneLeft (field R) (rmul (rinv a) (rinv b)))

-- (a/b)*(c/d) = (a*c)/(b*d). The standard rational-multiplication identity.
-- Needs b ≠ 0 and d ≠ 0 (for invMul). The proof is mostly associativity
-- and commutativity to bring matched terms together, then sym-invMul
-- combines 1/b * 1/d into 1/(b*d).
mulDivDiv : {R : Real} -> (a b c d : Carrier R) -> (Equal b (rzero R) -> Void) -> (Equal d (rzero R) -> Void) -> Equal (rmul (rdiv a b) (rdiv c d)) (rdiv (rmul a c) (rmul b d)) := by
  intros R a b c d bne dne
  erw (CompleteOrderedField.mulAssoc (field R) a (rinv b) (rmul c (rinv d))), (sym (CompleteOrderedField.mulAssoc (field R) (rinv b) c (rinv d))), (CompleteOrderedField.mulComm (field R) (rinv b) c), (CompleteOrderedField.mulAssoc (field R) c (rinv b) (rinv d)), (sym (CompleteOrderedField.mulAssoc (field R) a c (rmul (rinv b) (rinv d)))), (cong (\\z => rmul (rmul a c) z) (sym (invMul b d bne dne)))

-- Generic division helpers used to prove addRealOfRat by case-splitting
-- on the two Rat denominators.

-- (a*e)/e = a for e ≠ 0
divCancel : {R : Real} -> (a e : Carrier R) -> (Equal e (rzero R) -> Void) -> Equal (rdiv (rmul a e) e) a
divCancel {R} a e ene = trans (CompleteOrderedField.mulAssoc (field R) a e (rinv e)) (trans (cong (\\z => rmul a z) (CompleteOrderedField.mulInvRight (field R) e ene)) (CompleteOrderedField.mulOneRight (field R) a))

-- x/e + y/e = (x+y)/e
addDivSame : {R : Real} -> (x y e : Carrier R) -> Equal (radd (rdiv x e) (rdiv y e)) (rdiv (radd x y) e)
addDivSame {R} x y e = sym (CompleteOrderedField.distribRight (field R) x y (rinv e))

-- x/b = (x*d)/(b*d) for b, d ≠ 0 (denominator expansion via multiplication by d/d=1).
divDenomExpand : {R : Real} -> (x b d : Carrier R) -> (Equal b (rzero R) -> Void) -> (Equal d (rzero R) -> Void) -> Equal (rdiv x b) (rdiv (rmul x d) (rmul b d))
divDenomExpand {R} x b d bne dne = trans (sym (CompleteOrderedField.mulOneRight (field R) (rdiv x b))) (trans (cong (\\z => rmul (rdiv x b) z) (sym (CompleteOrderedField.mulInvRight (field R) d dne))) (mulDivDiv x b d d bne dne))

-- (x/b) + (y/d) = (x*d + y*b)/(b*d). The cross-multiplication identity.
addDivDiv : {R : Real} -> (x b y d : Carrier R) -> (Equal b (rzero R) -> Void) -> (Equal d (rzero R) -> Void) -> Equal (radd (rdiv x b) (rdiv y d)) (rdiv (radd (rmul x d) (rmul y b)) (rmul b d))
addDivDiv {R} x b y d bne dne = trans (cong (\\z => radd z (rdiv y d)) (divDenomExpand x b d bne dne)) (trans (cong (\\z => radd (rdiv (rmul x d) (rmul b d)) z) (trans (divDenomExpand y d b dne bne) (cong (\\w => rdiv (rmul y b) w) (CompleteOrderedField.mulComm (field R) d b)))) (addDivSame (rmul x d) (rmul y b) (rmul b d)))

-- a + c/e = (a*e + c)/e for e ≠ 0
addCommonDenom : {R : Real} -> (a c e : Carrier R) -> (Equal e (rzero R) -> Void) -> Equal (radd a (rdiv c e)) (rdiv (radd (rmul a e) c) e)
addCommonDenom {R} a c e ene = trans (cong (\\z => radd z (rdiv c e)) (sym (divCancel a e ene))) (addDivSame (rmul a e) c e)

-- a/e + c = (a + c*e)/e for e ≠ 0
addCommonDenomLeft : {R : Real} -> (a c e : Carrier R) -> (Equal e (rzero R) -> Void) -> Equal (radd (rdiv a e) c) (rdiv (radd a (rmul c e)) e)
addCommonDenomLeft {R} a c e ene = trans (cong (\\z => radd (rdiv a e) z) (sym (divCancel c e ene))) (addDivSame a (rmul c e) e)

-- addRealOfRat and subRealOfRat are defined further down, after mulRealOfInt.

-- c*(-b) = -(c*b)
mulNegRight : {R : Real} -> (c b : Carrier R) -> Equal (rmul c (rneg b)) (rneg (rmul c b))
mulNegRight {R} c b = negUnique (rmul c b) (rmul c (rneg b)) (trans (sym (CompleteOrderedField.distribLeft (field R) c b (rneg b))) (trans (cong (\\z => rmul c z) (CompleteOrderedField.negRight (field R) b)) (mulZeroRight c)))

-- (-a) * b = -(a * b)
mulNegLeft : {R : Real} -> (a b : Carrier R) -> Equal (rmul (rneg a) b) (rneg (rmul a b)) := by
  intros R a b
  erw (CompleteOrderedField.mulComm (field R) (rneg a) b), (mulNegRight b a), (CompleteOrderedField.mulComm (field R) b a)

-- rneg (y/e) = (rneg y)/e — pulling negation through division.
negDivLeft : {R : Real} -> (y e : Carrier R) -> Equal (rneg (rdiv y e)) (rdiv (rneg y) e)
negDivLeft {R} y e = sym (mulNegLeft y (rinv e))

-- Subtraction-side analogues of addDivSame/addCommonDenom/addCommonDenomLeft/addDivDiv,
-- derived by pulling rneg into divisions and reusing the addition variants.
subDivSame : {R : Real} -> (x y e : Carrier R) -> Equal (rsub (rdiv x e) (rdiv y e)) (rdiv (rsub x y) e)
subDivSame {R} x y e = trans (cong (\\z => radd (rdiv x e) z) (negDivLeft y e)) (addDivSame x (rneg y) e)

subCommonDenom : {R : Real} -> (a c e : Carrier R) -> (Equal e (rzero R) -> Void) -> Equal (rsub a (rdiv c e)) (rdiv (rsub (rmul a e) c) e)
subCommonDenom {R} a c e ene = trans (cong (\\z => radd a z) (negDivLeft c e)) (addCommonDenom a (rneg c) e ene)

subCommonDenomLeft : {R : Real} -> (a c e : Carrier R) -> (Equal e (rzero R) -> Void) -> Equal (rsub (rdiv a e) c) (rdiv (rsub a (rmul c e)) e)
subCommonDenomLeft {R} a c e ene = trans (addCommonDenomLeft a (rneg c) e ene) (cong (\\z => rdiv (radd a z) e) (mulNegLeft c e))

subDivDiv : {R : Real} -> (x b y d : Carrier R) -> (Equal b (rzero R) -> Void) -> (Equal d (rzero R) -> Void) -> Equal (rsub (rdiv x b) (rdiv y d)) (rdiv (rsub (rmul x d) (rmul y b)) (rmul b d))
subDivDiv {R} x b y d bne dne = trans (cong (\\z => radd (rdiv x b) z) (negDivLeft y d)) (trans (addDivDiv x b (rneg y) d bne dne) (cong (\\z => rdiv (radd (rmul x d) z) (rmul b d)) (mulNegLeft y b)))

------------------------------------------------------------
-- Absolute value properties (derived from leTotal)
------------------------------------------------------------

-- 0 <= |a|
absNonneg : {R : Real} -> (a : Carrier R) -> rle (rzero R) (rabs a)
absNonneg {R} a = absElim a (\\x => rle (rzero R) x) (\\h => h) (\\h => leNegNonneg a h)

-- |0| = 0
absZero : (R : Real) -> Equal (rabs (rzero R)) (rzero R)
absZero R = absElim (rzero R) (\\x => Equal x (rzero R)) (\\_ => refl) (\\_ => negZero R)

-- |a| = 0 implies a = 0
absEqZero : {R : Real} -> (a : Carrier R) -> Equal (rabs a) (rzero R) -> Equal a (rzero R)
absEqZero {R} a h = absElim a (\\x => Equal x (rzero R) -> Equal a (rzero R)) (\\_ eq => eq) (\\_ eq => trans (sym (negNeg a)) (trans (cong (\\z => rneg z) eq) (negZero R))) h

leAbs : {R : Real} -> (a : Carrier R) -> rle a (rabs a)
leAbs {R} a = absElim a (\\x => rle a x) (\\_ => CompleteOrderedField.leRefl (field R) a) (\\h => CompleteOrderedField.leTrans (field R) a (rzero R) (rneg a) h (leNegNonneg a h))

leAbsNeg : {R : Real} -> (a : Carrier R) -> rle (rneg a) (rabs a)
leAbsNeg {R} a = absElim a (\\x => rle (rneg a) x) (\\h => CompleteOrderedField.leTrans (field R) (rneg a) (rzero R) a (negNonpos a h) h) (\\_ => CompleteOrderedField.leRefl (field R) (rneg a))

absTriangle : {R : Real} -> (a b : Carrier R) -> rle (rabs (radd a b)) (radd (rabs a) (rabs b))
absTriangle {R} a b = absElim (radd a b) (\\x => rle x (radd (rabs a) (rabs b))) (\\_ => addLeBoth a (rabs a) b (rabs b) (leAbs a) (leAbs b)) (\\_ => replace (\\z => rle z (radd (rabs a) (rabs b))) (sym (negAdd a b)) (addLeBoth (rneg a) (rabs a) (rneg b) (rabs b) (leAbsNeg a) (leAbsNeg b)))

absOfNonneg : {R : Real} -> (a : Carrier R) -> rle (rzero R) a -> Equal (rabs a) a
absOfNonneg {R} a h = absElim a (\\x => Equal x a) (\\_ => refl) (\\h2 => trans (cong (\\z => rneg z) (sym (CompleteOrderedField.leAntisym (field R) (rzero R) a h h2))) (trans (negZero R) (CompleteOrderedField.leAntisym (field R) (rzero R) a h h2)))

absOfNonpos : {R : Real} -> (a : Carrier R) -> rle a (rzero R) -> Equal (rabs a) (rneg a)
absOfNonpos {R} a h = absElim a (\\x => Equal x (rneg a)) (\\h2 => trans (sym (CompleteOrderedField.leAntisym (field R) (rzero R) a h2 h)) (sym (trans (negZero R) (CompleteOrderedField.leAntisym (field R) (rzero R) a h2 h)))) (\\_ => refl)

negMulNeg : {R : Real} -> (a b : Carrier R) -> Equal (rmul (rneg a) (rneg b)) (rmul a b)
negMulNeg {R} a b = trans (mulNegLeft a (rneg b)) (trans (cong (\\z => rneg z) (mulNegRight a b)) (negNeg (rmul a b)))

mulNonnegNonpos : {R : Real} -> (a b : Carrier R) -> rle (rzero R) a -> rle b (rzero R) -> rle (rmul a b) (rzero R)
mulNonnegNonpos {R} a b ha hb = replace (\\z => rle z (rzero R)) (negNeg (rmul a b)) (negNonpos (rneg (rmul a b)) (replace (\\z => rle (rzero R) z) (mulNegRight a b) (CompleteOrderedField.mulNonneg (field R) a (rneg b) ha (leNegNonneg b hb))))

mulNegNeg : {R : Real} -> (a b : Carrier R) -> rle a (rzero R) -> rle b (rzero R) -> rle (rzero R) (rmul a b)
mulNegNeg {R} a b ha hb = replace (\\z => rle (rzero R) z) (negMulNeg a b) (CompleteOrderedField.mulNonneg (field R) (rneg a) (rneg b) (leNegNonneg a ha) (leNegNonneg b hb))

absMul : {R : Real} -> (a b : Carrier R) -> Equal (rabs (rmul a b)) (rmul (rabs a) (rabs b))
absMul {R} a b = absElim a (\\va => Equal (rabs (rmul a b)) (rmul va (rabs b))) (\\ha => absElim b (\\vb => Equal (rabs (rmul a b)) (rmul a vb)) (\\hb => absOfNonneg (rmul a b) (CompleteOrderedField.mulNonneg (field R) a b ha hb)) (\\hb => trans (absOfNonpos (rmul a b) (mulNonnegNonpos a b ha hb)) (sym (mulNegRight a b)))) (\\ha => absElim b (\\vb => Equal (rabs (rmul a b)) (rmul (rneg a) vb)) (\\hb => trans (absOfNonpos (rmul a b) (replace (\\z => rle z (rzero R)) (CompleteOrderedField.mulComm (field R) b a) (mulNonnegNonpos b a hb ha))) (sym (mulNegLeft a b))) (\\hb => trans (absOfNonneg (rmul a b) (mulNegNeg a b ha hb)) (sym (negMulNeg a b))))

------------------------------------------------------------
-- THE THEOREM: lim(f) + lim(g) = lim(f + g)
------------------------------------------------------------

-- Core estimate: |f(x)-L| < he, |g(x)-M| < he => |(f+g)(x)-(L+M)| < he+he
-- Uses triangle inequality and addLtBoth
coreEstimate : {R : Real} -> (f g : Carrier R -> Carrier R) -> (x0 L M he : Carrier R) -> (x : Carrier R) -> rlt (rabs (rsub (f x) L)) he -> rlt (rabs (rsub (g x) M)) he -> rlt (rabs (rsub (radd (f x) (g x)) (radd L M))) (radd he he)
coreEstimate {R} f g x0 L M he x hfx hgx = (leLtTrans (rabs (rsub (radd (f x) (g x)) (radd L M))) (radd (rabs (rsub (f x) L)) (rabs (rsub (g x) M))) (radd he he) (replace (\\z => rle (rabs z) (radd (rabs (rsub (f x) L)) (rabs (rsub (g x) M)))) (sym (subAddSub (f x) (g x) L M)) (absTriangle (rsub (f x) L) (rsub (g x) M))) (addLtBoth (rabs (rsub (f x) L)) he (rabs (rsub (g x) M)) he hfx hgx))

-- Bridge: (1/2)*e = e/2 (by mul commutativity)
halfEqDiv : {R : Real} -> (e : Carrier R) -> Equal (rmul (rhalf R) e) (rdiv e (rtwo R))
halfEqDiv {R} e = CompleteOrderedField.mulComm (field R) (rhalf R) e

-- 0 < e => 0 < e/2
divTwoPos : {R : Real} -> (e : Carrier R) -> rlt (rzero R) e -> rlt (rzero R) (rdiv e (rtwo R))
divTwoPos {R} e hlt = replace (\\z => rlt (rzero R) z) (halfEqDiv e) (halfMulEpsPos e hlt)

-- e/2 + e/2 = e
divTwoAddEq : {R : Real} -> (e : Carrier R) -> Equal (radd (rdiv e (rtwo R)) (rdiv e (rtwo R))) e
divTwoAddEq {R} e = replace (\\z => Equal (radd z z) e) (halfEqDiv e) (halfMulEps e)

-- Convert < (e/2 + e/2) to < e
convertEps : {R : Real} -> (ε v : Carrier R) -> rlt v (radd (rdiv ε (rtwo R)) (rdiv ε (rtwo R))) -> rlt v ε
convertEps {R} ε v hlt = replace (\\z => rlt v z) (divTwoAddEq ε) hlt

-- lim_{x->x0} f(x) = L  and  lim_{x->x0} g(x) = M
--   =>  lim_{x->x0} (f(x) + g(x)) = L + M
-- pickDelta is inlined: uses eitherElim on leTotal to pick smaller delta,
-- each case builds the EpsDeltaWitness via convertEps + coreEstimate + ltLeTrans
limitAdd : {R : Real} -> (f g : Carrier R -> Carrier R) -> (x0 L M : Carrier R) -> Limit f x0 L -> Limit g x0 M -> Limit (\\x => radd (f x) (g x)) x0 (radd L M) := by
  intros R f g x0 L M limF limG
  constructor
  intros ε hε
  cases (Limit.eps_delta limF (rdiv ε (rtwo R)) (divTwoPos ε hε)) with
  | MkDPair δF (MkPair posF boundF) =>
    cases (Limit.eps_delta limG (rdiv ε (rtwo R)) (divTwoPos ε hε)) with
    | MkDPair δG (MkPair posG boundG) =>
      cases (CompleteOrderedField.leTotal (field R) δF δG) with
      | Left hle =>
        constructor
        · exact δF
        · constructor
          · exact posF
          · exact (\\x hx0 hxd => convertEps ε (rabs (rsub (radd (f x) (g x)) (radd L M))) (coreEstimate f g x0 L M (rdiv ε (rtwo R)) x (boundF x hx0 hxd) (boundG x hx0 (ltLeTrans (rabs (rsub x x0)) δF δG hxd hle))))
      | Right hle =>
        constructor
        · exact δG
        · constructor
          · exact posG
          · exact (\\x hx0 hxd => convertEps ε (rabs (rsub (radd (f x) (g x)) (radd L M))) (coreEstimate f g x0 L M (rdiv ε (rtwo R)) x (boundF x hx0 (ltLeTrans (rabs (rsub x x0)) δG δF hxd hle)) (boundG x hx0 hxd)))

-- lim (f+g+h) = (L+M)+N: three-function limit addition via two applications of limitAdd
limitAdd3 : {R : Real} -> (f g h : Carrier R -> Carrier R) -> (x0 L M N : Carrier R) -> Limit f x0 L -> Limit g x0 M -> Limit h x0 N -> Limit (\\x => radd (radd (f x) (g x)) (h x)) x0 (radd (radd L M) N)
limitAdd3 {R} f g h x0 L M N limF limG limH = limitAdd (\\x => radd (f x) (g x)) h x0 (radd L M) N (limitAdd f g x0 L M limF limG) limH

------------------------------------------------------------
-- The lim operator: projecting the limit value
------------------------------------------------------------

-- a - a = 0
subSelf : {R : Real} -> (a : Carrier R) -> Equal (rsub a a) (rzero R)
subSelf {R} a = CompleteOrderedField.negRight (field R) a

-- zeroLtOne moved earlier (above the Rat homomorphism section) so the
-- positivity lemmas there can use it.

-- The limit of a constant function: lim_{x->x0} k = k
-- Proof: For any eps > 0, pick delta = 1. Then |k - k| = 0 < eps.
limitConst : {R : Real} -> (k x0 : Carrier R) -> Limit (\\_ => k) x0 k := by
  intros R k x0
  constructor
  intros eps heps
  exact (MkDPair (rone R) (MkPair (zeroLtOne R) (\\x hx0 hxd => replace (\\z => rlt (rabs z) eps) (sym (subSelf k)) (replace (\\z => rlt z eps) (sym (absZero R)) heps))))

-- lim: extract the limit value from a convergence proof
-- Given f, x0, and a proof that lim_{x->x0} f(x) = L, returns L
lim : {R : Real} -> {L : Carrier R} -> (f : Carrier R -> Carrier R) -> (x0 : Carrier R) -> Limit f x0 L -> Carrier R
lim {R} {L} f x0 pf = L

-- lim f + lim g = lim (f + g): both sides reduce to Lf + Lg
limit_pull_radd : {R : Real} -> (f g : Carrier R -> Carrier R) -> (x0 Lf Lg : Carrier R) -> (limF : Limit f x0 Lf) -> (limG : Limit g x0 Lg) -> Equal (radd (lim f x0 limF) (lim g x0 limG)) (lim (\\x => radd (f x) (g x)) x0 (limitAdd f g x0 Lf Lg limF limG))
limit_pull_radd _ _ _ _ _ _ _ = refl

-- (lim f + lim g) + lim h = lim ((f+g)+h): both sides reduce to (Lf+Lg)+Lh
limit_pull_radd3 : {R : Real} -> (f g h : Carrier R -> Carrier R) -> (x0 Lf Lg Lh : Carrier R) -> (limF : Limit f x0 Lf) -> (limG : Limit g x0 Lg) -> (limH : Limit h x0 Lh) -> Equal (radd (radd (lim f x0 limF) (lim g x0 limG)) (lim h x0 limH)) (lim (\\x => radd (radd (f x) (g x)) (h x)) x0 (limitAdd3 f g h x0 Lf Lg Lh limF limG limH))
limit_pull_radd3 _ _ _ _ _ _ _ _ _ _ = refl

-- c * lim f = lim (c * f): both sides reduce to c * Lf
-- NOTE: needs limitScalarAll which is in the commented-out derivatives section.
-- Uncomment that section to enable this theorem.
-- limit_pull_scalar : {R : Real} -> (c : Carrier R) -> (f : Carrier R -> Carrier R) -> (x0 Lf : Carrier R) -> (limF : Limit f x0 Lf) -> Equal (rmul c (lim f x0 limF)) (lim (\\x => rmul c (f x)) x0 (limitScalarAll c f x0 Lf limF))
-- limit_pull_scalar _ _ _ _ _ = refl

-- k = lim_{x->x0} k: both sides reduce to k
lim_const : {R : Real} -> (k x0 : Carrier R) -> Equal k (lim (\\_ => k) x0 (limitConst k x0))
lim_const _ _ = refl

-- k + lim f = lim (k + f): both sides reduce to k + Lf
limit_pull_const_add : {R : Real} -> (k : Carrier R) -> (f : Carrier R -> Carrier R) -> (x0 Lf : Carrier R) -> (limF : Limit f x0 Lf) -> Equal (radd k (lim f x0 limF)) (lim (\\x => radd k (f x)) x0 (limitAdd (\\_ => k) f x0 k Lf (limitConst k x0) limF))
limit_pull_const_add _ _ _ _ _ = refl

------------------------------------------------------------
-- DERIVATIVES
------------------------------------------------------------

-- Difference quotient: (f(x) - f(x0)) / (x - x0)
diffQuot : {R : Real} -> (f : Carrier R -> Carrier R) -> (x0 : Carrier R) -> Carrier R -> Carrier R
diffQuot {R} f x0 x = rmul (rsub (f x) (f x0)) (rinv (rsub x x0))

-- Definition: HasDerivative f x0 L means lim_{x->x0} (f(x)-f(x0))/(x-x0) = L
HasDerivative : {R : Real} -> (f : Carrier R -> Carrier R) -> (x0 : Carrier R) -> (L : Carrier R) -> Type
HasDerivative {R} f x0 L = Limit (diffQuot f x0) x0 L

-- deriv: extract the derivative value from a differentiability proof
-- Given f, x0, and a proof that f is differentiable at x0 with derivative L, returns L
deriv : {R : Real} -> {L : Carrier R} -> (f : Carrier R -> Carrier R) -> (x0 : Carrier R) -> HasDerivative f x0 L -> Carrier R
deriv {R} {L} f x0 hf = L

-- limitExt: if f and g agree pointwise, limits transfer
limitExt : {R : Real} -> (f g : Carrier R -> Carrier R) -> (x0 L : Carrier R) -> ((x : Carrier R) -> Equal (f x) (g x)) -> Limit f x0 L -> Limit g x0 L := by
  intros R f g x0 L ext limF
  constructor
  intros eps heps
  constructor
  · exact (DPair.fst (Limit.eps_delta limF eps heps))
  · constructor
    · exact (Pair.fst (DPair.snd (Limit.eps_delta limF eps heps)))
    · exact (\\x hx0 hxd => replace (\\z => rlt (rabs (rsub z L)) eps) (ext x) (Pair.snd (DPair.snd (Limit.eps_delta limF eps heps)) x hx0 hxd))

-- distribRight: (a+b)*c = a*c + b*c (from the ring axiom)
-- Already in the record as CompleteOrderedField.distribRight

-- Key algebraic identity for derivAdd:
-- diffQuot(f+g,x0,x) = diffQuot(f,x0,x) + diffQuot(g,x0,x)
-- i.e. ((f+g)(x)-(f+g)(x0)) * (x-x0)^{-1} = (f(x)-f(x0))*(x-x0)^{-1} + (g(x)-g(x0))*(x-x0)^{-1}
-- Proof: by distribRight and subAddSub
diffQuotAddEq : {R : Real} -> (f g : Carrier R -> Carrier R) -> (x0 x : Carrier R) -> Equal (radd (diffQuot f x0 x) (diffQuot g x0 x)) (diffQuot (\\y => radd (f y) (g y)) x0 x) := by
  intros R f g x0 x
  erw (sym (CompleteOrderedField.distribRight (field R) (rsub (f x) (f x0)) (rsub (g x) (g x0)) (rinv (rsub x x0)))), (cong (\\z => rmul z (rinv (rsub x x0))) (sym (subAddSub (f x) (g x) (f x0) (g x0))))

-- THE DERIVATIVE THEOREM: (f+g)' = f' + g'
derivAdd : {R : Real} -> (f g : Carrier R -> Carrier R) -> (x0 L M : Carrier R) -> HasDerivative f x0 L -> HasDerivative g x0 M -> HasDerivative (\\x => radd (f x) (g x)) x0 (radd L M)
derivAdd {R} f g x0 L M hf hg = limitExt (\\x => radd (diffQuot f x0 x) (diffQuot g x0 x)) (diffQuot (\\y => radd (f y) (g y)) x0) x0 (radd L M) (diffQuotAddEq f g x0) (limitAdd (diffQuot f x0) (diffQuot g x0) x0 L M hf hg)

------------------------------------------------------------
-- SCALAR MULTIPLICATION OF LIMITS AND DERIVATIVES
------------------------------------------------------------

-- c*(a-b) = c*a - c*b
mulSubDistrib : {R : Real} -> (c a b : Carrier R) -> Equal (rmul c (rsub a b)) (rsub (rmul c a) (rmul c b)) := by
  intros R c a b
  erw (CompleteOrderedField.distribLeft (field R) c a (rneg b)), (mulNegRight c b)

-- Key algebraic identity for derivScalar:
-- c * diffQuot(f,x0,x) = diffQuot(c*f,x0,x)
-- i.e. c * ((f(x)-f(x0)) * inv(x-x0)) = (c*f(x) - c*f(x0)) * inv(x-x0)
-- Proof: c*(A*B) = (c*A)*B by assoc, then c*A = c*fx - c*fx0 by distribLeft
diffQuotScalarEq : {R : Real} -> (c : Carrier R) -> (f : Carrier R -> Carrier R) -> (x0 x : Carrier R) -> Equal (rmul c (diffQuot f x0 x)) (diffQuot (\\y => rmul c (f y)) x0 x) := by
  intros R c f x0 x
  erw (sym (CompleteOrderedField.mulAssoc (field R) c (rsub (f x) (f x0)) (rinv (rsub x x0)))), (cong (\\z => rmul z (rinv (rsub x x0))) (mulSubDistrib c (f x) (f x0)))

------------------------------------------------------------
-- Infrastructure: abs, ordering, and multiplication lemmas
------------------------------------------------------------

-- (a - b) + b = a
subCancel : {R : Real} -> (a b : Carrier R) -> Equal (radd (rsub a b) b) a := by
  intros R a b
  erw (CompleteOrderedField.addAssoc (field R) a (rneg b) b), (negLeft b), (CompleteOrderedField.addZeroRight (field R) a)

-- |c| > 0 when c /= 0
absPos : {R : Real} -> (c : Carrier R) -> (Equal c (rzero R) -> Void) -> rlt (rzero R) (rabs c) := by
  intros R c hne
  constructor
  · exact (absNonneg c)
  · exact (\\heq => hne (absEqZero c (sym heq)))

-- a <= b => 0 <= b - a
leToSubNonneg : {R : Real} -> (a b : Carrier R) -> rle a b -> rle (rzero R) (rsub b a) := by
  intros R a b hab
  rewrite (sym (subSelf a))
  exact (addLeRight a b (rneg a) hab)

-- 0 <= c, a <= b => c*a <= c*b
-- Proof: 0 <= b-a, so 0 <= c*(b-a) = c*b - c*a, add c*a: c*a <= c*b
mulLeLeft : {R : Real} -> (c a b : Carrier R) -> rle (rzero R) c -> rle a b -> rle (rmul c a) (rmul c b)
mulLeLeft {R} c a b hc hab = replace (\\z => rle (rmul c a) z) (subCancel (rmul c b) (rmul c a)) (replace (\\z => rle (rmul c a) (radd z (rmul c a))) (mulSubDistrib c b a) (replace (\\z => rle z (radd (rmul c (rsub b a)) (rmul c a))) (addZeroLeft (rmul c a)) (addLeRight (rzero R) (rmul c (rsub b a)) (rmul c a) (CompleteOrderedField.mulNonneg (field R) c (rsub b a) hc (leToSubNonneg a b hab)))))

-- 1 <= |c| + 1 (used for absPlusOnePos)
-- From absNonneg: 0 <= |c|. addLeLeft: le (1+0) (1+|c|). Commute to get le 1 (|c|+1).
oneLeAbsPlusOne : {R : Real} -> (c : Carrier R) -> rle (rone R) (radd (rabs c) (rone R))
oneLeAbsPlusOne {R} c = replace (\\z => rle (rone R) z) (CompleteOrderedField.addComm (field R) (rone R) (rabs c)) (replace (\\z => rle z (radd (rone R) (rabs c))) (CompleteOrderedField.addZeroRight (field R) (rone R)) (CompleteOrderedField.addLeLeft (field R) (rzero R) (rabs c) (rone R) (absNonneg c)))

-- |c| + 1 > 0
absPlusOnePos : {R : Real} -> (c : Carrier R) -> rlt (rzero R) (radd (rabs c) (rone R))
absPlusOnePos {R} c = ltLeTrans (rzero R) (rone R) (radd (rabs c) (rone R)) (zeroLtOne R) (oneLeAbsPlusOne c)

-- |c| + 1 /= 0
absPlusOneNe : {R : Real} -> (c : Carrier R) -> Equal (radd (rabs c) (rone R)) (rzero R) -> Void
absPlusOneNe {R} c heq = Pair.snd (absPlusOnePos c) (sym heq)

-- Strict: 0 < c, a < b => c*a < c*b
-- le part: from mulLeLeft. ne part: c*a = c*b => a = b (multiply both sides by inv(c) on the left)
-- a = 1*a = (inv(c)*c)*a = inv(c)*(c*a) = inv(c)*(c*b) = (inv(c)*c)*b = 1*b = b
mulLtLeftNe : {R : Real} -> (c a b : Carrier R) -> rle (rzero R) c -> (Equal c (rzero R) -> Void) -> rle a b -> Equal (rmul c a) (rmul c b) -> Equal a b := by
  intros R c a b hc hcne hab heq
  erw (sym (CompleteOrderedField.mulOneLeft (field R) a)), (cong (\\z => rmul z a) (sym (trans (CompleteOrderedField.mulComm (field R) (rinv c) c) (CompleteOrderedField.mulInvRight (field R) c hcne)))), (CompleteOrderedField.mulAssoc (field R) (rinv c) c a), (cong (\\z => rmul (rinv c) z) heq), (sym (CompleteOrderedField.mulAssoc (field R) (rinv c) c b)), (cong (\\z => rmul z b) (trans (CompleteOrderedField.mulComm (field R) (rinv c) c) (CompleteOrderedField.mulInvRight (field R) c hcne))), (CompleteOrderedField.mulOneLeft (field R) b)

mulLtLeft : {R : Real} -> (c a b : Carrier R) -> rlt (rzero R) c -> rlt a b -> rlt (rmul c a) (rmul c b) := by
  intros R c a b hc hab
  constructor
  · exact (mulLeLeft c a b (Pair.fst hc) (Pair.fst hab))
  · exact (\\heq => Pair.snd hab (mulLtLeftNe c a b (Pair.fst hc) (Pair.snd hc) (Pair.fst hab) heq))

-- a <= b, 0 <= c => a*c <= b*c (right multiplication variant)
mulLeRight : {R : Real} -> (a b c : Carrier R) -> rle a b -> rle (rzero R) c -> rle (rmul a c) (rmul b c)
mulLeRight {R} a b c hab hc = replace (\\z => rle z (rmul b c)) (CompleteOrderedField.mulComm (field R) c a) (replace (\\z => rle (rmul c a) z) (CompleteOrderedField.mulComm (field R) c b) (mulLeLeft c a b hc hab))

-- |c| <= |c| + 1
absLeAbsPlusOne : {R : Real} -> (c : Carrier R) -> rle (rabs c) (radd (rabs c) (rone R))
absLeAbsPlusOne {R} c = replace (\\z => rle z (radd (rabs c) (rone R))) (CompleteOrderedField.addZeroRight (field R) (rabs c)) (CompleteOrderedField.addLeLeft (field R) (rzero R) (rone R) (rabs c) (CompleteOrderedField.zeroLeOne (field R)))

-- M * (a * inv(M)) = a when M /= 0
mulInvCancel : {R : Real} -> (M a : Carrier R) -> (Equal M (rzero R) -> Void) -> Equal (rmul M (rmul a (rinv M))) a := by
  intros R M a hne
  erw (sym (CompleteOrderedField.mulAssoc (field R) M a (rinv M))), (CompleteOrderedField.mulComm (field R) M a), (CompleteOrderedField.mulAssoc (field R) a M (rinv M)), (CompleteOrderedField.mulInvRight (field R) M hne), (CompleteOrderedField.mulOneRight (field R) a)

-- 0 < eps, 0 < M => 0 < eps * inv(M)
-- Proof: le part from mulNonneg + invPos; ne part from eps * inv(M) = 0 => eps = 0
epsOverMPos : {R : Real} -> (eps M : Carrier R) -> rlt (rzero R) eps -> rlt (rzero R) M -> rlt (rzero R) (rmul eps (rinv M)) := by
  intros R eps M heps hM
  constructor
  · exact (CompleteOrderedField.mulNonneg (field R) eps (rinv M) (Pair.fst heps) (CompleteOrderedField.invPos (field R) M (Pair.fst hM) (Pair.snd hM)))
  · exact (\\heq => Pair.snd heps (trans heq (trans (cong (\\z => rmul z (rinv M)) (sym (mulZeroLeft (rinv M)))) (sym (CompleteOrderedField.mulAssoc (field R) (rzero R) (rinv M) (rinv M))))))

------------------------------------------------------------
-- Scalar multiplication of limits (proved)
------------------------------------------------------------

-- Helper: |c*(a-b)| <= (|c|+1) * |a-b|
-- Proof: |c*(a-b)| = |c|*|a-b| <= (|c|+1)*|a-b|
scalarAbsBound : {R : Real} -> (c a b : Carrier R) -> rle (rabs (rsub (rmul c a) (rmul c b))) (rmul (radd (rabs c) (rone R)) (rabs (rsub a b)))
scalarAbsBound {R} c a b = replace (\\z => rle (rabs z) (rmul (radd (rabs c) (rone R)) (rabs (rsub a b)))) (mulSubDistrib c a b) (replace (\\z => rle z (rmul (radd (rabs c) (rone R)) (rabs (rsub a b)))) (sym (absMul c (rsub a b))) (mulLeRight (rabs c) (radd (rabs c) (rone R)) (rabs (rsub a b)) (absLeAbsPlusOne c) (absNonneg (rsub a b))))

-- lim(c*f) = c*L for all c (including c = 0)
-- Proof: Use M = |c| + 1 > 0. Get delta from limF at eps/M.
-- Then |c*f(x) - c*L| = |c|*|f(x)-L| <= M*|f(x)-L| < M*(eps/M) = eps.
limitScalarAll : {R : Real} -> (c : Carrier R) -> (h : Carrier R -> Carrier R) -> (x0 L : Carrier R) -> Limit h x0 L -> Limit (\\x => rmul c (h x)) x0 (rmul c L) := by
  intros R c h x0 L limH
  constructor
  intros eps heps
  constructor
  · exact (DPair.fst (Limit.eps_delta limH (rmul eps (rinv (radd (rabs c) (rone R)))) (epsOverMPos eps (radd (rabs c) (rone R)) heps (absPlusOnePos c))))
  · constructor
    · exact (Pair.fst (DPair.snd (Limit.eps_delta limH (rmul eps (rinv (radd (rabs c) (rone R)))) (epsOverMPos eps (radd (rabs c) (rone R)) heps (absPlusOnePos c)))))
    · exact (\\x hx0 hxd => replace (\\z => rlt (rabs (rsub (rmul c (h x)) (rmul c L))) z) (mulInvCancel (radd (rabs c) (rone R)) eps (absPlusOneNe c)) (leLtTrans (rabs (rsub (rmul c (h x)) (rmul c L))) (rmul (radd (rabs c) (rone R)) (rabs (rsub (h x) L))) (rmul (radd (rabs c) (rone R)) (rmul eps (rinv (radd (rabs c) (rone R))))) (scalarAbsBound c (h x) L) (mulLtLeft (radd (rabs c) (rone R)) (rabs (rsub (h x) L)) (rmul eps (rinv (radd (rabs c) (rone R)))) (absPlusOnePos c) (Pair.snd (DPair.snd (Limit.eps_delta limH (rmul eps (rinv (radd (rabs c) (rone R)))) (epsOverMPos eps (radd (rabs c) (rone R)) heps (absPlusOnePos c)))) x hx0 hxd))))

-- limitScalar: special case for c /= 0 (calls limitScalarAll)
limitScalar : {R : Real} -> (c : Carrier R) -> (Equal c (rzero R) -> Void) -> (f : Carrier R -> Carrier R) -> (x0 L : Carrier R) -> Limit f x0 L -> Limit (\\x => rmul c (f x)) x0 (rmul c L)
limitScalar {R} c hcnz f x0 L limF = limitScalarAll c f x0 L limF

-- THE DERIVATIVE THEOREM: (c*f)' = c*f'
derivScalar : {R : Real} -> (c : Carrier R) -> (Equal c (rzero R) -> Void) -> (f : Carrier R -> Carrier R) -> (x0 L : Carrier R) -> HasDerivative f x0 L -> HasDerivative (\\x => rmul c (f x)) x0 (rmul c L)
derivScalar {R} c hcnz f x0 L hf = limitExt (\\x => rmul c (diffQuot f x0 x)) (diffQuot (\\y => rmul c (f y)) x0) x0 (rmul c L) (diffQuotScalarEq c f x0) (limitScalar c hcnz (diffQuot f x0) x0 L hf)

------------------------------------------------------------
-- Infrastructure for the chain rule
------------------------------------------------------------

-- a - 0 = a
subZeroRight : {R : Real} -> (a : Carrier R) -> Equal (rsub a (rzero R)) a := by
  intros R a
  erw (negZero R), (CompleteOrderedField.addZeroRight (field R) a)

------------------------------------------------------------
-- Int -> Real arithmetic homomorphisms
------------------------------------------------------------

-- Field-algebra: a - b = (1+a) - (1+b). From subAddSub + subSelf:
-- (1+a) - (1+b) = (1-1) + (a-b) = 0 + (a-b) = a-b. Helper for
-- subNatNatLemma's recursive case.
subSuccSucc : {R : Real} -> (a b : Carrier R) -> Equal (rsub a b) (rsub (radd (rone R) a) (radd (rone R) b)) := by
  intros R a b
  erw (sym (addZeroLeft (rsub a b))), (cong (\\z => radd z (rsub a b)) (sym (subSelf (rone R)))), (sym (subAddSub (rone R) a (rone R) b))

-- subNatNat homomorphism: realOfInt R (subNatNat m n) = realOfNat R m - realOfNat R n.
-- Four pattern cases mirroring subNatNat's definition. The recursive case
-- uses subSuccSucc to bridge (1+m)-(1+n) and m-n.
subNatNatLemma : (R : Real) -> (m n : Nat) -> Equal (realOfInt R (subNatNat m n)) (rsub (realOfNat R m) (realOfNat R n))
subNatNatLemma R Zero Zero = sym (subZeroRight (rzero R))
subNatNatLemma R (Succ m) Zero = sym (subZeroRight (realOfNat R (Succ m)))
subNatNatLemma R Zero (Succ n) = sym (addZeroLeft (rneg (radd (rone R) (realOfNat R n))))
subNatNatLemma R (Succ m) (Succ n) = trans (subNatNatLemma R m n) (subSuccSucc (realOfNat R m) (realOfNat R n))

-- Int -> Real addition homomorphism: 4 cases by pattern on both Ints.
--   ofNat   + ofNat   : addRealOfNat directly
--   ofNat   + negSucc : sym subNatNatLemma (rsub form matches LHS)
--   negSucc + ofNat   : addComm to flip the sign + sym subNatNatLemma
--   negSucc + negSucc : negAdd + the (1+m,1+n) shuffle
addRealOfInt : (R : Real) -> (a b : Int) -> Equal (radd (realOfInt R a) (realOfInt R b)) (realOfInt R (intAdd a b))
addRealOfInt R (IntOfNat m) (IntOfNat n) = addRealOfNat R m n
addRealOfInt R (IntOfNat m) (IntNegSucc n) = sym (subNatNatLemma R m (Succ n))
addRealOfInt R (IntNegSucc m) (IntOfNat n) = trans (CompleteOrderedField.addComm (field R) (rneg (radd (rone R) (realOfNat R m))) (realOfNat R n)) (sym (subNatNatLemma R n (Succ m)))
addRealOfInt R (IntNegSucc m) (IntNegSucc n) = trans (sym (negAdd (radd (rone R) (realOfNat R m)) (radd (rone R) (realOfNat R n)))) (cong rneg (addOnePlusOneShuffle R m n))

-- Int subtraction homomorphism. Reduces to addRealOfInt via intSub a c := intAdd a (intNeg c).
subRealOfInt : (R : Real) -> (a c : Int) -> Equal (rsub (realOfInt R a) (realOfInt R c)) (realOfInt R (intSub a c))
subRealOfInt R a c = trans (cong (\\z => radd (realOfInt R a) z) (negRealOfInt R c)) (addRealOfInt R a (intNeg c))

-- Helper: rneg (realOfNat R k) = realOfInt R (negOfNat k). Two cases
-- by pattern on k. The Zero case needs negZero; the Succ case is rfl.
negOfNatLemma : (R : Real) -> (k : Nat) -> Equal (rneg (realOfNat R k)) (realOfInt R (negOfNat k))
negOfNatLemma R Zero = negZero R
negOfNatLemma R (Succ p) = refl

-- Int -> Real multiplication homomorphism: 4 cases by pattern on both Ints.
--   ofNat   * ofNat   : mulRealOfNat directly
--   ofNat   * negSucc : mulNegRight + mulRealOfNat + negOfNatLemma
--   negSucc * ofNat   : mulNegLeft  + mulRealOfNat + negOfNatLemma
--   negSucc * negSucc : negMulNeg (the negs cancel) + mulRealOfNat
mulRealOfInt : (R : Real) -> (a b : Int) -> Equal (rmul (realOfInt R a) (realOfInt R b)) (realOfInt R (intMul a b))
mulRealOfInt R (IntOfNat m) (IntOfNat n) = mulRealOfNat R m n
mulRealOfInt R (IntOfNat m) (IntNegSucc n) = trans (mulNegRight (realOfNat R m) (radd (rone R) (realOfNat R n))) (trans (cong rneg (mulRealOfNat R m (Succ n))) (negOfNatLemma R (mult m (Succ n))))
mulRealOfInt R (IntNegSucc m) (IntOfNat n) = trans (mulNegLeft (radd (rone R) (realOfNat R m)) (realOfNat R n)) (trans (cong rneg (mulRealOfNat R (Succ m) n)) (negOfNatLemma R (mult (Succ m) n)))
mulRealOfInt R (IntNegSucc m) (IntNegSucc n) = trans (negMulNeg (radd (rone R) (realOfNat R m)) (radd (rone R) (realOfNat R n))) (mulRealOfNat R (Succ m) (Succ n))

-- Nat right-identities, needed for mulRealOfRat denominator manipulation.
plusZeroRight : (n : Nat) -> Equal (plus n Zero) n
plusZeroRight Zero = refl
plusZeroRight (Succ k) = cong Succ (plusZeroRight k)

multOneRight : (n : Nat) -> Equal (mult n (Succ Zero)) n
multOneRight Zero = refl
multOneRight (Succ k) = cong Succ (multOneRight k)

-- a * 1 = a in Int (right identity for intMul).
intMulOneRight : (a : Int) -> Equal (intMul a (IntOfNat (Succ Zero))) a
intMulOneRight (IntOfNat m) = cong IntOfNat (multOneRight m)
intMulOneRight (IntNegSucc m) = cong IntNegSucc (multOneRight m)

-- Rat -> Real multiplication homomorphism. Proved by case-split on each
-- denominator (Succ Zero vs Succ (Succ _)) so realOfRat fires its correct
-- clause on each side, then bridged via mulDivAssoc / divMulRight / mulDivDiv.
-- Tagged @simp so clicking \`a * b\` where both operands are literal coercions
-- offers a one-click reduction via @ratMul (the kernel BigInt fast path).
@syntax @simp
mulRealOfRat : (R : Real) -> (a b : Rat) -> Equal (rmul (realOfRat R a) (realOfRat R b)) (realOfRat R (ratMult a b))
mulRealOfRat R (MkRat a (Succ Zero) pa) (MkRat c (Succ Zero) pc) = mulRealOfInt R a c
mulRealOfRat R (MkRat a (Succ Zero) pa) (MkRat c (Succ (Succ d1)) pd) = trans (mulDivAssoc (realOfInt R a) (realOfInt R c) (realOfNat R (Succ (Succ d1)))) (trans (cong (\\z => rdiv z (realOfNat R (Succ (Succ d1)))) (mulRealOfInt R a c)) (cong (\\z => rdiv (realOfInt R (intMul a c)) (realOfNat R (Succ (Succ z)))) (sym (plusZeroRight d1))))
mulRealOfRat R (MkRat a (Succ (Succ b1)) pb) (MkRat c (Succ Zero) pc) = trans (divMulRight (realOfInt R a) (realOfNat R (Succ (Succ b1))) (realOfInt R c)) (trans (cong (\\z => rdiv z (realOfNat R (Succ (Succ b1)))) (mulRealOfInt R a c)) (cong (\\z => rdiv (realOfInt R (intMul a c)) (realOfNat R (Succ (Succ z)))) (sym (multOneRight b1))))
mulRealOfRat R (MkRat a (Succ (Succ b1)) pb) (MkRat c (Succ (Succ d1)) pd) = trans (mulDivDiv (realOfInt R a) (realOfNat R (Succ (Succ b1))) (realOfInt R c) (realOfNat R (Succ (Succ d1))) (realOfNatSuccNeZero R (Succ b1)) (realOfNatSuccNeZero R (Succ d1))) (trans (cong (\\z => rdiv z (rmul (realOfNat R (Succ (Succ b1))) (realOfNat R (Succ (Succ d1))))) (mulRealOfInt R a c)) (cong (\\z => rdiv (realOfInt R (intMul a c)) z) (mulRealOfNat R (Succ (Succ b1)) (Succ (Succ d1)))))

-- Rat -> Real addition homomorphism. Same 4-case structure as mulRealOfRat:
-- one case per (denominator-type-1, denominator-type-2) combination. The
-- general case (Succ(Succ _), Succ(Succ _)) uses addDivDiv (cross-mult), the
-- mixed cases use addCommonDenom / addCommonDenomLeft, and (1,1) reduces to
-- addRealOfInt directly.
-- Tagged @simp so \`1 + (-1)\`, \`2 + (-1)\`, etc. reduce in one click via
-- the kernel's @ratAdd BigInt fast path (no axiom chasing needed).
@syntax @simp
addRealOfRat : (R : Real) -> (a b : Rat) -> Equal (radd (realOfRat R a) (realOfRat R b)) (realOfRat R (ratPlus a b))
addRealOfRat R (MkRat a (Succ Zero) pa) (MkRat c (Succ Zero) pc) = trans (addRealOfInt R a c) (cong (realOfInt R) (trans (cong (\\z => intAdd z c) (sym (intMulOneRight a))) (cong (\\z => intAdd (intMul a (IntOfNat (Succ Zero))) z) (sym (intMulOneRight c)))))
addRealOfRat R (MkRat a (Succ Zero) pa) (MkRat c (Succ (Succ d1)) pd) = trans (addCommonDenom (realOfInt R a) (realOfInt R c) (realOfNat R (Succ (Succ d1))) (realOfNatSuccNeZero R (Succ d1))) (trans (cong (\\z => rdiv z (realOfNat R (Succ (Succ d1)))) (trans (cong (\\z => radd z (realOfInt R c)) (mulRealOfInt R a (IntOfNat (Succ (Succ d1))))) (trans (addRealOfInt R (intMul a (IntOfNat (Succ (Succ d1)))) c) (cong (\\z => realOfInt R (intAdd (intMul a (IntOfNat (Succ (Succ d1)))) z)) (sym (intMulOneRight c)))))) (cong (\\z => rdiv (realOfInt R (intAdd (intMul a (IntOfNat (Succ (Succ d1)))) (intMul c (IntOfNat (Succ Zero))))) (realOfNat R (Succ (Succ z)))) (sym (plusZeroRight d1))))
addRealOfRat R (MkRat a (Succ (Succ b1)) pb) (MkRat c (Succ Zero) pc) = trans (addCommonDenomLeft (realOfInt R a) (realOfInt R c) (realOfNat R (Succ (Succ b1))) (realOfNatSuccNeZero R (Succ b1))) (trans (cong (\\z => rdiv z (realOfNat R (Succ (Succ b1)))) (trans (cong (\\z => radd (realOfInt R a) z) (mulRealOfInt R c (IntOfNat (Succ (Succ b1))))) (trans (addRealOfInt R a (intMul c (IntOfNat (Succ (Succ b1))))) (cong (\\z => realOfInt R (intAdd z (intMul c (IntOfNat (Succ (Succ b1)))))) (sym (intMulOneRight a)))))) (cong (\\z => rdiv (realOfInt R (intAdd (intMul a (IntOfNat (Succ Zero))) (intMul c (IntOfNat (Succ (Succ b1)))))) (realOfNat R (Succ (Succ z)))) (sym (multOneRight b1))))
addRealOfRat R (MkRat a (Succ (Succ b1)) pb) (MkRat c (Succ (Succ d1)) pd) = trans (addDivDiv (realOfInt R a) (realOfNat R (Succ (Succ b1))) (realOfInt R c) (realOfNat R (Succ (Succ d1))) (realOfNatSuccNeZero R (Succ b1)) (realOfNatSuccNeZero R (Succ d1))) (trans (cong (\\z => rdiv z (rmul (realOfNat R (Succ (Succ b1))) (realOfNat R (Succ (Succ d1))))) (trans (cong (\\z => radd z (rmul (realOfInt R c) (realOfNat R (Succ (Succ b1))))) (mulRealOfInt R a (IntOfNat (Succ (Succ d1))))) (trans (cong (\\z => radd (realOfInt R (intMul a (IntOfNat (Succ (Succ d1))))) z) (mulRealOfInt R c (IntOfNat (Succ (Succ b1))))) (addRealOfInt R (intMul a (IntOfNat (Succ (Succ d1)))) (intMul c (IntOfNat (Succ (Succ b1)))))))) (cong (\\z => rdiv (realOfInt R (intAdd (intMul a (IntOfNat (Succ (Succ d1)))) (intMul c (IntOfNat (Succ (Succ b1)))))) z) (mulRealOfNat R (Succ (Succ b1)) (Succ (Succ d1)))))

-- Rat -> Real subtraction homomorphism. Same 4-case structure as addRealOfRat,
-- with subCommonDenom / subCommonDenomLeft / subDivDiv on the Carrier side and
-- subRealOfInt collapsing the numerator.
-- Tagged @simp so \`185.6 - 85.7\`, etc. reduce in one click via @ratSub.
@syntax @simp
subRealOfRat : (R : Real) -> (a b : Rat) -> Equal (rsub (realOfRat R a) (realOfRat R b)) (realOfRat R (ratSub a b))
subRealOfRat R (MkRat a (Succ Zero) pa) (MkRat c (Succ Zero) pc) = trans (subRealOfInt R a c) (cong (realOfInt R) (trans (cong (\\z => intSub z c) (sym (intMulOneRight a))) (cong (\\z => intSub (intMul a (IntOfNat (Succ Zero))) z) (sym (intMulOneRight c)))))
subRealOfRat R (MkRat a (Succ Zero) pa) (MkRat c (Succ (Succ d1)) pd) = trans (subCommonDenom (realOfInt R a) (realOfInt R c) (realOfNat R (Succ (Succ d1))) (realOfNatSuccNeZero R (Succ d1))) (trans (cong (\\z => rdiv z (realOfNat R (Succ (Succ d1)))) (trans (cong (\\z => rsub z (realOfInt R c)) (mulRealOfInt R a (IntOfNat (Succ (Succ d1))))) (trans (subRealOfInt R (intMul a (IntOfNat (Succ (Succ d1)))) c) (cong (\\z => realOfInt R (intSub (intMul a (IntOfNat (Succ (Succ d1)))) z)) (sym (intMulOneRight c)))))) (cong (\\z => rdiv (realOfInt R (intSub (intMul a (IntOfNat (Succ (Succ d1)))) (intMul c (IntOfNat (Succ Zero))))) (realOfNat R (Succ (Succ z)))) (sym (plusZeroRight d1))))
subRealOfRat R (MkRat a (Succ (Succ b1)) pb) (MkRat c (Succ Zero) pc) = trans (subCommonDenomLeft (realOfInt R a) (realOfInt R c) (realOfNat R (Succ (Succ b1))) (realOfNatSuccNeZero R (Succ b1))) (trans (cong (\\z => rdiv z (realOfNat R (Succ (Succ b1)))) (trans (cong (\\z => rsub (realOfInt R a) z) (mulRealOfInt R c (IntOfNat (Succ (Succ b1))))) (trans (subRealOfInt R a (intMul c (IntOfNat (Succ (Succ b1))))) (cong (\\z => realOfInt R (intSub z (intMul c (IntOfNat (Succ (Succ b1)))))) (sym (intMulOneRight a)))))) (cong (\\z => rdiv (realOfInt R (intSub (intMul a (IntOfNat (Succ Zero))) (intMul c (IntOfNat (Succ (Succ b1)))))) (realOfNat R (Succ (Succ z)))) (sym (multOneRight b1))))
subRealOfRat R (MkRat a (Succ (Succ b1)) pb) (MkRat c (Succ (Succ d1)) pd) = trans (subDivDiv (realOfInt R a) (realOfNat R (Succ (Succ b1))) (realOfInt R c) (realOfNat R (Succ (Succ d1))) (realOfNatSuccNeZero R (Succ b1)) (realOfNatSuccNeZero R (Succ d1))) (trans (cong (\\z => rdiv z (rmul (realOfNat R (Succ (Succ b1))) (realOfNat R (Succ (Succ d1))))) (trans (cong (\\z => rsub z (rmul (realOfInt R c) (realOfNat R (Succ (Succ b1))))) (mulRealOfInt R a (IntOfNat (Succ (Succ d1))))) (trans (cong (\\z => rsub (realOfInt R (intMul a (IntOfNat (Succ (Succ d1))))) z) (mulRealOfInt R c (IntOfNat (Succ (Succ b1))))) (subRealOfInt R (intMul a (IntOfNat (Succ (Succ d1)))) (intMul c (IntOfNat (Succ (Succ b1)))))))) (cong (\\z => rdiv (realOfInt R (intSub (intMul a (IntOfNat (Succ (Succ d1)))) (intMul c (IntOfNat (Succ (Succ b1)))))) z) (mulRealOfNat R (Succ (Succ b1)) (Succ (Succ d1)))))

-- |a * b| = |a| * |b| (convenience alias)
absOfMul : {R : Real} -> (a b : Carrier R) -> Equal (rabs (rmul a b)) (rmul (rabs a) (rabs b))
absOfMul {R} a b = absMul a b

-- |0| = 0 (convenience alias)
absOfZero : (R : Real) -> Equal (rabs (rzero R)) (rzero R)
absOfZero R = absZero R

-- 0 * a = 0 * b (trivially, both are 0)
-- Useful to avoid re-proving for specific instantiations
mulZeroBoth : {R : Real} -> (a b : Carrier R) -> Equal (rmul (rzero R) a) (rmul (rzero R) b)
mulZeroBoth {R} a b = trans (mulZeroLeft a) (sym (mulZeroLeft b))

-- Weaken rlt to rle
ltToLe : {R : Real} -> (a b : Carrier R) -> rlt a b -> rle a b
ltToLe {R} a b h = Pair.fst h

-- |a| < b implies |a| ≤ b (extract le from lt)
absLtToLe : {R : Real} -> (a b : Carrier R) -> rlt (rabs a) b -> rle (rabs a) b
absLtToLe {R} a b h = Pair.fst h

-- (a - c) + (c - b) = a - b
-- Proof: (a+(-c)) + (c+(-b)) = (a+c) + ((-c)+(-b)) by fourTermRearrange... no
-- Simpler: use subCancel on the inner c
subSplit : {R : Real} -> (a b c : Carrier R) -> Equal (radd (rsub a c) (rsub c b)) (rsub a b) := by
  intros R a b c
  erw (CompleteOrderedField.addAssoc (field R) a (rneg c) (rsub c b)), (cong (\\z => radd a z) (trans (sym (CompleteOrderedField.addAssoc (field R) (rneg c) c (rneg b))) (trans (cong (\\z => radd z (rneg b)) (negLeft c)) (addZeroLeft (rneg b)))))

-- Triangle inequality for subtraction: |a - b| ≤ |a - c| + |c - b|
-- Proof: a - b = (a - c) + (c - b), then apply absTriangle
subTriangle : {R : Real} -> (a b c : Carrier R) -> rle (rabs (rsub a b)) (radd (rabs (rsub a c)) (rabs (rsub c b)))
subTriangle {R} a b c = replace (\\z => rle (rabs z) (radd (rabs (rsub a c)) (rabs (rsub c b)))) (subSplit a b c) (absTriangle (rsub a c) (rsub c b))

-- (a - b) * c = a*c - b*c — right distributivity for subtraction
mulSubDistribRight : {R : Real} -> (a b c : Carrier R) -> Equal (rmul (rsub a b) c) (rsub (rmul a c) (rmul b c)) := by
  intros R a b c
  erw (CompleteOrderedField.distribRight (field R) a (rneg b) c), (mulNegLeft b c)

-- a * (inv(a) * b) = b when a /= 0 (variant of mulInvCancel)
mulInvLeftCancel : {R : Real} -> (a b : Carrier R) -> (Equal a (rzero R) -> Void) -> Equal (rmul a (rmul (rinv a) b)) b := by
  intros R a b hne
  erw (sym (CompleteOrderedField.mulAssoc (field R) a (rinv a) b)), (CompleteOrderedField.mulInvRight (field R) a hne), (CompleteOrderedField.mulOneLeft (field R) b)

-- (a*inv(b) - c) * b = a - c*b when b /= 0
-- Proof: distribRight gives (a*inv(b))*b - c*b. Then a*inv(b)*b = a*(inv(b)*b) = a*1 = a.
diffQuotSubMulEq : {R : Real} -> (a b c : Carrier R) -> (Equal b (rzero R) -> Void) -> Equal (rmul (rsub (rmul a (rinv b)) c) b) (rsub a (rmul c b)) := by
  intros R a b c hne
  erw (mulSubDistribRight (rmul a (rinv b)) c b), (cong (\\z => rsub z (rmul c b)) (trans (CompleteOrderedField.mulAssoc (field R) a (rinv b) b) (trans (cong (\\z => rmul a z) (trans (CompleteOrderedField.mulComm (field R) (rinv b) b) (CompleteOrderedField.mulInvRight (field R) b hne))) (CompleteOrderedField.mulOneRight (field R) a))))

eqOrNeZeroLeft : {R : Real} -> (a : Carrier R) -> Equal (rzero R) (rabs a) -> Equal a (rzero R)
eqOrNeZeroLeft {R} a h = absEqZero a (sym h)

eqOrNeZeroRight : {R : Real} -> (a : Carrier R) -> (Equal (rzero R) (rabs a) -> Void) -> Equal a (rzero R) -> Void
eqOrNeZeroRight {R} a hne heq = hne (sym (trans (cong (\\z => rabs z) heq) (absOfZero R)))

eqOrNeZero : {R : Real} -> (a : Carrier R) -> Either (Equal a (rzero R)) (Equal a (rzero R) -> Void)
eqOrNeZero {R} a = eitherElim (\\h => Left (eqOrNeZeroLeft a h)) (\\h => Right (eqOrNeZeroRight a (Pair.snd h))) (CompleteOrderedField.leToEqOrLt (field R) (rzero R) (rabs a) (absNonneg a))

-- Unpunctured differentiability bound (derivBound):
-- If g is differentiable at y0 with derivative Lg, then for any eta > 0,
-- exists delta_g > 0 such that for ALL y with |y - y0| < delta_g:
--   |g(y) - g(y0) - Lg*(y - y0)| <= eta * |y - y0|
-- This holds INCLUDING y = y0 (where both sides are 0).
--
-- Proof: Get delta_g from g's derivative at eta. For each y with |y-y0| < delta_g:
--   Case y-y0 = 0: LHS = |g(y0)-g(y0)-Lg*0| = 0. RHS = eta*0 = 0. Done by leRefl.
--   Case y-y0 /= 0: 0 < |y-y0|, so derivative gives |diffQuot(g)-Lg| < eta.
--     LHS = |(diffQuot-Lg)*(y-y0)| = |diffQuot-Lg|*|y-y0| <= eta*|y-y0| = RHS.

-- When d = 0: |g(y0)-g(y0)-Lg*0| = 0 and eta*|0| = 0, so 0 <= 0
-- We use cong to rewrite both sides to 0, then leRefl.
derivBoundZero : (R : Real) -> (g : Carrier R -> Carrier R) -> (y0 Lg eta : Carrier R) -> rle (rabs (rsub (rsub (g y0) (g y0)) (rmul Lg (rzero R)))) (rmul eta (rabs (rzero R)))
derivBoundZero R g y0 Lg eta = replace (\\z => rle z (rmul eta (rabs (rzero R)))) (sym (trans (cong (\\z => rabs (rsub (rsub (g y0) (g y0)) z)) (mulZeroRight Lg)) (trans (cong (\\z => rabs z) (subZeroRight (rsub (g y0) (g y0)))) (trans (cong (\\z => rabs z) (subSelf (g y0))) (absOfZero R))))) (replace (\\z => rle (rzero R) z) (sym (trans (cong (\\z => rmul eta z) (absOfZero R)) (mulZeroRight eta))) (CompleteOrderedField.leRefl (field R) (rzero R)))

-- a - b = 0 implies a = b
-- Proof: a = a - b + b = 0 + b = b
subEqZeroToEq : {R : Real} -> (a b : Carrier R) -> Equal (rsub a b) (rzero R) -> Equal a b := by
  intros R a b h
  erw (sym (subCancel a b)), h, (addZeroLeft b)

-- When d = y - y0 /= 0: 0 < |d|, so derivative gives |diffQuot(g)-Lg| < eta.
-- Then |g(y)-g(y0)-Lg*(y-y0)| = |(diffQuot-Lg)*(y-y0)| = |diffQuot-Lg|*|y-y0| <= eta*|y-y0|.
-- This needs: diffQuotSubMulEq, absMul, mulLeRight
derivBoundNonzero : (R : Real) -> (g : Carrier R -> Carrier R) -> (y0 Lg eta : Carrier R) -> (y : Carrier R) -> (Equal (rsub y y0) (rzero R) -> Void) -> rle (rabs (rsub (diffQuot g y0 y) Lg)) eta -> rle (rabs (rsub (rsub (g y) (g y0)) (rmul Lg (rsub y y0)))) (rmul eta (rabs (rsub y y0)))
derivBoundNonzero R g y0 Lg eta y hne hle = replace (\\z => rle (rabs z) (rmul eta (rabs (rsub y y0)))) (diffQuotSubMulEq (rsub (g y) (g y0)) (rsub y y0) Lg hne) (replace (\\z => rle z (rmul eta (rabs (rsub y y0)))) (sym (absOfMul (rsub (diffQuot g y0 y) Lg) (rsub y y0))) (mulLeRight (rabs (rsub (diffQuot g y0 y) Lg)) eta (rabs (rsub y y0)) hle (absNonneg (rsub y y0))))

-- Type for derivBound witness: delta > 0, and the unpunctured bound holds
DerivBoundWitness : (R : Real) -> (g : Carrier R -> Carrier R) -> (y0 Lg eta : Carrier R) -> Carrier R -> Type
DerivBoundWitness R g y0 Lg eta dg = Pair (rlt (rzero R) dg) ((y : Carrier R) -> rlt (rabs (rsub y y0)) dg -> rle (rabs (rsub (rsub (g y) (g y0)) (rmul Lg (rsub y y0)))) (rmul eta (rabs (rsub y y0))))

-- Full derivBound: case split on y-y0 = 0 vs y-y0 /= 0
derivBound : {R : Real} -> (g : Carrier R -> Carrier R) -> (y0 Lg : Carrier R) -> HasDerivative g y0 Lg -> (eta : Carrier R) -> rlt (rzero R) eta -> (delta : Carrier R ** DerivBoundWitness R g y0 Lg eta delta) := by
  intros R g y0 Lg hg eta heta
  constructor
  · exact (DPair.fst (Limit.eps_delta hg eta heta))
  · constructor
    · exact (Pair.fst (DPair.snd (Limit.eps_delta hg eta heta)))
    · exact (\\y hyd => eitherElim
        (\\heq => replace (\\z => rle (rabs (rsub (rsub (g z) (g y0)) (rmul Lg (rsub z y0)))) (rmul eta (rabs (rsub z y0)))) (sym (subEqZeroToEq y y0 heq)) (replace (\\z => rle (rabs (rsub (rsub (g y0) (g y0)) (rmul Lg z))) (rmul eta (rabs z))) (sym (subSelf y0)) (derivBoundZero R g y0 Lg eta)))
        (\\hne => derivBoundNonzero R g y0 Lg eta y hne (ltToLe (rabs (rsub (diffQuot g y0 y) Lg)) eta (Pair.snd (DPair.snd (Limit.eps_delta hg eta heta)) y (absPos (rsub y y0) hne) hyd)))
        (eqOrNeZero (rsub y y0)))

-- a < b => a + c < b + c
addLtRight : {R : Real} -> (a b c : Carrier R) -> rlt a b -> rlt (radd a c) (radd b c) := by
  intros R a b c h
  constructor
  · exact (addLeRight a b c (Pair.fst h))
  · exact (\\heq => Pair.snd h (addCancelRight a b c heq))

-- |a| <= |a - b| + |b| (variant of triangle inequality)
absSubAdd : {R : Real} -> (a b : Carrier R) -> rle (rabs a) (radd (rabs (rsub a b)) (rabs b))
absSubAdd {R} a b = replace (\\z => rle (rabs z) (radd (rabs (rsub a b)) (rabs b))) (subCancel a b) (absTriangle (rsub a b) b)

-- DiffQuot is bounded near x0 by |Lf| + 1
-- Returns: delta, delta > 0, and for 0 < |x-x0| < delta: |diffQuot(f)| <= |Lf|+1
DiffQuotBoundWitness : (R : Real) -> (f : Carrier R -> Carrier R) -> (x0 Lf : Carrier R) -> Carrier R -> Type
DiffQuotBoundWitness R f x0 Lf df = Pair (rlt (rzero R) df) ((x : Carrier R) -> rlt (rzero R) (rabs (rsub x x0)) -> rlt (rabs (rsub x x0)) df -> rlt (rabs (diffQuot f x0 x)) (radd (rabs Lf) (rone R)))

diffQuotBounded : {R : Real} -> (f : Carrier R -> Carrier R) -> (x0 Lf : Carrier R) -> HasDerivative f x0 Lf -> (delta : Carrier R ** DiffQuotBoundWitness R f x0 Lf delta) := by
  intros R f x0 Lf hf
  constructor
  · exact (DPair.fst (Limit.eps_delta hf (rone R) (zeroLtOne R)))
  · constructor
    · exact (Pair.fst (DPair.snd (Limit.eps_delta hf (rone R) (zeroLtOne R))))
    · exact (\\x hx0 hxd => leLtTrans (rabs (diffQuot f x0 x))
        (radd (rabs (rsub (diffQuot f x0 x) Lf)) (rabs Lf))
        (radd (rabs Lf) (rone R)) (absSubAdd (diffQuot f x0 x) Lf)
        (replace (\\z => rlt (radd (rabs (rsub (diffQuot f x0 x) Lf)) (rabs Lf)) z)
          (CompleteOrderedField.addComm (field R) (rone R) (rabs Lf))
          (addLtRight (rabs (rsub (diffQuot f x0 x) Lf)) (rone R) (rabs Lf)
            (Pair.snd (DPair.snd (Limit.eps_delta hf (rone R) (zeroLtOne R))) x hx0 hxd))))

-- diffQuot(f,x0,x) * (x-x0) = f(x)-f(x0) when x-x0 /= 0
-- Proof: (a*inv(b))*b = a*(inv(b)*b) = a*1 = a
diffQuotTimesH : {R : Real} -> (f : Carrier R -> Carrier R) -> (x0 x : Carrier R) -> (Equal (rsub x x0) (rzero R) -> Void) -> Equal (rmul (diffQuot f x0 x) (rsub x x0)) (rsub (f x) (f x0)) := by
  intros R f x0 x hne
  erw (CompleteOrderedField.mulAssoc (field R) (rsub (f x) (f x0)) (rinv (rsub x x0)) (rsub x x0)), (cong (\\z => rmul (rsub (f x) (f x0)) z) (trans (CompleteOrderedField.mulComm (field R) (rinv (rsub x x0)) (rsub x x0)) (CompleteOrderedField.mulInvRight (field R) (rsub x x0) hne))), (CompleteOrderedField.mulOneRight (field R) (rsub (f x) (f x0)))

-- |diffQuot(f,x0,x)| * |x-x0| = |f(x)-f(x0)| when x-x0 /= 0
absDiffQuotTimesH : {R : Real} -> (f : Carrier R -> Carrier R) -> (x0 x : Carrier R) -> (Equal (rsub x x0) (rzero R) -> Void) -> Equal (rmul (rabs (diffQuot f x0 x)) (rabs (rsub x x0))) (rabs (rsub (f x) (f x0)))
absDiffQuotTimesH {R} f x0 x hne = trans (sym (absOfMul (diffQuot f x0 x) (rsub x x0))) (cong (\\z => rabs z) (diffQuotTimesH f x0 x hne))

-- Differentiability implies continuity (limit sense):
-- HasDerivative f x0 Lf implies: for any target > 0, exists delta > 0,
-- 0 < |x-x0| < delta => |f(x)-f(x0)| < target.
-- Proof: |f(x)-f(x0)| = |diffQuot(f)|*|x-x0| <= (|Lf|+1)*|x-x0| < (|Lf|+1) * target/(|Lf|+1) = target
ContinuousWitness : {R : Real} -> (f : Carrier R -> Carrier R) -> (x0 target : Carrier R) -> Carrier R -> Type
ContinuousWitness {R} f x0 target dc = Pair (rlt (rzero R) dc) ((x : Carrier R) -> rlt (rzero R) (rabs (rsub x x0)) -> rlt (rabs (rsub x x0)) dc -> rlt (rabs (rsub (f x) (f x0))) target)

-- Helper: |a| * |b| < c * |b| when |a| < c and 0 < |b|  (using mulLtLeft on absNonneg)
-- Actually we need: |a| <= M, |b| < eps => |a|*|b| < M*eps (when M > 0)
-- Use: |a|*|b| <= M*|b| by mulLeLeft, and M*|b| < M*eps by mulLtLeft
absMulBound : {R : Real} -> (a b M eps : Carrier R) -> rle (rabs a) M -> rlt (rabs b) eps -> rlt (rzero R) M -> rlt (rmul (rabs a) (rabs b)) (rmul M eps)
absMulBound {R} a b M eps hle hlt hM = leLtTrans (rmul (rabs a) (rabs b)) (rmul M (rabs b)) (rmul M eps) (mulLeRight (rabs a) M (rabs b) hle (absNonneg b)) (mulLtLeft M (rabs b) eps hM hlt)

-- Core bound lemma: Given |diffQuot(f)| < M and |x-x0| < eps where M*eps = target,
-- prove |f(x)-f(x0)| < target. This is stated with simple Pi types to avoid
-- constraint solver issues with deeply nested ContinuousWitness types.
continuityBound : {R : Real} -> (f : Carrier R -> Carrier R) -> (x0 x Lf target : Carrier R) -> rle (rabs (diffQuot f x0 x)) (radd (rabs Lf) (rone R)) -> rlt (rabs (rsub x x0)) (rmul target (rinv (radd (rabs Lf) (rone R)))) -> (Equal (rsub x x0) (rzero R) -> Void) -> rlt (rabs (rsub (f x) (f x0))) target
continuityBound {R} f x0 x lf target hdq hdelta hne = replace (\\z => rlt z target) (absDiffQuotTimesH f x0 x hne) (replace (\\z => rlt (rmul (rabs (diffQuot f x0 x)) (rabs (rsub x x0))) z) (mulInvCancel (radd (rabs lf) (rone R)) target (absPlusOneNe lf)) (absMulBound (diffQuot f x0 x) (rsub x x0) (radd (rabs lf) (rone R)) (rmul target (rinv (radd (rabs lf) (rone R)))) hdq hdelta (absPlusOnePos lf)))

-- Differentiability implies continuity
continuousFromDeriv : {R : Real} -> (f : Carrier R -> Carrier R) -> (x0 Lf : Carrier R) -> HasDerivative f x0 Lf -> (target : Carrier R) -> rlt (rzero R) target -> (dc : Carrier R ** ContinuousWitness f x0 target dc) := by
  intros R f x0 Lf hf target htarget
  have dqb := diffQuotBounded f x0 Lf hf
  cases (CompleteOrderedField.leTotal (field R) (DPair.fst dqb) (rmul target (rinv (radd (rabs Lf) (rone R))))) with
  | Left hle => exact (MkDPair (DPair.fst dqb) (MkPair (Pair.fst (DPair.snd dqb)) (\\x hx0 hxd => continuityBound f x0 x Lf target (ltToLe (rabs (diffQuot f x0 x)) (radd (rabs Lf) (rone R)) (Pair.snd (DPair.snd dqb) x hx0 hxd)) (ltLeTrans (rabs (rsub x x0)) (DPair.fst dqb) (rmul target (rinv (radd (rabs Lf) (rone R)))) hxd hle) (eqOrNeZeroRight (rsub x x0) (Pair.snd hx0)))))
  | Right hle => exact (MkDPair (rmul target (rinv (radd (rabs Lf) (rone R)))) (MkPair (epsOverMPos target (radd (rabs Lf) (rone R)) htarget (absPlusOnePos Lf)) (\\x hx0 hxd => continuityBound f x0 x Lf target (ltToLe (rabs (diffQuot f x0 x)) (radd (rabs Lf) (rone R)) (Pair.snd (DPair.snd dqb) x hx0 (ltLeTrans (rabs (rsub x x0)) (rmul target (rinv (radd (rabs Lf) (rone R)))) (DPair.fst dqb) hxd hle))) hxd (eqOrNeZeroRight (rsub x x0) (Pair.snd hx0)))))

------------------------------------------------------------
-- THE CHAIN RULE: (g . f)'(x0) = g'(f(x0)) . f'(x0)
------------------------------------------------------------

-- The "error term" in the chain rule decomposition:
-- A(x) = (g(f(x)) - g(f(x0)) - g'*(f(x) - f(x0))) * inv(x - x0)
-- This measures how well g's linear approximation at f(x0) predicts g(f(x)),
-- normalized by (x - x0). Crucially, A(x) = 0 when f(x) = f(x0) (no case split needed).
chainTermA : {R : Real} -> (g f : Carrier R -> Carrier R) -> (x0 Lg : Carrier R) -> Carrier R -> Carrier R
chainTermA {R} g f x0 Lg x = rmul (rsub (rsub (g (f x)) (g (f x0))) (rmul Lg (rsub (f x) (f x0)))) (rinv (rsub x x0))

-- Core algebraic identity for the chain rule:
-- A(x) + g' * diffQuot(f, x0, x) = diffQuot(g.f, x0, x)
--
-- Proof: Let D = g(f(x))-g(f(x0)), B = f(x)-f(x0), C = inv(x-x0).
-- A(x) + g'*diffQuot(f)
--   = (D - g'*B)*C + g'*(B*C)         [definitions]
--   = (D - g'*B)*C + (g'*B)*C         [associativity]
--   = ((D - g'*B) + g'*B)*C           [distribRight]
--   = D*C                              [cancellation: (a-b)+b = a]
--   = diffQuot(g.f, x0, x)            [definition]
chainAlgId : {R : Real} -> (g f : Carrier R -> Carrier R) -> (x0 Lg : Carrier R) -> (x : Carrier R) -> Equal (radd (chainTermA g f x0 Lg x) (rmul Lg (diffQuot f x0 x))) (diffQuot (\\y => g (f y)) x0 x) := by
  intros R g f x0 Lg x
  erw (cong (\\z => radd (chainTermA g f x0 Lg x) z) (sym (CompleteOrderedField.mulAssoc (field R) Lg (rsub (f x) (f x0)) (rinv (rsub x x0))))), (sym (CompleteOrderedField.distribRight (field R) (rsub (rsub (g (f x)) (g (f x0))) (rmul Lg (rsub (f x) (f x0)))) (rmul Lg (rsub (f x) (f x0))) (rinv (rsub x x0)))), (cong (\\z => rmul z (rinv (rsub x x0))) (subCancel (rsub (g (f x)) (g (f x0))) (rmul Lg (rsub (f x) (f x0)))))

-- Core bound for chainTermALimit:
-- |num| ≤ η*|f(x)-f(x0)| and |diffQuot(f)| < M and η*M = eps => |num*inv(x-x0)| < eps
-- Steps: |num*inv(h)| = |num|*|inv(h)| ≤ η*|Δf|*|inv(h)| = η*|diffQuot(f)| < η*M = eps
-- Step: (eta*|a|)*|b| = eta*(|a|*|b|) by mulAssoc
-- Step: eta*(|a|*|b|) = eta*|a*b| by cong+absMul
-- Combined: (eta*|a|)*|b| ≤ eta*|a*b| (as equality)
mulAssocAbs : {R : Real} -> (eta a b : Carrier R) -> Equal (rmul (rmul eta (rabs a)) (rabs b)) (rmul eta (rabs (rmul a b))) := by
  intros R eta a b
  erw (CompleteOrderedField.mulAssoc (field R) eta (rabs a) (rabs b)), (cong (\\z => rmul eta z) (sym (absOfMul a b)))

chainBound : {R : Real} -> (num fxfx0 h eta M eps : Carrier R) -> rle (rabs num) (rmul eta (rabs fxfx0)) -> rlt (rabs (rmul fxfx0 (rinv h))) M -> rlt (rzero R) eta -> Equal (rmul eta M) eps -> rlt (rabs (rmul num (rinv h))) eps
chainBound {R} num fxfx0 h eta M eps hdb hdq heta hmul = replace (\\z => rlt (rabs (rmul num (rinv h))) z) hmul (leLtTrans (rabs (rmul num (rinv h))) (rmul eta (rabs (rmul fxfx0 (rinv h)))) (rmul eta M) (replace (\\z => rle z (rmul eta (rabs (rmul fxfx0 (rinv h))))) (sym (absOfMul num (rinv h))) (replace (\\z => rle (rmul (rabs num) (rabs (rinv h))) z) (mulAssocAbs eta fxfx0 (rinv h)) (mulLeRight (rabs num) (rmul eta (rabs fxfx0)) (rabs (rinv h)) hdb (absNonneg (rinv h))))) (mulLtLeft eta (rabs (rmul fxfx0 (rinv h))) M heta hdq))

-- The heart of the chain rule: A(x) -> 0 as x -> x0
-- Uses derivBound (unpunctured), diffQuotBounded (strict), and continuousFromDeriv.
chainTermALimit : {R : Real} -> (g f : Carrier R -> Carrier R) -> (x0 Lg Lf : Carrier R) -> HasDerivative f x0 Lf -> HasDerivative g (f x0) Lg -> Limit (chainTermA g f x0 Lg) x0 (rzero R) := by
  intros R g f x0 Lg Lf hf hg
  constructor
  intros eps heps
  have dqb := diffQuotBounded f x0 Lf hf
  have epsM := rmul eps (rinv (radd (rabs Lf) (rone R)))
  have hepsM := epsOverMPos eps (radd (rabs Lf) (rone R)) heps (absPlusOnePos Lf)
  have db := derivBound g (f x0) Lg hg epsM hepsM
  have cfd := continuousFromDeriv f x0 Lf hf (DPair.fst db) (Pair.fst (DPair.snd db))
  cases (CompleteOrderedField.leTotal (field R) (DPair.fst cfd) (DPair.fst dqb)) with
  | Left hle =>
    exact (MkDPair (DPair.fst cfd) (MkPair (Pair.fst (DPair.snd cfd)) (\\x hx0 hxd => replace (\\z => rlt (rabs z) eps) (sym (subZeroRight (chainTermA g f x0 Lg x))) (chainBound (rsub (rsub (g (f x)) (g (f x0))) (rmul Lg (rsub (f x) (f x0)))) (rsub (f x) (f x0)) (rsub x x0) epsM (radd (rabs Lf) (rone R)) eps (Pair.snd (DPair.snd db) (f x) (Pair.snd (DPair.snd cfd) x hx0 hxd)) (Pair.snd (DPair.snd dqb) x hx0 (ltLeTrans (rabs (rsub x x0)) (DPair.fst cfd) (DPair.fst dqb) hxd hle)) hepsM (trans (CompleteOrderedField.mulComm (field R) epsM (radd (rabs Lf) (rone R))) (mulInvCancel (radd (rabs Lf) (rone R)) eps (absPlusOneNe Lf)))))))
  | Right hle =>
    exact (MkDPair (DPair.fst dqb) (MkPair (Pair.fst (DPair.snd dqb)) (\\x hx0 hxd => replace (\\z => rlt (rabs z) eps) (sym (subZeroRight (chainTermA g f x0 Lg x))) (chainBound (rsub (rsub (g (f x)) (g (f x0))) (rmul Lg (rsub (f x) (f x0)))) (rsub (f x) (f x0)) (rsub x x0) epsM (radd (rabs Lf) (rone R)) eps (Pair.snd (DPair.snd db) (f x) (Pair.snd (DPair.snd cfd) x hx0 (ltLeTrans (rabs (rsub x x0)) (DPair.fst dqb) (DPair.fst cfd) hxd hle))) (Pair.snd (DPair.snd dqb) x hx0 hxd) hepsM (trans (CompleteOrderedField.mulComm (field R) epsM (radd (rabs Lf) (rone R))) (mulInvCancel (radd (rabs Lf) (rone R)) eps (absPlusOneNe Lf)))))))

-- THE CHAIN RULE
-- Proof: By the algebraic identity, diffQuot(g.f, x0, x) = A(x) + g'*diffQuot(f, x0, x).
-- Taking limits:
--   lim diffQuot(g.f) = lim A(x) + g' * lim diffQuot(f)    [limitAdd + limitScalar]
--                      = 0       + g' * f'                   [chainTermALimit + hypothesis]
--                      = g' * f'                              [addZeroLeft]
derivChain : {R : Real} -> (g f : Carrier R -> Carrier R) -> (x0 Lf Lg : Carrier R) -> HasDerivative f x0 Lf -> HasDerivative g (f x0) Lg -> HasDerivative (\\x => g (f x)) x0 (rmul Lg Lf) := by
  intros R g f x0 Lf Lg hf hg
  -- Reduce to proving the limit of A(x) + Lg*diffQuot(f, x0, x)
  suffices h : Limit (\\x => radd (chainTermA g f x0 Lg x) (rmul Lg (diffQuot f x0 x))) x0 (rmul Lg Lf) by
    exact limitExt (\\x => radd (chainTermA g f x0 Lg x) (rmul Lg (diffQuot f x0 x))) (diffQuot (\\y => g (f y)) x0) x0 (rmul Lg Lf) (chainAlgId g f x0 Lg) h
  -- Split the limit of a sum into two limits
  have hA := chainTermALimit g f x0 Lg Lf hf hg
  have hScale := limitScalarAll Lg (diffQuot f x0) x0 Lf hf
  have hSum := limitAdd (chainTermA g f x0 Lg) (\\x => rmul Lg (diffQuot f x0 x)) x0 (rzero R) (rmul Lg Lf) hA hScale
  -- Rewrite 0 + Lg*Lf = Lg*Lf
  exact replace (\\z => Limit (\\x => radd (chainTermA g f x0 Lg x) (rmul Lg (diffQuot f x0 x))) x0 z) (addZeroLeft (rmul Lg Lf)) hSum

-- Chain rule (equational form): deriv(g . f, x0) = deriv(g, f(x0)) * deriv(f, x0)
-- Proof is refl since deriv just extracts L and derivChain produces rmul Lg Lf
derivChainEq : {R : Real} -> (g f : Carrier R -> Carrier R) -> (x0 Lf Lg : Carrier R) -> (hf : HasDerivative f x0 Lf) -> (hg : HasDerivative g (f x0) Lg) -> Equal (deriv (\\x => g (f x)) x0 (derivChain g f x0 Lf Lg hf hg)) (rmul (deriv g (f x0) hg) (deriv f x0 hf))
derivChainEq {R} g f x0 Lf Lg hf hg = refl

------------------------------------------------------------
-- Demo / scratch goal for testing the @simp suggestion strip.
-- Click on subterms (1 + -1, 0 < ε/2, etc.) and see what
-- suggestions surface. The hole \`?TODO\` keeps the proof open
-- so the suggestion strip is always available.
------------------------------------------------------------
demoTestLiterals : (R : Real) -> rle 1 2
demoTestLiterals R = ?TODO
`;
