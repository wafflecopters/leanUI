export const REAL_ANALYSIS_CODE = `-- Real Analysis: algebraic hierarchy, ordered fields, and epsilon-delta limits
-- Builds from scratch to the real numbers and the definition of a limit

------------------------------------------------------------
-- Foundation: basic types and equality
------------------------------------------------------------

inductive Void : Type where

absurd : {A : Type} -> Void -> A

inductive Equal : {A : Type} -> A -> A -> Type where
  refl : {A : Type} -> {a : A} -> Equal a a

sym : {A : Type} -> {x y : A} -> Equal x y -> Equal y x
sym refl = refl

trans : {A : Type} -> {x y z : A} -> Equal x y -> Equal y z -> Equal x z
trans refl refl = refl

cong : {A B : Type} -> {x y : A} -> (f : A -> B) -> Equal x y -> Equal (f x) (f y)
cong f refl = refl

inductive Either : Type -> Type -> Type where
  Left : {A B : Type} -> A -> Either A B
  Right : {A B : Type} -> B -> Either A B

record Pair (A B : Type) where
  constructor MkPair
  fst : A
  snd : B

record DPair {u v : ULevel} (A : Type u) (B : A -> Type v) : Type (UMax u v) where
  constructor MkDPair
  fst : A
  snd : B fst

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
-- The order fields satisfy exactly the TotalOrder axioms.
record OrderedField (A : Type) : Type 1 extends Field A where
  le : A -> A -> Type
  leRefl : (a : A) -> le a a
  leAntisym : (a b : A) -> le a b -> le b a -> Equal a b
  leTrans : (a b c : A) -> le a b -> le b c -> le a c
  leTotal : (a b : A) -> Either (le a b) (le b a)
  -- Compatibility: adding preserves order, product of nonneg is nonneg
  addLeLeft : (a b c : A) -> le a b -> le (add c a) (add c b)
  mulNonneg : (a b : A) -> le zero a -> le zero b -> le zero (mul a b)

------------------------------------------------------------
-- Complete Ordered Field: the Dedekind completeness axiom
------------------------------------------------------------

-- Every nonempty bounded-above subset has a least upper bound.
-- Here P : A -> Type represents a subset (elements a where P a is inhabited).
-- We make sup total (defined for all predicates) with LUB axioms.
record CompleteOrderedField (A : Type) : Type 1 extends OrderedField A where
  sup : (A -> Type) -> A
  supUpperBound : (P : A -> Type) -> (x : A) -> P x -> le x (sup P)
  supLeast : (P : A -> Type) -> (b : A) -> ((x : A) -> P x -> le x b) -> le (sup P) b

------------------------------------------------------------
-- The Real Numbers
------------------------------------------------------------

-- The reals exist: a type equipped with a complete ordered field structure.
-- We postulate their existence as a dependent pair (Sigma type).
postulate RealPkg : DPair (Type) CompleteOrderedField

-- The carrier type
Real : Type
Real = DPair.fst RealPkg

-- The field structure on Real
realField : CompleteOrderedField Real
realField = DPair.snd RealPkg

------------------------------------------------------------
-- Convenience: field operations on Real
------------------------------------------------------------

radd : Real -> Real -> Real
radd = CompleteOrderedField.add realField

rmul : Real -> Real -> Real
rmul = CompleteOrderedField.mul realField

rzero : Real
rzero = CompleteOrderedField.zero realField

rone : Real
rone = CompleteOrderedField.one realField

rneg : Real -> Real
rneg = CompleteOrderedField.neg realField

rinv : Real -> Real
rinv = CompleteOrderedField.inv realField

rle : Real -> Real -> Type
rle = CompleteOrderedField.le realField

-- Subtraction: a - b = a + (-b)
rsub : Real -> Real -> Real
rsub a b = radd a (rneg b)

-- Strict ordering: a < b iff a <= b and a /= b
rlt : Real -> Real -> Type
rlt a b = Pair (rle a b) (Equal a b -> Void)

-- Absolute value (postulated — requires case analysis on order)
postulate rabs : Real -> Real

------------------------------------------------------------
-- Limits: the epsilon-delta definition
------------------------------------------------------------

-- Epsilon-delta witness: given delta, prove delta > 0
-- and the epsilon-delta condition
EpsDeltaWitness : (f : Real -> Real) -> (x0 : Real) -> (L : Real) -> (eps : Real) -> Real -> Type
EpsDeltaWitness f x0 L eps delta = Pair (rlt rzero delta) ((x : Real) -> rlt (rabs (rsub x x0)) delta -> rlt (rabs (rsub (f x) L)) eps)

-- A proof that lim_{x -> x0} f(x) = L.
-- For every epsilon > 0, there exists delta > 0 such that
-- for all x, |x - x0| < delta implies |f(x) - L| < epsilon.
record Limit (f : Real -> Real) (x0 : Real) (L : Real) where
  eps_delta : (eps : Real) -> rlt rzero eps ->
              DPair Real (EpsDeltaWitness f x0 L eps)
`;
