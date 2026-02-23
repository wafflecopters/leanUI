export const REAL_ANALYSIS_CODE = `-- Real Analysis: algebraic hierarchy, ordered fields, limits, and derivatives
-- Proves (f+g)' = f' + g', (c*f)' = c*f', and the chain rule (g.f)' = g'(f(x0)) * f'(x0)

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

-- Transport: rewrite along an equality proof
replace : {A : Type} -> {x y : A} -> (P : A -> Type) -> Equal x y -> P x -> P y
replace P refl px = px

inductive Either : Type -> Type -> Type where
  Left : {A B : Type} -> A -> Either A B
  Right : {A B : Type} -> B -> Either A B

eitherElim : {A B C : Type} -> (A -> C) -> (B -> C) -> Either A B -> C
eitherElim f g (Left a) = f a
eitherElim f g (Right b) = g b

record Pair (A B : Type) where
  constructor MkPair
  fst : A
  snd : B

record DPair {u v : ULevel} (A : Type u) (B : A -> Type v) : Type (UMax u v) where
  constructor MkDPair
  fst : A
  snd : B fst

-- Sigma: DPair at universe level 0 (avoids parser issue with DPair {0} {0})
Sigma : (A : Type) -> (B : A -> Type) -> Type
Sigma A B = DPair A B

-- mkSigma: construct Sigma with explicit P (avoids implicit P conflict in MkDPair)
mkSigma : (A : Type) -> (P : A -> Type) -> (a : A) -> P a -> Sigma A P
mkSigma A P a pa = MkDPair a pa

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
  -- Absolute value: standard ordered field properties
  abs : A -> A
  absTriangle : (a b : A) -> le (abs (add a b)) (add (abs a) (abs b))
  absMul : (a b : A) -> Equal (abs (mul a b)) (mul (abs a) (abs b))
  absNonneg : (a : A) -> le zero (abs a)
  absZero : Equal (abs zero) zero
  absEqZero : (a : A) -> Equal (abs a) zero -> Equal a zero
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
Real = DPair (Type) CompleteOrderedField

-- Convenience: extract carrier type and field structure
Carrier : Real -> Type
Carrier R = DPair.fst R

field : (R : Real) -> CompleteOrderedField (Carrier R)
field R = DPair.snd R

------------------------------------------------------------
-- Field operations, parametric over any Real
------------------------------------------------------------

radd : (R : Real) -> Carrier R -> Carrier R -> Carrier R
radd R = CompleteOrderedField.add (field R)

rmul : (R : Real) -> Carrier R -> Carrier R -> Carrier R
rmul R = CompleteOrderedField.mul (field R)

rzero : (R : Real) -> Carrier R
rzero R = CompleteOrderedField.zero (field R)

rone : (R : Real) -> Carrier R
rone R = CompleteOrderedField.one (field R)

rneg : (R : Real) -> Carrier R -> Carrier R
rneg R = CompleteOrderedField.neg (field R)

rinv : (R : Real) -> Carrier R -> Carrier R
rinv R = CompleteOrderedField.inv (field R)

rle : (R : Real) -> Carrier R -> Carrier R -> Type
rle R = CompleteOrderedField.le (field R)

-- Subtraction: a - b = a + (-b)
rsub : (R : Real) -> Carrier R -> Carrier R -> Carrier R
rsub R a b = radd R a (rneg R b)

-- Strict ordering: a < b iff a <= b and a /= b
rlt : (R : Real) -> Carrier R -> Carrier R -> Type
rlt R a b = Pair (rle R a b) (Equal a b -> Void)

-- Absolute value
rabs : (R : Real) -> Carrier R -> Carrier R
rabs R = CompleteOrderedField.abs (field R)

------------------------------------------------------------
-- Limits: the epsilon-delta definition
------------------------------------------------------------

-- Epsilon-delta witness: given delta, prove delta > 0
-- and the epsilon-delta condition
EpsDeltaWitness : (R : Real) -> (f : Carrier R -> Carrier R) -> (x0 : Carrier R) -> (L : Carrier R) -> (eps : Carrier R) -> Carrier R -> Type
EpsDeltaWitness R f x0 L eps delta = Pair (rlt R (rzero R) delta) ((x : Carrier R) -> rlt R (rzero R) (rabs R (rsub R x x0)) -> rlt R (rabs R (rsub R x x0)) delta -> rlt R (rabs R (rsub R (f x) L)) eps)

-- A proof that lim_{x -> x0} f(x) = L.
-- For every epsilon > 0, there exists delta > 0 such that
-- for all x, |x - x0| < delta implies |f(x) - L| < epsilon.
record Limit (R : Real) (f : Carrier R -> Carrier R) (x0 : Carrier R) (L : Carrier R) where
  eps_delta : (eps : Carrier R) -> rlt R (rzero R) eps ->
              DPair (Carrier R) (EpsDeltaWitness R f x0 L eps)

------------------------------------------------------------
-- Algebraic lemmas
------------------------------------------------------------

addZeroLeft : (R : Real) -> (a : Carrier R) -> Equal (radd R (rzero R) a) a := by
  intros R a
  erw (CompleteOrderedField.addComm (field R) (rzero R) a), (CompleteOrderedField.addZeroRight (field R) a)

negLeft : (R : Real) -> (a : Carrier R) -> Equal (radd R (rneg R a) a) (rzero R) := by
  intros R a
  erw (CompleteOrderedField.addComm (field R) (rneg R a) a), (CompleteOrderedField.negRight (field R) a)

addLeRight : (R : Real) -> (a b c : Carrier R) -> rle R a b -> rle R (radd R a c) (radd R b c)
addLeRight R a b c h = (replace (\\z => rle R z (radd R b c)) (CompleteOrderedField.addComm (field R) c a) (replace (\\z => rle R (radd R c a) z) (CompleteOrderedField.addComm (field R) c b) (CompleteOrderedField.addLeLeft (field R) a b c h)))

addLeBoth : (R : Real) -> (a b c d : Carrier R) -> rle R a b -> rle R c d -> rle R (radd R a c) (radd R b d)
addLeBoth R a b c d hab hcd = (CompleteOrderedField.leTrans (field R) (radd R a c) (radd R b c) (radd R b d) (addLeRight R a b c hab) (CompleteOrderedField.addLeLeft (field R) c d b hcd))

-- leLtTrans: a <= b, b < c => a < c
leLtTransLe : (R : Real) -> (a b c : Carrier R) -> rle R a b -> rle R b c -> rle R a c
leLtTransLe R a b c hab hbc = CompleteOrderedField.leTrans (field R) a b c hab hbc

leLtTransNe : (R : Real) -> (a b c : Carrier R) -> rle R a b -> rle R b c -> (Equal b c -> Void) -> Equal a c -> Void
leLtTransNe R a b c hab hbc nebc eq = nebc (CompleteOrderedField.leAntisym (field R) b c hbc (replace (\\z => rle R z b) eq hab))

leLtTrans : (R : Real) -> (a b c : Carrier R) -> rle R a b -> rlt R b c -> rlt R a c
leLtTrans R a b c hab hbc = MkPair (leLtTransLe R a b c hab (Pair.fst hbc)) (leLtTransNe R a b c hab (Pair.fst hbc) (Pair.snd hbc))

-- ltLeTrans: a < b, b <= c => a < c
ltLeTransLe : (R : Real) -> (a b c : Carrier R) -> rle R a b -> rle R b c -> rle R a c
ltLeTransLe R a b c hab hbc = CompleteOrderedField.leTrans (field R) a b c hab hbc

ltLeTransNe : (R : Real) -> (a b c : Carrier R) -> rle R a b -> (Equal a b -> Void) -> rle R b c -> Equal a c -> Void
ltLeTransNe R a b c hab neab hbc eq = neab (CompleteOrderedField.leAntisym (field R) a b hab (CompleteOrderedField.leTrans (field R) b c a hbc (replace (\\z => rle R z a) eq (CompleteOrderedField.leRefl (field R) a))))

ltLeTrans : (R : Real) -> (a b c : Carrier R) -> rlt R a b -> rle R b c -> rlt R a c
ltLeTrans R a b c hab hbc = MkPair (ltLeTransLe R a b c (Pair.fst hab) hbc) (ltLeTransNe R a b c (Pair.fst hab) (Pair.snd hab) hbc)

-- Cancellation: a + c = b + c => a = b
addCancelRightHelper : (R : Real) -> (x c : Carrier R) -> Equal (radd R (radd R x c) (rneg R c)) x := by
  intros R x c
  erw (CompleteOrderedField.addAssoc (field R) x c (rneg R c)), (CompleteOrderedField.negRight (field R) c), (CompleteOrderedField.addZeroRight (field R) x)

addCancelRight : (R : Real) -> (a b c : Carrier R) -> Equal (radd R a c) (radd R b c) -> Equal a b := by
  intros R a b c h
  erw (sym (addCancelRightHelper R a c)), h, (addCancelRightHelper R b c)

-- Strict addition: a < b, c < d => a + c < b + d
addLtBothNe : (R : Real) -> (a b c d : Carrier R) -> rle R a b -> (Equal a b -> Void) -> rle R c d -> Equal (radd R a c) (radd R b d) -> Void
addLtBothNe R a b c d leab neab lecd eq = (neab (addCancelRight R a b c (CompleteOrderedField.leAntisym (field R) (radd R a c) (radd R b c) (addLeRight R a b c leab) (CompleteOrderedField.leTrans (field R) (radd R b c) (radd R b d) (radd R a c) (CompleteOrderedField.addLeLeft (field R) c d b lecd) (replace (\\z => rle R (radd R b d) z) (sym eq) (CompleteOrderedField.leRefl (field R) (radd R b d)))))))

addLtBoth : (R : Real) -> (a b c d : Carrier R) -> rlt R a b -> rlt R c d -> rlt R (radd R a c) (radd R b d)
addLtBoth R a b c d hab hcd = MkPair (addLeBoth R a b c d (Pair.fst hab) (Pair.fst hcd)) (addLtBothNe R a b c d (Pair.fst hab) (Pair.snd hab) (Pair.fst hcd))

------------------------------------------------------------
-- Halving: 1/2 * eps + 1/2 * eps = eps
------------------------------------------------------------

rtwo : (R : Real) -> Carrier R
rtwo R = radd R (rone R) (rone R)

rhalf : (R : Real) -> Carrier R
rhalf R = rinv R (rtwo R)

oneLeTwo : (R : Real) -> rle R (rone R) (rtwo R)
oneLeTwo R = (replace (\\z => rle R z (rtwo R)) (addZeroLeft R (rone R)) (addLeRight R (rzero R) (rone R) (rone R) (CompleteOrderedField.zeroLeOne (field R))))

twoNeZero : (R : Real) -> Equal (rtwo R) (rzero R) -> Void
twoNeZero R eq = (CompleteOrderedField.zeroNeOne (field R) (CompleteOrderedField.leAntisym (field R) (rzero R) (rone R) (CompleteOrderedField.zeroLeOne (field R)) (replace (\\z => rle R (rone R) z) eq (oneLeTwo R))))

-- 1/2 + 1/2 = 1
halfPlusHalf : (R : Real) -> Equal (radd R (rhalf R) (rhalf R)) (rone R) := by
  intros R
  erw (cong (\\z => radd R z z) (sym (CompleteOrderedField.mulOneLeft (field R) (rhalf R)))), (sym (CompleteOrderedField.distribRight (field R) (rone R) (rone R) (rhalf R))), (CompleteOrderedField.mulInvRight (field R) (rtwo R) (twoNeZero R))

-- (1/2)*e + (1/2)*e = e
halfMulEps : (R : Real) -> (e : Carrier R) -> Equal (radd R (rmul R (rhalf R) e) (rmul R (rhalf R) e)) e := by
  intros R e
  erw (sym (CompleteOrderedField.distribRight (field R) (rhalf R) (rhalf R) e)), (halfPlusHalf R), (CompleteOrderedField.mulOneLeft (field R) e)

zeroLeTwo : (R : Real) -> rle R (rzero R) (rtwo R)
zeroLeTwo R = CompleteOrderedField.leTrans (field R) (rzero R) (rone R) (rtwo R) (CompleteOrderedField.zeroLeOne (field R)) (oneLeTwo R)

halfPos : (R : Real) -> rle R (rzero R) (rhalf R)
halfPos R = CompleteOrderedField.invPos (field R) (rtwo R) (zeroLeTwo R) (twoNeZero R)

halfMulEpsLe : (R : Real) -> (e : Carrier R) -> rle R (rzero R) e -> rle R (rzero R) (rmul R (rhalf R) e)
halfMulEpsLe R e hle = CompleteOrderedField.mulNonneg (field R) (rhalf R) e (halfPos R) hle

halfMulEpsNe : (R : Real) -> (e : Carrier R) -> rle R (rzero R) e -> (Equal (rzero R) e -> Void) -> Equal (rzero R) (rmul R (rhalf R) e) -> Void
halfMulEpsNe R e hle hne heq = hne (trans (sym (addZeroLeft R (rzero R))) (trans (cong (\\z => radd R z z) heq) (halfMulEps R e)))

-- 0 < e => 0 < (1/2)*e
halfMulEpsPos : (R : Real) -> (e : Carrier R) -> rlt R (rzero R) e -> rlt R (rzero R) (rmul R (rhalf R) e)
halfMulEpsPos R e hlt := by
  constructor
  · exact (halfMulEpsLe R e (Pair.fst hlt))
  · exact (halfMulEpsNe R e (Pair.fst hlt) (Pair.snd hlt))

------------------------------------------------------------
-- Negation distributes over addition: -(a+b) = (-a)+(-b)
------------------------------------------------------------

addSumNeg : (R : Real) -> (a b : Carrier R) -> Equal (radd R (radd R a b) (rneg R a)) b := by
  intros R a b
  erw (CompleteOrderedField.addComm (field R) (radd R a b) (rneg R a)), (sym (CompleteOrderedField.addAssoc (field R) (rneg R a) a b)), (negLeft R a), (addZeroLeft R b)

negAddCancel : (R : Real) -> (a b : Carrier R) -> Equal (radd R (radd R a b) (radd R (rneg R a) (rneg R b))) (rzero R) := by
  intros R a b
  erw (sym (CompleteOrderedField.addAssoc (field R) (radd R a b) (rneg R a) (rneg R b))), (addSumNeg R a b), (CompleteOrderedField.negRight (field R) b)

negUnique : (R : Real) -> (a b : Carrier R) -> Equal (radd R a b) (rzero R) -> Equal b (rneg R a) := by
  intros R a b h
  erw (sym (addZeroLeft R b)), (sym (negLeft R a)), (CompleteOrderedField.addAssoc (field R) (rneg R a) a b), h, (CompleteOrderedField.addZeroRight (field R) (rneg R a))

negAdd : (R : Real) -> (a b : Carrier R) -> Equal (rneg R (radd R a b)) (radd R (rneg R a) (rneg R b)) := by
  intros R a b
  erw (sym (negUnique R (radd R a b) (radd R (rneg R a) (rneg R b)) (negAddCancel R a b)))

------------------------------------------------------------
-- (a+b)-(c+d) = (a-c)+(b-d)
------------------------------------------------------------

fourTermRearrange : (R : Real) -> (a b c d : Carrier R) -> Equal (radd R (radd R a b) (radd R c d)) (radd R (radd R a c) (radd R b d)) := by
  intros R a b c d
  erw (CompleteOrderedField.addAssoc (field R) a b (radd R c d)), (cong (\\z => radd R a z) (trans (CompleteOrderedField.addComm (field R) b (radd R c d)) (trans (CompleteOrderedField.addAssoc (field R) c d b) (cong (\\z => radd R c z) (CompleteOrderedField.addComm (field R) d b))))), (sym (CompleteOrderedField.addAssoc (field R) a c (radd R b d)))

subAddSub : (R : Real) -> (a b c d : Carrier R) -> Equal (rsub R (radd R a b) (radd R c d)) (radd R (rsub R a c) (rsub R b d)) := by
  intros R a b c d
  erw (cong (\\z => radd R (radd R a b) z) (negAdd R c d)), (fourTermRearrange R a b (rneg R c) (rneg R d))

------------------------------------------------------------
-- THE THEOREM: lim(f) + lim(g) = lim(f + g)
------------------------------------------------------------

-- Core estimate: |f(x)-L| < he, |g(x)-M| < he => |(f+g)(x)-(L+M)| < he+he
-- Uses triangle inequality and addLtBoth
coreEstimate : (R : Real) -> (f g : Carrier R -> Carrier R) -> (x0 L M he : Carrier R) -> (x : Carrier R) -> rlt R (rabs R (rsub R (f x) L)) he -> rlt R (rabs R (rsub R (g x) M)) he -> rlt R (rabs R (rsub R (radd R (f x) (g x)) (radd R L M))) (radd R he he)
coreEstimate R f g x0 L M he x hfx hgx = (leLtTrans R (rabs R (rsub R (radd R (f x) (g x)) (radd R L M))) (radd R (rabs R (rsub R (f x) L)) (rabs R (rsub R (g x) M))) (radd R he he) (replace (\\z => rle R (rabs R z) (radd R (rabs R (rsub R (f x) L)) (rabs R (rsub R (g x) M)))) (sym (subAddSub R (f x) (g x) L M)) (CompleteOrderedField.absTriangle (field R) (rsub R (f x) L) (rsub R (g x) M))) (addLtBoth R (rabs R (rsub R (f x) L)) he (rabs R (rsub R (g x) M)) he hfx hgx))

-- Convert < (he+he) to < eps via halfMulEps
convertEps : (R : Real) -> (eps v : Carrier R) -> rlt R v (radd R (rmul R (rhalf R) eps) (rmul R (rhalf R) eps)) -> rlt R v eps
convertEps R eps v hlt = replace (\\z => rlt R v z) (halfMulEps R eps) hlt

-- lim_{x->x0} f(x) = L  and  lim_{x->x0} g(x) = M
--   =>  lim_{x->x0} (f(x) + g(x)) = L + M
-- pickDelta is inlined: uses eitherElim on leTotal to pick smaller delta,
-- each case builds the EpsDeltaWitness via convertEps + coreEstimate + ltLeTrans
limitAdd : (R : Real) -> (f g : Carrier R -> Carrier R) -> (x0 L M : Carrier R) -> Limit R f x0 L -> Limit R g x0 M -> Limit R (\\x => radd R (f x) (g x)) x0 (radd R L M)
limitAdd R f g x0 L M limF limG := by
  constructor
  intros eps heps
  have dF := Limit.eps_delta limF (rmul R (rhalf R) eps) (halfMulEpsPos R eps heps)
  have dG := Limit.eps_delta limG (rmul R (rhalf R) eps) (halfMulEpsPos R eps heps)
  cases (CompleteOrderedField.leTotal (field R) (DPair.fst dF) (DPair.fst dG)) with
  | Left hle =>
    exact (MkDPair (DPair.fst dF) (MkPair (Pair.fst (DPair.snd dF)) (\\x hx0 hxd => convertEps R eps (rabs R (rsub R (radd R (f x) (g x)) (radd R L M))) (coreEstimate R f g x0 L M (rmul R (rhalf R) eps) x (Pair.snd (DPair.snd dF) x hx0 hxd) (Pair.snd (DPair.snd dG) x hx0 (ltLeTrans R (rabs R (rsub R x x0)) (DPair.fst dF) (DPair.fst dG) hxd hle))))))
  | Right hle =>
    exact (MkDPair (DPair.fst dG) (MkPair (Pair.fst (DPair.snd dG)) (\\x hx0 hxd => convertEps R eps (rabs R (rsub R (radd R (f x) (g x)) (radd R L M))) (coreEstimate R f g x0 L M (rmul R (rhalf R) eps) x (Pair.snd (DPair.snd dF) x hx0 (ltLeTrans R (rabs R (rsub R x x0)) (DPair.fst dG) (DPair.fst dF) hxd hle)) (Pair.snd (DPair.snd dG) x hx0 hxd)))))

------------------------------------------------------------
-- DERIVATIVES
------------------------------------------------------------

-- Difference quotient: (f(x) - f(x0)) / (x - x0)
diffQuot : (R : Real) -> (f : Carrier R -> Carrier R) -> (x0 : Carrier R) -> Carrier R -> Carrier R
diffQuot R f x0 x = rmul R (rsub R (f x) (f x0)) (rinv R (rsub R x x0))

-- Definition: HasDerivative R f x0 L means lim_{x->x0} (f(x)-f(x0))/(x-x0) = L
HasDerivative : (R : Real) -> (f : Carrier R -> Carrier R) -> (x0 : Carrier R) -> (L : Carrier R) -> Type
HasDerivative R f x0 L = Limit R (diffQuot R f x0) x0 L

-- limitExt: if f and g agree pointwise, limits transfer
limitExt : (R : Real) -> (f g : Carrier R -> Carrier R) -> (x0 L : Carrier R) -> ((x : Carrier R) -> Equal (f x) (g x)) -> Limit R f x0 L -> Limit R g x0 L
limitExt R f g x0 L ext limF := by
  constructor
  intros eps heps
  constructor
  · exact (DPair.fst (Limit.eps_delta limF eps heps))
  · constructor
    · exact (Pair.fst (DPair.snd (Limit.eps_delta limF eps heps)))
    · exact (\\x hx0 hxd => replace (\\z => rlt R (rabs R (rsub R z L)) eps) (ext x) (Pair.snd (DPair.snd (Limit.eps_delta limF eps heps)) x hx0 hxd))

-- distribRight: (a+b)*c = a*c + b*c (from the ring axiom)
-- Already in the record as CompleteOrderedField.distribRight

-- Key algebraic identity for derivAdd:
-- diffQuot(f+g,x0,x) = diffQuot(f,x0,x) + diffQuot(g,x0,x)
-- i.e. ((f+g)(x)-(f+g)(x0)) * (x-x0)^{-1} = (f(x)-f(x0))*(x-x0)^{-1} + (g(x)-g(x0))*(x-x0)^{-1}
-- Proof: by distribRight and subAddSub
diffQuotAddEq : (R : Real) -> (f g : Carrier R -> Carrier R) -> (x0 x : Carrier R) -> Equal (radd R (diffQuot R f x0 x) (diffQuot R g x0 x)) (diffQuot R (\\y => radd R (f y) (g y)) x0 x) := by
  intros R f g x0 x
  erw (sym (CompleteOrderedField.distribRight (field R) (rsub R (f x) (f x0)) (rsub R (g x) (g x0)) (rinv R (rsub R x x0)))), (cong (\\z => rmul R z (rinv R (rsub R x x0))) (sym (subAddSub R (f x) (g x) (f x0) (g x0))))

-- THE DERIVATIVE THEOREM: (f+g)' = f' + g'
derivAdd : (R : Real) -> (f g : Carrier R -> Carrier R) -> (x0 L M : Carrier R) -> HasDerivative R f x0 L -> HasDerivative R g x0 M -> HasDerivative R (\\x => radd R (f x) (g x)) x0 (radd R L M)
derivAdd R f g x0 L M hf hg = limitExt R (\\x => radd R (diffQuot R f x0 x) (diffQuot R g x0 x)) (diffQuot R (\\y => radd R (f y) (g y)) x0) x0 (radd R L M) (diffQuotAddEq R f g x0) (limitAdd R (diffQuot R f x0) (diffQuot R g x0) x0 L M hf hg)

------------------------------------------------------------
-- SCALAR MULTIPLICATION OF LIMITS AND DERIVATIVES
------------------------------------------------------------

-- 0*a = 0 (proved from ring axioms: 0*a + 0*a = (0+0)*a = 0*a = 0 + 0*a, cancel 0*a)
mulZeroLeft : (R : Real) -> (a : Carrier R) -> Equal (rmul R (rzero R) a) (rzero R)
mulZeroLeft R a = addCancelRight R (rmul R (rzero R) a) (rzero R) (rmul R (rzero R) a) (trans (sym (CompleteOrderedField.distribRight (field R) (rzero R) (rzero R) a)) (trans (cong (\\z => rmul R z a) (addZeroLeft R (rzero R))) (sym (addZeroLeft R (rmul R (rzero R) a)))))

-- Helper: c*0 = 0
mulZeroRight : (R : Real) -> (c : Carrier R) -> Equal (rmul R c (rzero R)) (rzero R) := by
  intros R c
  erw (CompleteOrderedField.mulComm (field R) c (rzero R)), (mulZeroLeft R c)

-- Helper: neg distributes through mul on the right: c*(-b) = -(c*b)
-- Proof: c*(-b) + c*b = c*((-b)+b) = c*0 = 0, so c*(-b) = -(c*b)
mulNegRight : (R : Real) -> (c b : Carrier R) -> Equal (rmul R c (rneg R b)) (rneg R (rmul R c b))
mulNegRight R c b = negUnique R (rmul R c b) (rmul R c (rneg R b)) (trans (sym (CompleteOrderedField.distribLeft (field R) c b (rneg R b))) (trans (cong (\\z => rmul R c z) (CompleteOrderedField.negRight (field R) b)) (mulZeroRight R c)))

-- Helper: c*(a-b) = c*a - c*b
mulSubDistrib : (R : Real) -> (c a b : Carrier R) -> Equal (rmul R c (rsub R a b)) (rsub R (rmul R c a) (rmul R c b)) := by
  intros R c a b
  erw (CompleteOrderedField.distribLeft (field R) c a (rneg R b)), (mulNegRight R c b)

-- Key algebraic identity for derivScalar:
-- c * diffQuot(f,x0,x) = diffQuot(c*f,x0,x)
-- i.e. c * ((f(x)-f(x0)) * inv(x-x0)) = (c*f(x) - c*f(x0)) * inv(x-x0)
-- Proof: c*(A*B) = (c*A)*B by assoc, then c*A = c*fx - c*fx0 by distribLeft
diffQuotScalarEq : (R : Real) -> (c : Carrier R) -> (f : Carrier R -> Carrier R) -> (x0 x : Carrier R) -> Equal (rmul R c (diffQuot R f x0 x)) (diffQuot R (\\y => rmul R c (f y)) x0 x) := by
  intros R c f x0 x
  erw (sym (CompleteOrderedField.mulAssoc (field R) c (rsub R (f x) (f x0)) (rinv R (rsub R x x0)))), (cong (\\z => rmul R z (rinv R (rsub R x x0))) (mulSubDistrib R c (f x) (f x0)))

------------------------------------------------------------
-- Infrastructure: abs, ordering, and multiplication lemmas
------------------------------------------------------------

-- a - a = 0
subSelf : (R : Real) -> (a : Carrier R) -> Equal (rsub R a a) (rzero R)
subSelf R a = CompleteOrderedField.negRight (field R) a

-- (a - b) + b = a
subCancel : (R : Real) -> (a b : Carrier R) -> Equal (radd R (rsub R a b) b) a := by
  intros R a b
  erw (CompleteOrderedField.addAssoc (field R) a (rneg R b) b), (negLeft R b), (CompleteOrderedField.addZeroRight (field R) a)

-- |c| > 0 when c /= 0
absPos : (R : Real) -> (c : Carrier R) -> (Equal c (rzero R) -> Void) -> rlt R (rzero R) (rabs R c)
absPos R c hne := by
  constructor
  · exact (CompleteOrderedField.absNonneg (field R) c)
  · exact (\\heq => hne (CompleteOrderedField.absEqZero (field R) c (sym heq)))

-- a <= b => 0 <= b - a
leToSubNonneg : (R : Real) -> (a b : Carrier R) -> rle R a b -> rle R (rzero R) (rsub R b a)
leToSubNonneg R a b hab := by
  rewrite (sym (subSelf R a))
  exact (addLeRight R a b (rneg R a) hab)

-- 0 <= c, a <= b => c*a <= c*b
-- Proof: 0 <= b-a, so 0 <= c*(b-a) = c*b - c*a, add c*a: c*a <= c*b
mulLeLeft : (R : Real) -> (c a b : Carrier R) -> rle R (rzero R) c -> rle R a b -> rle R (rmul R c a) (rmul R c b)
mulLeLeft R c a b hc hab = replace (\\z => rle R (rmul R c a) z) (subCancel R (rmul R c b) (rmul R c a)) (replace (\\z => rle R (rmul R c a) (radd R z (rmul R c a))) (mulSubDistrib R c b a) (replace (\\z => rle R z (radd R (rmul R c (rsub R b a)) (rmul R c a))) (addZeroLeft R (rmul R c a)) (addLeRight R (rzero R) (rmul R c (rsub R b a)) (rmul R c a) (CompleteOrderedField.mulNonneg (field R) c (rsub R b a) hc (leToSubNonneg R a b hab)))))

-- 0 < 1
zeroLtOne : (R : Real) -> rlt R (rzero R) (rone R)
zeroLtOne R := by
  constructor
  · exact (CompleteOrderedField.zeroLeOne (field R))
  · exact (CompleteOrderedField.zeroNeOne (field R))

-- 1 <= |c| + 1 (used for absPlusOnePos)
-- From absNonneg: 0 <= |c|. addLeLeft: le (1+0) (1+|c|). Commute to get le 1 (|c|+1).
oneLeAbsPlusOne : (R : Real) -> (c : Carrier R) -> rle R (rone R) (radd R (rabs R c) (rone R))
oneLeAbsPlusOne R c = replace (\\z => rle R (rone R) z) (CompleteOrderedField.addComm (field R) (rone R) (rabs R c)) (replace (\\z => rle R z (radd R (rone R) (rabs R c))) (CompleteOrderedField.addZeroRight (field R) (rone R)) (CompleteOrderedField.addLeLeft (field R) (rzero R) (rabs R c) (rone R) (CompleteOrderedField.absNonneg (field R) c)))

-- |c| + 1 > 0
absPlusOnePos : (R : Real) -> (c : Carrier R) -> rlt R (rzero R) (radd R (rabs R c) (rone R))
absPlusOnePos R c = ltLeTrans R (rzero R) (rone R) (radd R (rabs R c) (rone R)) (zeroLtOne R) (oneLeAbsPlusOne R c)

-- |c| + 1 /= 0
absPlusOneNe : (R : Real) -> (c : Carrier R) -> Equal (radd R (rabs R c) (rone R)) (rzero R) -> Void
absPlusOneNe R c heq = Pair.snd (absPlusOnePos R c) (sym heq)

-- Strict: 0 < c, a < b => c*a < c*b
-- le part: from mulLeLeft. ne part: c*a = c*b => a = b (multiply both sides by inv(c) on the left)
-- a = 1*a = (inv(c)*c)*a = inv(c)*(c*a) = inv(c)*(c*b) = (inv(c)*c)*b = 1*b = b
mulLtLeftNe : (R : Real) -> (c a b : Carrier R) -> rle R (rzero R) c -> (Equal c (rzero R) -> Void) -> rle R a b -> Equal (rmul R c a) (rmul R c b) -> Equal a b := by
  intros R c a b hc hcne hab heq
  erw (sym (CompleteOrderedField.mulOneLeft (field R) a)), (cong (\\z => rmul R z a) (sym (trans (CompleteOrderedField.mulComm (field R) (rinv R c) c) (CompleteOrderedField.mulInvRight (field R) c hcne)))), (CompleteOrderedField.mulAssoc (field R) (rinv R c) c a), (cong (\\z => rmul R (rinv R c) z) heq), (sym (CompleteOrderedField.mulAssoc (field R) (rinv R c) c b)), (cong (\\z => rmul R z b) (trans (CompleteOrderedField.mulComm (field R) (rinv R c) c) (CompleteOrderedField.mulInvRight (field R) c hcne))), (CompleteOrderedField.mulOneLeft (field R) b)

mulLtLeft : (R : Real) -> (c a b : Carrier R) -> rlt R (rzero R) c -> rlt R a b -> rlt R (rmul R c a) (rmul R c b)
mulLtLeft R c a b hc hab := by
  constructor
  · exact (mulLeLeft R c a b (Pair.fst hc) (Pair.fst hab))
  · exact (\\heq => Pair.snd hab (mulLtLeftNe R c a b (Pair.fst hc) (Pair.snd hc) (Pair.fst hab) heq))

-- a <= b, 0 <= c => a*c <= b*c (right multiplication variant)
mulLeRight : (R : Real) -> (a b c : Carrier R) -> rle R a b -> rle R (rzero R) c -> rle R (rmul R a c) (rmul R b c)
mulLeRight R a b c hab hc = replace (\\z => rle R z (rmul R b c)) (CompleteOrderedField.mulComm (field R) c a) (replace (\\z => rle R (rmul R c a) z) (CompleteOrderedField.mulComm (field R) c b) (mulLeLeft R c a b hc hab))

-- |c| <= |c| + 1
absLeAbsPlusOne : (R : Real) -> (c : Carrier R) -> rle R (rabs R c) (radd R (rabs R c) (rone R))
absLeAbsPlusOne R c = replace (\\z => rle R z (radd R (rabs R c) (rone R))) (CompleteOrderedField.addZeroRight (field R) (rabs R c)) (CompleteOrderedField.addLeLeft (field R) (rzero R) (rone R) (rabs R c) (CompleteOrderedField.zeroLeOne (field R)))

-- M * (a * inv(M)) = a when M /= 0
mulInvCancel : (R : Real) -> (M a : Carrier R) -> (Equal M (rzero R) -> Void) -> Equal (rmul R M (rmul R a (rinv R M))) a := by
  intros R M a hne
  erw (sym (CompleteOrderedField.mulAssoc (field R) M a (rinv R M))), (CompleteOrderedField.mulComm (field R) M a), (CompleteOrderedField.mulAssoc (field R) a M (rinv R M)), (CompleteOrderedField.mulInvRight (field R) M hne), (CompleteOrderedField.mulOneRight (field R) a)

-- 0 < eps, 0 < M => 0 < eps * inv(M)
-- Proof: le part from mulNonneg + invPos; ne part from eps * inv(M) = 0 => eps = 0
epsOverMPos : (R : Real) -> (eps M : Carrier R) -> rlt R (rzero R) eps -> rlt R (rzero R) M -> rlt R (rzero R) (rmul R eps (rinv R M))
epsOverMPos R eps M heps hM := by
  constructor
  · exact (CompleteOrderedField.mulNonneg (field R) eps (rinv R M) (Pair.fst heps) (CompleteOrderedField.invPos (field R) M (Pair.fst hM) (Pair.snd hM)))
  · exact (\\heq => Pair.snd heps (trans heq (trans (cong (\\z => rmul R z (rinv R M)) (sym (mulZeroLeft R (rinv R M)))) (sym (CompleteOrderedField.mulAssoc (field R) (rzero R) (rinv R M) (rinv R M))))))

------------------------------------------------------------
-- Scalar multiplication of limits (proved)
------------------------------------------------------------

-- Helper: |c*(a-b)| <= (|c|+1) * |a-b|
-- Proof: |c*(a-b)| = |c|*|a-b| <= (|c|+1)*|a-b|
scalarAbsBound : (R : Real) -> (c a b : Carrier R) -> rle R (rabs R (rsub R (rmul R c a) (rmul R c b))) (rmul R (radd R (rabs R c) (rone R)) (rabs R (rsub R a b)))
scalarAbsBound R c a b = replace (\\z => rle R (rabs R z) (rmul R (radd R (rabs R c) (rone R)) (rabs R (rsub R a b)))) (mulSubDistrib R c a b) (replace (\\z => rle R z (rmul R (radd R (rabs R c) (rone R)) (rabs R (rsub R a b)))) (sym (CompleteOrderedField.absMul (field R) c (rsub R a b))) (mulLeRight R (rabs R c) (radd R (rabs R c) (rone R)) (rabs R (rsub R a b)) (absLeAbsPlusOne R c) (CompleteOrderedField.absNonneg (field R) (rsub R a b))))

-- lim(c*f) = c*L for all c (including c = 0)
-- Proof: Use M = |c| + 1 > 0. Get delta from limF at eps/M.
-- Then |c*f(x) - c*L| = |c|*|f(x)-L| <= M*|f(x)-L| < M*(eps/M) = eps.
limitScalarAll : (R : Real) -> (c : Carrier R) -> (h : Carrier R -> Carrier R) -> (x0 L : Carrier R) -> Limit R h x0 L -> Limit R (\\x => rmul R c (h x)) x0 (rmul R c L)
limitScalarAll R c h x0 L limH := by
  constructor
  intros eps heps
  constructor
  · exact (DPair.fst (Limit.eps_delta limH (rmul R eps (rinv R (radd R (rabs R c) (rone R)))) (epsOverMPos R eps (radd R (rabs R c) (rone R)) heps (absPlusOnePos R c))))
  · constructor
    · exact (Pair.fst (DPair.snd (Limit.eps_delta limH (rmul R eps (rinv R (radd R (rabs R c) (rone R)))) (epsOverMPos R eps (radd R (rabs R c) (rone R)) heps (absPlusOnePos R c)))))
    · exact (\\x hx0 hxd => replace (\\z => rlt R (rabs R (rsub R (rmul R c (h x)) (rmul R c L))) z) (mulInvCancel R (radd R (rabs R c) (rone R)) eps (absPlusOneNe R c)) (leLtTrans R (rabs R (rsub R (rmul R c (h x)) (rmul R c L))) (rmul R (radd R (rabs R c) (rone R)) (rabs R (rsub R (h x) L))) (rmul R (radd R (rabs R c) (rone R)) (rmul R eps (rinv R (radd R (rabs R c) (rone R))))) (scalarAbsBound R c (h x) L) (mulLtLeft R (radd R (rabs R c) (rone R)) (rabs R (rsub R (h x) L)) (rmul R eps (rinv R (radd R (rabs R c) (rone R)))) (absPlusOnePos R c) (Pair.snd (DPair.snd (Limit.eps_delta limH (rmul R eps (rinv R (radd R (rabs R c) (rone R)))) (epsOverMPos R eps (radd R (rabs R c) (rone R)) heps (absPlusOnePos R c)))) x hx0 hxd))))

-- limitScalar: special case for c /= 0 (calls limitScalarAll)
limitScalar : (R : Real) -> (c : Carrier R) -> (Equal c (rzero R) -> Void) -> (f : Carrier R -> Carrier R) -> (x0 L : Carrier R) -> Limit R f x0 L -> Limit R (\\x => rmul R c (f x)) x0 (rmul R c L)
limitScalar R c hcnz f x0 L limF = limitScalarAll R c f x0 L limF

-- THE DERIVATIVE THEOREM: (c*f)' = c*f'
derivScalar : (R : Real) -> (c : Carrier R) -> (Equal c (rzero R) -> Void) -> (f : Carrier R -> Carrier R) -> (x0 L : Carrier R) -> HasDerivative R f x0 L -> HasDerivative R (\\x => rmul R c (f x)) x0 (rmul R c L)
derivScalar R c hcnz f x0 L hf = limitExt R (\\x => rmul R c (diffQuot R f x0 x)) (diffQuot R (\\y => rmul R c (f y)) x0) x0 (rmul R c L) (diffQuotScalarEq R c f x0) (limitScalar R c hcnz (diffQuot R f x0) x0 L hf)

------------------------------------------------------------
-- Infrastructure for the chain rule
------------------------------------------------------------

-- neg(0) = 0
negZero : (R : Real) -> Equal (rneg R (rzero R)) (rzero R) := by
  intros R
  erw (sym (addZeroLeft R (rneg R (rzero R)))), (CompleteOrderedField.negRight (field R) (rzero R))

-- a - 0 = a
subZeroRight : (R : Real) -> (a : Carrier R) -> Equal (rsub R a (rzero R)) a := by
  intros R a
  erw (negZero R), (CompleteOrderedField.addZeroRight (field R) a)

-- |a * b| = |a| * |b| (convenience alias)
absOfMul : (R : Real) -> (a b : Carrier R) -> Equal (rabs R (rmul R a b)) (rmul R (rabs R a) (rabs R b))
absOfMul R a b = CompleteOrderedField.absMul (field R) a b

-- |0| = 0 (convenience alias)
absOfZero : (R : Real) -> Equal (rabs R (rzero R)) (rzero R)
absOfZero R = CompleteOrderedField.absZero (field R)

-- 0 * a = 0 * b (trivially, both are 0)
-- Useful to avoid re-proving for specific instantiations
mulZeroBoth : (R : Real) -> (a b : Carrier R) -> Equal (rmul R (rzero R) a) (rmul R (rzero R) b)
mulZeroBoth R a b = trans (mulZeroLeft R a) (sym (mulZeroLeft R b))

-- Weaken rlt to rle
ltToLe : (R : Real) -> (a b : Carrier R) -> rlt R a b -> rle R a b
ltToLe R a b h = Pair.fst h

-- |a| < b implies |a| ≤ b (extract le from lt)
absLtToLe : (R : Real) -> (a b : Carrier R) -> rlt R (rabs R a) b -> rle R (rabs R a) b
absLtToLe R a b h = Pair.fst h

-- (a - c) + (c - b) = a - b
-- Proof: (a+(-c)) + (c+(-b)) = (a+c) + ((-c)+(-b)) by fourTermRearrange... no
-- Simpler: use subCancel on the inner c
subSplit : (R : Real) -> (a b c : Carrier R) -> Equal (radd R (rsub R a c) (rsub R c b)) (rsub R a b) := by
  intros R a b c
  erw (CompleteOrderedField.addAssoc (field R) a (rneg R c) (rsub R c b)), (cong (\\z => radd R a z) (trans (sym (CompleteOrderedField.addAssoc (field R) (rneg R c) c (rneg R b))) (trans (cong (\\z => radd R z (rneg R b)) (negLeft R c)) (addZeroLeft R (rneg R b)))))

-- Triangle inequality for subtraction: |a - b| ≤ |a - c| + |c - b|
-- Proof: a - b = (a - c) + (c - b), then apply absTriangle
subTriangle : (R : Real) -> (a b c : Carrier R) -> rle R (rabs R (rsub R a b)) (radd R (rabs R (rsub R a c)) (rabs R (rsub R c b)))
subTriangle R a b c = replace (\\z => rle R (rabs R z) (radd R (rabs R (rsub R a c)) (rabs R (rsub R c b)))) (subSplit R a b c) (CompleteOrderedField.absTriangle (field R) (rsub R a c) (rsub R c b))

-- Split a value into a = 0 or a /= 0
-- Proof: from absNonneg (0 <= |a|), leToEqOrLt gives Either (0 = |a|) (0 < |a|).
-- Left: 0 = |a| implies |a| = 0 implies a = 0 by absEqZero.
-- Right: 0 /= |a|, so if a = 0 then |a| = |0| = 0, contradicting 0 /= |a|.
-- (-a) * b = -(a * b) — negation on the left of multiplication
mulNegLeft : (R : Real) -> (a b : Carrier R) -> Equal (rmul R (rneg R a) b) (rneg R (rmul R a b)) := by
  intros R a b
  erw (CompleteOrderedField.mulComm (field R) (rneg R a) b), (mulNegRight R b a), (CompleteOrderedField.mulComm (field R) b a)

-- (a - b) * c = a*c - b*c — right distributivity for subtraction
mulSubDistribRight : (R : Real) -> (a b c : Carrier R) -> Equal (rmul R (rsub R a b) c) (rsub R (rmul R a c) (rmul R b c)) := by
  intros R a b c
  erw (CompleteOrderedField.distribRight (field R) a (rneg R b) c), (mulNegLeft R b c)

-- a * (inv(a) * b) = b when a /= 0 (variant of mulInvCancel)
mulInvLeftCancel : (R : Real) -> (a b : Carrier R) -> (Equal a (rzero R) -> Void) -> Equal (rmul R a (rmul R (rinv R a) b)) b := by
  intros R a b hne
  erw (sym (CompleteOrderedField.mulAssoc (field R) a (rinv R a) b)), (CompleteOrderedField.mulInvRight (field R) a hne), (CompleteOrderedField.mulOneLeft (field R) b)

-- (a*inv(b) - c) * b = a - c*b when b /= 0
-- Proof: distribRight gives (a*inv(b))*b - c*b. Then a*inv(b)*b = a*(inv(b)*b) = a*1 = a.
diffQuotSubMulEq : (R : Real) -> (a b c : Carrier R) -> (Equal b (rzero R) -> Void) -> Equal (rmul R (rsub R (rmul R a (rinv R b)) c) b) (rsub R a (rmul R c b)) := by
  intros R a b c hne
  erw (mulSubDistribRight R (rmul R a (rinv R b)) c b), (cong (\\z => rsub R z (rmul R c b)) (trans (CompleteOrderedField.mulAssoc (field R) a (rinv R b) b) (trans (cong (\\z => rmul R a z) (trans (CompleteOrderedField.mulComm (field R) (rinv R b) b) (CompleteOrderedField.mulInvRight (field R) b hne))) (CompleteOrderedField.mulOneRight (field R) a))))

eqOrNeZeroLeft : (R : Real) -> (a : Carrier R) -> Equal (rzero R) (rabs R a) -> Equal a (rzero R)
eqOrNeZeroLeft R a h = CompleteOrderedField.absEqZero (field R) a (sym h)

eqOrNeZeroRight : (R : Real) -> (a : Carrier R) -> (Equal (rzero R) (rabs R a) -> Void) -> Equal a (rzero R) -> Void
eqOrNeZeroRight R a hne heq = hne (sym (trans (cong (\\z => rabs R z) heq) (absOfZero R)))

eqOrNeZero : (R : Real) -> (a : Carrier R) -> Either (Equal a (rzero R)) (Equal a (rzero R) -> Void)
eqOrNeZero R a = eitherElim (\\h => Left (eqOrNeZeroLeft R a h)) (\\h => Right (eqOrNeZeroRight R a (Pair.snd h))) (CompleteOrderedField.leToEqOrLt (field R) (rzero R) (rabs R a) (CompleteOrderedField.absNonneg (field R) a))

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
derivBoundZero : (R : Real) -> (g : Carrier R -> Carrier R) -> (y0 Lg eta : Carrier R) -> rle R (rabs R (rsub R (rsub R (g y0) (g y0)) (rmul R Lg (rzero R)))) (rmul R eta (rabs R (rzero R)))
derivBoundZero R g y0 Lg eta = replace (\\z => rle R z (rmul R eta (rabs R (rzero R)))) (sym (trans (cong (\\z => rabs R (rsub R (rsub R (g y0) (g y0)) z)) (mulZeroRight R Lg)) (trans (cong (\\z => rabs R z) (subZeroRight R (rsub R (g y0) (g y0)))) (trans (cong (\\z => rabs R z) (subSelf R (g y0))) (absOfZero R))))) (replace (\\z => rle R (rzero R) z) (sym (trans (cong (\\z => rmul R eta z) (absOfZero R)) (mulZeroRight R eta))) (CompleteOrderedField.leRefl (field R) (rzero R)))

-- a - b = 0 implies a = b
-- Proof: a = a - b + b = 0 + b = b
subEqZeroToEq : (R : Real) -> (a b : Carrier R) -> Equal (rsub R a b) (rzero R) -> Equal a b := by
  intros R a b h
  erw (sym (subCancel R a b)), h, (addZeroLeft R b)

-- When d = y - y0 /= 0: 0 < |d|, so derivative gives |diffQuot(g)-Lg| < eta.
-- Then |g(y)-g(y0)-Lg*(y-y0)| = |(diffQuot-Lg)*(y-y0)| = |diffQuot-Lg|*|y-y0| <= eta*|y-y0|.
-- This needs: diffQuotSubMulEq, absMul, mulLeRight
derivBoundNonzero : (R : Real) -> (g : Carrier R -> Carrier R) -> (y0 Lg eta : Carrier R) -> (y : Carrier R) -> (Equal (rsub R y y0) (rzero R) -> Void) -> rle R (rabs R (rsub R (diffQuot R g y0 y) Lg)) eta -> rle R (rabs R (rsub R (rsub R (g y) (g y0)) (rmul R Lg (rsub R y y0)))) (rmul R eta (rabs R (rsub R y y0)))
derivBoundNonzero R g y0 Lg eta y hne hle = replace (\\z => rle R (rabs R z) (rmul R eta (rabs R (rsub R y y0)))) (diffQuotSubMulEq R (rsub R (g y) (g y0)) (rsub R y y0) Lg hne) (replace (\\z => rle R z (rmul R eta (rabs R (rsub R y y0)))) (sym (absOfMul R (rsub R (diffQuot R g y0 y) Lg) (rsub R y y0))) (mulLeRight R (rabs R (rsub R (diffQuot R g y0 y) Lg)) eta (rabs R (rsub R y y0)) hle (CompleteOrderedField.absNonneg (field R) (rsub R y y0))))

-- Type for derivBound witness: delta > 0, and the unpunctured bound holds
DerivBoundWitness : (R : Real) -> (g : Carrier R -> Carrier R) -> (y0 Lg eta : Carrier R) -> Carrier R -> Type
DerivBoundWitness R g y0 Lg eta dg = Pair (rlt R (rzero R) dg) ((y : Carrier R) -> rlt R (rabs R (rsub R y y0)) dg -> rle R (rabs R (rsub R (rsub R (g y) (g y0)) (rmul R Lg (rsub R y y0)))) (rmul R eta (rabs R (rsub R y y0))))

-- Full derivBound: case split on y-y0 = 0 vs y-y0 /= 0
derivBound : (R : Real) -> (g : Carrier R -> Carrier R) -> (y0 Lg : Carrier R) -> HasDerivative R g y0 Lg -> (eta : Carrier R) -> rlt R (rzero R) eta -> Sigma (Carrier R) (DerivBoundWitness R g y0 Lg eta)
derivBound R g y0 Lg hg eta heta := by
  constructor
  · exact (DPair.fst (Limit.eps_delta hg eta heta))
  · constructor
    · exact (Pair.fst (DPair.snd (Limit.eps_delta hg eta heta)))
    · exact (\\y hyd => eitherElim
        (\\heq => replace (\\z => rle R (rabs R (rsub R (rsub R (g z) (g y0)) (rmul R Lg (rsub R z y0)))) (rmul R eta (rabs R (rsub R z y0)))) (sym (subEqZeroToEq R y y0 heq)) (replace (\\z => rle R (rabs R (rsub R (rsub R (g y0) (g y0)) (rmul R Lg z))) (rmul R eta (rabs R z))) (sym (subSelf R y0)) (derivBoundZero R g y0 Lg eta)))
        (\\hne => derivBoundNonzero R g y0 Lg eta y hne (ltToLe R (rabs R (rsub R (diffQuot R g y0 y) Lg)) eta (Pair.snd (DPair.snd (Limit.eps_delta hg eta heta)) y (absPos R (rsub R y y0) hne) hyd)))
        (eqOrNeZero R (rsub R y y0)))

-- a < b => a + c < b + c
addLtRight : (R : Real) -> (a b c : Carrier R) -> rlt R a b -> rlt R (radd R a c) (radd R b c)
addLtRight R a b c h := by
  constructor
  · exact (addLeRight R a b c (Pair.fst h))
  · exact (\\heq => Pair.snd h (addCancelRight R a b c heq))

-- |a| <= |a - b| + |b| (variant of triangle inequality)
absSubAdd : (R : Real) -> (a b : Carrier R) -> rle R (rabs R a) (radd R (rabs R (rsub R a b)) (rabs R b))
absSubAdd R a b = replace (\\z => rle R (rabs R z) (radd R (rabs R (rsub R a b)) (rabs R b))) (subCancel R a b) (CompleteOrderedField.absTriangle (field R) (rsub R a b) b)

-- DiffQuot is bounded near x0 by |Lf| + 1
-- Returns: delta, delta > 0, and for 0 < |x-x0| < delta: |diffQuot(f)| <= |Lf|+1
DiffQuotBoundWitness : (R : Real) -> (f : Carrier R -> Carrier R) -> (x0 Lf : Carrier R) -> Carrier R -> Type
DiffQuotBoundWitness R f x0 Lf df = Pair (rlt R (rzero R) df) ((x : Carrier R) -> rlt R (rzero R) (rabs R (rsub R x x0)) -> rlt R (rabs R (rsub R x x0)) df -> rlt R (rabs R (diffQuot R f x0 x)) (radd R (rabs R Lf) (rone R)))

diffQuotBounded : (R : Real) -> (f : Carrier R -> Carrier R) -> (x0 Lf : Carrier R) -> HasDerivative R f x0 Lf -> Sigma (Carrier R) (DiffQuotBoundWitness R f x0 Lf)
diffQuotBounded R f x0 Lf hf := by
  constructor
  · exact (DPair.fst (Limit.eps_delta hf (rone R) (zeroLtOne R)))
  · constructor
    · exact (Pair.fst (DPair.snd (Limit.eps_delta hf (rone R) (zeroLtOne R))))
    · exact (\\x hx0 hxd => leLtTrans R (rabs R (diffQuot R f x0 x))
        (radd R (rabs R (rsub R (diffQuot R f x0 x) Lf)) (rabs R Lf))
        (radd R (rabs R Lf) (rone R)) (absSubAdd R (diffQuot R f x0 x) Lf)
        (replace (\\z => rlt R (radd R (rabs R (rsub R (diffQuot R f x0 x) Lf)) (rabs R Lf)) z)
          (CompleteOrderedField.addComm (field R) (rone R) (rabs R Lf))
          (addLtRight R (rabs R (rsub R (diffQuot R f x0 x) Lf)) (rone R) (rabs R Lf)
            (Pair.snd (DPair.snd (Limit.eps_delta hf (rone R) (zeroLtOne R))) x hx0 hxd))))

-- diffQuot(f,x0,x) * (x-x0) = f(x)-f(x0) when x-x0 /= 0
-- Proof: (a*inv(b))*b = a*(inv(b)*b) = a*1 = a
diffQuotTimesH : (R : Real) -> (f : Carrier R -> Carrier R) -> (x0 x : Carrier R) -> (Equal (rsub R x x0) (rzero R) -> Void) -> Equal (rmul R (diffQuot R f x0 x) (rsub R x x0)) (rsub R (f x) (f x0)) := by
  intros R f x0 x hne
  erw (CompleteOrderedField.mulAssoc (field R) (rsub R (f x) (f x0)) (rinv R (rsub R x x0)) (rsub R x x0)), (cong (\\z => rmul R (rsub R (f x) (f x0)) z) (trans (CompleteOrderedField.mulComm (field R) (rinv R (rsub R x x0)) (rsub R x x0)) (CompleteOrderedField.mulInvRight (field R) (rsub R x x0) hne))), (CompleteOrderedField.mulOneRight (field R) (rsub R (f x) (f x0)))

-- |diffQuot(f,x0,x)| * |x-x0| = |f(x)-f(x0)| when x-x0 /= 0
absDiffQuotTimesH : (R : Real) -> (f : Carrier R -> Carrier R) -> (x0 x : Carrier R) -> (Equal (rsub R x x0) (rzero R) -> Void) -> Equal (rmul R (rabs R (diffQuot R f x0 x)) (rabs R (rsub R x x0))) (rabs R (rsub R (f x) (f x0))) := by
  intros R f x0 x hne
  erw (sym (absOfMul R (diffQuot R f x0 x) (rsub R x x0))), (cong (\\z => rabs R z) (diffQuotTimesH R f x0 x hne))

-- Differentiability implies continuity (limit sense):
-- HasDerivative R f x0 Lf implies: for any target > 0, exists delta > 0,
-- 0 < |x-x0| < delta => |f(x)-f(x0)| < target.
-- Proof: |f(x)-f(x0)| = |diffQuot(f)|*|x-x0| <= (|Lf|+1)*|x-x0| < (|Lf|+1) * target/(|Lf|+1) = target
ContinuousWitness : (R : Real) -> (f : Carrier R -> Carrier R) -> (x0 target : Carrier R) -> Carrier R -> Type
ContinuousWitness R f x0 target dc = Pair (rlt R (rzero R) dc) ((x : Carrier R) -> rlt R (rzero R) (rabs R (rsub R x x0)) -> rlt R (rabs R (rsub R x x0)) dc -> rlt R (rabs R (rsub R (f x) (f x0))) target)

-- Helper: |a| * |b| < c * |b| when |a| < c and 0 < |b|  (using mulLtLeft on absNonneg)
-- Actually we need: |a| <= M, |b| < eps => |a|*|b| < M*eps (when M > 0)
-- Use: |a|*|b| <= M*|b| by mulLeLeft, and M*|b| < M*eps by mulLtLeft
absMulBound : (R : Real) -> (a b M eps : Carrier R) -> rle R (rabs R a) M -> rlt R (rabs R b) eps -> rlt R (rzero R) M -> rlt R (rmul R (rabs R a) (rabs R b)) (rmul R M eps)
absMulBound R a b M eps hle hlt hM = leLtTrans R (rmul R (rabs R a) (rabs R b)) (rmul R M (rabs R b)) (rmul R M eps) (mulLeRight R (rabs R a) M (rabs R b) hle (CompleteOrderedField.absNonneg (field R) b)) (mulLtLeft R M (rabs R b) eps hM hlt)

-- Differentiability implies continuity
-- For any target > 0, exists delta > 0, 0 < |x-x0| < delta => |f(x)-f(x0)| < target
-- We need min of two deltas: d1 from diffQuotBounded, d2 = target/(|Lf|+1)
continuousFromDeriv : (R : Real) -> (f : Carrier R -> Carrier R) -> (x0 Lf : Carrier R) -> HasDerivative R f x0 Lf -> (target : Carrier R) -> rlt R (rzero R) target -> Sigma (Carrier R) (ContinuousWitness R f x0 target)
continuousFromDeriv R f x0 Lf hf target htarget := by
  have dqb := diffQuotBounded R f x0 Lf hf
  cases (CompleteOrderedField.leTotal (field R) (DPair.fst dqb) (rmul R target (rinv R (radd R (rabs R Lf) (rone R))))) with
  | Left hle =>
    exact (mkSigma (Carrier R) (ContinuousWitness R f x0 target) (DPair.fst dqb) (MkPair (Pair.fst (DPair.snd dqb)) (\\x hx0 hxd => replace (\\z => rlt R z target) (absDiffQuotTimesH R f x0 x (eqOrNeZeroRight R (rsub R x x0) (Pair.snd hx0))) (replace (\\z => rlt R (rmul R (rabs R (diffQuot R f x0 x)) (rabs R (rsub R x x0))) z) (mulInvCancel R (radd R (rabs R Lf) (rone R)) target (absPlusOneNe R Lf)) (absMulBound R (diffQuot R f x0 x) (rsub R x x0) (radd R (rabs R Lf) (rone R)) (rmul R target (rinv R (radd R (rabs R Lf) (rone R)))) (ltToLe R (rabs R (diffQuot R f x0 x)) (radd R (rabs R Lf) (rone R)) (Pair.snd (DPair.snd dqb) x hx0 hxd)) (ltLeTrans R (rabs R (rsub R x x0)) (DPair.fst dqb) (rmul R target (rinv R (radd R (rabs R Lf) (rone R)))) hxd hle) (absPlusOnePos R Lf))))))
  | Right hle =>
    exact (mkSigma (Carrier R) (ContinuousWitness R f x0 target) (rmul R target (rinv R (radd R (rabs R Lf) (rone R)))) (MkPair (epsOverMPos R target (radd R (rabs R Lf) (rone R)) htarget (absPlusOnePos R Lf)) (\\x hx0 hxd => replace (\\z => rlt R z target) (absDiffQuotTimesH R f x0 x (eqOrNeZeroRight R (rsub R x x0) (Pair.snd hx0))) (replace (\\z => rlt R (rmul R (rabs R (diffQuot R f x0 x)) (rabs R (rsub R x x0))) z) (mulInvCancel R (radd R (rabs R Lf) (rone R)) target (absPlusOneNe R Lf)) (absMulBound R (diffQuot R f x0 x) (rsub R x x0) (radd R (rabs R Lf) (rone R)) (rmul R target (rinv R (radd R (rabs R Lf) (rone R)))) (Pair.snd (DPair.snd dqb) x hx0 (ltLeTrans R (rabs R (rsub R x x0)) (rmul R target (rinv R (radd R (rabs R Lf) (rone R)))) (DPair.fst dqb) hxd hle)) hxd (absPlusOnePos R Lf))))))

------------------------------------------------------------
-- THE CHAIN RULE: (g . f)'(x0) = g'(f(x0)) . f'(x0)
------------------------------------------------------------

-- The "error term" in the chain rule decomposition:
-- A(x) = (g(f(x)) - g(f(x0)) - g'*(f(x) - f(x0))) * inv(x - x0)
-- This measures how well g's linear approximation at f(x0) predicts g(f(x)),
-- normalized by (x - x0). Crucially, A(x) = 0 when f(x) = f(x0) (no case split needed).
chainTermA : (R : Real) -> (g f : Carrier R -> Carrier R) -> (x0 Lg : Carrier R) -> Carrier R -> Carrier R
chainTermA R g f x0 Lg x = rmul R (rsub R (rsub R (g (f x)) (g (f x0))) (rmul R Lg (rsub R (f x) (f x0)))) (rinv R (rsub R x x0))

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
chainAlgId : (R : Real) -> (g f : Carrier R -> Carrier R) -> (x0 Lg : Carrier R) -> (x : Carrier R) -> Equal (radd R (chainTermA R g f x0 Lg x) (rmul R Lg (diffQuot R f x0 x))) (diffQuot R (\\y => g (f y)) x0 x) := by
  intros R g f x0 Lg x
  erw (cong (\\z => radd R (chainTermA R g f x0 Lg x) z) (sym (CompleteOrderedField.mulAssoc (field R) Lg (rsub R (f x) (f x0)) (rinv R (rsub R x x0))))), (sym (CompleteOrderedField.distribRight (field R) (rsub R (rsub R (g (f x)) (g (f x0))) (rmul R Lg (rsub R (f x) (f x0)))) (rmul R Lg (rsub R (f x) (f x0))) (rinv R (rsub R x x0)))), (cong (\\z => rmul R z (rinv R (rsub R x x0))) (subCancel R (rsub R (g (f x)) (g (f x0))) (rmul R Lg (rsub R (f x) (f x0)))))

-- Core bound for chainTermALimit:
-- |num| ≤ η*|f(x)-f(x0)| and |diffQuot(f)| < M and η*M = eps => |num*inv(x-x0)| < eps
-- Steps: |num*inv(h)| = |num|*|inv(h)| ≤ η*|Δf|*|inv(h)| = η*|diffQuot(f)| < η*M = eps
-- Step: (eta*|a|)*|b| = eta*(|a|*|b|) by mulAssoc
-- Step: eta*(|a|*|b|) = eta*|a*b| by cong+absMul
-- Combined: (eta*|a|)*|b| ≤ eta*|a*b| (as equality)
mulAssocAbs : (R : Real) -> (eta a b : Carrier R) -> Equal (rmul R (rmul R eta (rabs R a)) (rabs R b)) (rmul R eta (rabs R (rmul R a b))) := by
  intros R eta a b
  erw (CompleteOrderedField.mulAssoc (field R) eta (rabs R a) (rabs R b)), (cong (\\z => rmul R eta z) (sym (absOfMul R a b)))

chainBound : (R : Real) -> (num fxfx0 h eta M eps : Carrier R) -> rle R (rabs R num) (rmul R eta (rabs R fxfx0)) -> rlt R (rabs R (rmul R fxfx0 (rinv R h))) M -> rlt R (rzero R) eta -> Equal (rmul R eta M) eps -> rlt R (rabs R (rmul R num (rinv R h))) eps
chainBound R num fxfx0 h eta M eps hdb hdq heta hmul = replace (\\z => rlt R (rabs R (rmul R num (rinv R h))) z) hmul (leLtTrans R (rabs R (rmul R num (rinv R h))) (rmul R eta (rabs R (rmul R fxfx0 (rinv R h)))) (rmul R eta M) (replace (\\z => rle R z (rmul R eta (rabs R (rmul R fxfx0 (rinv R h))))) (sym (absOfMul R num (rinv R h))) (replace (\\z => rle R (rmul R (rabs R num) (rabs R (rinv R h))) z) (mulAssocAbs R eta fxfx0 (rinv R h)) (mulLeRight R (rabs R num) (rmul R eta (rabs R fxfx0)) (rabs R (rinv R h)) hdb (CompleteOrderedField.absNonneg (field R) (rinv R h))))) (mulLtLeft R eta (rabs R (rmul R fxfx0 (rinv R h))) M heta hdq))

-- The heart of the chain rule: A(x) -> 0 as x -> x0
-- Uses derivBound (unpunctured), diffQuotBounded (strict), and continuousFromDeriv.
chainTermALimit : (R : Real) -> (g f : Carrier R -> Carrier R) -> (x0 Lg Lf : Carrier R) -> HasDerivative R f x0 Lf -> HasDerivative R g (f x0) Lg -> Limit R (chainTermA R g f x0 Lg) x0 (rzero R)
chainTermALimit R g f x0 Lg Lf hf hg := by
  constructor
  intros eps heps
  have dqb := diffQuotBounded R f x0 Lf hf
  have epsM := rmul R eps (rinv R (radd R (rabs R Lf) (rone R)))
  have hepsM := epsOverMPos R eps (radd R (rabs R Lf) (rone R)) heps (absPlusOnePos R Lf)
  have db := derivBound R g (f x0) Lg hg epsM hepsM
  have cfd := continuousFromDeriv R f x0 Lf hf (DPair.fst db) (Pair.fst (DPair.snd db))
  cases (CompleteOrderedField.leTotal (field R) (DPair.fst cfd) (DPair.fst dqb)) with
  | Left hle =>
    exact (MkDPair (DPair.fst cfd) (MkPair (Pair.fst (DPair.snd cfd)) (\\x hx0 hxd => replace (\\z => rlt R (rabs R z) eps) (sym (subZeroRight R (chainTermA R g f x0 Lg x))) (chainBound R (rsub R (rsub R (g (f x)) (g (f x0))) (rmul R Lg (rsub R (f x) (f x0)))) (rsub R (f x) (f x0)) (rsub R x x0) epsM (radd R (rabs R Lf) (rone R)) eps (Pair.snd (DPair.snd db) (f x) (Pair.snd (DPair.snd cfd) x hx0 hxd)) (Pair.snd (DPair.snd dqb) x hx0 (ltLeTrans R (rabs R (rsub R x x0)) (DPair.fst cfd) (DPair.fst dqb) hxd hle)) hepsM (trans (CompleteOrderedField.mulComm (field R) epsM (radd R (rabs R Lf) (rone R))) (mulInvCancel R (radd R (rabs R Lf) (rone R)) eps (absPlusOneNe R Lf)))))))
  | Right hle =>
    exact (MkDPair (DPair.fst dqb) (MkPair (Pair.fst (DPair.snd dqb)) (\\x hx0 hxd => replace (\\z => rlt R (rabs R z) eps) (sym (subZeroRight R (chainTermA R g f x0 Lg x))) (chainBound R (rsub R (rsub R (g (f x)) (g (f x0))) (rmul R Lg (rsub R (f x) (f x0)))) (rsub R (f x) (f x0)) (rsub R x x0) epsM (radd R (rabs R Lf) (rone R)) eps (Pair.snd (DPair.snd db) (f x) (Pair.snd (DPair.snd cfd) x hx0 (ltLeTrans R (rabs R (rsub R x x0)) (DPair.fst dqb) (DPair.fst cfd) hxd hle))) (Pair.snd (DPair.snd dqb) x hx0 hxd) hepsM (trans (CompleteOrderedField.mulComm (field R) epsM (radd R (rabs R Lf) (rone R))) (mulInvCancel R (radd R (rabs R Lf) (rone R)) eps (absPlusOneNe R Lf)))))))

-- THE CHAIN RULE
-- Proof: By the algebraic identity, diffQuot(g.f, x0, x) = A(x) + g'*diffQuot(f, x0, x).
-- Taking limits:
--   lim diffQuot(g.f) = lim A(x) + g' * lim diffQuot(f)    [limitAdd + limitScalar]
--                      = 0       + g' * f'                   [chainTermALimit + hypothesis]
--                      = g' * f'                              [addZeroLeft]
derivChain : (R : Real) -> (g f : Carrier R -> Carrier R) -> (x0 Lf Lg : Carrier R) -> HasDerivative R f x0 Lf -> HasDerivative R g (f x0) Lg -> HasDerivative R (\\x => g (f x)) x0 (rmul R Lg Lf)
derivChain R g f x0 Lf Lg hf hg := by
  -- Reduce to proving the limit of A(x) + Lg*diffQuot(f, x0, x)
  suffices h : Limit R (\\x => radd R (chainTermA R g f x0 Lg x) (rmul R Lg (diffQuot R f x0 x))) x0 (rmul R Lg Lf) by
    exact limitExt R (\\x => radd R (chainTermA R g f x0 Lg x) (rmul R Lg (diffQuot R f x0 x))) (diffQuot R (\\y => g (f y)) x0) x0 (rmul R Lg Lf) (chainAlgId R g f x0 Lg) h
  -- Split the limit of a sum into two limits
  have hA := chainTermALimit R g f x0 Lg Lf hf hg
  have hScale := limitScalarAll R Lg (diffQuot R f x0) x0 Lf hf
  have hSum := limitAdd R (chainTermA R g f x0 Lg) (\\x => rmul R Lg (diffQuot R f x0 x)) x0 (rzero R) (rmul R Lg Lf) hA hScale
  -- Rewrite 0 + Lg*Lf = Lg*Lf
  exact replace (\\z => Limit R (\\x => radd R (chainTermA R g f x0 Lg x) (rmul R Lg (diffQuot R f x0 x))) x0 z) (addZeroLeft R (rmul R Lg Lf)) hSum
`;
