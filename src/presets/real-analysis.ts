export const REAL_ANALYSIS_CODE = `-- Real Analysis: algebraic hierarchy, ordered fields, and epsilon-delta limits
-- Builds from scratch to the real numbers and proves lim(f+g) = lim(f) + lim(g)

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
  -- Absolute value and triangle inequality
  abs : A -> A
  absTriangle : (a b : A) -> le (abs (add a b)) (add (abs a) (abs b))
  -- Positivity axioms
  zeroLeOne : le zero one
  zeroNeOne : Equal zero one -> Void
  invPos : (a : A) -> le zero a -> (Equal a zero -> Void) -> le zero (inv a)

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
EpsDeltaWitness R f x0 L eps delta = Pair (rlt R (rzero R) delta) ((x : Carrier R) -> rlt R (rabs R (rsub R x x0)) delta -> rlt R (rabs R (rsub R (f x) L)) eps)

-- A proof that lim_{x -> x0} f(x) = L.
-- For every epsilon > 0, there exists delta > 0 such that
-- for all x, |x - x0| < delta implies |f(x) - L| < epsilon.
record Limit (R : Real) (f : Carrier R -> Carrier R) (x0 : Carrier R) (L : Carrier R) where
  eps_delta : (eps : Carrier R) -> rlt R (rzero R) eps ->
              DPair (Carrier R) (EpsDeltaWitness R f x0 L eps)

------------------------------------------------------------
-- Algebraic lemmas
------------------------------------------------------------

addZeroLeft : (R : Real) -> (a : Carrier R) -> Equal (radd R (rzero R) a) a
addZeroLeft R a = trans (CompleteOrderedField.addComm (field R) (rzero R) a) (CompleteOrderedField.addZeroRight (field R) a)

negLeft : (R : Real) -> (a : Carrier R) -> Equal (radd R (rneg R a) a) (rzero R)
negLeft R a = trans (CompleteOrderedField.addComm (field R) (rneg R a) a) (CompleteOrderedField.negRight (field R) a)

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
addCancelRightHelper : (R : Real) -> (x c : Carrier R) -> Equal (radd R (radd R x c) (rneg R c)) x
addCancelRightHelper R x c = (trans (CompleteOrderedField.addAssoc (field R) x c (rneg R c)) (trans (cong (\\z => radd R x z) (CompleteOrderedField.negRight (field R) c)) (CompleteOrderedField.addZeroRight (field R) x)))

addCancelRight : (R : Real) -> (a b c : Carrier R) -> Equal (radd R a c) (radd R b c) -> Equal a b
addCancelRight R a b c h = (trans (sym (addCancelRightHelper R a c)) (trans (cong (\\z => radd R z (rneg R c)) h) (addCancelRightHelper R b c)))

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
halfPlusHalf : (R : Real) -> Equal (radd R (rhalf R) (rhalf R)) (rone R)
halfPlusHalf R = (trans (trans (cong (\\z => radd R z z) (sym (CompleteOrderedField.mulOneLeft (field R) (rhalf R)))) (sym (CompleteOrderedField.distribRight (field R) (rone R) (rone R) (rhalf R)))) (CompleteOrderedField.mulInvRight (field R) (rtwo R) (twoNeZero R)))

-- (1/2)*e + (1/2)*e = e
halfMulEps : (R : Real) -> (e : Carrier R) -> Equal (radd R (rmul R (rhalf R) e) (rmul R (rhalf R) e)) e
halfMulEps R e = (trans (sym (CompleteOrderedField.distribRight (field R) (rhalf R) (rhalf R) e)) (trans (cong (\\z => rmul R z e) (halfPlusHalf R)) (CompleteOrderedField.mulOneLeft (field R) e)))

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
halfMulEpsPos R e hlt = MkPair (halfMulEpsLe R e (Pair.fst hlt)) (halfMulEpsNe R e (Pair.fst hlt) (Pair.snd hlt))

------------------------------------------------------------
-- Negation distributes over addition: -(a+b) = (-a)+(-b)
------------------------------------------------------------

addSumNeg : (R : Real) -> (a b : Carrier R) -> Equal (radd R (radd R a b) (rneg R a)) b
addSumNeg R a b = (trans (CompleteOrderedField.addComm (field R) (radd R a b) (rneg R a)) (trans (sym (CompleteOrderedField.addAssoc (field R) (rneg R a) a b)) (trans (cong (\\z => radd R z b) (negLeft R a)) (addZeroLeft R b))))

negAddCancel : (R : Real) -> (a b : Carrier R) -> Equal (radd R (radd R a b) (radd R (rneg R a) (rneg R b))) (rzero R)
negAddCancel R a b = (trans (sym (CompleteOrderedField.addAssoc (field R) (radd R a b) (rneg R a) (rneg R b))) (trans (cong (\\z => radd R z (rneg R b)) (addSumNeg R a b)) (CompleteOrderedField.negRight (field R) b)))

negUnique : (R : Real) -> (a b : Carrier R) -> Equal (radd R a b) (rzero R) -> Equal b (rneg R a)
negUnique R a b h = (trans (sym (addZeroLeft R b)) (trans (cong (\\z => radd R z b) (sym (negLeft R a))) (trans (CompleteOrderedField.addAssoc (field R) (rneg R a) a b) (trans (cong (\\z => radd R (rneg R a) z) h) (CompleteOrderedField.addZeroRight (field R) (rneg R a))))))

negAdd : (R : Real) -> (a b : Carrier R) -> Equal (rneg R (radd R a b)) (radd R (rneg R a) (rneg R b))
negAdd R a b = sym (negUnique R (radd R a b) (radd R (rneg R a) (rneg R b)) (negAddCancel R a b))

------------------------------------------------------------
-- (a+b)-(c+d) = (a-c)+(b-d)
------------------------------------------------------------

fourTermRearrange : (R : Real) -> (a b c d : Carrier R) -> Equal (radd R (radd R a b) (radd R c d)) (radd R (radd R a c) (radd R b d))
fourTermRearrange R a b c d = (trans (CompleteOrderedField.addAssoc (field R) a b (radd R c d)) (trans (cong (\\z => radd R a z) (trans (CompleteOrderedField.addComm (field R) b (radd R c d)) (trans (CompleteOrderedField.addAssoc (field R) c d b) (cong (\\z => radd R c z) (CompleteOrderedField.addComm (field R) d b))))) (sym (CompleteOrderedField.addAssoc (field R) a c (radd R b d)))))

subAddSub : (R : Real) -> (a b c d : Carrier R) -> Equal (rsub R (radd R a b) (radd R c d)) (radd R (rsub R a c) (rsub R b d))
subAddSub R a b c d = trans (cong (\\z => radd R (radd R a b) z) (negAdd R c d)) (fourTermRearrange R a b (rneg R c) (rneg R d))

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

-- Pick the smaller delta using leTotal (inlined with eitherElim)
-- Each case inlines boundFnLeft/boundFnRight: uses convertEps + coreEstimate + ltLeTrans
pickDelta : (R : Real) -> (f g : Carrier R -> Carrier R) -> (x0 L M eps d1 d2 : Carrier R) -> rlt R (rzero R) d1 -> rlt R (rzero R) d2 -> ((x : Carrier R) -> rlt R (rabs R (rsub R x x0)) d1 -> rlt R (rabs R (rsub R (f x) L)) (rmul R (rhalf R) eps)) -> ((x : Carrier R) -> rlt R (rabs R (rsub R x x0)) d2 -> rlt R (rabs R (rsub R (g x) M)) (rmul R (rhalf R) eps)) -> Either (rle R d1 d2) (rle R d2 d1) -> DPair (Carrier R) (EpsDeltaWitness R (\\x => radd R (f x) (g x)) x0 (radd R L M) eps)
pickDelta R f g x0 L M eps d1 d2 hd1 hd2 hf hg tot = eitherElim (\\hle => MkDPair d1 (MkPair hd1 (\\x hx => convertEps R eps (rabs R (rsub R (radd R (f x) (g x)) (radd R L M))) (coreEstimate R f g x0 L M (rmul R (rhalf R) eps) x (hf x hx) (hg x (ltLeTrans R (rabs R (rsub R x x0)) d1 d2 hx hle)))))) (\\hle => MkDPair d2 (MkPair hd2 (\\x hx => convertEps R eps (rabs R (rsub R (radd R (f x) (g x)) (radd R L M))) (coreEstimate R f g x0 L M (rmul R (rhalf R) eps) x (hf x (ltLeTrans R (rabs R (rsub R x x0)) d2 d1 hx hle)) (hg x hx))))) tot

-- Assemble the eps-delta proof for the sum
limitAddEpsDelta : (R : Real) -> (f g : Carrier R -> Carrier R) -> (x0 L M : Carrier R) -> Limit R f x0 L -> Limit R g x0 M -> (eps : Carrier R) -> rlt R (rzero R) eps -> DPair (Carrier R) (EpsDeltaWitness R (\\x => radd R (f x) (g x)) x0 (radd R L M) eps)
limitAddEpsDelta R f g x0 L M limF limG eps heps = (pickDelta R f g x0 L M eps (DPair.fst (Limit.eps_delta limF (rmul R (rhalf R) eps) (halfMulEpsPos R eps heps))) (DPair.fst (Limit.eps_delta limG (rmul R (rhalf R) eps) (halfMulEpsPos R eps heps))) (Pair.fst (DPair.snd (Limit.eps_delta limF (rmul R (rhalf R) eps) (halfMulEpsPos R eps heps)))) (Pair.fst (DPair.snd (Limit.eps_delta limG (rmul R (rhalf R) eps) (halfMulEpsPos R eps heps)))) (Pair.snd (DPair.snd (Limit.eps_delta limF (rmul R (rhalf R) eps) (halfMulEpsPos R eps heps)))) (Pair.snd (DPair.snd (Limit.eps_delta limG (rmul R (rhalf R) eps) (halfMulEpsPos R eps heps)))) (CompleteOrderedField.leTotal (field R) (DPair.fst (Limit.eps_delta limF (rmul R (rhalf R) eps) (halfMulEpsPos R eps heps))) (DPair.fst (Limit.eps_delta limG (rmul R (rhalf R) eps) (halfMulEpsPos R eps heps)))))

-- lim_{x->x0} f(x) = L  and  lim_{x->x0} g(x) = M
--   =>  lim_{x->x0} (f(x) + g(x)) = L + M
limitAdd : (R : Real) -> (f g : Carrier R -> Carrier R) -> (x0 L M : Carrier R) -> Limit R f x0 L -> Limit R g x0 M -> Limit R (\\x => radd R (f x) (g x)) x0 (radd R L M)
limitAdd R f g x0 L M limF limG = MkLimit (limitAddEpsDelta R f g x0 L M limF limG)
`;
