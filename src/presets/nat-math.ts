export const NAT_MATH_CODE = `-- Nat Math: semiring, triangle sum, and ordering proofs by pattern matching
-- Includes all 12 semiring properties, sum(1..n) = n(n+1)/2, and Leq properties

@syntax \\N
inductive Nat : Type where
  @syntax 0
  Zero : Nat
  @syntax $0\\prime
  Succ : Nat -> Nat

@syntax $0 =_{$A} $1
inductive Equal : {A : Type} -> A -> A -> Type where
  refl : {A : Type} -> {a : A} -> Equal a a

@syntax $0 + $1
plus : Nat -> Nat -> Nat
plus Zero m = m
plus (Succ n) m = Succ (plus n m)

@syntax $0 \\cdot $1
mul : Nat -> Nat -> Nat
mul Zero m = Zero
mul (Succ n) m = plus m (mul n m)

@syntax 1 @becomes Succ Zero
one : Nat
one = Succ Zero

-- Helpers
congSucc : {n m : Nat} -> Equal n m -> Equal (Succ n) (Succ m)
congSucc refl = refl

succInj : {n m : Nat} -> Equal (Succ n) (Succ m) -> Equal n m
succInj refl = refl

sym : {A : Type} -> {x y : A} -> Equal x y -> Equal y x
sym refl = refl

trans : {A : Type} -> {x y z : A} -> Equal x y -> Equal y z -> Equal x z
trans refl refl = refl

-- Addition properties
plusZeroLeft : (n : Nat) -> Equal (plus Zero n) n
plusZeroLeft n = refl

plusZeroRight : (n : Nat) -> Equal (plus n Zero) n
plusZeroRight Zero = refl
plusZeroRight (Succ n) = congSucc (plusZeroRight n)

plusSuccRight : (n m : Nat) -> Equal (plus n (Succ m)) (Succ (plus n m))
plusSuccRight Zero m = refl
plusSuccRight (Succ n) m = congSucc (plusSuccRight n m)

plusAssoc : (n m p : Nat) -> Equal (plus (plus n m) p) (plus n (plus m p))
plusAssoc Zero m p = refl
plusAssoc (Succ n) m p = congSucc (plusAssoc n m p)

plusComm : (n m : Nat) -> Equal (plus n m) (plus m n)
plusComm Zero m = sym (plusZeroRight m)
plusComm (Succ n) m = trans (congSucc (plusComm n m)) (sym (plusSuccRight m n))

congPlusRight : {n m : Nat} -> (p : Nat) -> Equal n m -> Equal (plus p n) (plus p m)
congPlusRight Zero eq = eq
congPlusRight (Succ p) eq = congSucc (congPlusRight p eq)

congPlusLeft : {n m : Nat} -> (p : Nat) -> Equal n m -> Equal (plus n p) (plus m p)
congPlusLeft p refl = refl

plusLeftComm : (m n p : Nat) -> Equal (plus m (plus n p)) (plus n (plus m p))
plusLeftComm m n p = trans (sym (plusAssoc m n p)) (trans (congPlusLeft p (plusComm m n)) (plusAssoc n m p))

succPlusOneLeft : (n : Nat) -> Equal (Succ n) (plus one n)
succPlusOneLeft n = refl

succPlusOneRight : (n : Nat) -> Equal (Succ n) (plus n one)
succPlusOneRight n = plusComm one n

-- Multiplication properties
mulZeroLeft : (n : Nat) -> Equal (mul Zero n) Zero
mulZeroLeft n = refl

mulZeroRight : (n : Nat) -> Equal (mul n Zero) Zero
mulZeroRight Zero = refl
mulZeroRight (Succ n) = mulZeroRight n

mulOneLeft : (n : Nat) -> Equal (mul one n) n
mulOneLeft n = plusZeroRight n

mulOneRight : (n : Nat) -> Equal (mul n one) n
mulOneRight Zero = refl
mulOneRight (Succ n) = congSucc (mulOneRight n)

mulSuccRight : (n m : Nat) -> Equal (mul n (Succ m)) (plus n (mul n m))
mulSuccRight Zero m = refl
mulSuccRight (Succ n) m = congSucc (trans (congPlusRight m (mulSuccRight n m)) (plusLeftComm m n (mul n m)))

mulComm : (n m : Nat) -> Equal (mul n m) (mul m n)
mulComm Zero m = sym (mulZeroRight m)
mulComm (Succ n) m = trans (congPlusRight m (mulComm n m)) (sym (mulSuccRight m n))

mulDistribRight : (n m p : Nat) -> Equal (mul (plus n m) p) (plus (mul n p) (mul m p))
mulDistribRight Zero m p = refl
mulDistribRight (Succ n) m p = trans (congPlusRight p (mulDistribRight n m p)) (sym (plusAssoc p (mul n p) (mul m p)))

mulAssoc : (n m p : Nat) -> Equal (mul (mul n m) p) (mul n (mul m p))
mulAssoc Zero m p = refl
mulAssoc (Succ n) m p = trans (mulDistribRight m (mul n m) p) (congPlusRight (mul m p) (mulAssoc n m p))

mulDistribLeft : (n m p : Nat) -> Equal (mul n (plus m p)) (plus (mul n m) (mul n p))
mulDistribLeft Zero m p = refl
mulDistribLeft (Succ n) m p = trans (congPlusRight (plus m p) (mulDistribLeft n m p)) (trans (plusAssoc m p (plus (mul n m) (mul n p))) (trans (congPlusRight m (plusLeftComm p (mul n m) (mul n p))) (sym (plusAssoc m (mul n m) (plus p (mul n p))))))

-- Semiring record and instance
record Semiring (A : Type) where
  constructor MkSemiring
  add : A -> A -> A
  mul : A -> A -> A
  zero : A
  oneS : A
  addZeroLeft : (a : A) -> Equal (add zero a) a
  addZeroRight : (a : A) -> Equal (add a zero) a
  addComm : (a b : A) -> Equal (add a b) (add b a)
  addAssoc : (a b c : A) -> Equal (add (add a b) c) (add a (add b c))
  mulZeroL : (a : A) -> Equal (mul zero a) zero
  mulZeroR : (a : A) -> Equal (mul a zero) zero
  mulOneL : (a : A) -> Equal (mul oneS a) a
  mulOneR : (a : A) -> Equal (mul a oneS) a
  mulComm : (a b : A) -> Equal (mul a b) (mul b a)
  mulAssoc : (a b c : A) -> Equal (mul (mul a b) c) (mul a (mul b c))
  distribL : (a b c : A) -> Equal (mul a (add b c)) (add (mul a b) (mul a c))
  distribR : (a b c : A) -> Equal (mul (add a b) c) (add (mul a c) (mul b c))

natSemiring : Semiring Nat
natSemiring = MkSemiring plus mul Zero one plusZeroLeft plusZeroRight plusComm plusAssoc mulZeroLeft mulZeroRight mulOneLeft mulOneRight mulComm mulAssoc mulDistribLeft mulDistribRight

------------------------------------------------------------
-- Leq: ordering on Nat with reflexivity, transitivity, antisymmetry
------------------------------------------------------------

@syntax $0 \\leq $1
inductive Leq : Nat -> Nat -> Type where
  LeqZero : {n : Nat} -> Leq Zero n
  LeqSucc : {n m : Nat} -> Leq n m -> Leq (Succ n) (Succ m)

-- Reflexivity: a <= a
leqRefl : (n : Nat) -> Leq n n
leqRefl Zero = LeqZero
leqRefl (Succ n) = LeqSucc (leqRefl n)

-- Transitivity: a <= b /\\ b <= c => a <= c
leqTrans : {a b c : Nat} -> Leq a b -> Leq b c -> Leq a c
leqTrans LeqZero _ = LeqZero
leqTrans (LeqSucc p) (LeqSucc q) = LeqSucc (leqTrans p q)

-- Antisymmetry: a <= b /\\ b <= a => a = b
leqAntisym : {a b : Nat} -> Leq a b -> Leq b a -> Equal a b
leqAntisym LeqZero LeqZero = refl
leqAntisym (LeqSucc p) (LeqSucc q) = congSucc (leqAntisym p q)

------------------------------------------------------------
-- Subtraction and minus-Leq lemmas
------------------------------------------------------------

@syntax $0 - $1
minus : Nat -> Nat -> Nat
minus a Zero = a
minus Zero _ = Zero
minus (Succ a) (Succ b) = minus a b

minusSucc : {i n : Nat} -> Leq i n -> Equal (minus (Succ n) i) (Succ (minus n i))
minusSucc LeqZero = refl
minusSucc (LeqSucc l) = minusSucc l

minusEqSuccMinusSucc : {a b : Nat} -> Equal (minus a b) (minus (Succ a) (Succ b))
minusEqSuccMinusSucc {a} {b} = refl

plusMinusCancel : {i n : Nat} -> Leq i n -> Equal (plus i (minus n i)) n
plusMinusCancel LeqZero = refl
plusMinusCancel (LeqSucc l) = congSucc (plusMinusCancel l)

minusSelf : {n : Nat} -> Equal (minus n n) Zero
minusSelf {n:=Zero} = refl
minusSelf {n:=Succ n} = trans (sym minusEqSuccMinusSucc) minusSelf

-- Leq weakening: i <= n implies i <= Succ n
leqSuccRight : {i n : Nat} -> Leq i n -> Leq i (Succ n)
leqSuccRight LeqZero = LeqZero
leqSuccRight (LeqSucc l) = LeqSucc (leqSuccRight l)

-- General congruence (implicits first for tactic compatibility)
cong : {A B : Type} -> {x y : A} -> (f : A -> B) -> Equal x y -> Equal (f x) (f y)
cong f refl = refl

replace : {A : Type} -> {x y : A} -> (P : A -> Type) -> Equal x y -> P x -> P y
replace P refl px = px

-- Key helper: plus i (minus (Succ n) i) = Succ n (when Leq i n)
plusMinusSucc : {i n : Nat} -> Leq i n -> Equal (plus i (minus (Succ n) i)) (Succ n)
plusMinusSucc LeqZero = refl
plusMinusSucc (LeqSucc l) = congSucc (plusMinusSucc l)

------------------------------------------------------------
-- Summation: sum, sumStartCount, splitting
------------------------------------------------------------

sumStartCount : (start count : Nat) -> (Nat -> Nat) -> Nat
sumStartCount start Zero f = Zero
sumStartCount start (Succ k) f = plus (sumStartCount start k f) (f (plus start k))

sumStartCountSplit : (s k : Nat) -> (f : Nat -> Nat) -> Equal (sumStartCount s (Succ k) f) (plus (sumStartCount s k f) (f (plus s k)))
sumStartCountSplit s k f = refl

sumStartCountZero : (s : Nat) -> (f : Nat -> Nat) -> Equal (sumStartCount s Zero f) Zero
sumStartCountZero s f = refl

sumStartCountOne : (s : Nat) -> (f : Nat -> Nat) -> Equal (sumStartCount s (Succ Zero) f) (f s)
sumStartCountOne s f = cong f (plusZeroRight s)

@syntax \\sum_{$0 = $1}^{$2} $3 @becomes sum $$1 $$2 (\\$0 => $$3)
sum : (start end : Nat) -> (Nat -> Nat) -> Nat
sum start end f = sumStartCount start (minus (Succ end) start) f

-- Summation splitting: sum from i to (n+1) = sum from i to n + f(n+1)
summationSplit : (i n : Nat) -> Leq i n -> (f : Nat -> Nat) -> Equal (sum i (Succ n) f) (plus (sum i n f) (f (Succ n))) := by
  intros i n l f
  -- Step 1: rewrite the count in sumStartCount using minusSucc
  apply trans
  exact (cong (\\k => sumStartCount i k f) (minusSucc (leqSuccRight l)))
  -- Step 2: rewrite f(plus i (minus (Succ n) i)) to f(Succ n)
  apply congPlusRight
  exact (cong f (plusMinusSucc l))

summationBase : (i : Nat) -> (f : Nat -> Nat) -> Equal (sum i i f) (f i) := by
  intros i f
  unfold sum
  rewrite minusSucc
  rewrite minusSelf
  rewrite sumStartCountOne
  exact refl

@syntax 2 @becomes Succ (Succ Zero)
two : Nat
two = Succ (Succ Zero)

triangleSum : (n : Nat) -> Equal (mul two (sum Zero n (\\i => i))) (mul (plus n one) n) := by
  ?TODO
`;
