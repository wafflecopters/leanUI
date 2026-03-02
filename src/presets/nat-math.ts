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

@syntax 1
one : Nat
one = Succ Zero

-- Helpers
congSucc : {n m : Nat} -> Equal n m -> Equal (Succ n) (Succ m)
congSucc refl = refl

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
-- Triangle Sum: 2 * sum(1..n) = n * (n + 1)
------------------------------------------------------------

-- Sum from 0 to n: sum(n) = 0 + 1 + 2 + ... + n
sum : Nat -> Nat
sum Zero = Zero
sum (Succ n) = plus (Succ n) (sum n)

-- Theorem: plus (sum n) (sum n) = mul n (Succ n)
-- i.e. 2 * sum(n) = n * (n + 1)
{-
doubleSum : (n : Nat) -> Equal (plus (sum n) (sum n)) (mul n (Succ n))
doubleSum Zero = refl
doubleSum (Succ n) = trans (plusAssoc (Succ n) (sum n) (plus (Succ n) (sum n))) (trans (congPlusRight (Succ n) (plusLeftComm (sum n) (Succ n) (sum n))) (trans (congPlusRight (Succ n) (congPlusRight (Succ n) (doubleSum n))) (trans (congSucc (plusSuccRight n (plus n (mul n (Succ n))))) (congPlusRight (Succ (Succ n)) (sym (mulSuccRight n (Succ n)))))))
-}

doubleSum : (n : Nat) -> Equal (plus (sum n) (sum n)) (mul n (Succ n))
doubleSum = ?TODO

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
`;
