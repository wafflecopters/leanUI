export const NAT_MATH_TACTICS_CODE = `-- Nat Math (Tactics): same theorems as Nat Math, proven via tactics
-- Showcases induction, multi-tactic branches, intro, exact, and more

inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Equal : {A : Type} -> A -> A -> Type where
  refl : {A : Type} -> {a : A} -> Equal a a

plus : Nat -> Nat -> Nat
plus Zero m = m
plus (Succ n) m = Succ (plus n m)

mul : Nat -> Nat -> Nat
mul Zero m = Zero
mul (Succ n) m = plus m (mul n m)

one : Nat
one = Succ Zero

-- Utility helpers (pattern matching — 1-line utility proofs)
congSucc : {n m : Nat} -> Equal n m -> Equal (Succ n) (Succ m)
congSucc refl = refl

sym : {A : Type} -> {x y : A} -> Equal x y -> Equal y x
sym refl = refl

trans : {A : Type} -> {x y z : A} -> Equal x y -> Equal y z -> Equal x z
trans refl refl = refl

congPlusRight : {n m : Nat} -> (p : Nat) -> Equal n m -> Equal (plus p n) (plus p m)
congPlusRight Zero eq = eq
congPlusRight (Succ p) eq = congSucc (congPlusRight p eq)

congPlusLeft : {n m : Nat} -> (p : Nat) -> Equal n m -> Equal (plus n p) (plus m p)
congPlusLeft p refl = refl

------------------------------------------------------------
-- Addition properties via tactics (induction on first arg)
------------------------------------------------------------

plusZeroLeft : (n : Nat) -> Equal (plus Zero n) n := by
  intro n; exact refl

plusZeroRight : (n : Nat) -> Equal (plus n Zero) n := by
  intro n
  induction n with
  | Zero => exact refl
  | Succ n' IH => exact (congSucc IH)

plusSuccRight : (n m : Nat) -> Equal (plus n (Succ m)) (Succ (plus n m)) := by
  intro n
  induction n with
  | Zero =>
    intro m
    exact refl
  | Succ n' IH =>
    intro m
    exact (congSucc (IH m))

plusAssoc : (n m p : Nat) -> Equal (plus (plus n m) p) (plus n (plus m p)) := by
  intro n
  induction n with
  | Zero =>
    intros m p
    exact refl
  | Succ n' IH =>
    intros m p
    exact (congSucc (IH m p))

plusComm : (n m : Nat) -> Equal (plus n m) (plus m n) := by
  intro n
  induction n with
  | Zero =>
    intro m
    apply sym
    exact (plusZeroRight m)
  | Succ n' IH =>
    intro m
    apply trans
    apply congSucc
    exact (IH m)
    apply sym
    exact (plusSuccRight m n')

plusLeftComm : (m n p : Nat) -> Equal (plus m (plus n p)) (plus n (plus m p)) := by
  intros m n p
  apply trans
  exact (sym (plusAssoc m n p))
  apply trans
  exact (congPlusLeft p (plusComm m n))
  exact (plusAssoc n m p)

------------------------------------------------------------
-- Multiplication properties via tactics
------------------------------------------------------------

mulZeroLeft : (n : Nat) -> Equal (mul Zero n) Zero := by
  intro n; exact refl

mulZeroRight : (n : Nat) -> Equal (mul n Zero) Zero := by
  intro n
  induction n with
  | Zero => exact refl
  | Succ n' IH => exact IH

mulOneLeft : (n : Nat) -> Equal (mul one n) n := by
  intro n; exact (plusZeroRight n)

mulOneRight : (n : Nat) -> Equal (mul n one) n := by
  intro n
  induction n with
  | Zero => exact refl
  | Succ n' IH => exact (congSucc IH)

mulSuccRight : (n m : Nat) -> Equal (mul n (Succ m)) (plus n (mul n m)) := by
  intro n
  induction n with
  | Zero =>
    intro m
    exact refl
  | Succ n' IH =>
    intro m
    exact (congSucc (trans (congPlusRight m (IH m)) (plusLeftComm m n' (mul n' m))))

mulComm : (n m : Nat) -> Equal (mul n m) (mul m n) := by
  intro n
  induction n with
  | Zero =>
    intro m
    exact (sym (mulZeroRight m))
  | Succ n' IH =>
    intro m
    exact (trans (congPlusRight m (IH m)) (sym (mulSuccRight m n')))

mulDistribRight : (n m p : Nat) -> Equal (mul (plus n m) p) (plus (mul n p) (mul m p)) := by
  intro n
  induction n with
  | Zero =>
    intros m p
    exact refl
  | Succ n' IH =>
    intros m p
    exact (trans (congPlusRight p (IH m p)) (sym (plusAssoc p (mul n' p) (mul m p))))

mulAssoc : (n m p : Nat) -> Equal (mul (mul n m) p) (mul n (mul m p)) := by
  intro n
  induction n with
  | Zero =>
    intros m p
    exact refl
  | Succ n' IH =>
    intros m p
    exact (trans (mulDistribRight m (mul n' m) p) (congPlusRight (mul m p) (IH m p)))

mulDistribLeft : (n m p : Nat) -> Equal (mul n (plus m p)) (plus (mul n m) (mul n p)) := by
  intro n
  induction n with
  | Zero =>
    intros m p; exact refl
  | Succ n' IH =>
    intros m p
    apply trans
    exact (congPlusRight (plus m p) (IH m p))
    apply trans
    exact (plusAssoc m p (plus (mul n' m) (mul n' p)))
    apply trans
    exact (congPlusRight m (plusLeftComm p (mul n' m) (mul n' p)))
    exact (sym (plusAssoc m (mul n' m) (plus p (mul n' p))))

------------------------------------------------------------
-- Triangle Sum: 2 * sum(1..n) = n * (n + 1)
------------------------------------------------------------

sum : Nat -> Nat
sum Zero = Zero
sum (Succ n) = plus (Succ n) (sum n)

-- Triangle sum proof: 2 * sum(1..n) = n * (n + 1)
-- Best-practice: incremental proof with apply/exact, not nested terms
doubleSum : (n : Nat) -> Equal (plus (sum n) (sum n)) (mul n (Succ n)) := by
  intro n
  induction n with
  | Zero => exact refl
  | Succ n' IH =>
    -- Goal: (n'+1) + sum(n') + (n'+1) + sum(n') = (n'+1) * (n'+2)
    apply trans
    exact (plusAssoc (Succ n') (sum n') (plus (Succ n') (sum n')))
    apply trans
    apply congPlusRight
    exact (plusLeftComm (sum n') (Succ n') (sum n'))
    apply trans
    apply congPlusRight
    apply congPlusRight
    exact IH
    apply trans
    apply congSucc
    exact (plusSuccRight n' (plus n' (mul n' (Succ n'))))
    apply congPlusRight
    apply sym
    exact (mulSuccRight n' (Succ n'))

------------------------------------------------------------
-- Leq: ordering on Nat
------------------------------------------------------------

inductive Leq : Nat -> Nat -> Type where
  LeqZero : {n : Nat} -> Leq Zero n
  LeqSucc : {n m : Nat} -> Leq n m -> Leq (Succ n) (Succ m)

leqRefl : (n : Nat) -> Leq n n := by
  intro n
  induction n with
  | Zero => exact LeqZero
  | Succ n' IH => exact (LeqSucc IH)

leqTrans : {a b c : Nat} -> Leq a b -> Leq b c -> Leq a c := by
  intros a b c hab hbc
  cases hab with
  | LeqZero => exact LeqZero
  | LeqSucc p =>
    cases hbc with
    | LeqSucc q => exact (LeqSucc (leqTrans p q))

leqAntisym : {a b : Nat} -> Leq a b -> Leq b a -> Equal a b := by
  intros a b hab hba
  cases hab with
  | LeqZero =>
    cases hba with
    | LeqZero => exact refl
  | LeqSucc p =>
    cases hba with
    | LeqSucc q => exact (congSucc (leqAntisym p q))


record DPair (A : Type) (fn : A -> Type) where
  fst : A
  snd : fn fst

succInj: {u v : Nat} -> Equal (Succ u) (Succ v) -> Equal u v
succInj refl = refl

succCong: {u v : Nat} -> Equal u v -> Equal (Succ u) (Succ v)
succCong refl = refl

leqImpliesSum : (a b : Nat) -> Leq a b -> DPair Nat (\\n => Equal b (plus a n))
leqImpliesSum Zero b LeqZero = MkDPair b refl
leqImpliesSum (Succ a) (Succ b) (LeqSucc leq) with leqImpliesSum a b leq
  | MkDPair n pf => MkDPair n (succCong pf)

sigmaSumStartCount : (start count : Nat) -> (fn : (index : Nat) -> Nat) -> Nat
sigmaSumStartCount start Zero fn = Zero
sigmaSumStartCount start (Succ count) fn = plus (fn (plus start count)) (sigmaSumStartCount start count fn)

-- Helper lemma for sigmaSumStartCountAdditive inductive step
sigmaSumAddSuccHelper : (start count : Nat) -> (f g : (index : Nat) -> Nat) ->
  Equal (plus (sigmaSumStartCount start count f) (sigmaSumStartCount start count g)) (sigmaSumStartCount start count (\\n => plus (f n) (g n))) ->
  Equal (plus (sigmaSumStartCount start (Succ count) f) (sigmaSumStartCount start (Succ count) g)) (sigmaSumStartCount start (Succ count) (\\n => plus (f n) (g n))) := by
  intros start count f g recPrf
  -- Rearrange: plus (plus (f x) sumF) (plus (g x) sumG) = plus (plus (f x) (g x)) (plus sumF sumG)
  apply trans
  exact (plusAssoc (f (plus start count)) (sigmaSumStartCount start count f) (plus (g (plus start count)) (sigmaSumStartCount start count g)))
  apply trans
  apply congPlusRight
  exact (plusLeftComm (sigmaSumStartCount start count f) (g (plus start count)) (sigmaSumStartCount start count g))
  apply trans
  exact (sym (plusAssoc (f (plus start count)) (g (plus start count)) (plus (sigmaSumStartCount start count f) (sigmaSumStartCount start count g))))
  apply congPlusRight
  exact recPrf

sigmaSumStartCountAdditive : (start count : Nat) ->
  (f g : (index : Nat) -> Nat) ->
  Equal (plus (sigmaSumStartCount start count f) (sigmaSumStartCount start count g)) (sigmaSumStartCount start count (\\n => plus (f n) (g n)))
sigmaSumStartCountAdditive start Zero f g = refl
sigmaSumStartCountAdditive start (Succ count) f g with sigmaSumStartCountAdditive start count f g
  | recPrf => sigmaSumAddSuccHelper start count f g recPrf

inductive Void : Type where

zeroNeqSucc : {n : Nat} -> (Equal Zero (Succ n) -> Void)

inductive DecEq : {A : Type} -> (a b : A) -> Type where
  Yes : {A : Type} -> {a b : A} -> Equal a b -> DecEq a b
  No : {A : Type} -> {a b : A} -> (Equal a b -> Void) -> DecEq a b

decEqNat : (x y : Nat) -> DecEq x y
decEqNat Zero Zero = Yes refl
decEqNat Zero (Succ y) = No zeroNeqSucc
decEqNat (Succ x) Zero = No (\\eq => zeroNeqSucc (sym eq))
decEqNat (Succ x) (Succ y) with decEqNat x y
  | Yes eq => Yes (succCong eq)
  | No neq => No (\\eq => neq (succInj eq))

LessThan : Nat -> Nat -> Type
LessThan a b = Leq (Succ a) b

inductive Either : Type -> Type -> Type where
  inl : {L R : Type} -> L -> Either L R
  inr : {L R : Type} -> R -> Either L R

decGeq : (a b : Nat) -> Either (Leq a b) (LessThan b a)
decGeq Zero b = inl LeqZero
decGeq (Succ a) Zero = inr (LeqSucc (LeqZero {n:=a}))
decGeq (Succ a) (Succ b) with decGeq a b
  | inl aLeqB => inl (LeqSucc aLeqB)
  | inr bLeA => inr (LeqSucc bLeA)

sigmaSum : (start end : Nat) -> (fn : (index : Nat) -> Nat) -> Nat
sigmaSum start end fn with decGeq start end
  | inl startLeqEnd with leqImpliesSum start end startLeqEnd
    | MkDPair count _ => sigmaSumStartCount start count fn
  | inr endLeStart => Zero
`;
