export const GRAB_BAG_CODE = `inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

plus : Nat -> Nat -> Nat
plus Zero b = b
plus (Succ a) b = Succ (plus a b)

inductive Vec : Type -> Nat -> Type where
  VNil : {A: Type} -> Vec A Zero
  VCons : {A : Type} -> {n : Nat} -> A -> Vec A n -> Vec A (Succ n)

inductive Fin : Nat -> Type where
  FZero : {n : Nat} -> Fin (Succ n)
  FSucc : {n : Nat} -> Fin n -> Fin (Succ n)

nth : {A : Type} -> {n : Nat} -> Vec A n -> Fin n -> A
nth (VCons h _) FZero = h
nth (VCons h tail) (FSucc f) = nth tail f

inductive Void : Type where

absurd : {A : Type} -> Void -> A

inductive Equal : {u : ULevel} -> {A : Type u} -> A -> A -> Type where
  refl : {u : ULevel} -> {A : Type u} -> {a : A} -> Equal a a

zeroNeqSucc : {n : Nat} -> Equal Zero (Succ n) -> Void
zeroNeqSucc refl = #absurd

double : Nat -> Nat
double n = ?sorry

right : {A : Type} -> {B : Type} -> B -> A -> B
right {A} b = \\(x: A) => b

qux : Type
qux = Nat

qux' : Nat -> Type
qux' n = Nat

const : {A : Type} -> {B : Type} -> A -> B -> A
const a = \\ _ => a

swap : {A B C : Type} -> (f : A -> B -> C) -> B -> A -> C
swap f = \\ x y => f y x

vecConcat : {A : Type} -> {a b : Nat} -> Vec A a -> Vec A b -> Vec A (plus a b)
vecConcat VNil v = v
vecConcat (VCons h tail) v = VCons h (vecConcat tail v)

vecConcat' : {A : Type} -> {a b : Nat} -> Vec A a -> Vec A b -> Vec A (plus a b)
vecConcat' VNil v = v
vecConcat' {a := Succ p} (VCons h tail) v = VCons h (vecConcat' {a := p} tail v)

vecConcat'' : {A : Type} -> {a b : Nat} -> Vec A a -> Vec A b -> Vec A (plus a b)
vecConcat'' VNil v = v
vecConcat'' {a:=Succ p} (VCons h tail) v = swap VCons (vecConcat'' {a:=(\\x => x) p} tail v) h

fox : Nat
fox = (\\x => x) Zero

sym : {A : Type} -> {u v : A} -> Equal u v -> Equal v u
sym refl = refl

trans : {A : Type} -> {u v w : A} -> Equal u v -> Equal v w -> Equal u w
trans refl refl = refl

cong : {A B : Type} -> {u v : A} -> {f : A -> B} -> Equal u v -> Equal (f u) (f v)
cong refl = refl

replace : {x y : Type} -> {f : Type -> Type} -> Equal x y -> f x -> f y
replace refl fx = fx

record Pair (A B : Type) : Type where
  constructor MkPair
  fst: A
  snd: B

inductive DPairInd : {u v : ULevel} -> (A : Type u) -> (B : A -> Type v) -> Type (UMax u v) where
  MkDPairInd: {u v : ULevel} -> {A : Type u} -> {B : A -> Type v} -> (a : A) -> B a -> DPairInd A B

record DPair {u v : ULevel} (A : Type u) (B : A -> Type v) : Type (UMax u v) where
  constructor MkDPair
  dfst: A
  dsnd: B dfst

record Semigroup {u : ULevel} (A : Type u) where
  op : A -> A -> A
  assoc : (a b c : A) -> Equal (op (op a b) c) (op a (op b c))

record Monoid {u : ULevel} (A : Type u) : Type u extends Semigroup {u} A where
  e : A
  identLeft : (a : A) -> Equal (op e a) a
  identRight : (a : A) -> Equal (op a e) a

record Group {u : ULevel} (A : Type u) : Type u extends Monoid A where
  inv : A -> A
  invLeft : (a : A) -> Equal (op (inv a) a) e
  invRight : (a : A) -> Equal (op a (inv a)) e

plusZeroRight : {n : Nat} -> Equal n (plus n Zero)
plusZeroRight {n:=Zero} = refl {A:=Nat} {a:=Zero}
plusZeroRight {n:=Succ n} = let rec = plusZeroRight {n} in
  cong rec

plusComm : {a b : Nat} -> Equal (plus a b) (plus b a)
plusComm {a:=Zero}   {b:=Zero}   = refl
plusComm {a:=Succ a} {b:=Zero}   = let tmp = plusZeroRight in ?B
plusComm {a:=Zero}   {b:=Succ b} = ?C
plusComm {a:=Succ a} {b:=Succ b} = ?D

inductive List : Type -> Type where
  Nil : {A : Type} -> List A
  Cons : {A : Type} -> A -> List A -> List A

inductive Bool : Type where
  True : Bool
  False : Bool

filter : {A : Type} -> (A -> Bool) -> List A -> List A
filter f Nil = Nil
filter f (Cons x xs) with f x
  | True => Cons x (filter f xs)
  | False => filter f xs

inductive DecEq : Nat -> Nat -> Type where
  Yes : {m n : Nat} -> Equal m n -> DecEq m n
  No : {m n : Nat} -> (Equal m n -> Void) -> DecEq m n

succInj : {j k : Nat} -> Equal (Succ j) (Succ k) -> Equal j k
succInj refl = refl

compose : {u v w : ULevel} -> {A : Type u} -> {B : Type v} -> {C : Type w} -> (B -> C) -> (A -> B) -> (A -> C)
compose g f = \\a => g (f a)

decEqNat : (x y : Nat) -> DecEq x y
decEqNat Zero Zero = Yes refl
decEqNat Zero (Succ y) = No zeroNeqSucc
decEqNat (Succ x) Zero = No (compose zeroNeqSucc sym)
decEqNat (Succ x) (Succ y) with decEqNat x y
  | Yes eq => Yes (cong eq)
  | No neq => No (compose neq succInj)
`;
