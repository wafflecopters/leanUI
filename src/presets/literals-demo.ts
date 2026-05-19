/**
 * Generic Literals Demo preset.
 *
 * Proves the @carrier* annotation system (carrierAdd / carrierMul /
 * carrierValue / carrierBridge) is genuinely generic by defining THREE
 * different abstract numeric types in ONE preset, all using the same
 * tag system. None of them is "real-analysis" — none uses `r*` names or
 * the `Carrier R` shape — yet all of them get the full literals system
 * (norm_num Compute suggestions, registry-driven rendering of literals,
 * arithmetic homomorphism through addRealOfRat-style lemmas).
 *
 * The three types:
 *   1. Magnitude  — a tagged Nat (additive monoid + multiplicative semiring)
 *   2. Score      — a tagged Int (full additive group)
 *   3. Fraction   — a tagged Rat-like pair (field-shaped)
 *
 * Each tags its own arithmetic operations with `@carrierAdd`/`@carrierMul`/
 * `@carrierNeg`/etc. and its named literals with `@carrierValue N`. The
 * generic kernel infra (inferIsRat, isCarrierArithHead, the renderer's
 * carrierValueDisplay map) picks them up automatically. The UI's
 * Compute suggestion works on subterm clicks in any of the three
 * algebras — no preset-specific code in the kernel or pipeline.
 */
export const LITERALS_DEMO_CODE = `-- =====================================================================
-- Generic Literals Demo — three different algebras share one tag system
-- =====================================================================
--
-- The point of this preset: show that @carrierAdd / @carrierValue / etc.
-- work for ANY type, not just Real Analysis. Three distinct abstract
-- numeric structures here, each tagged with the same generic annotations.
-- The Compute suggestion in the UI fires on subterm clicks in any of them.

inductive Void : Type where

@syntax @impl=nat
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

@syntax @natAdd
plus : Nat -> Nat -> Nat
plus Zero m = m
plus (Succ n) m = Succ (plus n m)

@syntax @natMul
mult : Nat -> Nat -> Nat
mult Zero m = Zero
mult (Succ n) m = plus m (mult n m)

-- =====================================================================
-- ALGEBRA 1: Magnitude (a tagged Nat — additive semiring)
-- =====================================================================

inductive Magnitude : Type where
  MkMag : Nat -> Magnitude

@syntax @carrierValue 0
mzero : Magnitude
mzero = MkMag Zero

@syntax @carrierValue 1
mone : Magnitude
mone = MkMag (Succ Zero)

@syntax @carrierValue 2
mtwo : Magnitude
mtwo = MkMag (Succ (Succ Zero))

@syntax @carrierValue 3
mthree : Magnitude
mthree = MkMag (Succ (Succ (Succ Zero)))

@syntax @carrierAdd
madd : Magnitude -> Magnitude -> Magnitude
madd (MkMag a) (MkMag b) = MkMag (plus a b)

@syntax @carrierMul
mmul : Magnitude -> Magnitude -> Magnitude
mmul (MkMag a) (MkMag b) = MkMag (mult a b)

-- =====================================================================
-- ALGEBRA 2: Score (a tagged Int — additive group with negation)
-- =====================================================================

@syntax @impl=int
inductive Int : Type where
  IntOfNat   : Nat -> Int      -- non-negative
  IntNegSucc : Nat -> Int      -- -(n+1) — never represents 0

intNeg : Int -> Int
intNeg (IntOfNat Zero)     = IntOfNat Zero
intNeg (IntOfNat (Succ n)) = IntNegSucc n
intNeg (IntNegSucc n)      = IntOfNat (Succ n)

-- subNatNat n m = n - m (as Int). Structurally recursive on both args.
subNatNat : Nat -> Nat -> Int
subNatNat Zero     Zero     = IntOfNat Zero
subNatNat (Succ n) Zero     = IntOfNat (Succ n)
subNatNat Zero     (Succ m) = IntNegSucc m
subNatNat (Succ n) (Succ m) = subNatNat n m

-- Int addition via subNatNat (no self-recursion — easier on the totality checker).
intAdd : Int -> Int -> Int
intAdd (IntOfNat n)   (IntOfNat m)   = IntOfNat (plus n m)
intAdd (IntOfNat n)   (IntNegSucc m) = subNatNat n (Succ m)
intAdd (IntNegSucc n) (IntOfNat m)   = subNatNat m (Succ n)
intAdd (IntNegSucc n) (IntNegSucc m) = IntNegSucc (Succ (plus n m))

inductive Score : Type where
  MkScore : Int -> Score

@syntax @carrierValue 0
szero : Score
szero = MkScore (IntOfNat Zero)

@syntax @carrierValue 1
sone : Score
sone = MkScore (IntOfNat (Succ Zero))

@syntax @carrierValue -1
sneg_one : Score
sneg_one = MkScore (IntNegSucc Zero)

@syntax @carrierValue 2
stwo : Score
stwo = MkScore (IntOfNat (Succ (Succ Zero)))

@syntax @carrierAdd
sadd : Score -> Score -> Score
sadd (MkScore a) (MkScore b) = MkScore (intAdd a b)

@syntax @carrierNeg
sneg : Score -> Score
sneg (MkScore a) = MkScore (intNeg a)

-- =====================================================================
-- ALGEBRA 3: Fraction (a tagged Nat/Nat pair — field-shaped without
-- a denominator-nonzero proof; for demonstration purposes only)
-- =====================================================================

inductive Fraction : Type where
  MkFrac : Nat -> Nat -> Fraction       -- num, den

@syntax @carrierValue 0
fzero : Fraction
fzero = MkFrac Zero (Succ Zero)

@syntax @carrierValue 1
fone : Fraction
fone = MkFrac (Succ Zero) (Succ Zero)

@syntax @carrierValue 1/2
fhalf : Fraction
fhalf = MkFrac (Succ Zero) (Succ (Succ Zero))

@syntax @carrierValue 2/3
ftwoThirds : Fraction
ftwoThirds = MkFrac (Succ (Succ Zero)) (Succ (Succ (Succ Zero)))

@syntax @carrierAdd
fadd : Fraction -> Fraction -> Fraction
fadd (MkFrac a b) (MkFrac c d) = MkFrac (plus (mult a d) (mult c b)) (mult b d)

@syntax @carrierMul
fmul : Fraction -> Fraction -> Fraction
fmul (MkFrac a b) (MkFrac c d) = MkFrac (mult a c) (mult b d)

-- =====================================================================
-- Try clicking arithmetic subterms in any of these:
-- =====================================================================

magnitudeExample : Magnitude
magnitudeExample = madd mtwo mone        -- expect: Compute = 3

scoreExample : Score
scoreExample = sadd stwo sneg_one        -- expect: Compute = 1

fractionExample : Fraction
fractionExample = fadd fhalf fhalf       -- expect: Compute = 1

mixedExample : Magnitude
mixedExample = mmul mtwo mthree          -- expect: Compute = 6
`;
