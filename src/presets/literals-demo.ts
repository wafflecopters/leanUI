/**
 * Generic Literals Demo preset.
 *
 * Demonstrates the @carrier* / @ofNat literal system across FOUR canonical
 * numeric algebras — Nat, Int, Real, Complex — in ONE preset, each closing
 * the same theorem `1 + 4 = 5` written with BARE NUMERALS. The kernel
 * auto-coerces each `1`, `4`, `5` through the matching algebra's
 * @impl=int / @ofNat path. Same source-level appearance, four very
 * different elaborated kernel terms — and each one reduces to refl.
 */
export const LITERALS_DEMO_CODE = `-- =====================================================================
-- Generic Literals Demo — four numeric algebras, ONE syntax
-- =====================================================================
--
-- Numeric literals (\`1\`, \`4\`, \`5\`) work in any algebra that registers
-- either a Nat / Int / Rat kernel impl OR a function tagged \`@ofNat\` /
-- \`@ofInt\` / \`@ofRat\` whose return type is the target algebra. The
-- elaborator finds the right coercion automatically from context.
--
-- Each section closes "1 + 4 = 5" by refl, written exactly that way.

inductive Void : Type where

inductive Equal : {A : Type} -> A -> A -> Type where
  refl : {A : Type} -> {a : A} -> Equal a a

-- =====================================================================
-- ℕ — Natural numbers (@impl=nat → literals are kernel-native NatLit)
-- =====================================================================

@syntax @impl=nat
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

@syntax @natAdd
@syntax @carrierAdd
plus : Nat -> Nat -> Nat
plus Zero m = m
plus (Succ n) m = Succ (plus n m)

@syntax @natMul
@syntax @carrierMul
mult : Nat -> Nat -> Nat
mult Zero m = Zero
mult (Succ n) m = plus m (mult n m)

-- 1 + 4 = 5 in ℕ. \`1\`, \`4\`, \`5\` are NatLits at the kernel level;
-- the @natAdd fast-path collapses \`plus NatLit(1) NatLit(4)\` to NatLit(5).
natOnePlusFour : Equal (plus 1 4) 5
natOnePlusFour = refl

-- =====================================================================
-- ℤ — Integers (@impl=int → literals expand to IntOfNat n directly)
-- =====================================================================

@syntax @impl=int
inductive Int : Type where
  IntOfNat   : Nat -> Int
  IntNegSucc : Nat -> Int

intNeg : Int -> Int
intNeg (IntOfNat Zero)     = IntOfNat Zero
intNeg (IntOfNat (Succ n)) = IntNegSucc n
intNeg (IntNegSucc n)      = IntOfNat (Succ n)

subNatNat : Nat -> Nat -> Int
subNatNat Zero     Zero     = IntOfNat Zero
subNatNat (Succ n) Zero     = IntOfNat (Succ n)
subNatNat Zero     (Succ m) = IntNegSucc m
subNatNat (Succ n) (Succ m) = subNatNat n m

@syntax @carrierAdd
intAdd : Int -> Int -> Int
intAdd (IntOfNat n)   (IntOfNat m)   = IntOfNat (plus n m)
intAdd (IntOfNat n)   (IntNegSucc m) = subNatNat n (Succ m)
intAdd (IntNegSucc n) (IntOfNat m)   = subNatNat m (Succ n)
intAdd (IntNegSucc n) (IntNegSucc m) = IntNegSucc (Succ (plus n m))

@syntax @carrierNeg
intNegFn : Int -> Int
intNegFn = intNeg

-- 1 + 4 = 5 in ℤ. Each literal expands to \`IntOfNat NatLit(_)\` via
-- @impl=int; intAdd's first clause reduces \`IntOfNat n + IntOfNat m\`
-- to \`IntOfNat (plus n m)\`, and @natAdd closes the rest. The explicit
-- \`{A := Int}\` pins Equal's implicit type parameter — without it, \`5\`
-- on the RHS defaults to Nat before the LHS resolves it to Int.
intOnePlusFour : Equal {A := Int} (intAdd 1 4) 5
intOnePlusFour = refl

-- =====================================================================
-- ℝ — Reals (no kernel impl — pure user algebra, literal-coerced via @ofNat)
-- =====================================================================

inductive Real : Type where
  MkReal : Int -> Real

@syntax @ofNat
realOfNat : Nat -> Real
realOfNat n = MkReal (IntOfNat n)

@syntax @carrierAdd
realAdd : Real -> Real -> Real
realAdd (MkReal a) (MkReal b) = MkReal (intAdd a b)

@syntax @carrierNeg
realNeg : Real -> Real
realNeg (MkReal a) = MkReal (intNeg a)

-- 1 + 4 = 5 in ℝ. The elaborator finds @ofNat at target head \`Real\`
-- and inserts \`realOfNat _\` around each literal. Reduction unfolds
-- realOfNat → MkReal (IntOfNat _), then realAdd / intAdd / @natAdd
-- bring the whole chain home.
realOnePlusFour : Equal {A := Real} (realAdd 1 4) 5
realOnePlusFour = refl

-- =====================================================================
-- ℂ — Complex numbers (pair of Reals, literal-coerced via @ofNat)
-- =====================================================================

inductive Complex : Type where
  MkComplex : Real -> Real -> Complex     -- (re, im)

@syntax @ofNat
complexOfNat : Nat -> Complex
complexOfNat n = MkComplex (realOfNat n) (realOfNat 0)

@syntax @carrierAdd
complexAdd : Complex -> Complex -> Complex
complexAdd (MkComplex a1 b1) (MkComplex a2 b2) = MkComplex (realAdd a1 a2) (realAdd b1 b2)

-- 1 + 4 = 5 in ℂ. Same surface form, deepest reduction chain: the
-- real-part component reduces via realAdd → intAdd → @natAdd, and the
-- imaginary-part components (both 0) collapse the same way. Every step
-- is definitional, so refl closes it.
complexOnePlusFour : Equal {A := Complex} (complexAdd 1 4) 5
complexOnePlusFour = refl
`;
