# Limit Operators in TT

## Current Focus

This document describes the design for the `lim` projection operator, which makes limit values usable as first-class terms in arithmetic expressions.

## Motivation

We have `Limit f x0 L` as a record type proving that `lim_{x→x0} f(x) = L`. But the `L` value is trapped inside the type — you can't write `lim f + lim g` in a natural way.

The issue becomes clear with `lim_{x→x₀} f(x) = L`. In the visual math editor, `=` gets parsed as `Equal`, but this isn't really an `Equal` — it's a statement about convergence. We need a way to extract `L` from a `Limit` proof so it can participate in arithmetic.

## Design: `lim` as a Projection Operator

Define `lim` as a function that extracts `L` from a `Limit f x0 L` proof:

```
lim : {R : Real} -> {L : Carrier R} -> (f : Carrier R -> Carrier R) -> (x0 : Carrier R)
    -> Limit f x0 L -> Carrier R
lim {R} {L} _ _ _ = L
```

Key properties:
- `L` is an **implicit** parameter inferred from the `Limit` proof's type
- `lim` definitionally reduces to `L` — it's just a projection
- This makes rewrite lemmas trivially `refl`

## Rewrite Lemmas (All `refl`)

Because `lim` simply returns `L`, and the limit operation theorems (`limitAdd`, `limitScalarAll`) produce `Limit` proofs whose `L` parameter matches the expected arithmetic expression, all rewrite lemmas are definitionally true:

### `limit_pull_radd`: lim f + lim g = lim (f + g)
```
-- LHS: radd (lim f x0 limF) (lim g x0 limG)
--     = radd Lf Lg                               (by def of lim)
-- RHS: lim (\x => radd (f x) (g x)) x0 (limitAdd f g x0 Lf Lg limF limG)
--     = radd Lf Lg                               (limitAdd returns Limit ... (radd Lf Lg))
-- Proof: refl
```

### `limit_pull_scalar`: c * lim f = lim (c * f)
```
-- LHS: rmul c (lim f x0 limF) = rmul c Lf
-- RHS: lim (\x => rmul c (f x)) x0 (limitScalarAll c f x0 Lf limF)
--     = rmul c Lf                                (limitScalarAll returns Limit ... (rmul c Lf))
-- Proof: refl
```

### `limit_pull_const_add`: k + lim f = lim (k + f)
```
-- Requires: limitConst k x0 : Limit (\_ => k) x0 k
-- LHS: radd k (lim f x0 limF) = radd k Lf
-- RHS: lim (\x => radd k (f x)) x0 (limitAdd (\_ => k) f x0 k Lf (limitConst k x0) limF)
--     = radd k Lf                                (limitAdd returns Limit ... (radd k Lf))
-- Proof: refl
```

### `lim_const`: k = lim (const k)
```
-- RHS: lim (\_ => k) x0 (limitConst k x0) = k   (by def of lim)
-- Proof: refl
```

## Supporting Definitions

### `limitConst`: Constant function limit
```
limitConst : {R : Real} -> (k x0 : Carrier R) -> Limit (\_ => k) x0 k
```
Proof: For any ε > 0, pick δ = 1. Then |k - k| = 0 < ε.

### `subSelf`: a - a = 0
```
subSelf : {R : Real} -> (a : Carrier R) -> Equal (rsub a a) (rzero R)
```
Simple wrapper around `negRight`.

## Why This Works

The key insight is that `lim` is a **type-directed projection**. The limit value `L` is already determined by the `Limit f x0 L` proof's type. All `lim` does is make it available as a term.

This means:
1. **No computation needed** — `lim` just extracts what's already there
2. **Type safety preserved** — you can only get a limit value if you have a convergence proof
3. **Rewrite lemmas are free** — since both sides reduce to the same value by definition
4. **Composable** — `lim f + lim g` is well-formed arithmetic on `Carrier R`

## Future: Instance Resolution

Currently, the `Limit` proof must be passed explicitly: `lim f x0 limF`. In the future, with instance/typeclass resolution, we could make the proof truly implicit:

```
-- Future: pf resolved by instance search
lim : {R : Real} -> {L : Carrier R} -> (f : Carrier R -> Carrier R) -> (x0 : Carrier R)
    -> {{pf : Limit f x0 L}} -> Carrier R
```

Then `lim f x0` would automatically find the appropriate limit proof in scope.

## Visual Math Editor Integration

In the structured math editor, the pattern:
```
lim_{x → x₀} f(x) = L
```
Should NOT be parsed as `Equal (Limit ...) L`. Instead, with the `lim` operator, it can be naturally expressed as:
```
Equal (lim (\x => f x) x0 proof) L
```
or used directly in arithmetic contexts like:
```
lim_{x → x₀} f(x) + lim_{x → x₀} g(x) = lim_{x → x₀} (f(x) + g(x))
```
