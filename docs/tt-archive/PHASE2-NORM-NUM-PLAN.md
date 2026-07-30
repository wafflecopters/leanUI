# Phase 2: `normNum`-style decision procedure for closed arithmetic

## Why we need this (and why Phase 1 alone isn't enough)

The user's bug was: clicking `2 + (-1)` on a `Carrier R` goal should reduce to `1`. With the `rtwoAsRealOfRat` @simp bridge shipped in commit `e8cb354`, the simp chain works for THIS specific case:

```
rtwo R + realOfRat -1
  → realOfRat 2 + realOfRat -1     [rtwoAsRealOfRat]
  → realOfRat (ratPlus 2 -1)        [addRealOfRat]
  → realOfRat 1                     [BigInt fast-path]
  → rone R                          [realOfRatOne]
```

But the @simp set has gaps. Cases that DON'T close via simp today:
- `rone R + rone R` — no rewrite from `radd rone rone` to anything (would need `roneAsRealOfRat` as @simp, but that LOOPS with `realOfRatOne`).
- `rzero R + rone R` — no @simp `addZeroLeft` (concerns about loops with `addNegRight` etc. were not investigated, but conservatively excluded).
- Larger closed integers: `realOfRat 100 + realOfRat 200` works via `addRealOfRat`, but the result `realOfRat 300` doesn't simplify further (no `realOfRat 300 → rXXX` bridges for arbitrary integers).
- Negation of literals: `rneg (rone R)` ≠ `realOfRat (-1)` definitionally; no bridge.

These gaps were the agent's reason for recommending `norm_num`:
> A decision procedure on a kernel with three competing literal forms fights itself.
> Do NOT try (b) [norm_num] without (a) [unify the kernel].

But (a) doesn't work for us — see `PHASE1-LESSONS-LEARNED` below. So we do (b) anyway, accepting that the procedure has to bridge representations as it walks.

## What we tried and learned (Phase 1)

Attempted: redefine `rtwo R = realOfRat R 2` so the kernel sees `rtwo` and the elaborator-produced `realOfRat 2` as definitionally equal terms (via β/ι/δ-unfolding through `realOfNat`).

Result: ~20 cascading proof failures across the preset. Lemmas like `oneLeTwo`, `twoNeZero`, `halfPlusHalf`, `halfMulEps`, `divTwoPos`, `convertEps`, `limitAdd`, `limit_pull_const_add`, `derivAdd`, `derivChain` all explicitly construct or pattern-match on `radd (rone R) (rone R)` and rely on its definitional equality with `rtwo R`. Changing `rtwo`'s body breaks the unification of these proof terms with their declared types.

The Mathlib insight stands: **canonical-form invariance is a tactic-level property, not an elaboration-level one.** Mathlib also has multiple kernel forms for `(2 : ℝ)` and reconciles them via `norm_num` / `norm_cast` / `push_cast`. The 20 cascading failures we hit are the LeanUI analogue of Mathlib's "you can't make `(2 : ℝ)` and `(1 + 1 : ℝ)` and `((2 : ℕ) : ℝ)` all be the same kernel term without breaking some existing theory."

## What Phase 2 actually does

Build a TS-side tactic `NormNumTactic` (mirroring Mathlib's `Mathlib/Tactic/NormNum/Core.lean`) that:

### Step 1 — Walk the goal, build `IsRat` certificates

A pure function `inferIsRat(term, definitions)` that, given a `TTKTerm` of type `Carrier R`, returns:

```typescript
type IsRatCert =
  | { kind: 'literal'; q: { num: bigint; den: bigint }; term: TTKTerm; proof: TTKTerm }
  | null;  // cannot classify
```

Recognized leaf forms:
- `rzero R` → q = 0/1, proof = `rzeroAsRealOfRat R`
- `rone R`  → q = 1/1, proof = `roneAsRealOfRat R`
- `rtwo R`  → q = 2/1, proof = `rtwoAsRealOfRat R`
- `realOfRat R (MkRat (IntOfNat n) d _)` → q = +n/d, proof = `refl`
- `realOfRat R (MkRat (IntNegSucc n) d _)` → q = -(n+1)/d, proof = `refl`
- `realOfNat R n` (closed) → q = n/1, proof via `realOfNatN` chain
- `realOfInt R i` (closed) → q from i, proof via `realOfIntN` chain
- `realOfRat R (RatLit k m)` → q = k/m, proof = `refl`

Recognized compound forms (children classified recursively):
- `radd a b` where `IsRat a (p)` and `IsRat b (q)` → `IsRat (radd a b) (ratPlus p q)`, proof via `addRealOfRat`
- `rsub a b` similarly via `subRealOfRat`
- `rmul a b` similarly via `mulRealOfRat`
- `rneg a` where `IsRat a (p)` → `IsRat (rneg a) (-p)`, proof via a new `negRealOfRat` lemma
- `rinv a` where `IsRat a (p)` and `p ≠ 0` → `IsRat (rinv a) (1/p)`, proof via a new `invRealOfRat` lemma

### Step 2 — Use certificates to close goals

The tactic itself: given a goal, classify both sides as `IsRat`. If both classify to the SAME canonical Rat (kernel BigInt equality), produce the proof by chaining the LHS certificate, `trans`, and the inverse of the RHS certificate.

- `Equal a b` where `inferIsRat(a) = (q_a, proof_a)` and `inferIsRat(b) = (q_b, proof_b)` and `q_a = q_b` → proof: `trans proof_a (sym proof_b)`.
- `rle a b` similarly, but check `q_a ≤ q_b` instead of equality.
- `rlt a b` check `q_a < q_b`.

### Step 3 — Hook into the suggestion pipeline

When the user clicks a closed-arithmetic subterm, call `inferIsRat`. If it returns a non-null certificate AND the rendered Rat value is meaningfully different from the input rendering (e.g., `2 + (-1)` certifies to `1`), surface a `Compute → 1` suggestion. One click closes any closed arithmetic.

### Sizing

- `inferIsRat` core walk: ~80 LOC TS
- Lemma references and proof assembly: ~50 LOC TS
- 2 new preset lemmas (`negRealOfRat`, `invRealOfRat`): ~10 LOC each
- Suggestion-pipeline integration: ~30 LOC TS
- Tests: ~5 regression test cases (closed arith of various shapes)

Total: ~250 LOC, probably 2-3 hours of focused work in a dedicated session.

## What's still missing after Phase 2

Inequality on non-closed terms (`0 < x + 1` where `x` is a hypothesis) — that's `polyrith`/`linarith` territory, not `norm_num`. Out of scope for this plan.

## Order of operations for the dedicated Phase 2 session

1. Write `inferIsRat` with unit tests for each leaf and compound form.
2. Add `negRealOfRat` and `invRealOfRat` to the preset.
3. Write the closing tactic.
4. Add suggestion-pipeline integration.
5. Write end-to-end regression: user clicks `2 + (-1)`, sees `Compute → 1`, applies it, goal closes.
6. Audit which Phase 1 @simp lemmas can be removed once `normNum` covers them (likely `rtwoAsRealOfRat` becomes redundant for arithmetic, though still useful as a manual rewrite).
