# Numeric Literals Plan

## Goals

- User types `1784` and it becomes a single kernel node, not a 1784-deep `Succ` chain.
- Same source `1784` works for `Nat`, `Int`, `Real`, `BigDec`, etc. — the type comes from context.
- `-1784` works without hardcoding sign logic in the kernel.
- `5/8` becomes a rational literal for types that support division.
- Kernel stays domain-agnostic (no `rzero`/`rone`/`Carrier` knowledge).

## Non-Goals

- Full arbitrary-precision arithmetic in the kernel (`+`, `*` between literals stays in user-land for now).
- Floating-point literals (`3.14` as IEEE 754) — out of scope; handle as rationals.
- Unicode digit literals (٠١٢, ０１２) — out of scope.

---

## Architecture: NatLit + coercion protocol

### Why one primitive (`NatLit`) instead of two (`NatLit` + `IntLit`)?

A single `NatLit n` (with n : non-negative BigInt) keeps the kernel minimal. **Sign is a coercion**, not part of the literal:

- `1784` → `NatLit 1784`
- `-1784` → `coerce_neg (NatLit 1784)` where `coerce_neg` is supplied by the preset for types that have negation
- `5/8` → `coerce_div (NatLit 5) (NatLit 8)` — supplied by the preset for types with division

This way the kernel knows about ONE primitive literal form, and presets layer all the type-specific machinery on top.

### Why not pure `Succ` chains?

- 1784 nodes deep means O(n) memory and O(n) traversal for every operation.
- Pretty-printing has to scan and recognize the chain structurally.
- WHNF/unification on giant terms gets slow.
- Pattern matching `Succ x` against `Succ(Succ(...Zero))` works but is gratuitous.

`NatLit` keeps the literal as a primitive AND exposes the `Succ`-view for iota-reduction (see below).

---

## Phase 1: Kernel addition of `NatLit`

### 1.1 Add tag to `TTKTerm` (and `TTerm` surface)

```typescript
// src/compiler/kernel.ts
export type TTKTerm =
  | { tag: 'Var'; index: number }
  | { tag: 'Const'; name: string }
  | { tag: 'App'; fn: TTKTerm; arg: TTKTerm }
  | { tag: 'Binder'; ... }
  | { tag: 'Sort'; level: TTKTerm }
  | { tag: 'Hole'; id: string }
  | { tag: 'Meta'; id: string }
  | { tag: 'Match'; ... }
  | { tag: 'NatLit'; value: bigint }   // ← NEW
  | ...
```

Use `bigint` not `number` so we can represent literals beyond 2^53.

Same change in `TTerm` (surface) so the parser can produce them.

### 1.2 Parser

Tokenizer recognizes a run of digits as `NatLit`. The parser produces `NatLit(bigint)` for any pure-digit token.

```typescript
if (/^\d+$/.test(token)) return { tag: 'NatLit', value: BigInt(token) };
```

### 1.3 WHNF — treat as normal form

`NatLit` is already normal. Just add a case that returns it unchanged.

### 1.4 Unification — structural on the value

```typescript
if (a.tag === 'NatLit' && b.tag === 'NatLit') {
  return a.value === b.value ? success : conflict;
}
```

### 1.5 Substitution / shifting — no-op

Literals have no free variables — `subst` and `shiftTerm` are identity.

### 1.6 Type inference

Initially: `NatLit n` has no inherent type — it's elaborated to a coerced form (see Phase 3). Until elaboration, treat as a meta-typed term: type is a fresh meta resolved by the coercion search.

**Decision needed**: do we add `NatLit` to the kernel BEFORE coercion, with type inference deferred to elaboration? Or do we type it as `Nat` always and coerce only on use? Lean uses the former (more flexible). Recommend: defer to elaboration.

---

## Phase 2: Iota-reduction view

For pattern matching to work — e.g., `match n { Zero => ... | Succ k => ... }` against `NatLit 5` — the kernel needs a reduction rule:

```
NatLit 0      ↦  Zero (after iota: matches Zero clause)
NatLit (n+1)  ↦  Succ (NatLit n)  (after iota: matches Succ clause, k = NatLit n)
```

This is a kernel rule baked into `whnf` when the scrutinee is a `Match` and the head is `NatLit`. The rule fires only when iota would need it — otherwise `NatLit 1784` stays as a literal.

### Why not structural detection?

"Just check if the inductive has 1 nullary + 1 unary-recursive constructor" is appealing but has problems:

- **Multiple Nat-shaped types in scope.** If a preset defines both `Nat` (`Zero`/`Succ`) and `BinNat` (`Bzero`/`Bsucc`), structural detection can't pick which one a `NatLit` should iota-reduce to. The choice depends on the Match's expected scrutinee type, which we may not have at WHNF time.
- **False matches.** Other 1-nullary + 1-unary-recursive shapes exist in the wild (think custom positional encodings). Iota-reducing them as Nat literals would be a soundness disaster.
- **Surprise factor.** Users get confused when their custom type silently inherits literal coercion. Explicit > implicit.

### Use a declared role + structural check

The preset declares the role (just one tag), and the kernel figures out the rest:

```
@impl=nat
inductive Nat : Type where
  | Zero : Nat
  | Succ : Nat -> Nat
```

The constructor names are NOT in the annotation. The kernel verifies the inductive has the Nat shape and **finds** Zero/Succ structurally:

- Exactly 2 constructors
- One has 0 args (or only non-recursive args) and returns the inductive — that's the **base** ("Zero")
- The other has exactly 1 recursive arg of the inductive itself and returns the inductive — that's the **step** ("Succ")
- If shape doesn't match: compile error on the annotation, "@impl=nat requires Zero-like + Succ-like constructors".

Resulting `NatImpl` (populated by the kernel from the annotation):

```typescript
interface NatImpl {
  inductiveName: string;     // "Nat" (from the annotated decl)
  zeroCtor: string;          // discovered: e.g. "Zero" or "Z" or "O"
  succCtor: string;          // discovered: e.g. "Succ" or "S" or "Suc"
}
```

### Why "@impl=ROLE" instead of "@nat-impl"

The general protocol is `@impl=<role>` where `<role>` is a known kernel-level concept. Future roles slot into the same syntax:

- `@impl=nat` — Peano nat (NatLit literals)
- `@impl=string` — character list / rope (string literals)
- `@impl=list` — homogeneous list (list-literal syntax `[a, b, c]`)
- `@impl=bool` — `True`/`False` (boolean literals)
- `@impl=int` — signed-integer encoding (lifts NatLit + sign)

Each role has its own structural shape requirement that the kernel checks. Users write the same one-tag annotation regardless.

### Multiple @impl=nat in scope

Allowed but unusual. If both `Nat` and `BinNat` are tagged `@impl=nat`, the kernel registers both NatImpls. At iota time, the Match's pattern constructors disambiguate (each NatImpl owns its own ctor names — Zero/Succ vs Bzero/Bsucc — so the lookup is unique).

### Iota rule

When WHNF encounters `Match scrutinee clauses` with `scrutinee = NatLit n`:

1. Walk the Match's clauses to find a constructor pattern (`PCtor name args`).
2. Look up `name` in the NatImpl registry.
3. If found:
   - If `n = 0`: rewrite scrutinee to `Const(zeroCtor)`. Iota fires the `Zero` clause.
   - If `n > 0`: rewrite scrutinee to `App(Const(succCtor), NatLit (n-1))`. Iota fires the `Succ` clause with the predecessor as the bound variable.
4. If no clause's constructor is in the registry: leave as `NatLit n` (stuck Match — error reported by checker).

### What if no `@nat-impl` is registered?

A preset without `@nat-impl` still gets the `NatLit` primitive (so the parser can produce literals and the renderer can show them) but iota-reduction never fires. Pattern matching against literals fails — fine, because no preset has Nat-shaped types in this case.

### Future: structural fallback (deferred)

If we later want structural detection as a convenience, gate it behind an opt-in flag (`@nat-auto-detect`) so the kernel default stays explicit-and-safe.

---

## Phase 3: Coercion protocol (`@ofNat`, `@neg`, `@div`)

The preset declares how a `NatLit` becomes a value of a specific type:

```
@ofNat Real
realOfNat : (R : Real) -> NatLit -> Carrier R
realOfNat R n = ... -- e.g. via repeated addition or fast doubling

@ofNat Nat
natOfNat : NatLit -> Nat
natOfNat n = ... -- materializes Succ chain only when forced

@neg Real
realNeg : (R : Real) -> Carrier R -> Carrier R
realNeg = rneg

@div Real
realDiv : (R : Real) -> Carrier R -> Carrier R -> Carrier R
realDiv = rdiv
```

The elaborator, when seeing `NatLit n` in a context expecting type `T`:
1. Look up `@ofNat T` in the registry.
2. Insert the registered function applied to `n`.
3. If no `@ofNat T`, error: "no numeric coercion for type T".

For `-1784` in surface: parser produces `App(NegMarker, NatLit 1784)` where `NegMarker` is a special sentinel. Elaborator sees this in context expecting type `T`:
1. Coerce `NatLit 1784` to `T` via `@ofNat T`.
2. Apply `@neg T` to the result.

For `5/8`: parser produces `App(App(DivMarker, NatLit 5), NatLit 8)`. Elaborator coerces both to `T`, then applies `@div T`.

---

## Phase 4: Pretty-printing

`renderTerm` for `NatLit n` simply outputs `n.toString()`. Easy.

For coerced forms: when rendering `App(realOfNat, App(R, NatLit 1784))`, the renderer should fold this back to `1784`. Implement via the existing alias-fold map: register that `realOfNat R (NatLit n)` displays as `n`. This generalizes to all `@ofNat`-registered coercions automatically.

---

## Phase 5: Performance

Once `NatLit` is in the kernel, optional performance wins:

- Primitive `NatLitAdd`, `NatLitMul`, `NatLitSub` — kernel computes `1 + 1 = 2` in O(1) when both args are `NatLit`. Fires during WHNF.
- Required for `rtwo R = rone R + rone R` to fold to `NatLit 2` in displays without manual alias rules.
- Skip if not needed initially — start with literals as opaque, optimize later.

---

## Phase 6: Migration

### Code changes (in order, each landable independently):

1. **Add `NatLit` to `TTKTerm` and `TTerm`** with type errors marking every switch statement that needs a new case. Add no-op cases everywhere (returns `term` unchanged) to compile.
2. **Parser**: recognize digit tokens as `NatLit`.
3. **Pretty-printer**: render `NatLit n` as `n.toString()`.
4. **WHNF / unification / subst / shift**: handle `NatLit`.
5. **Add `@impl=nat` annotation parser** (in syntax-registry) + structural verification + NatImpl registry population.
6. **Iota view rule**: WHNF Match scrutinee = NatLit lookup against NatImpl registry to expand to `Zero` / `Succ (NatLit (n-1))`.
7. **Update preset** (`real-analysis.ts`) to add `@impl=nat` to the `Nat` inductive type.
8. **Add `@ofNat` annotation** to the syntax-registry parser.
9. **Elaborator**: insert coercions for `NatLit` based on expected type, looking up `@ofNat T` in the registry.
10. **Add `@neg`, `@div` annotations** for sign and rational handling.
11. **Update preset** to register `@ofNat Real`, `@neg Real`, `@div Real`.
12. **Remove kernel pollution** that hardcoded `0/1/2 → rzero/rone/rtwo` (already done; this plan is the proper replacement).

### Tests (each phase needs):

- Parser: `1784` parses to `NatLit(1784n)`.
- WHNF: `NatLit(5)` is normal.
- Iota: `match (NatLit 0) { Zero => "z" | Succ _ => "s" }` reduces to `"z"`. Same for `NatLit 5` → `"s"`.
- Elaboration: `1 : Carrier R` (via `@ofNat Real`) gives the registered coerced term.
- Pretty: rendering `realOfNat R (NatLit 1784)` shows `1784`.
- E2E: `exact 1784` on a `Carrier R` goal succeeds via `@ofNat Real` registration.

---

## Open Questions

1. **NatLit type inference**: do we type `NatLit n : ?T` (deferred meta) or `NatLit n : Nat` (with coercion on use)? Recommend deferred — matches Lean and avoids spurious `Nat` → `Real` coercions when the literal was meant for `Real` to begin with.

2. **`@ofNat` lookup**: keyed on the exact target type, or by inductive head with implicit args? E.g., `Carrier R` is `App(Const("Carrier"), Var)`. Lookup by `head.name = "Carrier"` and the elaborator passes the implicit args through. Same as how `apply` already handles return-type-head matching.

3. **Decimal precedence**: should `-5/8` be `-(5/8)` or `(-5)/8`? Convention: `-(5/8)`. Parser handles via standard operator precedence.

4. **Recursion in `@ofNat` definitions**: `realOfNat R (n+1) = radd R (rone R) (realOfNat R n)` would be O(n) eager evaluation. Use binary doubling (`realOfNat R 2k = double (realOfNat R k)`) for O(log n) or skip and keep the literal opaque (recommended).

5. **Backwards compat**: existing `Zero`/`Succ` proofs should still work. The iota view ensures `NatLit 0` matches `Zero` patterns. New code uses `NatLit`; old code stays unchanged.

---

## Recommended Initial Slice (smallest useful PR)

**PR 1 — Phase 1 only**: kernel `NatLit` primitive + parser + render + no-op cases for WHNF/unify/subst/shift. ~6 tests:

- Parser: `parseExactExpr("1784")` → `NatLit(1784n)`
- Parser: `parseExactExpr("0")` → `NatLit(0n)`
- Parser: large literal `parseExactExpr("12345678901234567890")` → `NatLit(12345678901234567890n)` (exercises BigInt path)
- Render: `renderTerm(NatLit(1784n))` → `"1784"`
- WHNF identity: `whnf(NatLit(5n))` → `NatLit(5n)`
- Unification: `unifyTerms(NatLit(5n), NatLit(5n))` succeeds; `unifyTerms(NatLit(5n), NatLit(6n))` fails (conflict)
- Shift identity: `shiftTerm(NatLit(5n), 1, 0)` → `NatLit(5n)` (no free vars)
- Subst identity: `subst(0, term, NatLit(5n))` → `NatLit(5n)` (no Var refs)

Zero coercion logic, zero iota rules. `NatLit` is just an inert primitive. **This is the foundation.**

**PR 2 — Phase 2**: `@impl=nat` annotation parser + structural verification + NatImpl registry + iota-view rule. Tests:

- `@impl=nat` on a valid Nat inductive parses and registers; kernel discovers Zero/Succ ctors structurally
- `@impl=nat` on a malformed inductive (3 ctors, or wrong arities) fails with a clear error
- `@impl=nat` works for `Zero`/`Succ` AND for `Z`/`S` (name-independence)
- `match (NatLit 0) { Zero => "z" | Succ _ => "s" }` reduces to `"z"`
- `match (NatLit 5) { Zero => "z" | Succ k => k }` reduces to `NatLit 4`
- Match without a registered NatImpl leaves `NatLit` stuck (no spurious reduction)
- Two `@impl=nat` types in scope (Nat + BinNat with different ctor names): each works for its own constructors

**PR 3 — Phase 3**: `@ofNat` + elaborator integration. Requires reading checker.ts thoroughly first — separate design pass before coding.

**PR 4 — Phase 4**: pretty-print folding for coerced literals.

**PR 5 — Phase 5** (optional): primitive `NatLitAdd`/`NatLitMul`.

Each PR is independently shippable, independently testable, and each one earns the next.
