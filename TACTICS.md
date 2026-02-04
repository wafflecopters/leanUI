# Tactics System

## Overview

The tactics system provides an interactive proof construction mode where the user writes proof steps (tactics) that transform a goal into subgoals until all goals are solved. The result is a kernel proof term that the type checker can verify.

```
Source: `f := by intro x; exact x`
  → Parser: TacticBlock with TacticCommand list
  → Elaboration: elaborateTacticBlock runs tactics, produces TTKTerm
  → Compilation: proof term registered as definition value
```

## Available Tactics

| Tactic | Arguments | Description |
|--------|-----------|-------------|
| `intro` | `[name]` | Introduce one Pi binder into the context |
| `intros` | `[names...]` | Introduce all Pi binders (optionally named) |
| `exact` | `<term>` | Solve goal by providing the exact proof term |
| `apply` | `<fn>` | Apply a function, creating subgoals for its arguments |
| `assumption` | | Search context for a term matching the goal type |
| `cases` | `<term>` | Case split on an inductive type |
| `induction` | `<term>` | Induction on an inductive type with IH |
| `reflexivity` | | Prove `Equal a a` |
| `rewrite` | `<proof>` | Substitute using an equality proof |
| `symmetry` | | Flip `Equal a b` to `Equal b a` |
| `transitivity` | `<middle>` | Split `Equal a c` into `Equal a b` and `Equal b c` |
| `cong` | `<proof>` | Congruence: from `Equal a b` derive `Equal (f a) (f b)` |

## Syntax

### Basic Tactic Block

```
definition : Type := by
  tactic1
  tactic2
  tactic3
```

### Structured Cases

```
f : Nat -> Nat := by
  intro n
  cases n with
  | Zero => exact Zero
  | Succ m => exact m
```

### Multi-Tactic Branches

Branches support **multiple tactics** in three ways:

**1. Multi-line (indented):**
```
| Succ n' IH =>
  apply congSucc
  apply trans
  exact IH
```

**2. Semicolon-separated (single line):**
```
| Succ n' IH => apply congSucc; exact IH
```

**3. Nested cases/induction:**
```
f : List Nat -> Nat -> Maybe Nat := by
  intros xs n
  cases xs with
  | Nil => exact Nothing
  | Cons x rest =>
    cases n with
    | Zero => exact (Just x)
    | Succ m => exact Nothing
```

## Architecture

### Key Files

| File | Purpose |
|------|---------|
| `src/tactics/tactic.ts` | Tactic interface, ExactTactic, IntroTactic, ApplyTactic, AssumptionTactic |
| `src/tactics/tacticsEngine.ts` | Immutable TacticEngine proof state |
| `src/tactics/cases-tactic.ts` | Cases tactic (pattern matching with branching) |
| `src/tactics/induction-tactic.ts` | Induction tactic with IH |
| `src/tactics/reflexivity-tactic.ts` | Reflexivity tactic |
| `src/tactics/rewrite-tactic.ts` | Rewrite tactic |
| `src/tactics/symmetry-tactic.ts` | Symmetry tactic |
| `src/tactics/transitivity-tactic.ts` | Transitivity tactic |
| `src/tactics/cong-tactic.ts` | Congruence tactic |
| `src/tactics/proof-state.ts` | Proof state representation for IDE |
| `src/tactics/info-tree.ts` | InfoTree recording for IDE integration |
| `src/tactics/execute-with-info.ts` | Execute tactics with InfoTree recording |
| `src/tactics/apply-tactic.ts` | Unified tactic dispatch API |
| `src/compiler/compile.ts` | `elaborateTacticBlock()` — tactic elaboration entry point |
| `src/parser/parser.ts` | `parseTacticBlock()` / `parseTactic()` — syntax parsing |

### Data Flow

```
TacticBlock (parsed)
  → elaborateTacticBlock()
    → TacticEngine (initial: one goal = expected type)
    → for each tactic command:
        1. Get focused goal
        2. Elaborate args in goal's context (surface → kernel)
        3. Build Tactic object via tacticCommandToTactic()
        4. tactic.apply(engine, goal, goalId) → new engine
        5. Handle structured cases branches recursively
    → engine.zonk() → final proof term (TTKTerm)
```

### Proof Term Construction

- **Simple tactics** (exact, intro, apply): Build lambdas, applications, or direct terms
- **Cases tactic**: Builds a `Match` term with `PCtor` patterns and meta RHS per constructor
- **Compilation bypass**: Tactic-produced terms skip `checkType` since each tactic validates its own step. The type checker doesn't handle Match inference, so tactic Match terms are trusted.

### Implicit Argument Handling

When tactic arguments contain function applications (e.g., `exact (Just x)`), the surface-to-kernel conversion inserts Holes for implicit parameters. This mirrors what the elaboration pipeline does for normal definitions. Without this, `App(Just, x)` would fail because the type checker's App inference doesn't insert implicits.

---

## Integration Milestones

### Milestone 1: Nat Semiring — COMPLETE

All 12 semiring properties proven via direct pattern matching, plus `Semiring` record instantiation.

**Properties proven** (in `src/test-programs/nat-semiring/`):

| File | Property |
|------|----------|
| `addition-properties.tt` | plusZeroLeft, plusZeroRight, plusSuccRight |
| `plus-comm.tt` | plusComm |
| `plus-assoc.tt` | plusAssoc |
| `multiplication-properties.tt` | mulZeroLeft, mulZeroRight, mulOneLeft, mulOneRight |
| `mul-succ-right.tt` | mulSuccRight (+ helpers: congPlusRight, congPlusLeft, plusLeftComm) |
| `mul-comm.tt` | mulComm |
| `mul-distrib-right.tt` | mulDistribRight |
| `mul-distrib-left.tt` | mulDistribLeft |
| `mul-assoc.tt` | mulAssoc |
| `nat-semiring.tt` | Semiring record + natSemiring instance with all 12 proofs |

**Status**: All 11 test files pass. Proofs use equational reasoning with helper lemmas (congSucc, sym, trans, congPlusRight, congPlusLeft, plusLeftComm).

### Milestone 2: Triangle Sum (sum of 1..n = n(n+1)/2) — TODO

Prove `trisum : (n : Nat) -> Equal (sum n) (half (mul n (Succ n)))` both via:
- Direct pattern matching proof
- Tactic proof (induction + rewrite)

Requires: `sum`, `half` (or `div2`), and multiplication helpers from Milestone 1.

### Milestone 3: Leq (ordering on Nat) — TODO

In a single file, define Nat, Leq, and Equal, then prove:
- `leqRefl : (a : Nat) -> Leq a a`
- `leqTrans : Leq a b -> Leq b c -> Leq a c`
- `leqAntisym : Leq a b -> Leq b a -> Equal a b`

Leq as an inductive:
```
data Leq : Nat -> Nat -> Type where
  LeqZero : {n : Nat} -> Leq Zero n
  LeqSucc : {n m : Nat} -> Leq n m -> Leq (Succ n) (Succ m)
```

### Milestone 4: decEqNat via Tactics — TODO

Implement decidable equality on Nat using tactics:
```
decEqNat : (n m : Nat) -> Either (Equal n m) (Equal n m -> Empty) := by
  ...
```

Requires: `Empty` type, nested cases, and ability to construct contradiction proofs.

---

## Best Practices

### Current System Capabilities

The tactics system supports **incremental proof construction** using `apply` for proof combinators and `exact` for lemmas. This is best-practice for readable, maintainable proofs.

### Example: Equational Reasoning

From [semiring-tactics.tt](src/test-programs/nat-semiring/semiring-tactics.tt):

```
mulDistribLeft : (n m p : Nat) -> Equal (mul n (plus m p)) (plus (mul n m) (mul n p)) := by
  intro n
  induction n with
  | Zero =>
    intros m p
    exact refl
  | Succ n' IH =>
    intros m p
    -- mul (Succ n') (m + p) = (m + p) + mul n' (m + p)
    --                       = (m + p) + (mul n' m + mul n' p)       [by IH]
    --                       = m + (p + (mul n' m + mul n' p))       [by plusAssoc]
    --                       = m + (mul n' m + (p + mul n' p))       [by plusLeftComm]
    --                       = (m + mul n' m) + (p + mul n' p)       [by plusAssoc]
    apply trans
    apply congPlusRight
    exact (IH m p)
    apply trans
    exact (plusAssoc m p (plus (mul n' m) (mul n' p)))
    apply trans
    apply congPlusRight
    exact (plusLeftComm p (mul n' m) (mul n' p))
    apply sym
    exact (plusAssoc m (mul n' m) (plus p (mul n' p)))
```

**Key techniques:**
- Comments show the mathematical equality chain
- `apply trans` builds the chain incrementally (creates 2 subgoals each time)
- `apply congPlusRight` / `apply sym` decompose proof structure
- `exact (lemma args)` instantiates lemmas with their required arguments
- No blank lines between tactics in a branch (parser requirement)

### Example: Induction with Equational Steps

From [doublesum-best-practice.tt](src/test-programs/tactics/doublesum-best-practice.tt):

```
doubleSum : (n : Nat) -> Equal (plus (sum n) (sum n)) (mul n (Succ n)) := by
  intro n
  induction n with
  | Zero =>
    exact refl
  | Succ n' IH =>
    -- Goal: (n'+1) + sum(n') + (n'+1) + sum(n') = (n'+1) * (n'+2)
    -- Strategy: reassociate, commute, apply IH, simplify
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
```

### What Makes This "Best Practice"?

✅ **Each tactic is one logical step** - easy to understand what's happening
✅ **Comments explain the math** - not just tactic mechanics
✅ **Incremental construction** - `apply trans` chains equalities step-by-step
✅ **Clear structure** - if a step fails, you know exactly which one
✅ **Maintainable** - changes to one step don't affect others

### Limitations of Current System

The `exact (lemma arg1 arg2 ...)` pattern may look like "big terms," but they're just **lemma instantiations** - the smallest possible proof step for that equality. To be more incremental (avoiding arguments in `exact`), we'd need:

1. **`calc` mode** - Lean-style equational reasoning syntax
2. **Better `rewrite`** - automatic subterm rewriting
3. **Implicit inference in `apply`** - so `apply plusAssoc` works without args

---

## Known Issues & Limitations

### Soundness

- **Tactic proof terms skip `checkType`**: Since the type checker doesn't implement Match inference, tactic-produced terms containing Match nodes bypass type checking. Each tactic validates its own step, but there's no end-to-end re-check of the assembled proof term. Adding Match to `checkType` would close this gap.

- **Induction tactic motive construction**: The induction tactic uses a placeholder approach for building the motive term. Complex induction proofs may produce incorrect proof terms.

### Implementation Gaps

- **No `calc` mode**: Equational reasoning requires manual `apply trans` chains. A `calc` block (like Lean 4) would make equality proofs more readable.

- **Limited `rewrite`**: The rewrite tactic exists but needs improvement - can't rewrite in hypotheses, can't chain rewrites, limited subterm matching.

- **No `have` tactic**: Can't introduce intermediate lemmas within a tactic proof.

- **No `refine` tactic**: Can't provide a partial term with holes.

- **No `simp` tactic**: No simplification with a lemma database.

- **Implicit arguments in `apply`**: When using `apply lemma`, you must provide all arguments explicitly. Better unification would allow `apply lemma` to infer arguments from the goal.

- **No tactic combinators**: No `try`, `repeat`, `<;>`, or `<|>` for tactic composition.

- **No `revert` tactic**: Can't move hypotheses back to the goal type.

- **Limited error messages**: Some tactic failures produce cryptic kernel-level errors.

### IDE Integration

- **Syntax highlighting**: No dedicated syntax highlighting for tactic blocks. `by`, tactic names, `|`, `=>` are tokenized but not semantically colored as tactics.

- **Info-at-cursor**: The InfoTree infrastructure exists (`info-tree.ts`, `execute-with-info.ts`) and can record goal state at each tactic step, but it's not yet wired into the IDE's hover/cursor system.

- **Goal display**: `ProofState` and `GoalState` types exist for IDE display, but no UI component renders them yet.

---

## Future Tactics Roadmap

### Priority 1: Readability (Biggest Impact)

These features would make proofs dramatically more readable and are commonly needed:

1. **`calc` mode** - Structured equational reasoning (like Lean 4's calc)
   ```
   calc a + b + c
       = a + (b + c)  := plusAssoc a b c
     _ = (b + c) + a  := plusComm a (b + c)
     _ = b + (c + a)  := plusAssoc b c a
   ```
   **Impact**: Eliminates manual `apply trans` chains, shows equality steps clearly

2. **Better `rewrite` tactic** - Chain rewrites, rewrite in hypotheses
   ```
   rewrite h1         -- rewrite using h1
   rewrite h2 at h3   -- rewrite in hypothesis h3
   rewrite [h1, h2]   -- chain multiple rewrites
   ```
   **Impact**: More direct proof style, less manual transitivity

3. **`have` tactic** - Introduce intermediate lemmas
   ```
   have h : x = y
     apply lemma1
     exact proof
   rewrite h
   ```
   **Impact**: Break complex proofs into named steps

### Priority 2: Usability

4. **Implicit argument inference in `apply`** - Let tactics infer arguments
   ```
   apply plusAssoc  -- instead of: exact (plusAssoc a b c)
   ```
   **Impact**: More concise, matches Lean/Coq style

5. **`simp` tactic** - Simplification with lemma database
   ```
   simp [plusZero, mulOne, plusComm]
   ```
   **Impact**: Automate repetitive simplification steps

6. **Better error messages** - Show goal state when tactics fail
   **Impact**: Easier debugging

### Priority 3: Soundness & Completeness

7. **Add Match case to `checkType`** - End-to-end validation
   **Impact**: Close soundness gap, verify tactic-generated proofs

8. **Fix induction tactic motive construction** - Handle complex motives correctly
   **Impact**: More reliable induction proofs

### Priority 4: Advanced Features

9. **Tactic combinators** - `try`, `repeat`, `<;>`, `<|>`
   **Impact**: Compose tactics, handle optional steps

10. **Decision procedures** - `omega` for linear arithmetic, `lia` for integer arithmetic
    **Impact**: Automate numeric proofs

11. **Tactic macros** - User-defined tactics
    **Impact**: Domain-specific proof automation

12. **Auto tactic** - Simple proof search
    **Impact**: Automate trivial proofs

### Priority 5: IDE Integration

- Goal display panel in IDE
- Wire InfoTree into hover/cursor system
- Syntax highlighting for tactic blocks
- Live goal state updates as you type

---

## Example Proofs

### Modus Ponens

```
modusPonens : {A B : Type} -> A -> (A -> B) -> B := by
  intros A B a f
  apply f
  exact a
```

### Identity Function

```
id : {A : Type} -> A -> A := by
  intros A a
  exact a
```

### Cases on Nat

```
natId : Nat -> Nat := by
  intro n
  cases n with
  | Zero => exact Zero
  | Succ m => exact (Succ m)
```

### Nested Cases

```
nth : List Nat -> Nat -> Maybe Nat := by
  intros xs n
  cases xs with
  | Nil => exact Nothing
  | Cons x rest =>
    cases n with
    | Zero => exact (Just x)
    | Succ m => exact Nothing
```

### Apply Constructor with Implicits

```
singleton : Nat -> List Nat := by
  intro n
  apply Cons
  exact n
  exact Nil
```
