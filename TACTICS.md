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

Branches can span multiple lines:

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

## Known Issues & Limitations

### Soundness

- **Tactic proof terms skip `checkType`**: Since the type checker doesn't implement Match inference, tactic-produced terms containing Match nodes bypass type checking. Each tactic validates its own step, but there's no end-to-end re-check of the assembled proof term. Adding Match to `checkType` would close this gap.

- **Induction tactic motive construction**: The induction tactic uses a placeholder approach for building the motive term. Complex induction proofs may produce incorrect proof terms.

### Implementation Gaps

- **No multiple tactics per branch**: Each `| Ctor => ` branch supports one tactic (which can itself be a nested `cases ... with`). Multi-tactic branches like `| Succ m => rewrite h; exact refl` aren't supported yet.

- **No `have` tactic**: Can't introduce intermediate lemmas within a tactic proof.

- **No `refine` tactic**: Can't provide a partial term with holes.

- **No tactic combinators**: No `try`, `repeat`, `<;>`, or `<|>` for tactic composition.

- **No `revert` tactic**: Can't move hypotheses back to the goal type.

- **Limited error messages**: Some tactic failures produce cryptic kernel-level errors.

### IDE Integration

- **Syntax highlighting**: No dedicated syntax highlighting for tactic blocks. `by`, tactic names, `|`, `=>` are tokenized but not semantically colored as tactics.

- **Info-at-cursor**: The InfoTree infrastructure exists (`info-tree.ts`, `execute-with-info.ts`) and can record goal state at each tactic step, but it's not yet wired into the IDE's hover/cursor system.

- **Goal display**: `ProofState` and `GoalState` types exist for IDE display, but no UI component renders them yet.

---

## Future Tactics Roadmap

### Near-term

- [ ] Multi-tactic branches: `| Succ m => rewrite h; exact refl`
- [ ] `have` tactic: introduce intermediate lemmas
- [ ] `refine` tactic: exact with holes
- [ ] `revert` tactic: opposite of intro
- [ ] Add Match case to `checkType` for end-to-end validation
- [ ] Fix induction tactic motive construction

### Medium-term

- [ ] Tactic combinators: `try`, `repeat`, `<;>`, `<|>`
- [ ] Wire InfoTree into IDE hover/cursor system
- [ ] Syntax highlighting for tactic blocks
- [ ] Goal display panel in IDE
- [ ] Better error messages with goal context

### Long-term

- [ ] Tactic macros (user-defined tactics)
- [ ] Decision procedures (omega/lia)
- [ ] Auto tactic (simple proof search)
- [ ] `simp` tactic (simplification with lemma set)

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
