# Named & Implicit Arguments Implementation Plan

## Implementation Order Context

This feature is part of a larger roadmap. The implementation order is:

1. **Implicit/Named Arguments** (this plan) - **First priority**
2. **Universe Levels** (`LEVELS_PLAN.md`) - Second priority
3. **Multi-Variable Binders** (`MULTI_ARGS_PLAN.md`) - Third priority
4. **Records** - Fourth priority (plan TBD)

### Why This Order?

- **Implicit args first**: The foundation for many other features. Multi-variable implicit binders (`{A B : Type}`) require this infrastructure.
- **Levels depend on implicits**: Universe polymorphism often uses implicit level parameters (`{u : Level} -> Type u`).
- **Multi-var builds on implicits**: `{A B : Type}` desugars to `{A : Type} -> {B : Type}` which requires implicit binders.
- **Records build on everything**: Record syntax typically uses implicit type parameters and may have multi-field shorthand.

---

## Overview

Add support for:
1. **Implicit binders in types:** `{x : A} -> B` (argument auto-filled with metavar)
2. **Named arguments at call sites:** `foo {x = a} b` (apply by name, not position)
3. **Mixed ordering:** positional and named args can be interleaved freely
4. **Pattern extraction:** `qux {x} a b = ...` to bind implicit arg in patterns

---

## Core Design Principles

### Kernel Stays Simple
- **No implicit flag in kernel (TTK)** - elaborator resolves everything to explicit Pi/App
- Implicits are a surface syntax (TT) feature only
- After elaboration: `f x` becomes `App(App(f, ?meta), x)` with metavar for implicit

### Named Args = Positional Resolution
Named arguments are resolved to positions at elaboration time:
```
foo : (x : Nat) -> (y : Nat) -> Nat

foo a b           -- positional: x=a, y=b
foo {x = a} b     -- named x, positional y: x=a, y=b
foo {y = b} a     -- named y, positional x: x=a, y=b
foo {y = b} {x = a}  -- all named: x=a, y=b
```

---

## Syntax Summary

### Type Signatures
```
-- Explicit arg (must be provided or positionally filled)
(x : A) -> B

-- Implicit arg (auto-filled with metavar if not provided)
{x : A} -> B

-- Mixed
{A : Type} -> (x : A) -> {y : A} -> A
```

### Call Sites
```
f a b c           -- all positional
f {x = a} b       -- x by name, rest positional
f {y = b} {x = a} -- all by name (any order)
f a {z = c}       -- mix positional and named
```

### Pattern Matching (Function Definitions)
```
-- Extract implicit arg into scope (must use declared name)
qux : {n : Nat} -> (a : A) -> (b : B) -> C
qux {n} a b = ... n ...

-- Pattern match on implicit arg
qux {n = Zero} a b = ...
qux {n = Succ m} a b = ...

-- Args must be in declaration order
-- If qux : {n : Nat} -> (a : A) -> (b : B) -> C
-- Then pattern must be: qux {n} a b (or qux {n = pat} a b)
-- NOT: qux a {n} b (wrong order)
```

---

## Elaboration Algorithm

### Call Site Elaboration: `elaborate(fnExpr, args)`

Input: function expression + list of `Arg = Named(name, expr) | Positional(expr)`

```
1. Infer type of fnExpr, get Pi-chain: [(name1, type1, implicit1), (name2, type2, implicit2), ...]

2. Create assignment array: slots[i] = null for each Pi parameter

3. First pass - assign named args:
   For each Named(name, expr) in args:
     Find index i where Pi-chain[i].name == name
     If not found: ERROR "unknown parameter name"
     If slots[i] != null: ERROR "duplicate argument for parameter"
     slots[i] = elaborate(expr, expected=Pi-chain[i].type)

4. Second pass - assign positional args (left-to-right):
   positionalIdx = 0
   For each Positional(expr) in args:
     Find next i >= positionalIdx where slots[i] == null AND Pi-chain[i].implicit == false
     If not found: ERROR "too many positional arguments"
     slots[i] = elaborate(expr, expected=Pi-chain[i].type)
     positionalIdx = i + 1

5. Third pass - fill implicit holes with metavars:
   For each i where slots[i] == null AND Pi-chain[i].implicit == true:
     slots[i] = freshMetavar(type=Pi-chain[i].type)

6. Determine application extent:
   lastFilledIdx = max index where slots[i] != null
   For each i < lastFilledIdx where slots[i] == null:
     If Pi-chain[i].implicit == false:
       ERROR "missing explicit argument: " + Pi-chain[i].name
     Else:
       slots[i] = freshMetavar(type=Pi-chain[i].type)

7. Build result:
   result = fnExpr
   For i = 0 to lastFilledIdx:
     result = App(result, slots[i])
   Return result
```

### Example Walkthrough

```
bar : (x : Nat) -> (y : Nat) -> (z : Nat) -> Nat
bar {z = c} a {y = b}
```

1. Pi-chain: [(x, Nat, explicit), (y, Nat, explicit), (z, Nat, explicit)]
2. slots = [null, null, null]
3. Named pass:
   - `{z = c}` → slots[2] = c
   - `{y = b}` → slots[1] = b
   - slots = [null, b, c]
4. Positional pass:
   - `a` → find first null explicit slot → index 0
   - slots = [a, b, c]
5. Implicit pass: (none are implicit)
6. lastFilledIdx = 2, all slots filled
7. Result: `App(App(App(bar, a), b), c)`

---

## Implementation Phases

### Phase 1: Extend Surface Syntax Types
**Files:** `src/types/tt-core.ts`

```typescript
// Binder info for surface syntax (TT only, not kernel)
export type BinderInfo = 'explicit' | 'implicit';

// Extend BinderKind to include info
export type BinderKind =
  | { tag: 'BPi'; info: BinderInfo }
  | { tag: 'BLam'; info: BinderInfo }
  | { tag: 'BLet'; defVal: TTerm }

// Call site argument (surface syntax)
export type TArg =
  | { tag: 'Positional'; expr: TTerm }
  | { tag: 'Named'; name: string; expr: TTerm }

// New surface term for function calls with args
// Preserves named/positional structure until elaboration
export type TTerm =
  // ... existing variants ...
  | { tag: 'Call'; fn: TTerm; args: TArg[] }  // NEW: f {x = a} b c

// Pattern argument (for function definitions)
export type TPatternArg =
  | { tag: 'ExplicitPat'; pattern: TPattern }
  | { tag: 'ImplicitPat'; name: string; pattern: TPattern }  // {n} or {n = pat}
```

The `Call` node preserves the original argument structure. During elaboration, it becomes a chain of kernel `App` nodes.

### Phase 2: Parser Updates
**Files:** `src/parser/tt-parser.ts`

1. **Implicit binders:** Parse `{x : A}` in type position
   - Reuse existing `LBRACE`/`RBRACE` tokens
   - In `parseParenExpr` area, add branch for `{`

2. **Named arguments:** Parse `{x = expr}` in application position
   - When we see `{` after a function, parse as named arg
   - `{name = expr}` or just `{name}` (shorthand for `{name = name}`)

3. **Pattern syntax:** Parse `{x}` and `{x = pat}` in patterns

### Phase 3: Elaboration Engine
**Files:** `src/types/tt-elab.ts` (major expansion)

1. Implement the call site elaboration algorithm above
2. Track implicit/explicit info from parsed Pi types
3. Generate fresh metavars for unfilled implicits
4. Convert surface App+args to kernel App chain

### Phase 4: Update Type Inference
**Files:** `src/types/tt-typecheck.ts`, `src/types/tt-typecheck-inference.ts`

1. Surface type checker needs to handle BinderInfo
2. Kernel type checker unchanged (no implicits in kernel)

### Phase 5: Pattern Matching Updates
**Files:** `src/parser/tt-parser.ts`, `src/types/tt-pattern-match.ts`

1. Parse `{n}` and `{n = pat}` in pattern position (where `n` is the declared param name)
2. Patterns must be in declaration order (no reordering like at call sites)
3. `{n}` is shorthand for `{n = n}` (bind to variable with same name)
4. During pattern elaboration, implicit pattern args become regular pattern bindings

### Phase 6: Pretty Printing
**Files:** `src/types/tt-core.ts`

1. Print `{x : A} -> B` for implicit Pi
2. Consider: should we print named args in error messages?

---

## Critical Files

| File | Changes |
|------|---------|
| `src/types/tt-core.ts` | Add BinderInfo, TArg types |
| `src/types/tt-kernel.ts` | **Unchanged** (no implicits in kernel) |
| `src/parser/tt-parser.ts` | Parse `{x : A}`, `{x = e}`, patterns |
| `src/types/tt-elab.ts` | Elaboration algorithm (major) |
| `src/types/tt-typecheck.ts` | Handle BinderInfo in surface checking |
| `src/types/tt-pattern-match.ts` | Implicit patterns |

---

## Testing Strategy

### Parser Tests
- `{x : A} -> B` parses as implicit Pi
- `{x : A} -> (y : B) -> {z : C} -> D` mixed chain
- `f {x = a} b` parses with named arg
- `f {x}` shorthand parses

### Elaboration Tests
```
-- Basic implicit
id : {A : Type} -> A -> A
id x = x
-- Calling: id 5 elaborates to id ?A 5, solves ?A = Nat

-- Named args
foo : (x : Nat) -> (y : Nat) -> Nat
foo {y = 1} 2  -- elaborates to foo 2 1

-- Mixed implicit + named
bar : {A : Type} -> (x : A) -> (y : A) -> A
bar {y = b} a  -- elaborates to bar ?A a b

-- Partial application
add : (x : Nat) -> (y : Nat) -> Nat
add 1  -- valid partial application, returns Nat -> Nat
```

### Error Cases
- `foo {z = 1} 2` where foo has no param `z` → error
- `foo {x = 1} {x = 2}` → duplicate error
- `foo 1 2 3` when foo only takes 2 args → too many args
- Missing explicit arg in middle → error

---

## Design Decisions (Resolved)

1. **Shorthand `{x}` at call site:** Yes, `f {x}` means `f {x = x}` (pass variable named x to param x)

2. **Named args work for ALL params:** `{x = e}` syntax works whether param was declared `(x : A)` or `{x : A}`. The curly braces at call site mean "named argument", not "implicit argument".

3. **Pattern arg order:** Pattern args must be in same order as definition. `qux {n} a b` extracts implicit `n` by its declared name.

4. **Surface AST preserves structure:** TT (pre-elab) keeps full info about named vs positional args. Elaborator resolves to kernel App chain.

---

## Inaccessible (Forced/Dot) Patterns

When pattern matching on indexed types, some pattern positions are **forced** by unification
rather than freely chosen. These must be marked as inaccessible to prevent confusion and bugs.

### The Problem

Consider `Equal : (A : Type) -> A -> A -> Type` with constructor `refl : (A : Type) -> (x : A) -> Equal A x x`.

When we match on `eq : Equal Nat a b`:
```
foo : (a : Nat) -> (b : Nat) -> Equal Nat a b -> Nat
foo a b eq = ...
```

The `refl` constructor forces `a` and `b` to be equal. If we write:
```
foo x y (refl _ _) = ...
```

The user might think `x` and `y` are independent, but they're forced to be identical.
This is confusing and error-prone.

### The Rules

1. **Forced patterns must use `_` (wildcard)**
   - A pattern position is "forced" if unification determines its value from other patterns
   - Forced positions must be written as `_` (inaccessible/dot pattern)
   - Example: `foo a _ (refl _ _) = ...` where the second arg is forced to equal `a`

2. **Same variable name used twice must unify to identical**
   - If the same name appears in two pattern positions, they MUST unify
   - Error if unification fails
   - Example: `foo a a (refl _ _) = ...` is valid (both `a`s are the same)
   - Example: `foo a a (refl _ _) = ...` on type `Equal Nat a b` would ERROR if `a ≠ b`

3. **Different names for unified positions is an error**
   - If two positions unify to the same value but use different variable names, error
   - Forces the user to explicitly acknowledge the dependency
   - Example: `foo x y (refl _ _) = ...` is ERROR if `x` and `y` are forced equal
   - Fix: Use `foo x _ (refl _ _)` or `foo _ y (refl _ _)` or `foo x x (refl _ _)`

### Named Arg Syntax for Inaccessible Patterns

With named/implicit arguments, the inaccessible pattern syntax extends naturally:

```
-- Explicit inaccessible (positional)
foo a _ (refl _ _) = ...

-- Named inaccessible
foo a {y = _} (refl {A = _} {x = _}) = ...

-- Same name twice (must unify)
foo {x = a} {y = a} eq = ...  -- valid if x and y unify

-- Different names for unified positions (ERROR)
foo {x = a} {y = b} eq = ...  -- ERROR: a and b forced equal but named differently
```

### Implementation Notes

1. **During pattern checking**: Track which pattern positions are "free" vs "forced"
2. **Unification tracking**: When unification succeeds, record which variables were unified
3. **Name collision detection**: After checking all patterns, verify:
   - Forced positions use `_`
   - Same-named variables unified to identical terms
   - Different-named variables at unified positions → error
4. **Error messages**: Clearly indicate which positions are forced and why

### Examples

```
-- VALID: inaccessible position marked with _
symm : {A : Type} -> {x : A} -> {y : A} -> Equal A x y -> Equal A y x
symm {_} {a} {_} (refl _ _) = refl _ a

-- VALID: same name for unified positions
trans : {A : Type} -> {x : A} -> {y : A} -> {z : A}
      -> Equal A x y -> Equal A y z -> Equal A x z
trans {_} {a} {a} {_} (refl _ _) eq2 = eq2

-- ERROR: different names for forced-equal positions
bad : {A : Type} -> {x : A} -> {y : A} -> Equal A x y -> A
bad {_} {a} {b} (refl _ _) = a   -- ERROR: a and b forced equal
-- Fix: bad {_} {a} {_} (refl _ _) = a

-- ERROR: non-wildcard in forced position
bad2 : {A : Type} -> {x : A} -> {y : A} -> Equal A x y -> A
bad2 {_} {a} {(Succ n)} (refl _ _) = a  -- ERROR: can't pattern match forced position
-- The {y = ...} position is forced by unification, must be _
```

---

## Fully-Solved AST Architecture

### The Problem

Currently, type-checking verifies correctness but doesn't return the solved/elaborated AST.
When we have:
```
foo : (a : Nat) -> (b : Nat) -> Equal Nat a b -> Nat
foo a b eq = Zero
```

The type query for `eq` shows `Equal Nat a b` (the original type from the telescope),
but after pattern matching on `refl`, we know `a = b`. The *solved* type should be
`Equal Nat a a` (with the unification applied).

This matters for:
1. **UI display**: Show users the actual solved types, not the pre-unification versions
2. **Hole filling**: When showing what metavariables were solved to
3. **Error messages**: Reference the concrete types after unification
4. **IDE features**: Hover tooltips, go-to-definition with solved types

### Current Architecture

```
Source → Parse → TT (Surface) → Elaborate → TTK (Kernel)
                                    ↓
                              Type Check
                                    ↓
                              Success/Error
```

The type-checker returns `CheckResult<void>` or `CheckResult<TTKTerm>` (inferred type).
It does NOT return:
- The substitution from unification
- The elaborated term with holes filled
- The context with solved variable types

### Target Architecture

```
Source → Parse → TT (Surface) → Elaborate → TTK (Kernel)
                                    ↓
                              Type Check
                                    ↓
                    ElaborationResult {
                      term: TTKTerm,           // Elaborated term with holes solved
                      type: TTKTerm,           // Solved type
                      substitution: Substitution,  // Full unification results
                      context: TTKContext,     // Context with solved types
                    }
```

### Implementation Plan

#### Phase 1: Thread Substitution Through Type Checking

**Changes to `tt-typecheck.ts`:**

```typescript
// Current:
export function checkType(term: TTKTerm, type: TTKTerm, ctx: TTKContext, path?: IndexPath): void

// New:
export interface CheckResult {
  term: TTKTerm;           // Term with substitutions applied
  substitution: Substitution;
}

export function checkType(
  term: TTKTerm,
  type: TTKTerm,
  ctx: TTKContext,
  path?: IndexPath
): CheckResult
```

Every function that does unification must:
1. Return the substitution it computed
2. Apply the substitution to the term before returning
3. Compose substitutions when calling sub-functions

#### Phase 2: Update Pattern Matching

**Changes to `tt-pattern-match.ts`:**

The `checkClause` and `checkPattern` functions already return `PatternCheckResult` with a substitution.
We need to:
1. Apply the substitution to the RHS after checking it
2. Return the fully-solved clause
3. Update clause types to include the solved form

```typescript
// Current:
export function checkClause(...): TTKTerm  // Returns inferred return type

// New:
export interface ClauseCheckResult {
  clause: TTKClause;       // Clause with substitutions applied to RHS
  returnType: TTKTerm;     // Solved return type
  substitution: Substitution;
  bindings: Array<{ name: string; type: TTKTerm }>;  // With solved types
}

export function checkClause(...): ClauseCheckResult
```

#### Phase 3: Update Declaration Checking

**Changes to `tt-typecheck-decl.ts`:**

```typescript
// Current:
export type CheckResult<T = void> =
  | { success: true; value: T }
  | { success: false; errors: CheckError[] }

// New:
export type CheckResult<T = void> =
  | {
      success: true;
      value: T;
      elaboratedTerm?: TTKTerm;      // Fully solved term
      substitution?: Substitution;    // Unification results
    }
  | { success: false; errors: CheckError[] }
```

#### Phase 4: Update Type Query System

**Changes to `tt-type-query.ts`:**

The type query system needs access to the elaboration results:

```typescript
// New context for type queries
export interface ElaborationContext {
  originalTerm: TTKTerm;       // Before elaboration
  solvedTerm: TTKTerm;         // After elaboration
  substitution: Substitution;  // Unification results
  elabMap: ElabMap;           // Kernel path → surface path
}

// Query function uses solved context
export function queryTypeAtPath(
  path: IndexPath,
  elabCtx: ElaborationContext,
  ctx: TTKContext
): TypeQueryResult
```

#### Phase 5: Store Elaboration Results

**New: `tt-elaboration-store.ts`**

Cache elaboration results for efficient querying:

```typescript
export interface ElaborationStore {
  // Per-declaration results
  declarations: Map<string, {
    originalType: TTKTerm;
    solvedType: TTKTerm;
    originalValue?: TTKTerm;
    solvedValue?: TTKTerm;
    substitution: Substitution;
  }>;

  // Per-clause results (for function definitions)
  clauses: Map<string, Array<{
    bindings: Array<{ name: string; originalType: TTKTerm; solvedType: TTKTerm }>;
    rhsSubstitution: Substitution;
  }>>;
}
```

### Key Functions to Modify

1. **`inferType`** - Return `{ type: TTKTerm, substitution: Substitution }`
2. **`checkType`** - Return `{ term: TTKTerm, substitution: Substitution }`
3. **`checkPattern`** - Already returns substitution, add solved pattern
4. **`checkClause`** - Return solved clause and bindings
5. **`checkFunctionClauses`** - Return solved clauses array
6. **`checkTermDeclaration`** - Return solved term and type
7. **`checkInductiveDeclaration`** - Return solved constructor types

### Migration Strategy

1. **Phase 1**: Add return types without breaking existing code
   - Make substitution optional in return types
   - Callers can ignore it initially

2. **Phase 2**: Update callers one by one
   - Start with type query system
   - Then UI integration
   - Then error reporting

3. **Phase 3**: Make substitution required
   - Remove optional flags
   - All callers must handle substitution

### Example: Before and After

**Before:**
```
foo : (a : Nat) -> (b : Nat) -> Equal Nat a b -> Nat
foo a b eq = Zero
-- Type query for eq: "Equal Nat a b" (original telescope type)
```

**After:**
```
foo : (a : Nat) -> (b : Nat) -> Equal Nat a b -> Nat
foo a b eq = Zero
-- Pattern matching on eq with refl solves: b := a
-- Type query for eq: "Equal Nat a a" (solved type with substitution applied)
-- If eq was matched as (refl _ _), the solved context shows:
--   a : Nat
--   b : Nat [= a]  -- or just show "a" since they're unified
--   eq : Equal Nat a a
```

---

## Relationship to Universe Polymorphism

Once this is implemented, universe polymorphism becomes:
```
-- Parser sees:
id : (A : Type u) -> A -> A

-- Elaborates to (with implicit Level):
id : {u : Level} -> (A : Type u) -> A -> A

-- Call site:
id 5
-- Elaborates to:
id ?u ?A 5
-- Solver determines: ?u = 0, ?A = Nat
```

The `u` in `Type u` triggers implicit Level parameter insertion during elaboration.
