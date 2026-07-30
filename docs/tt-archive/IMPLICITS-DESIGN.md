# Path to Implicit Arguments

This document outlines how to evolve the current "named arguments" feature into full "implicit arguments" where the compiler can infer argument values.

## Implementation Status

- [x] Named parameters in type signatures: `{ A : Type } ->`
- [x] Named patterns in definitions: `id {A} x = x`
- [x] Named arguments in applications: `f { A := T }`
- [x] **Semantic invariant enforced**: Named params cannot be passed positionally
- [ ] Implicit argument inference (Phase 1: hole insertion)
- [ ] Unification-based solving (Phase 2)
- [ ] Instance arguments (Phase 3, future)

## Current State: Named Arguments

The current implementation supports **named arguments** with explicit syntax:

```
-- Declaration with named parameter
id : { A : Type } -> A -> A
id {A} x = x

-- Application with explicit named argument
useId : { T : Type } -> T -> T
useId {T} x = id { A := T } x
```

**Key characteristics:**
- Named parameters use `{ }` in type signatures
- Named patterns use `{name}` in definitions
- Named applications use `{ name := value }` syntax
- Arguments must be provided explicitly (no inference)

## Critical Semantic Invariant: Named vs Positional

**Named parameters can ONLY be passed using `{ name := value }` syntax, never positionally.**

This is the key distinction between named and positional parameters:

```
-- Positional parameter: (A : Type)
-- Named parameter: { A : Type }

-- Given:
Vec : { A : Type } -> Nat -> Type

-- CORRECT: Named arg passed with { := } syntax
example1 : Type
example1 = Vec { A := Nat } Zero

-- INCORRECT: Named arg passed positionally - should be rejected!
example2 : Type
example2 = Vec Nat Zero  -- ERROR: Vec expects 1 positional arg (Nat), got 2
```

### Why This Matters

1. **Arity calculation**: A function's "positional arity" is the count of positional (non-named) parameters. Named parameters don't count toward positional arity.

2. **Over-application detection**: `Vec Nat Zero` should be flagged as over-application because:
   - `Vec` has 0 positional parameters before the first positional one
   - Actually: `Vec` has 1 named param `{A}` and 1 positional param `Nat`
   - So `Vec` expects exactly 1 positional argument
   - Passing `Nat Zero` is 2 positional arguments = over-applied

3. **Path to implicits**: When we add inference, named parameters become implicit:
   - If `{ A := val }` is provided explicitly → use that value
   - If omitted → insert a metavariable hole to be solved by unification
   - Positional arguments are NEVER inferred (they must always be provided)

### Comparison Table

| Parameter Style | Declaration | Pattern | Application | Can be omitted (future) |
|-----------------|-------------|---------|-------------|-------------------------|
| Positional | `(A : Type) ->` | `A` | `f Nat` | No |
| Named | `{ A : Type } ->` | `{A}` | `f { A := Nat }` | Yes (becomes implicit) |

### Implementation (Completed)

The elaboration of applications (`elab.ts:reorderArgs`, `elab.ts:elabToKernelWithMap`) now:

1. Collects the named arg map for the function being called
2. Separates incoming arguments into named `{ x := v }` and positional
3. Places named arguments at their designated positions
4. Fills positional arguments ONLY into non-named positions
5. Errors if:
   - Too many positional arguments (over-application into named slots)
   - Named argument uses unknown name
   - Named argument provided for function without named params

Key files:
- `src/compiler/elab.ts`: `reorderArgs()` enforces positional-only-in-positional-slots
- `src/compiler/compile.ts`: Passes `appNamedArgLookup` during constructor type elaboration

## Goal: Implicit Arguments

The goal is to support **implicit arguments** where the compiler infers values:

```
-- Same declaration
id : { A : Type } -> A -> A
id {A} x = x

-- Application WITHOUT explicit argument - A is inferred from context
useId : { T : Type } -> T -> T
useId {T} x = id x  -- A := T inferred from x : T
```

## Implementation Phases

### Phase 1: Hole Insertion (Current Foundation)

Before inference can work, we need to insert holes where implicit arguments are missing:

```
-- User writes:
id x

-- Elaborator rewrites to:
id { A := ?_A } x

-- Where ?_A is a metavariable to be solved
```

**Changes needed:**
1. During elaboration of `App` nodes, check if the function has implicit parameters
2. If the application is missing implicit arguments, insert holes for them
3. Track which positions are implicit vs explicit

**Key insight:** The current `NamedArgMap` already tracks which positions are "named" (i.e., can be implicit). We just need to:
- Rename it to track "implicit" positions
- Add hole insertion during elaboration when implicit args are missing

### Phase 2: Unification-Based Inference

Once holes are inserted, the type checker's unification will solve them:

```
-- Given: id : { A : Type } -> A -> A
-- And: x : Nat
-- Checking: id ?_A x against expected type Nat

-- Unification of (A -> A)[A := ?_A] = (?_A -> ?_A) with Nat -> ?result
-- Solves: ?_A := Nat
```

**What we have:**
- Unification already exists in the type checker
- MetaVars are already tracked and solved

**What we need:**
- Connect hole insertion to metavar creation
- Ensure metavars from implicit args are solved during type checking
- Report unsolved metas as errors

### Phase 3: Instance Arguments (Future)

More advanced implicit arguments that are resolved via typeclass-like lookup:

```
-- Instance argument syntax (potential)
show : { A : Type } -> [Show A] -> A -> String
```

This is significantly more work and can be deferred.

## Detailed Design: Hole Insertion

### When to Insert Holes

Given a function application `f args...`:

1. Look up `f`'s type and its implicit argument positions
2. For each implicit position not explicitly provided with `{ name := val }`:
   - Insert a fresh hole/metavar at that position
3. Proceed with type checking

### Elaboration Changes

In `elabToKernelWithMap` for `App`:

```typescript
case 'App': {
  // Collect the application spine
  const { head, args } = collectAppSpine(term);

  // Look up implicit arg map for the function
  let implicitMap: ImplicitArgMap | undefined;
  if (head.tag === 'Const') {
    implicitMap = lookup(head.name);
  }

  if (implicitMap && implicitMap.size > 0) {
    // Check which implicit positions are missing
    const providedPositions = new Set(
      args.filter(a => a.kind === 'named')
          .map(a => implicitMap!.get(a.name))
          .filter(p => p !== undefined)
    );

    // Insert holes for missing implicit positions
    const argsWithHoles: SpineArg[] = [];
    let positionalIdx = 0;

    for (let pos = 0; pos < totalExpectedArgs; pos++) {
      if (implicitMap.has(positionToName(pos))) {
        if (!providedPositions.has(pos)) {
          // Insert hole for missing implicit
          argsWithHoles.push({
            kind: 'named',
            name: positionToName(pos),
            term: freshHole()
          });
        }
      }
      // ... handle explicit args
    }
  }
  // ...
}
```

### Type Checking Integration

The type checker already handles holes/metavars. Key integration points:

1. **Hole creation**: `freshHole()` should create a metavar that gets registered
2. **Unification**: When checking `f ?_A x : T`, unification constrains `?_A`
3. **Solution application**: After checking, apply metavar solutions to the term
4. **Error reporting**: Unsolved metas for implicit args = inference failure

## Data Structure Changes

### Current: NamedArgMap
```typescript
type NamedArgMap = Map<string, number>;  // name -> position
```

### Proposed: ImplicitArgInfo
```typescript
type ImplicitArgInfo = Map<string, {
  position: number;
  isImplicit: boolean;  // true = can be inferred, false = named but explicit
}>;
```

Or simply treat all named args as potentially implicit.

### Surface Syntax Options

**Option A: All named args are implicit**
- `{ A : Type }` = implicit (current named binder syntax)
- `(A : Type)` = explicit
- No new syntax needed

**Option B: Separate implicit and named**
- `{ A : Type }` = named but explicit
- `[A : Type]` = implicit (inferred)
- More syntax, more control

Recommend **Option A** for simplicity - it matches Agda/Lean behavior.

## Test Cases for Implicit Args

```
-- Basic inference
id : { A : Type } -> A -> A
id {A} x = x

-- Should infer A := Nat
test1 : Nat -> Nat
test1 n = id n

-- Should infer A := Nat, B := Bool
const : { A : Type } -> { B : Type } -> A -> B -> A
const {A} {B} a b = a

test2 : Nat -> Bool -> Nat
test2 n b = const n b

-- Explicit override when inference is wrong or ambiguous
test3 : Type -> Type
test3 T = id { A := T } T  -- Explicit: A := T
```

## Migration Path

1. **Named args work** (DONE) - explicit `{ A := T }` syntax
2. **Hole insertion** - missing implicit args become holes
3. **Inference** - unification solves the holes
4. **Error messages** - good errors for unsolved metas
5. **Instance args** (future) - typeclass-like resolution

## Open Questions

1. **Ambiguity**: What if inference is ambiguous? Error or pick first solution?
2. **Eager vs lazy**: Insert all implicit holes upfront, or lazily during checking?
3. **Syntax**: Allow `_` to mean "infer this"? e.g., `id _ x`
4. **Visibility**: Should implicit args be visible in error messages?

## References

- Agda implicit arguments: https://agda.readthedocs.io/en/latest/language/implicit-arguments.html
- Lean implicit arguments: https://lean-lang.org/lean4/doc/implicit.html
- Coq implicit arguments: https://coq.inria.fr/refman/language/extensions/implicit-arguments.html
