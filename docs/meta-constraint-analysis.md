# Meta-Variable and Constraint Handling Analysis

## The Problem

Consider this code:
```
swap : {A : Type} -> {B : Type} -> {C : Type} -> (f : A -> B -> C) -> (B -> A -> C)
swap f b a = f a b

myFunc : Nat -> Bool -> Bool
myFunc n b = b

test : Nat -> Bool
test n = swap myFunc n True
```

The `test` function should **fail** type checking:
- `swap myFunc` has type `(Bool -> Nat -> Bool)` (arguments swapped)
- So `swap myFunc n True` passes `n : Nat` where `Bool` is expected

But our type checker **accepts** this code. Why?

## Current Algorithm

### 1. Implicit Argument Elaboration (elab.ts)
When elaborating `swap myFunc n True`, implicit arguments are inserted as Holes:
```
swap ?_implicit0 ?_implicit1 ?_implicit2 myFunc n True
```

### 2. Type Inference for Application (checker.ts - APP rule)
For each application `f arg`:
1. Infer type of `f` → must be a Pi type `Π x : A. B`
2. Check `arg` against domain `A`
3. Return type is `B[x := arg]`

### 3. Hole Checking (checker.ts - HOLE rule)
When checking a Hole against expected type `T`:
1. Create a fresh meta `?m` with type `T`
2. Add to metaVars map
3. Return the meta as the elaborated term

### 4. Type Conversion (checker.ts - CONV rule)
When checking term `t` against expected type `T`:
1. Infer type of `t` → `T'`
2. Unify `T'` with `T`
3. If unification succeeds, `t` type-checks

### 5. Unification (unify.ts)
When unifying `A` with `B`:
- If either is a Meta → create constraint `meta = other`
- If both are Pi → unify domains, unify bodies
- etc.

Constraints are accumulated and returned, not immediately solved.

### 6. Constraint Solving (meta.ts)
`solveMetasAndConstraints` is called at definition boundaries:
- Turn constraints into solutions if the RHS is in scope
- Detect unsolvable constraints

## Where It Breaks: The Swap Example

Let's trace through `swap myFunc n True`:

**Step 1**: Check `swap` - infer its polymorphic type

**Step 2**: Check `?_implicit0` against `Type`
- Create meta `?m0` for the type
- After elaboration: `swap ?m0`

**Step 3**: Check `?_implicit1` against `Type`
- Create meta `?m1`
- After: `swap ?m0 ?m1`

**Step 4**: Check `?_implicit2` against `Type`
- Create meta `?m2`
- After: `swap ?m0 ?m1 ?m2`

**Step 5**: Check `myFunc` against `(?m0 -> ?m1 -> ?m2)`
- `myFunc : Nat -> Bool -> Bool`
- Unify `(Nat -> Bool -> Bool)` with `(?m0 -> ?m1 -> ?m2)`
- **GENERATES CONSTRAINTS**: `?m0 = Nat`, `?m1 = Bool`, `?m2 = Bool`
- After: `swap ?m0 ?m1 ?m2 myFunc` with constraints in env

**Step 6**: Compute result type
- Body of Pi after checking `myFunc` is `(?m1 -> ?m0 -> ?m2)` (swapped!)
- After substitution: `(?m1 -> ?m0 -> ?m2)`

**Step 7**: Check `n` against domain `?m1`
- `n : Nat`
- Unify `Nat` with `?m1`
- **GENERATES CONSTRAINT**: `?m1 = Nat`
- **BUG**: This should conflict with `?m1 = Bool` from Step 5!

**Step 8**: Check `True` against domain `?m0`
- `True : Bool`
- Unify `Bool` with `?m0`
- **GENERATES CONSTRAINT**: `?m0 = Bool`
- **BUG**: This should conflict with `?m0 = Nat` from Step 5!

## The Design Gap

The core issue is **deferred constraint solving**:

1. Constraints are generated during type checking
2. Constraints are NOT solved until `solveMetasAndConstraints` is called
3. During the APP rule, we use the function body type **with unresolved metas**
4. Subsequent arguments are checked against these unresolved metas
5. Conflicting constraints are generated but not detected

The fix in `combineUnificationResults` ensures constraints are properly accumulated during unification. But this doesn't help because:
- Constraints are still deferred
- When checking argument `n` against `?m1`, we don't know `?m1 = Bool` yet
- We just create a new constraint `?m1 = Nat`

## Possible Solutions

### Option A: Eager Constraint Solving
After each argument check in the APP rule, immediately solve constraints.
- **Pro**: Simple to implement
- **Con**: May solve constraints prematurely, breaking dependent types

### Option B: Constraint Conflict Detection
When adding a new constraint for a meta, check for existing constraints.
- **Pro**: Detects conflicts immediately
- **Con**: Complex interaction with scope, may cause false positives

### Option C: Zonking (Lean/GHC approach)
"Zonk" the result type by substituting solved metas before using it.
- **Pro**: Clean separation between generation and use
- **Con**: Need to be careful about De Bruijn indices across scopes

### Option D: Two-Phase Checking
First pass: infer types, generate constraints
Second pass: solve constraints, re-check with solutions
- **Pro**: Clean separation
- **Con**: Significant architectural change

## Research: How Other Systems Handle This

### Lean 4's Approach
([Source](https://leanprover-community.github.io/lean4-metaprogramming-book/main/04_metam.html))

Lean uses `isDefEq` for unification which can **immediately assign metavariables**. When unifying
`?m` with a term `t`, if `?m` is "assignable", it gets assigned `?m := t` right away. Subsequent
operations see the assignment.

Key insight: **Metavariables are mutable** - they get filled in during unification, not at a
later constraint-solving phase.

### GHC's "Zonking"
([Source](https://ghc-compiler-notes.readthedocs.io/en/latest/notes/compiler/typecheck/TcMType.hs.html))

GHC's "zonking" is the process of "ripping out mutable variables and replacing them with a real Type."
This is done:
1. **During type checking** - "zonk on the fly" to see current solutions
2. **At the end** - final cleanup of any remaining metavariables

The key insight: "Zonking is exactly analogous to our use of contexts as substitutions. Zonking a
unification variable replaces the variable with its solution, if any."

### Agda's Constraint Solving
([Source](https://agda.github.io/agda/Agda-TypeChecking-MetaVars.html))

Agda uses a more sophisticated constraint-based approach with **postponement**. When a constraint
can't be solved immediately, it's recorded and re-tried later when more information is available.

Key insight: Constraints can be **re-activated** when dependent metas are solved.

### Common Thread

All systems need to **propagate metavariable solutions** to subsequent type checking operations.
The difference is when and how:
- **Lean**: Immediate assignment during unification
- **GHC**: On-the-fly substitution ("zonking")
- **Agda**: Re-activation of postponed constraints

## Recommended Solution: Zonking on the Fly

Based on the research, the cleanest solution for our architecture is **zonking on the fly** during
unification. Specifically:

**Before unifying `A` with `B`, substitute any known meta solutions into both `A` and `B`.**

This ensures that when we unify `Nat` with `??m1`, if we already have a constraint `?m1 = Bool`,
we actually unify `Nat` with `Bool` → CONFLICT detected immediately.

### Implementation

In `TCEnv.unifyTerms()`:
```typescript
unifyTerms(lhs: TTKTerm, rhs: TTKTerm): TCEnv<S> {
  // ZONK: Substitute known meta solutions before unifying
  const zonkedLhs = this.zonkTerm(lhs);
  const zonkedRhs = this.zonkTerm(rhs);

  const result = unifyTerms(zonkedLhs, zonkedRhs, {
    mode: this.options.mode,
    definitions: this.definitions
  });
  // ... rest of the method
}

zonkTerm(term: TTKTerm): TTKTerm {
  // Look up constraints for any metas in the term
  // Replace with their RHS if found
  // Recursively zonk the result
}
```

### Why This Works

1. **For swap**: When checking `n` against `??m1`, we zonk `??m1` → `Bool` (from constraint).
   Then unify `Nat` with `Bool` → FAIL ✓

2. **For vecConcat**: The metas used in recursive calls have fresh constraints each time.
   Zonking doesn't introduce cross-scope issues because we're substituting the constraint
   RHS directly, not shifting De Bruijn indices.

### Key Difference from Previous Attempts

Previous attempts tried to substitute constraints into the **function body** before computing
the result type. This required shifting De Bruijn indices, which is error-prone.

The zonking approach substitutes constraints into the **terms being unified**, which are already
in the correct scope. No index shifting needed.

## Next Steps

1. Implement `zonkTerm` method on TCEnv
2. Call it at the start of `unifyTerms`
3. Test with both swap and vecConcat cases
4. Run full test suite
