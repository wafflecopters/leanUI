# Axiom K in LeanUI

## Overview

Axiom K (also called the deletion rule or K axiom) is a principle in dependent type theory that determines whether you can pattern match on equality proofs in certain ways. This document explains what axiom K is, what works with and without it, and how it's implemented in LeanUI.

## What Works WITHOUT Axiom K

These fundamental equality operations **do not require K** and should work even with `@assumeK` disabled:

### ✓ sym (Symmetry)
```
sym : {A : Type} -> {x y : A} -> Equal x y -> Equal y x
sym refl = refl
```
**Why it works:** Pattern matching on `refl : Equal a a` against expected type `Equal x y` unifies two **different** function parameters (`x` with `y`). This is allowed without K.

### ✓ trans (Transitivity)
```
trans : {A : Type} -> {x y z : A} -> Equal x y -> Equal y z -> Equal x z
trans refl refl = refl
```
**Why it works:** Each pattern match unifies different variables from the function signature.

### ✓ cong (Congruence)
```
cong : {A B : Type} -> (f : A -> B) -> {x y : A} -> Equal x y -> Equal (f x) (f y)
cong f refl = refl
```
**Why it works:** Matching `refl : Equal a a` against `Equal x y` unifies `x` with `y`.

### ✓ subst (Substitution)
```
subst : {A : Type} -> {x y : A} -> (P : A -> Type) -> Equal x y -> P x -> P y
subst P refl px = px
```
**Why it works:** Same reasoning as above.

### ✓ J Eliminator (Path Induction)
The fundamental eliminator for equality - present in all intensional type theories.

## What REQUIRES Axiom K

These operations **cannot be implemented** without axiom K:

### ✗ UIP (Uniqueness of Identity Proofs)
```
uip : {A : Type} -> {x y : A} -> (p q : Equal x y) -> Equal p q
uip refl refl = refl
```
**Why it needs K:** This requires pattern matching that forces equality proofs themselves to be equal, which goes beyond J.

### ✗ Streicher's K
```
K : {A : Type} -> {x : A} -> (P : Equal x x -> Type) ->
    P refl -> (e : Equal x x) -> P e
K P p refl = refl
```
**Why it needs K:** Pattern matching on `e : Equal x x` where the same variable appears on both sides requires the deletion rule.

### ✗ All Loops Are Refl
```
all-loops-refl : {A : Type} -> {x : A} -> (p : Equal x x) -> Equal p refl
all-loops-refl refl = refl
```
**Why it needs K:** Directly proves that all self-equality proofs are equal to reflexivity.

## The Technical Distinction

### The Deletion Rule

The **deletion rule** in unification states that reflexive equations of the form `x = x` can be automatically eliminated (deleted) as trivially satisfied.

**With K enabled:** Equations like `x = x` are deleted during unification.
**Without K:** These equations cannot be deleted, making certain pattern matches impossible.

### Pattern Matching: J vs K

The key difference is **what gets unified** during pattern matching:

| Pattern Match | Constructor Type | Expected Type | Indices Unified | Needs K? |
|--------------|------------------|---------------|-----------------|----------|
| `sym refl` | `Equal a a` | `Equal x y` | Different vars: `x`, `y` | **NO** |
| `K P p refl` | `Equal a a` | `Equal x x` | Same var twice: `x` | **YES** |
| `uip refl refl` | `Equal p p` | `Equal p q` | Proof objects | **YES** |

### Indices vs Parameters

For the type `Equal : {A : Type} -> A -> A -> Type`:
- `{A : Type}` is a **parameter** (same for all constructors)
- The two arguments of type `A` are **indices** (can vary)

The deletion rule check examines whether indices in the constructor's result type are definitionally equal to indices in the expected type **before** pattern matching forces them to be equal.

## Implementation in LeanUI

### Current Status

- **Default behavior:** Axiom K is ENABLED by default (matches Lean's behavior)
- **Directive:** `@assumeK` can be used to explicitly enable K
- **Without K:** Implementation needed in `src/compiler/unify.ts`

### The Correct Implementation

The deletion rule is implemented **inside unification**, NOT as a post-check. There are two key changes:

#### 1. Disable the Deletion Rule in Unification

When unifying `x = x` (reflexive equation), WITHOUT K you should get stuck instead of silently succeeding:

```typescript
// In src/compiler/unify.ts, in the Var case:
if (lhs.tag === 'Var' && rhs.tag === 'Var') {
  if (lhs.index === rhs.index) {
    // WITHOUT K: This is the deletion rule - reject it!
    if (!options.assumeK) {
      return {
        success: false,
        reason: 'deletion-rule' // or 'reflexive'
      };
    }
    // WITH K: Deletion rule succeeds (current behavior)
    return emptySuccess;
  } else {
    // Different variables: solution rule (always allowed)
    return unifyVariables(lhs.index, rhs.index, options);
  }
}
```

#### 2. Self-Unifiability Check for Injectivity

Before applying the injectivity rule for constructors, check that indices are self-unifiable:

```typescript
// In src/compiler/unify.ts, in the constructor case:
if (lhs.tag === 'Const' && rhs.tag === 'Const' && lhs.name === rhs.name) {
  // Injectivity rule: c s̄ = c t̄  →  s̄ = t̄

  // BUT FIRST: check that indices are self-unifiable
  const inductiveInfo = getIndexedFamilyInfo(lhs.name, options.definitions);
  if (inductiveInfo && inductiveInfo.indexCount > 0) {
    const indices = extractIndices(lhs, inductiveInfo.indexCount);
    const selfUnifyResult = unifyTerms(indices, indices, options);

    if (!selfUnifyResult.success && selfUnifyResult.reason === 'deletion-rule') {
      // Indices aren't self-unifiable → injectivity would need K
      return {
        success: false,
        reason: 'injectivity-blocked'
      };
    }
  }

  // Safe to proceed with injectivity
  return combineUnificationResults(
    unifyLevels(lhs.level, rhs.level, options),
    unifyArgs(lhs.args, rhs.args, options),
    options
  );
}
```

### Why This Works

**Example: `sym refl = refl`**
- Pattern: `refl : Equal a a` (pattern-local `a`)
- Expected: `Equal u v` (function params)
- Unification: `a = u` and `a = v`
- These are NOT reflexive equations (`a ≠ a`, it's `a = u` and `a = v`)
- Unification succeeds, derives `u = v` (J eliminator - allowed!)

**Example: Streicher's K**
- Pattern: `refl : Equal a a`
- Expected: `Equal x x` (SAME variable!)
- Unification: `a = x` and `a = x`
- When checking injectivity: need to verify indices `[x, x]` are self-unifiable
- Self-unify: `x = x` → **STUCK** (deletion rule blocked!)
- Injectivity fails → pattern match rejected

**Example: `uip refl refl`**
- First pattern succeeds (like sym)
- Second pattern: now matching on proof objects
- The structure forces reflexive equations in indices
- Self-unifiability check catches it

### Test Files

| File | Expected Behavior | Currently |
|------|-------------------|-----------|
| `pattern-without-k/valid-without-k.tt` | SUCCESS without K | ✓ Should pass |
| `pattern-without-k/uip-fails.tt` | FAILURE without K | × Currently expects zonk error |
| `pattern-without-k/uip-with-k.tt` | SUCCESS with @assumeK | × Currently expects failure |
| `pattern-without-k/streicher-k-fails.tt` | FAILURE without K | × Currently expects type error |
| `pattern-without-k/streicher-k-with-k.tt` | SUCCESS with @assumeK | ? Need to verify |
| `equality-proofs/sym.tt` | SUCCESS (no K needed) | ✓ Should pass |
| `equality-proofs/trans.tt` | SUCCESS (no K needed) | ✓ Should pass |

### Implementation Plan

1. **Remove incorrect `checkDeletionRule` function** - The post-unification check approach is wrong
2. **Implement deletion rule in `unify.ts`** - Add reflexive equation check in the Var case
3. **Add self-unifiability check** - Check indices before applying injectivity
4. **Add `@withoutK` directive** - For explicitly disabling K (opposite of `@assumeK`)
5. **Fix test expectations** - Update test files to expect correct errors
6. **Re-enable test suite** - Remove `describe.skip` from axiom-k-soundness.test.ts

### The Previous Bug

The previous implementation tried to check deletion rule AFTER unification as a post-check in pattern matching. This is **fundamentally wrong**:
- The deletion rule is part of unification itself, not a separate check
- Checking after unification is too late - unification already succeeded with deletion
- The check needs to happen DURING unification when we encounter `x = x`

## References

- [Without K — Agda Documentation](https://agda.readthedocs.io/en/latest/language/without-k.html)
- [Pattern Matching Without K (Cockx et al.)](https://dl.acm.org/doi/10.1145/2628136.2628139)
- [Programming Language Foundations in Agda – Equality](https://plfa.github.io/Equality/)
- [HoTT: Just Kidding](https://homotopytypetheory.org/2011/04/10/just-kidding-understanding-identity-elimination-in-homotopy-type-theory/)
- [nLab: Axiom K](https://ncatlab.org/nlab/show/axiom+K+(type+theory))

## Implementation TODO

- [ ] Modify `unify.ts` to reject reflexive equations (`x = x`) when K is disabled
- [ ] Add self-unifiability check before applying injectivity rule
- [ ] Remove incorrect `checkDeletionRule` function from `patterns.ts`
- [ ] Create `@withoutK` directive for explicitly disabling K (opposite of `@assumeK`)
- [ ] Update test file error expectations
- [ ] Re-enable axiom K test suite
- [ ] Add better error messages that explain WHY a pattern needs K
- [ ] Document the relationship between K and Homotopy Type Theory
