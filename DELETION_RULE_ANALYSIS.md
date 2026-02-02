# Deletion Rule Check: Detailed Analysis

This document traces through specific examples to understand exactly how the deletion rule check should work.

## Example 1: `sym` (Should Work Without K)

```
sym : {A : Type} -> {u v : A} -> Equal u v -> Equal v u
sym refl = refl
```

### Elaboration Context

When we elaborate the clause `sym refl = refl`:

**Function signature gives us:**
- Context: `A : Type, u : A, v : A, _arg : Equal u v`
- Expected RHS type: `Equal v u`

**Pattern: `refl`**
- Constructor type: `refl : {A : Type} -> {a : A} -> Equal a a`
- When matching against `_arg : Equal u v`

### What Happens During Unification

1. **Constructor result type (after instantiation):**
   - `refl` introduces a pattern-local binding `a` (fresh variable in pattern context)
   - Constructor result: `Equal a a`

2. **Expected type:** `Equal u v`

3. **Unification:** `Equal a a` with `Equal u v`
   - Extract indices: `[a, a]` vs `[u, v]`
   - Unify index 0: `a` with `u` → substitution `a := u`
   - Unify index 1: `a` with `v` → substitution `a := v`
   - Derived equation: `u = v` (which we already knew from input type!)

4. **Result:** Unification succeeds with substitution `a := u` (and derives `u = v`)

### Deletion Rule Check

**Question:** Are the constructor indices definitionally equal to expected indices **before** the pattern match forced them equal?

**Constructor indices:** `[a, a]` - same pattern-local variable
**Expected indices:** `[u, v]` - different function parameters

**Key insight:** The constructor has `a = a` (reflexive), but when we match it against `Equal u v`, we're unifying pattern-local `a` with rigid parameters `u` and `v`. The unification forces `u = v`, which is ALLOWED because:
- `u` and `v` are DIFFERENT variables in the function signature
- Pattern matching learns that they're equal (pattern refinement)
- This is the J eliminator - allowed without K!

**Deletion rule verdict:** ALLOWED without K because we're unifying different rigid variables.

### Why Current Implementation Might Reject It

If `checkDeletionRule` runs AFTER applying the substitution `a := u, u := v`:
- Constructor indices become: `[u, u]` (after subst)
- Expected indices become: `[u, u]` (after subst)
- They're equal! So it should PASS...

Actually, maybe the issue is different. Let me think about when `checkDeletionRule` is called at line 1086:

```typescript
checkDeletionRule(ctorTypeAfterHoles, expectedTypeAfterHoles, pattern.name, workEnv);
```

At this point, have we applied the substitutions from unification? Let me check the code structure.

Looking at `constructorDone` flow:
1. Line 964-989: Pop from stacks, get constructor type
2. Line 990-994: Unify constructor result with expected type
3. Line 996-1039: (Commented out) K check during unification
4. Line 1041-1048: Check unification success
5. Line 1050-1081: Apply substitutions to terms
6. Line 1083-1089: (Commented out) checkDeletionRule call

So `checkDeletionRule` is called AFTER applying substitutions. At that point, both types should have the substitutions applied, making them definitionally equal.

## Example 2: `uip` (Should FAIL Without K)

```
uip : {A : Type} -> {x y : A} -> (p q : Equal x y) -> Equal p q
uip refl refl = refl
```

### First Pattern: `refl` matching `p : Equal x y`

**Constructor result:** `Equal a a` (pattern-local `a`)
**Expected:** `Equal x y`
**Unification:** `a := x`, derives `x = y`
**After substitution:** Both become `Equal x x`

This part is ALLOWED (same as sym).

### Second Pattern: `refl` matching `q : Equal x y` (but now `x = y`)

After the first match, the context knows `x = y`.

**Constructor result:** `Equal b b` (pattern-local `b`)
**Expected:** `Equal x y` (but `x` and `y` are known equal)
**Unification:** `b := x`, and since `x = y`, we get `b := y` too

But wait - the pattern variables `p` and `q` are PROOF OBJECTS, not values!

### The Real Issue: Proof Object Indices

Actually, I think I'm confusing things. Let me look at the RESULT type of `uip`:

The function returns `Equal p q` where `p q : Equal x y`.

After matching both patterns as `refl`, we have:
- `p` has been refined to `refl : Equal x x`
- `q` has been refined to `refl : Equal x x`

Now the RHS `refl` needs to type check as `Equal p q`:
- RHS `refl` has type `Equal r r` for some pattern-local `r`
- Expected type: `Equal p q` where both are `refl : Equal x x`
- But `p` and `q` are TERMS (proof objects), not variables!

Hmm, but the function signature says `(p q : Equal x y)`, so `p` and `q` are function parameters of type `Equal x y`.

After pattern matching:
- First pattern `refl` forces `x = y`, so now `p : Equal x x`
- Second pattern `refl` forces... wait, it doesn't force anything new about `q`

Actually, I think the issue is that **both patterns are on the same indexed family**, and the second pattern match tries to match on an equality proof that's already been constrained.

Let me think about this differently.

## The Paper's Criterion

From "Pattern Matching Without K", the deletion rule check is about:
**When matching constructor `c` with result type `D pars is` against expected type `D pars is'`, the indices `is` must be self-unifiable and definitionally equal to `is'`.**

For `sym refl`:
- Constructor indices: `[a, a]` where `a` is pattern-local
- Expected indices: `[u, v]` where `u, v` are function params
- Check: Are `[a, a]` definitionally equal to `[u, v]`?
  - NO! `a` is a fresh variable, `u` and `v` are different parameters
  - But this is ALLOWED because unification learns `u = v` from the input type

Wait, but the input has type `Equal u v`, which means we already know `u` and `v` are POTENTIALLY equal (that's what the proof witnesses). The pattern match on `refl` forces them to be DEFINITIONALLY equal.

I think the key is: **before** the pattern match, are the indices definitionally equal?

For `sym`:
- Before match: `u` and `v` are not definitionally equal (just two parameters)
- Match forces: `u` and `v` to be definitionally equal
- This is ALLOWED without K (this is J!)

For Streicher's K:
```
K : (e : Equal a a) -> P e
K refl = ...
```
- Expected type: `Equal a a` (SAME variable)
- Constructor: `Equal b b`
- Before match: `a` and `a` are trivially definitionally equal (same var)
- Match forces: `b = a` (twice)
- This requires the DELETION RULE because we need to unify `a = a` reflexively

Aha! So the distinction is:
- **J pattern**: Expected type has DIFFERENT variables in indices → allowed
- **K pattern**: Expected type has SAME variable in indices → needs K

## The Correct Check

The deletion rule check should examine the **EXPECTED TYPE** indices, NOT the constructor indices:

```typescript
function checkDeletionRule(
  constructorResultType: TTKTerm,
  expectedType: TTKTerm,
  constructorName: string,
  env: TCEnv<unknown>
): void {
  // Extract indices from expected type
  const expectedIndices = extractIndices(expectedType, indexCount);

  // Check if expected indices are DISTINCT
  // If expected type is Equal x x (same var), this needs K
  // If expected type is Equal x y (different vars), this is J (allowed)

  for (let i = 0; i < expectedIndices.length; i++) {
    for (let j = i + 1; j < expectedIndices.length; j++) {
      const idx_i = expectedIndices[i];
      const idx_j = expectedIndices[j];

      // If indices are the same term, this might need K
      if (areTermsDefinitionallyEqual(idx_i, idx_j)) {
        // Check if this is a pattern match that requires deletion rule
        // ...
      }
    }
  }
}
```

Wait, but `Equal a a` where `a` is a single variable has definitionally equal indices (both are `a`), yet matching on it is ALLOWED for things like `subst : P a -> Equal a a -> P a`.

Let me re-read the paper's examples...

## From the Agda Docs

> "J eliminator definition is accepted. Pattern matching with the constructor refl on the argument x≡y causes x to be unified with y."

So `J P p x y (x≡y)` where we match `refl` on `x≡y : x ≡ y` is ALLOWED.

> "Axiom K is rejected."

So `K P p (e : x ≡ x)` where we match `refl` on `e : x ≡ x` is REJECTED.

The difference:
- J: matches on `x ≡ y` (different variables in TYPE SIGNATURE)
- K: matches on `x ≡ x` (same variable in TYPE SIGNATURE)

## Revised Understanding

The deletion rule check should look at:
**In the EXPECTED TYPE, are there indices that are syntactically the same variable from the FUNCTION SIGNATURE?**

For `sym : Equal u v -> ...` matching `refl` against `Equal u v`:
- Expected indices: `[u, v]`
- These are DIFFERENT variables → J eliminator → ALLOWED

For `K : (e : Equal a a) -> ...` matching `refl` against `Equal a a`:
- Expected indices: `[a, a]`
- These are the SAME variable → deletion rule → NEEDS K

For `subst : P a -> Equal a a -> P a` matching `refl` against `Equal a a`:
- Wait, this also has same variable!
- But this is in `equality-proofs/replace.tt` and should work...

Let me check the replace.tt file...

Actually, `replace.tt` (subst) is:
```
replace : {A : Type} -> {x y : A} -> (P : A -> Type) -> Equal x y -> P x -> P y
replace P refl px = px
```

So it's matching against `Equal x y` (different variables), not `Equal x x`. That's why it works!

## The Final Answer

**The deletion rule check should:**
1. Extract indices from the EXPECTED type (not constructor type)
2. Check if any pair of indices are the SAME RIGID VARIABLE (from function params)
3. If yes, and we're unifying a constructor with distinct indices, this requires K
4. If no (all indices are distinct variables), this is J (allowed)

But wait, sym has distinct variables (`u` and `v`), yet the constructor has `Equal a a` (same pattern-local variable). The unification forces `u = v`, which is fine!

The issue with K/UIP is different - it's about pattern matching on PROOF OBJECTS or about the expected type having reflexive indices.

I think I need to look at actual Agda unification algorithm to understand this properly.

## Summary

I'm still not 100% clear on the exact check, but the pattern is:
- **Allowed:** Expected type has distinct rigid variables as indices (`Equal x y`)
- **Needs K:** Expected type has same rigid variable as indices (`Equal x x`)
- **Special case:** UIP and proof object matching

The current `checkDeletionRule` implementation might be checking the wrong thing. Need to examine exactly what indices it's comparing and when.
