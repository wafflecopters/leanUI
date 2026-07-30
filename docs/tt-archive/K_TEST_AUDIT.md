# Axiom K Test Audit

This document tracks the status of all axiom K related tests and what needs to be fixed.

## Test Files Status

### ✅ Correctly Marked (Work Without K)

These tests should SUCCEED without axiom K and are correctly marked:

| File | Annotation | Status | Notes |
|------|------------|--------|-------|
| `equality-proofs/sym.tt` | `@test success` | ✓ Correct | Pattern matches `Equal u v` (different vars) |
| `equality-proofs/trans.tt` | `@test success` | ✓ Correct | Pattern matches `Equal u v` and `Equal v w` |
| `equality-proofs/cong.tt` | `@test success` | ✓ Correct | Pattern matches `Equal u v` (different vars) |
| `equality-proofs/replace.tt` | `@test success` | ✓ Correct | Pattern matches `Equal x y` (different vars, subst) |
| `pattern-without-k/valid-without-k.tt` | `@test success` | ✓ Correct | Matches `refl` against `Equal a a` (same var but valid) |

### ⚠️  Need Fixing (Require K but have wrong error expectations)

These tests should FAIL without K with "axiom K" error, but currently expect wrong errors:

| File | Current | Should Be | Issue |
|------|---------|-----------|-------|
| `pattern-without-k/uip-fails.tt` | `@test failure` + `@error "Zonk recheck"` | `@error "axiom K"` or `@error "deletion rule"` | Currently hits zonk error instead of K check |
| `pattern-without-k/uip-with-k.tt` | `@test failure` + `@error "Zonk recheck"` + `@assumeK` | `@test success` + `@assumeK` | With K enabled, should SUCCEED! |
| `pattern-without-k/streicher-k-fails.tt` | `@test failure` + `@error "has type"` | `@error "axiom K"` or `@error "deletion rule"` | Currently hits type error, needs K check |
| `pattern-without-k/streicher-k-with-k.tt` | `@test failure` + `@error "has type"` + `@assumeK` | Should investigate - might be legitimate type error |

## What Each Test Does

### UIP (Uniqueness of Identity Proofs)

```
uip : {A : Type} -> {x y : A} -> (p q : Equal x y) -> Equal p q
uip refl refl = refl
```

**Why it needs K:** Pattern matches on PROOF OBJECTS twice. The second `refl` pattern requires matching an arbitrary equality proof against the reflexivity constructor, which needs K.

**Expected behavior:**
- WITHOUT K (`uip-fails.tt`): Should fail with "requires axiom K" error
- WITH K (`uip-with-k.tt`): Should SUCCEED

### Streicher's K

```
streichersK : (A : Type) -> (a : A) -> (P : Equal a a -> Type) ->
              (p : P refl) -> (e : Equal a a) -> P e
streichersK A a P p refl = refl
```

**Why it needs K:** Pattern matches on `e : Equal a a` where BOTH indices are the same variable `a`. This is the canonical K elimination: proving that any self-equality proof behaves like `refl`.

**Expected behavior:**
- WITHOUT K (`streicher-k-fails.tt`): Should fail with "requires axiom K" error
- WITH K (`streicher-k-with-k.tt`): Need to investigate the type error - might be legitimate

### Valid Without K Examples

```
-- From valid-without-k.tt
subst : {A : Type} -> {a : A} -> (P : A -> Type) -> P a -> Equal a a -> P a
subst P pa refl = pa

cong_refl : {A B : Type} -> (f : A -> B) -> {a : A} -> Equal a a -> Equal (f a) (f a)
cong_refl f refl = refl
```

**Why these work:** Even though they match against `Equal a a` (same variable), the pattern matching is on the VALUE `a`, not the proof. The J eliminator allows this.

## Implementation TODO

1. **Fix UIP tests:**
   - Remove `@error "Zonk recheck"` from both files
   - `uip-fails.tt`: Add `@error "axiom K"` or `@error "deletion rule"`
   - `uip-with-k.tt`: Change to `@test success` (should pass with K!)

2. **Fix Streicher K tests:**
   - `streicher-k-fails.tt`: Change to `@error "axiom K"` or `@error "deletion rule"`
   - `streicher-k-with-k.tt`: Investigate the type error - might need fixing

3. **Implement deletion rule check:**
   - Re-enable `checkDeletionRule` call in patterns.ts:1089
   - Debug why it was rejecting sym/trans (should only reject K-requiring patterns)
   - Ensure error message mentions "axiom K" or "deletion rule"

4. **Fix any zonk recheck issues:**
   - The comments mention holes from padding wildcards causing zonk issues
   - This might be a separate bug from the K check

## The Deletion Rule Check

Based on research, the check should:

**REJECT (needs K):**
- Pattern matching on `Equal x x` where `x` is a single rigid variable AND the match is non-trivial
- UIP: matching proof objects that could be distinct
- Streicher's K: eliminating arbitrary self-equality proofs

**ACCEPT (J eliminator):**
- Pattern matching on `Equal x y` where `x` and `y` are different rigid variables
- Even `Equal x x` is allowed if it's just learning that a value equals itself (not about proofs)

The distinction is subtle and requires understanding the EXPECTED TYPE's structure before pattern-induced substitutions.

## Test Execution

To run these tests:
```bash
# All K-related tests
npx vitest run src/test-programs/tt-runner.test.ts -t "axiom K"

# Just UIP
npx vitest run src/test-programs/tt-runner.test.ts -t "UIP"

# Just Streicher
npx vitest run src/test-programs/tt-runner.test.ts -t "Streicher"

# Basic equality (should all pass without K)
npx vitest run src/test-programs/tt-runner.test.ts -t "sym\|trans\|cong\|replace"
```

## References

- See `AXIOM_K.md` for conceptual overview
- See `DELETION_RULE_ANALYSIS.md` for detailed technical analysis
- See `src/compiler/patterns.ts:867-959` for `checkDeletionRule` implementation
