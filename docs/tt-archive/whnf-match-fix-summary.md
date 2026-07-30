# Fix: WHNF Reduction of Match Terms and Type Alias Normalization

## Problem

The `#absurd` marker was failing when used with type aliases like `Not`:

```
Not : Type -> Type
Not A = A -> Void

succNotZero : {n : Nat} -> Not (Equal (Succ n) Zero)
succNotZero {n := _} eq = #absurd  -- FAILED
```

Two separate but related bugs:

### Bug 1: Match Terms with Hole Scrutinees Were Reducing Prematurely

**Symptom**: `Not (Equal Zero Zero)` reduced to `(?_scrutinee -> Void)` instead of `(Equal Zero Zero -> Void)`.

**Root Cause**: In type theory, pattern matching (ι-reduction) should only reduce when the scrutinee is a **known value** (constructor). When the scrutinee is unknown (Hole, Var, Meta), the match is **stuck** (neutral term) and should not reduce.

The bug: `whnf` was matching `PVar` patterns against `Hole(_scrutinee)`, creating spurious bindings:
1. Match term: `match ?_scrutinee with A => A -> Void`
2. `matchPattern(PVar "A", Hole(_scrutinee))` returned `[Hole(_scrutinee)]` ✗ WRONG
3. Substituted into rhs: `Pi _ : Hole(_scrutinee) . Void` ✗ WRONG

**Fix** ([whnf.ts:469-471](src/compiler/whnf.ts#L469-L471)): Don't perform ι-reduction when scrutinee is stuck:

```typescript
if (scrut.tag === 'Hole' || scrut.tag === 'Meta' || scrut.tag === 'Var') {
  // Scrutinee is stuck - don't reduce
  return { tag: 'Match', scrutinee: scrut, clauses: term.clauses };
}
```

### Bug 2: Normalization Wasn't Reducing Under Pi Binders

**Symptom**: Pattern arity checking failed because `Not (Equal ...)` wasn't being expanded.

**Root Cause**: `whnf` doesn't reduce under binders (standard for WHNF). When normalizing `{n : Nat} -> Not (Equal ...)`, the `Not` in the return type wasn't expanded.

**Fix** ([compile.ts:2847-2866](src/compiler/compile.ts#L2847-L2866), [compile.ts:5251-5270](src/compiler/compile.ts#L5251-L5270)): Extract the return type, normalize it, then reconstruct:

```typescript
// Extract Pi spine: {n : Nat} -> <body>
const piSpine = extractPiSpine(type);

// Normalize just the return type: Not A → A -> Void
const normalizedReturnType = whnf(piSpine.body, { definitions, fuel: 100 });

// Reconstruct: {n : Nat} -> (normalized return type)
let normalizedType = normalizedReturnType;
for (let i = piSpine.binders.length - 1; i >= 0; i--) {
  const binder = piSpine.binders[i];
  normalizedType = {
    tag: 'Binder',
    name: binder.name,
    binderKind: { tag: 'BPi' },
    domain: binder.type,
    body: normalizedType,
  };
}
```

## Theoretical Foundation

### Pattern Matching Reduction in Type Theory

In λ-calculus with pattern matching, a match expression:

```
case scrut of
  pat₁ -> e₁
  pat₂ -> e₂
```

reduces (ι-reduction) only when:
1. `scrut` is in weak head normal form (WHNF)
2. `scrut` matches a pattern definitively (i.e., is a constructor or known value)

When `scrut` is a variable `x`, meta `?m`, or hole, the match is **stuck** (neutral term). Even if the pattern is a catch-all `PVar`, we cannot reduce because we don't know what `scrut` is yet.

### Weak Head Normal Form (WHNF)

WHNF reduces the **head** of a term but not under binders:
- `(λx. e) v → e[x := v]` (β-reduction) ✓
- `λx. ((λy. e) v)` does NOT reduce to `λx. e[y := v]` ✗

This is why normalizing `{n : Nat} -> Not A` doesn't expand `Not` - it's under a binder!

### How Lean/Agda Handle This

Lean and Agda:
1. **Don't use Match for non-case-analysis definitions**: `def not (A : Type) := A → Empty` compiles to a constant, not a Match term
2. **Normalize types before arity checking**: Extract the return type, normalize it, count parameters
3. **Match terms remain stuck until applied**: Pattern matching only reduces when scrutinees are known

Our fix aligns with these principles.

## Testing

Created test: [src/test-programs/absurd-with-not.tt](src/test-programs/absurd-with-not.tt)

```
succNotZero : {n : Nat} -> Not (Equal (Succ n) Zero)
succNotZero {n := _} eq = #absurd
```

Now passes! ✓

All 1837 tests pass ✓
