# With Abstraction (Following Agda)

## Overview

Implement Agda-style `with` abstraction for pattern matching inside term bodies. This follows Agda's proven approach precisely:

1. **Syntax**: `with expr` introduces pattern matching on the expression
2. **Desugaring**: With-clauses compile to auxiliary functions
3. **Generalization**: Occurrences of the scrutinee in the goal type are generalized
4. **Pattern refinement**: Nested with can refine parent patterns

---

## Agda's With Abstraction (Reference)

### Basic Syntax

```agda
-- Agda syntax
filter : {A : Set} → (A → Bool) → List A → List A
filter p []       = []
filter p (x ∷ xs) with p x
...                  | true  = x ∷ filter p xs
...                  | false = filter p xs
```

Key points:
- `with e` introduces scrutinee `e` after the function patterns
- `...` repeats the parent patterns unchanged
- `| pat` matches the with-expression

### Multiple With Expressions

```agda
compare : Nat → Nat → Ordering
compare x y with x <? y | x ≟ y
...            | yes p | _      = less
...            | no _  | yes p  = equal
...            | no _  | no _   = greater
```

### Nested With (Pattern Refinement)

```agda
-- When with refines parent patterns
foo : (n : Nat) → Vec A n → B
foo n v with n
foo .zero    v | zero  = ...   -- v must be VNil (dot pattern shows refinement)
foo .(suc m) v | suc m = ...   -- v must be VCons
```

### Desugaring to Auxiliary Functions

Agda desugars `with` to auxiliary functions:

```agda
-- Original:
filter p (x ∷ xs) with p x
...                  | true  = x ∷ filter p xs
...                  | false = filter p xs

-- Desugared to:
filter p (x ∷ xs) = filter-aux p x xs (p x)
  where
    filter-aux : (A → Bool) → A → List A → Bool → List A
    filter-aux p x xs true  = x ∷ filter p xs
    filter-aux p x xs false = filter p xs
```

---

## LeanUI Syntax Design

### Basic With

```
-- LeanUI syntax (following Agda)
filter : {A : Type} -> (A -> Bool) -> List A -> List A
filter p Nil = Nil
filter p (Cons x xs) with p x
  | True => Cons x (filter p xs)
  | False => filter p xs
```

### Multiple Scrutinees

```
compare : Nat -> Nat -> Ordering
compare x y with ltNat x y, eqNat x y
  | True, _ => Less
  | False, True => Equal
  | False, False => Greater
```

### Nested With (Ellipsis for Parent Patterns)

```
foo : (n : Nat) -> Vec A n -> B
foo n v with n
  ... | Zero => ...     -- ellipsis = repeat 'foo n v' patterns unchanged
  ... | Succ m => ...

-- Or with explicit parent pattern refinement:
foo n v with n
  foo Zero v | Zero => ...         -- explicit: refine n to Zero
  foo (Succ m) v | Succ m => ...   -- explicit: refine n to Succ m
```

### Pattern Chain Syntax (Multiple Levels)

```
-- Right-to-left: innermost to outermost
foo n v with n
  ... | Zero with v
    ... | Zero | VNil => ...       -- Zero is outer (n), VNil is inner (v)
  ... | Succ m with v
    ... | Succ m | VCons h t => ...
```

### Ellipsis Rules

- `...` means "repeat the parent clause patterns unchanged"
- Only valid at start of clause (before first `|`)
- Alternative: explicitly write refined patterns (possibly with dot patterns)

---

## Implementation Strategy

### Desugaring to Auxiliary Functions

Follow Agda exactly - a with becomes a call to an auxiliary function that takes the original arguments plus the scrutinee value(s).

**Desugaring steps:**
1. Generate fresh name for auxiliary function
2. Compute auxiliary function type:
   - Original function's parameter types (up to the with point)
   - Plus scrutinee types
   - Returns original function's return type
3. Generate auxiliary function definition with the with-clauses as patterns
4. Replace with-clause with call to auxiliary function

**Example:**
```
-- Original:
isZero n with n
  | Zero => True
  | Succ m => False

-- Desugared to:
isZero n = isZero-with-1 n n
isZero-with-1 : Nat -> Nat -> Bool
isZero-with-1 n Zero = True
isZero-with-1 n (Succ m) = False
```

### Benefits of Desugaring

1. **Kernel stays simple**: No new kernel term type needed
2. **Reuses existing infrastructure**: Pattern matching, type checking, totality all work automatically
3. **Proven approach**: This is exactly what Agda does
4. **Easy to debug**: Can inspect the generated auxiliary functions

---

## Design Decisions

1. **Desugaring over direct handling**: Follow Agda - desugar to auxiliary functions rather than handling with directly in the type checker.

2. **Ellipsis syntax**: Use `...` for "repeat parent patterns unchanged" (same as Agda).

3. **Totality**: Required by default. Non-exhaustive with is a type error (via auxiliary function totality check).

4. **Syntax for with-expression**: Use `with e` followed by `| pat => rhs` clauses.

---

## References

- [Agda Documentation: With-Abstraction](https://agda.readthedocs.io/en/latest/language/with-abstraction.html)
- "Elaborating Dependent (Co)Pattern Matching" - Cockx & Abel
