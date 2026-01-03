# Eliminator Generation for Inductive Types

This document describes the implementation of eliminator (induction principle) generation for inductive types.

## What is an Eliminator?

An **eliminator** (also called an **induction principle** or **recursor**) is a function that allows you to prove properties about values of an inductive type by:
1. Providing a **motive**: the property you want to prove
2. Providing **methods**: proofs for each constructor case

## General Structure

For a simple inductive type `D : Type` with constructors `c₁, ..., cₖ`:

```
D-elim :
  (P : D → Type)          -- motive (property to prove)
  → P c₁                   -- case for constructor 1
  → ...
  → P cₖ                   -- case for constructor k
  → (x : D)                -- value to case-analyze
  → P x                    -- proof of property for x
```

## Examples

### Bool (Simple Case)

```lean
inductive Bool : Type where
  | true : Bool
  | false : Bool
```

Eliminator:
```lean
Bool-elim :
  (P : Bool → Type)
  → P true
  → P false
  → (b : Bool)
  → P b
```

**Usage**: To prove `P b` for any `b : Bool`, provide proofs of `P true` and `P false`.

### Nat (With Induction)

```lean
inductive Nat : Type where
  | zero : Nat
  | succ : Nat → Nat
```

Eliminator:
```lean
Nat-elim :
  (P : Nat → Type)
  → P zero
  → ((n : Nat) → P n → P (succ n))
  → (n : Nat)
  → P n
```

**Key difference**: The `succ` case includes an **inductive hypothesis** `P n`. This allows you to assume the property holds for `n` when proving it for `succ n`.

**Usage**: To prove `P n` for any `n : Nat`:
- Provide a proof of `P zero` (base case)
- Provide a proof that `P n → P (succ n)` for any `n` (inductive case)

### Empty (No Constructors)

```lean
inductive Empty : Type where
  (no constructors)
```

Eliminator:
```lean
Empty-elim :
  (P : Empty → Type)
  → (e : Empty)
  → P e
```

**Interpretation**: Since `Empty` has no values, you can prove anything about it (ex falso quodlibet).

### Unit (Single Constructor)

```lean
inductive Unit : Type where
  | unit : Unit
```

Eliminator:
```lean
Unit-elim :
  (P : Unit → Type)
  → P unit
  → (u : Unit)
  → P u
```

## Inductive Hypotheses

When a constructor has a **recursive argument** (an argument whose type is the inductive type being defined), the method for that constructor includes an **inductive hypothesis**.

Example: `succ : Nat → Nat`
- Recursive argument: `n : Nat`
- Method type: `(n : Nat) → P n → P (succ n)`
  - First argument: the value `n`
  - Second argument: the inductive hypothesis `P n`
  - Result: proof of `P (succ n)`

## Implementation Notes

The current implementation handles:
- ✅ Simple inductive types (`Type_0`)
- ✅ Nullary constructors
- ✅ Constructors with arguments
- ✅ Inductive hypotheses for recursive arguments
- ✅ Correct De Bruijn index calculations

Future enhancements:
- ⬜ Parameterized types (e.g., `List : Type → Type`)
- ⬜ Indexed types (e.g., `Vec : Type → Nat → Type`)
- ⬜ Dependent methods (stronger induction principles)

## File Structure

- `src/types/tt-eliminator.ts` - Main implementation
- `src/types/tt-eliminator.test.ts` - Comprehensive test suite
- `docs/eliminator-generation.md` - This documentation

## Running Tests

```bash
npx tsx src/types/tt-eliminator.test.ts
```

All tests should pass, including:
- Structure tests for Bool, Nat, Unit, Empty
- Method type structure tests
- Inductive hypothesis tests

## Usage Example

```typescript
import { generateEliminator } from './types/tt-eliminator';
import { makeNat } from './types/tt-examples';

const natDef = makeNat();
const natElim = generateEliminator(natDef);

// natElim is the type:
// (P : Nat → Type) → P zero → ((n : Nat) → P n → P (succ n)) → (n : Nat) → P n
```

## References

- Paulin-Mohring, C. "Inductive Definitions in the System Coq" (1993)
- The Coq Reference Manual: Chapter on Inductive Definitions
- Agda Documentation: Inductive Types and Pattern Matching
