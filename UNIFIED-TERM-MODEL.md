# Unified Term Model - Architecture Documentation

## Overview

The proof workspace now uses a **single unified TTerm** to represent the entire proof state. There is no separate "start proof" step - the term exists from the beginning and all UI operations modify parts of this one term.

## The Root Term Structure

```
let _root : (a: R) → (b: R) → P = ?proof
            ^^^^^^^^^^^^^^^^^^^     ^^^^^^
            Theorem Type            Proof Value
            (Pi with hypotheses)    (nested lets + hole)
```

### Components

1. **Root Let-Binding**: `let _root : TYPE = VALUE in _root`
   - Name: `_root` (the theorem itself)
   - Type: The theorem statement (Pi-type with hypotheses ending in goal)
   - Value: The proof term (nested lets ending in a hole)
   - Body: `Var(0)` (refers to itself)

2. **Theorem Type** (the `TYPE` part):
   ```
   (a: R) → (b: R) → P
   ```
   - Built from hypotheses using nested Pi-binders
   - Ends with the explicit goal type `P` (set by the UI)
   - This IS the theorem statement

3. **Proof Value** (the `VALUE` part):
   ```
   let x : Foo = Bar in
   let y : Baz = Qux x in
     ?proof
   ```
   - Nested let-bindings from the UI
   - Ends with a proof hole (`?proof`)
   - Type of `?proof` is the full theorem type `(a: R) → (b: R) → P`

## UI to TT Mapping

### Hypotheses Section
```
UI:                    TT (in root's TYPE):
───────────────        ────────────────────
a : R                  (a: R) →
b : R                  (b: R) →
                       → Goal
```

The hypotheses form the Pi-type prefix of the root's type annotation.

### Let-Bindings Section
```
UI:                    TT (in root's VALUE):
───────────────        ─────────────────────
x: Foo = Bar           let x : Foo = Bar in
y: Baz = Qux x         let y : Baz = Qux x in
                         ?proof
```

The let-bindings are nested `BLet` binders in the root's value.

### Goal Section
```
UI:                    TT:
───────────────        ───────────────────────
Goal: P                P (explicit in type)
                       ?proof (hole in value)
```

The goal is set explicitly in the theorem type (as the final codomain after all Pi-binders). There is only one hole: `?proof` for the proof term itself.

## Core Operations

### Creating the Initial Term

```typescript
createRootProofTerm(
  [["a", Real], ["b", Real]],
  Proposition  // explicit goal
)

// Returns:
// let _root : (a: R) → (b: R) → P
//          = ?proof
//    in _root
```

### Adding a Hypothesis

```typescript
addHypothesisToRoot(rootTerm, "c", Real)

// Updates root's type:
// let _root : (a: R) → (b: R) → (c: R) → P
//          = ?proof
//    in _root
```

### Getting and Setting the Goal

```typescript
// Get the current goal
const goal = getGoalFromRoot(rootTerm)  // Returns: P

// Update the goal
const updatedRoot = setGoalInRoot(rootTerm, NewGoal)
// Updates to: let _root : (a: R) → (b: R) → NewGoal = ?proof in _root
```

### Adding a Let-Binding

```typescript
addLetToProof(rootTerm, "x", Foo, Bar)

// Updates root's value:
// let _root : (a: R) → (b: R) → P
//          = let x : Foo = Bar in
//              ?proof
//    in _root
```

### Extracting Hypotheses

```typescript
extractHypothesesFromRoot(rootTerm)
// Returns: [["a", Real], ["b", Real]]
```

## Benefits

1. **Single Source of Truth**: One TTerm represents everything
2. **Type Safety**: The root's type IS the theorem statement
3. **Natural Structure**: Hypotheses as Pi-binders, lets as lets
4. **No "Start Proof"**: Term exists from the beginning
5. **Compositional**: Easy to add/remove hypotheses and lets
6. **Well-Typed**: Type checker can verify the entire term

## Implementation Files

- **Core helpers**: `src/types/tt-core.ts`
  - `createRootProofTerm()` - Create initial structure with explicit goal
  - `addLetToProof()` - Add let-bindings to proof value
  - `addHypothesisToRoot()` - Add hypotheses to Pi-type
  - `extractHypothesesFromRoot()` - Extract hypotheses from Pi-type
  - `getGoalFromRoot()` - Extract the goal type
  - `setGoalInRoot()` - Update the goal type
  - `hypothesesToPi()` - Convert hypotheses list to nested Pi-type

- **Type checker**: `src/types/tt-typecheck.ts`
  - Handles unified `Binder` type
  - Type-checks the entire structure

- **Bridge layer**: `src/types/tt-bridge.ts`
  - Converts UI operations to TT term modifications

## Migration Notes

The old model had:
- Separate hypotheses list
- "Start proof" button that created a proof context
- Disconnected let-bindings

The new model:
- Hypotheses are IN the term (as Pi-type)
- No "start" - term exists from the start
- Let-bindings are IN the term (as nested lets)
- Everything is one cohesive, type-checked structure

## Example: Complete Proof

```
UI Input:
────────
Hypotheses:
  a : R
  b : R

Goal:
  y = 2 * (a + b)

Let-bindings:
  x : R = a + b
  y : R = x * 2

TT Term Structure:
──────────────────
let _root : (a: R) → (b: R) → (y = 2 * (a + b))
         = let x : R = a + b in
           let y : R = x * 2 in
             ?proof
   in _root
```

**Key Points:**
- The goal `y = 2 * (a + b)` is set explicitly in the theorem type
- Hypotheses `a : R` and `b : R` form the Pi-type prefix
- Let-bindings are nested in the proof value
- Only one hole: `?proof` which should have type `(a: R) → (b: R) → (y = 2 * (a + b))`

When the proof is complete, `?proof` is replaced with a lambda that takes the hypotheses and produces a proof of the goal:
```
λ(a: R). λ(b: R). <actual proof term>
```
