# Type Shortcuts Feature

## Overview

When adding hypotheses or let-bindings, you can now use LaTeX-style shortcuts that automatically expand to Unicode mathematical symbols when you move to the next field (on blur).

## Usage

### Number Systems

Type these shortcuts and they'll automatically convert:

| Shortcut | Symbol | Meaning |
|----------|--------|---------|
| `\N` or `\Nat` | ℕ | Natural numbers |
| `\R` or `\Real` | ℝ | Real numbers |
| `\Z` or `\Int` | ℤ | Integers |
| `\Q` | ℚ | Rational numbers |
| `\C` | ℂ | Complex numbers |
| `\mathbb{N}` | ℕ | Natural numbers (LaTeX style) |
| `\mathbb{R}` | ℝ | Real numbers (LaTeX style) |
| `\mathbb{Z}` | ℤ | Integers (LaTeX style) |
| `\mathbb{Q}` | ℚ | Rationals (LaTeX style) |
| `\mathbb{C}` | ℂ | Complex (LaTeX style) |

### Comparison Operators

| Shortcut | Symbol | Meaning |
|----------|--------|---------|
| `\leq` | ≤ | Less than or equal |
| `\geq` | ≥ | Greater than or equal |
| `\neq` | ≠ | Not equal |

### Set Theory & Logic

| Shortcut | Symbol | Meaning |
|----------|--------|---------|
| `\in` | ∈ | Element of |
| `\notin` | ∉ | Not an element of |
| `\subset` | ⊂ | Subset of |
| `\subseteq` | ⊆ | Subset or equal |
| `\forall` | ∀ | For all |
| `\exists` | ∃ | There exists |

### Other Operators

| Shortcut | Symbol | Meaning |
|----------|--------|---------|
| `\times` | × | Multiplication/Cartesian product |
| `\cdot` | · | Dot product/multiplication |

## Examples

### Adding a Hypothesis

**Type:**
```
Name: h1
Expression: x : \R
Description: x is a real number
```

**Auto-expands to:**
```
Name: h1
Expression: x : ℝ
Description: x is a real number
```

### Creating a Let-Binding

**Type:**
```
Variable name: n
Expression: n \in \N
Type annotation: \N
```

**Auto-expands to:**
```
Variable name: n
Expression: n ∈ ℕ
Type annotation: ℕ
```

### Complex Expression

**Type:**
```
Expression: \forall x \in \R, x \leq x^2 + 1
```

**Auto-expands to:**
```
Expression: ∀ x ∈ ℝ, x ≤ x^2 + 1
```

## When It Triggers

The expansion happens **automatically when you move to the next field** (on blur event). This means:

1. You type `x : \R` in the expression field
2. You press Tab or click on the next field
3. The text automatically changes to `x : ℝ`

## Implementation

The feature is implemented in [LetManager.tsx](src/components/LetManager.tsx#L72) with the `expandTypeShortcuts()` function, which uses regex replacements to convert LaTeX-style shortcuts to Unicode symbols.

The function is called `onBlur` for:
- Hypothesis expression field
- Let-binding expression field
- Let-binding type annotation field

## Adding New Shortcuts

To add new shortcuts, edit the `expandTypeShortcuts()` function in [LetManager.tsx](src/components/LetManager.tsx#L72) and add new `.replace()` calls:

```typescript
.replace(/\\YourShortcut/g, 'YourSymbol')
```

The pattern `/(?![a-zA-Z])/` ensures shortcuts like `\N` don't match within larger words (e.g., `\Nat` would still work, but `\Natural` wouldn't accidentally match `\N`).
