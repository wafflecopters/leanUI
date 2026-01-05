# Structural Recursion Analysis

This document describes the implementation of structural recursion checking for term definitions.

## What is Structural Recursion?

**Structural recursion** is a pattern of recursion that is guaranteed to terminate because each recursive call operates on a structurally smaller argument. This is the foundation of termination checking in dependently typed languages.

### Why It Matters

- **Termination guarantee**: Structurally recursive functions always terminate
- **Type safety**: In dependent types, non-terminating functions can break soundness
- **Predictable evaluation**: Structural recursion has clear computational behavior

## Safe vs Unsafe Recursion

### Safe Structural Recursion

A recursive call is **safe** when:
1. It occurs inside a pattern match
2. The recursive argument is a variable bound by deconstructing a constructor
3. That variable is structurally smaller than the original argument

**Example** (safe):
```lean
plus : Nat → Nat → Nat
| zero,   b => b
| succ a, b => succ (plus a b)  -- ✓ 'a' is smaller than 'succ a'
```

### Unsafe Recursion Patterns

1. **General recursion** - Not on pattern-matched variables
   ```lean
   bad : Nat → Nat
   | n => bad n  -- ✗ Same argument (infinite loop)
   ```

2. **Non-decreasing recursion** - On a larger argument
   ```lean
   grows : Nat → Nat
   | n => grows (succ n)  -- ✗ Larger argument
   ```

3. **Complex arguments** - Not simple variables
   ```lean
   complex : Nat → Nat
   | succ a => complex (succ a)  -- ✗ Not structurally smaller
   ```

4. **Outside pattern matching** - No structural guarantee
   ```lean
   noMatch : Nat → Nat → Nat
   noMatch x y = noMatch y x  -- ✗ No pattern match
   ```

## The Algorithm

### Phase 1: Identify Recursive Calls

Traverse the term to find all applications of the function being defined.

### Phase 2: Check Pattern Context

For each recursive call:
1. Check if it's inside a pattern match clause
2. Identify which variables are bound by pattern matching
3. Verify that recursive arguments are pattern-bound variables

### Phase 3: Classify Recursion

- **Safe**: Recursive call uses pattern-bound variables
- **Unsafe**: Otherwise (with specific error message)

## Implementation Details

### Pattern Variable Tracking

The checker maintains a context tracking:
- `patternBoundVars`: Set of De Bruijn indices of pattern-bound variables
- `depth`: Current binding depth (for De Bruijn index calculations)

When entering a match clause:
1. Extract variables bound by the pattern
2. Add them to `patternBoundVars`
3. Analyze the clause RHS with this extended context

### De Bruijn Index Handling

Pattern-bound variables are tracked by their De Bruijn indices. When a pattern binds variable `x`:
- It gets index `depth + offset` where offset is position in the pattern
- This index is added to `patternBoundVars`
- Recursive calls check if arguments have indices in this set

### Error Messages

Unsafe recursion generates specific error messages:
- "recursive call does not use pattern-matched variables"
- "recursive call uses complex expressions (not simple variables)"
- "recursive call outside of pattern matching context"
- "Direct reference to 'f' without application"

## Examples

### Example 1: Factorial (Safe)

```lean
fact : Nat → Nat
| zero => 1
| succ n => (succ n) * (fact n)  -- ✓ Safe: 'n' is pattern-bound
```

Analysis:
```typescript
const analysis = analyzeRecursion('fact', factBody);
// analysis.safeRecursion: [path to 'fact n']
// analysis.unsafeRecursion: []
```

### Example 2: Infinite Loop (Unsafe)

```lean
loop : Nat → Nat
| n => loop n  -- ✗ Unsafe: same argument
```

Analysis:
```typescript
const analysis = analyzeRecursion('loop', loopBody);
// analysis.safeRecursion: []
// analysis.unsafeRecursion: [{ path: [...], error: "does not use pattern-matched variables" }]
```

### Example 3: Mixed Recursion

```lean
mixed : Nat → Nat
| zero => mixed zero      -- ✗ Unsafe: 'zero' not pattern-bound in this branch
| succ n => mixed n       -- ✓ Safe: 'n' is pattern-bound
```

Analysis:
```typescript
const analysis = analyzeRecursion('mixed', mixedBody);
// analysis.safeRecursion: [path to second 'mixed n']
// analysis.unsafeRecursion: [{ path to first 'mixed zero', error: ... }]
```

## Limitations

The current implementation:
- ✅ Detects simple structural recursion
- ✅ Handles pattern matching correctly
- ✅ Provides clear error messages
- ⬜ Does not handle mutual recursion
- ⬜ Does not detect size-change termination
- ⬜ Does not handle well-founded recursion

Future extensions could add:
- Mutual recursion detection
- Well-founded recursion (on custom measures)
- Lexicographic orderings
- Size-change principle

## API

### `analyzeRecursion`

```typescript
function analyzeRecursion(
  functionName: string,
  body: TTerm
): RecursionAnalysis

interface RecursionAnalysis {
  safeRecursion: IndexPath[];       // Paths to safe calls
  unsafeRecursion: UnsafeRecursion[]; // Paths to unsafe calls with errors
}

interface UnsafeRecursion {
  path: IndexPath;  // Location of unsafe call
  error: string;    // Human-readable explanation
}
```

### Usage

```typescript
import { analyzeRecursion } from './types/tt-recursion-check';

// Analyze a function definition
const analysis = analyzeRecursion('plus', plusBody);

// Check if all recursion is safe
if (analysis.unsafeRecursion.length === 0) {
  console.log('✓ All recursion is structurally safe');
} else {
  for (const unsafe of analysis.unsafeRecursion) {
    console.error(`✗ Unsafe recursion at ${unsafe.path}: ${unsafe.error}`);
  }
}
```

## Testing

Run the test suite:
```bash
npx tsx src/types/tt-recursion-check.test.ts
```

Tests cover:
- ✅ Safe recursion in pattern matches
- ✅ Multiple safe recursive calls
- ✅ Recursion with multiple arguments
- ✅ Nested pattern matching
- ✅ Unsafe recursion (same variable, complex expressions)
- ✅ Recursion outside pattern matching
- ✅ Mixed safe and unsafe recursion
- ✅ Edge cases (empty match, lambdas, Pi types)

## References

- Coquand, T. "Pattern Matching with Dependent Types" (1992)
- Giménez, E. "Structural Recursive Definitions in Type Theory" (1998)
- Abel, A. "Termination Checking with Types" (2004)
- The Coq Reference Manual: Chapter on Termination
- Agda Documentation: Termination Checking

## File Structure

- `src/types/ttk-recursion-check.ts` - Kernel-level implementation (used by type checker)
- `src/types/ttk-recursion-check.test.ts` - Test suite for kernel checker
- `src/types/tt-recursion-check.ts` - Surface-level implementation (legacy, for reference)
- `src/types/tt-recursion-check.test.ts` - Test suite for surface checker
- `docs/structural-recursion.md` - This documentation

Note: The type checker uses `ttk-recursion-check.ts` which operates on kernel terms (TTKTerm).
All verification passes happen in the kernel layer. See CLAUDE.md for the TT vs TTK architecture.
