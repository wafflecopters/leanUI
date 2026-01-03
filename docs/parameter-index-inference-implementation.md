# Parameter/Index Inference - Implementation Notes

## Summary

This document describes the implementation of the parameter/index inference algorithm for inductive type families.

## Files Created

1. **`src/types/tt-inductive-inference.ts`** - Main implementation
   - Exports `inferParameterIndices(def: InductiveTypeDef): IndexPositions`
   - Returns array of position indices that are type indices (all others are parameters)

2. **`src/types/tt-inductive-inference.test.ts`** - Comprehensive test suite
   - Tests simple types (Nat, Bool, Empty, Unit)
   - Tests parameterized types (List, Vec)
   - Tests indexed types (Fin)
   - Tests index promotion (Eq - the J eliminator case!)
   - Tests dependency validation (Weird type)

3. **`docs/parameter-index-inference.md`** - Algorithm specification
   - Complete algorithm description with examples
   - Phase-by-phase breakdown
   - Example walkthroughs for Eq, Vec, Fin

## Usage Example

```typescript
import { inferParameterIndices } from './types/tt-inductive-inference';

// For Vec : Type -> Nat -> Type
const vecDef = makeVec();
const indices = inferParameterIndices(vecDef);
// Returns [1] - position 0 is parameter (Type), position 1 is index (Nat)

// For Eq : (A : Type) -> A -> A -> Type
const eqDef = makeEq();
const indices = inferParameterIndices(eqDef);
// Returns [2] - positions 0,1 are parameters (A, x), position 2 is index
// This allows generating the J eliminator!
```

## Algorithm Phases

### Phase 1: Syntactic Parameter Detection
Identifies positions where:
- Every constructor passes a unique variable
- That variable appears exactly once in all positions

### Phase 2: Index Promotion
Finds equivalence classes of indices that are always equal:
- Promotes the leftmost position in each class to a parameter
- Only promotes if the term is a variable (not a complex term)

### Phase 3: Dependency Validation
Ensures parameters form a prefix:
- If position i is an index, all positions j > i must be indices
- This prevents scope issues in the eliminator

## Test Results

All 10 tests pass:

```
=== Simple Types (No Arguments) ===
✓ Nat has no indices (simple type)
✓ Bool has no indices (simple type)
✓ Empty has no indices (no constructors)
✓ Unit has no indices (single constructor)

=== Parameterized Types ===
✓ List has Type as parameter, no indices
✓ Vec has Type as parameter, Nat as index

=== Indexed Types ===
✓ Fin has Nat as index (complex term)

=== Advanced: Index Promotion ===
✓ Eq promotes second argument to parameter (J eliminator)

=== Advanced: Dependency Validation ===
✓ Weird has both positions as indices (dependency validation)
```

## Key Implementation Details

1. **Structural equality checking** - `termsEqual()` performs syntactic equality checking on terms

2. **Union-find for equivalence classes** - Efficient algorithm for computing transitive closure of equality relations

3. **De Bruijn index handling** - Correctly handles variables referenced by De Bruijn indices

4. **Prefix enforcement** - Ensures no parameter can depend on an index by requiring parameters to be a contiguous prefix

## Future Extensions

This implementation provides the foundation for:
- Generating strong eliminators (induction principles)
- Type inference for pattern matching
- Optimized compilation of inductive types
- Better error messages when eliminators fail to type check

## Running Tests

```bash
npx tsx src/types/tt-inductive-inference.test.ts
```

## References

- See `docs/parameter-index-inference.md` for the full algorithm specification
- See `src/types/tt-core.ts` for the term representation
- See `src/types/tt-examples.ts` for example inductive type definitions
