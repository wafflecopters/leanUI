# Test Suite Analysis and Expansion Plan

## Current State Summary

### Test Infrastructure
- **33 test files** total across `src/types/` and `src/parser/`
- **Mixed test frameworks**: Most files use custom `test()` helper functions; newer files use **vitest** (`describe`/`it`/`expect`)
- **31 test files fail to run** due to importing `bun:test` instead of `vitest`

### Test Run Results (as of analysis)
```
Test Files:  31 failed | 2 passed (33)
Tests:       4 failed | 112 passed | 1 skipped (117)
```

The 31 "failed" files are **framework compatibility issues** (using `bun:test` imports), not actual test failures.

The **4 actual test failures** are in `tt-pattern-typecheck.test.ts`:
1. `vhead` - Non-exhaustive pattern match (missing `VNil` case for `Succ n` index)
2. `vtail` - Same issue
3. `vecConcat` - Type mismatch with `plus Zero _` return type unification
4. `zipWith` - Type mismatch with vector length indices

These failures indicate **known limitations in indexed type unification** for dependent types.

---

## Test Coverage Analysis

### Well-Tested Modules (Have dedicated test files)
| Module | Test File | Coverage Level |
|--------|-----------|----------------|
| `tt-core.ts` | `tt-core.test.ts` | High - term construction, pretty printing |
| `tt-parser.ts` | `tt-parser.test.ts` + 4 regression tests | High - lexer, parser, operators |
| `tt-typecheck.ts` | `tt-typecheck.test.ts` | Medium - basic synthesis/checking |
| `tt-unify.ts` | `tt-unify.test.ts` | High - unification rules |
| `tt-pattern-match.ts` | `tt-pattern-typecheck.test.ts` | High - pattern matching |
| `ttk-totality-check.ts` | `ttk-totality-check.test.ts` | High - exhaustiveness |
| `ttk-recursion-check.ts` | `ttk-recursion-check.test.ts` | Medium |
| `tt-type-query.ts` | `tt-type-query.test.ts` | Very High - extensive |
| `name-resolution.ts` | `name-resolution.test.ts` | High |
| `tt-elab.ts` | `tt-elab.test.ts` | Medium |

### Under-Tested Modules (No dedicated test files)
| Module | Lines | Priority | Reason |
|--------|-------|----------|--------|
| `tt-kernel.ts` | 714 | **Critical** | Core kernel representation, only tested indirectly |
| `block-checker.ts` | 676 | **Critical** | Integration pipeline, orchestrates everything |
| `tt-bridge.ts` | 701 | High | TT↔TTK conversion utilities |
| `tt-source-query.ts` | 582 | High | Source position → AST path mapping |
| `tt-elab-source.ts` | ~200 | High | Elaboration with source tracking |
| `enhanced-focus.ts` | 1,140 | Medium | UI focus system |
| `pattern-rules.ts` | 896 | Medium | Algebraic transformation rules |
| `tt-constrained-typecheck.ts` | 677 | Medium | Constraint-based type checking |
| `tt-inductive-inference.ts` | 441 | Medium | Parameter/index classification |

---

## Recommended Test Expansion Strategy

### Phase 1: Fix Infrastructure (Immediate)
**Goal**: Get all 33 test files running consistently

1. **Standardize on vitest** - Convert remaining `bun:test` imports to vitest
   - Files affected: `tt-typecheck.test.ts`, `tt-unify.test.ts`, `ttk-recursion-check.test.ts`
   - Change: `import { describe, it, expect } from 'bun:test'` → `import { describe, it, expect } from 'vitest'`

2. **Convert custom test() helpers to vitest** - For consistency and better reporting
   - Many files use a custom `test(description, fn)` pattern
   - Consider wrapping in vitest's `describe`/`it` blocks

### Phase 2: Critical Coverage Gaps (High Priority)

#### 2.1 `tt-kernel.ts` Tests
Create `tt-kernel.test.ts` covering:
- Term construction helpers (`mkVar`, `mkPi`, `mkLambda`, `mkApp`, etc.)
- Substitution operations (`substitute`, `shift`)
- Pretty printing with various contexts
- Context manipulation functions
- Equality/structural comparison

```typescript
// Example test structure
describe('TTK Term Construction', () => {
  describe('mkPi', () => {
    it('should create non-dependent function type when name is _', () => { ... });
    it('should create dependent Pi type with named binder', () => { ... });
  });

  describe('substitute', () => {
    it('should replace Var(0) with substituted term', () => { ... });
    it('should adjust indices under binders', () => { ... });
    it('should handle nested substitution', () => { ... });
  });
});
```

#### 2.2 `block-checker.ts` Integration Tests
Create `block-checker.test.ts` covering:
- Full pipeline from source → type-checked result
- Error aggregation and reporting
- Multi-block processing
- Incremental checking scenarios
- Edge cases (empty blocks, syntax errors, type errors)

```typescript
describe('Block Checker Integration', () => {
  describe('checkSourceBlocks', () => {
    it('should type-check valid Nat definition', () => { ... });
    it('should report parse errors with correct positions', () => { ... });
    it('should report type errors with correct positions', () => { ... });
    it('should handle forward references between blocks', () => { ... });
  });
});
```

#### 2.3 `tt-bridge.ts` Tests
Create `tt-bridge.test.ts` covering:
- TT → TTK conversion
- TTK → TT conversion (if applicable)
- Round-trip preservation
- Edge cases in pattern conversion

### Phase 3: Feature Coverage Expansion (Medium Priority)

#### 3.1 Expand Type Checker Tests
Add to `tt-typecheck.test.ts`:
- Universe polymorphism edge cases
- Complex dependent types (indexed families)
- Recursive definitions
- Mutual recursion (if supported)
- Error message quality tests

#### 3.2 Expand Unification Tests
Add to `tt-unify.test.ts`:
- Dependent pattern unification (vectors, equality proofs)
- Stuck unification scenarios
- Constraint propagation through multiple equations
- Performance with deep terms

#### 3.3 Expand Pattern Matching Tests
Add to `tt-pattern-typecheck.test.ts`:
- Nested indexed types
- Multiple scrutinees with dependencies
- Inaccessible pattern detection
- With-abstraction patterns (if supported)

### Phase 4: New Test Files for Uncovered Modules

#### 4.1 `tt-source-query.test.ts`
```typescript
describe('Source Query System', () => {
  describe('findPathAtPosition', () => {
    it('should find innermost term at cursor position', () => { ... });
    it('should handle positions between terms', () => { ... });
  });

  describe('findPathsInRange', () => {
    it('should find all terms within selection', () => { ... });
    it('should find smallest containing term for selection', () => { ... });
  });
});
```

#### 4.2 `enhanced-focus.test.ts`
```typescript
describe('Enhanced Focus System', () => {
  describe('ExpressionNode', () => {
    it('should navigate to child nodes', () => { ... });
    it('should apply transformation rules', () => { ... });
  });

  describe('Focus Rules', () => {
    it('should apply commutativity rule', () => { ... });
    it('should apply associativity rule', () => { ... });
  });
});
```

#### 4.3 `pattern-rules.test.ts`
```typescript
describe('Pattern Rules', () => {
  describe('ENHANCED_FOCUS_RULES', () => {
    it('should match arithmetic patterns', () => { ... });
    it('should match equality patterns', () => { ... });
  });
});
```

### Phase 5: Property-Based Testing (Advanced)

Consider adding property-based tests using a library like `fast-check`:

```typescript
import * as fc from 'fast-check';

describe('Term Properties', () => {
  it('substitution preserves well-typedness', () => {
    fc.assert(fc.property(
      arbitraryWellTypedTerm,
      arbitraryWellTypedTerm,
      (term, sub) => {
        // If term : T and sub : A, then term[sub/0] : T[sub/0]
      }
    ));
  });

  it('shift is inverse of unshift', () => {
    fc.assert(fc.property(
      arbitraryTerm,
      fc.nat(),
      (term, cutoff) => {
        // shift(unshift(term, cutoff), cutoff) === term
      }
    ));
  });
});
```

---

## Test Categories to Add

### 1. Regression Tests
- Add tests for each bug fix
- Document the original issue in test comments
- Use descriptive names: `it('should not crash on empty pattern list (issue #123)')`

### 2. Edge Case Tests
- Empty inputs (empty context, empty term, etc.)
- Maximum depth terms
- Unicode in identifiers
- Very long identifiers
- Deeply nested expressions

### 3. Error Message Quality Tests
```typescript
describe('Error Messages', () => {
  it('should mention expected type in mismatch error', () => {
    const result = checkSourceBlocks('bad : Nat := True');
    expect(result[0].checkErrors[0].error.message).toContain('Nat');
    expect(result[0].checkErrors[0].error.message).toContain('Bool');
  });
});
```

### 4. Performance Tests
```typescript
describe('Performance', () => {
  it('should type-check 100 simple definitions in < 1s', () => {
    const start = Date.now();
    const source = generateNDefinitions(100);
    checkSourceBlocks(source);
    expect(Date.now() - start).toBeLessThan(1000);
  });
});
```

---

## Specific Test Cases to Add

### For Indexed Types (fixing the 4 failures)
```typescript
// These currently fail - document as known limitations or fix
describe('Indexed Types - Known Limitations', () => {
  it.skip('vhead with impossible VNil case', () => {
    // Document why this fails and what needs to change
  });

  it.skip('vecConcat requires plus computation', () => {
    // Document that this needs definitional equality with plus
  });
});
```

### For Type Queries
```typescript
describe('Type Query Edge Cases', () => {
  it('should handle queries in pattern LHS', () => { ... });
  it('should show solved types after unification', () => { ... });
  it('should handle recursive function references', () => { ... });
});
```

### For Parser
```typescript
describe('Parser Edge Cases', () => {
  it('should parse deeply nested parentheses', () => { ... });
  it('should handle Unicode operators', () => { ... });
  it('should report error for unclosed block comment', () => { ... });
  it('should handle Windows line endings', () => { ... });
});
```

---

## Implementation Recommendations

1. **Use vitest consistently** - Better error messages, watch mode, coverage
2. **Use `describe` blocks** - Group related tests logically
3. **Use `it.skip` for known failures** - Document limitations without breaking CI
4. **Add test coverage to CI** - Track coverage trends over time
5. **Create test fixtures** - Reusable source code snippets for common patterns
6. **Add snapshot tests** - For pretty printing and error messages

---

## Estimated Effort

| Phase | Effort | Tests Added |
|-------|--------|-------------|
| Phase 1: Infrastructure | 2-4 hours | 0 (fixes existing) |
| Phase 2: Critical Gaps | 8-16 hours | ~50-100 |
| Phase 3: Feature Expansion | 8-16 hours | ~50-100 |
| Phase 4: New Test Files | 16-24 hours | ~100-150 |
| Phase 5: Property Tests | 8-16 hours | ~20-50 |

**Total**: ~300-400 new tests, roughly doubling current coverage.

---

## Quick Wins (Can Add Today)

1. Fix the 3 files with `bun:test` imports (5 min each)
2. Add tests for `tt-kernel.ts` basic functions (1-2 hours)
3. Add edge case tests to existing `tt-parser.test.ts` (30 min)
4. Document the 4 failing indexed type tests with `.skip` (15 min)
5. Add `block-checker.test.ts` with 10 integration tests (2 hours)
