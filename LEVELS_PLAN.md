# Universe Level Polymorphism Implementation Plan

## Implementation Order Context

This feature is part of a larger roadmap. The implementation order is:

1. **Implicit/Named Arguments** (`NAMED_ARGS_PLAN.md`) - First priority
2. **Universe Levels** (this plan) - **Second priority**
3. **Multi-Variable Binders** (`MULTI_ARGS_PLAN.md`) - Third priority
4. **Records** - Fourth priority (plan TBD)

### Why This Order?

- **Implicit args before levels**: Universe polymorphism typically uses implicit level parameters (`{u : Level} -> Type u`). The implicit argument infrastructure must exist first.
- **Levels before multi-var**: While not strictly required, having levels enables more realistic multi-var examples like `{A B : Type u}`.
- **Multi-var can reference levels**: `(u v : Level) -> ...` is a natural use case for multi-variable binders.

---

## Overview

Add universe level polymorphism to support syntax like:
- `foo : (u : Level) -> (A : Type u) -> ...`
- `foo : (A : Type u) -> ...` (with inference)

This is a foundational change touching the kernel, parser, type-checker, unification, and elaboration.

---

## Level Type Definition

```typescript
// New file: src/types/tt-level.ts
export type Level =
  | { tag: 'LZero' }                          // 0
  | { tag: 'LSucc'; pred: Level }             // succ(l)
  | { tag: 'LMax'; left: Level; right: Level } // max(l1, l2)
  | { tag: 'LIMax'; left: Level; right: Level }// imax(l1, l2) - impredicative max
  | { tag: 'LParam'; name: string }           // level parameter (u, v, etc.)
  | { tag: 'LMVar'; id: string }              // level metavariable (?u)
```

**Key semantics:**
- `imax(l1, l2) = 0` if `l2 = 0`, else `max(l1, l2)` (preserves impredicativity)
- Level params are universally quantified at definition boundaries
- Level mvars are solved during elaboration/unification

---

## Implementation Phases

### Phase 1: Core Level Infrastructure
**Files:** NEW `src/types/tt-level.ts`, NEW `src/types/tt-level.test.ts`

1. Create Level type with all constructors
2. Implement helper functions:
   - `mkLZero`, `mkLSucc`, `mkLMax`, `mkLIMax`, `mkLParam`, `mkLMVar`
   - `mkLNum(n)` - convert number to Level
   - `levelToNumber(l)` - convert concrete Level to number (or null)
   - `simplifyLevel(l)` - normalize (e.g., `max(0, l) = l`, `imax(l, 0) = 0`)
   - `levelsEqual(l1, l2)` - structural equality
   - `prettyPrintLevel(l)` - display
   - `levelHasMVars(l)`, `levelHasParam(l, name)` - queries
3. Write comprehensive tests for all operations

### Phase 2: Kernel Integration
**Files:** `src/types/tt-kernel.ts`, `src/types/tt-core.ts`

1. Change `Sort` from `{ tag: 'Sort'; level: number }` to `{ tag: 'Sort'; level: Level }`
2. Update helper functions:
   - `mkProp()` → `{ tag: 'Sort', level: mkLZero() }`
   - `mkType(n)` → `{ tag: 'Sort', level: mkLNum(n) }` (backward compat)
   - Add `mkSort(level: Level)` for explicit level
3. Update `prettyPrint` to handle Level:
   - Concrete levels: `Prop`, `Type`, `Type 1`, etc.
   - Symbolic: `Sort u`, `Sort (max u v)`, etc.
4. Update `isDefinitionallyEqual` for Sort comparison
5. `subst` and `shift` - Sort case unchanged (levels don't contain term variables)

### Phase 3: Type Checker Updates
**Files:** `src/types/tt-typecheck.ts`, `src/types/tt-typecheck-inference.ts`

1. Update Sort inference rule:
   ```typescript
   case 'Sort':
     // Sort l : Sort (succ l)
     return mkSort(mkLSucc(term.level));
   ```

2. Update Pi type universe computation to use `imax`:
   ```typescript
   case 'BPi':
     // Pi has type imax(domain_level, body_level)
     // imax preserves impredicativity: if body is Prop, result is Prop
     const resultLevel = mkLIMax(domainType.level, bodyType.level);
     return mkSort(simplifyLevel(resultLevel));
   ```

3. Update `convertible` to handle level comparison (may need constraint generation)

### Phase 4: Level Unification
**Files:** NEW `src/types/tt-level-unify.ts`, NEW `src/types/tt-level-unify.test.ts`

1. Create level unification:
   ```typescript
   export type LevelUnifyResult =
     | { tag: 'success'; subst: Map<string, Level> }
     | { tag: 'failure'; reason: string }
     | { tag: 'stuck'; reason: string };

   export function unifyLevels(l1: Level, l2: Level): LevelUnifyResult;
   ```

2. Unification rules:
   - Structural equality → success with empty subst
   - `?u = l` → solve (with occurs check)
   - `succ(l1) = succ(l2)` → unify l1, l2
   - `max(a, b) = max(c, d)` → unify a=c, b=d
   - Concrete vs concrete → compare numerically

3. Add level substitution application

### Phase 5: Integrate Level Unification into Term Unification
**Files:** `src/types/tt-unify.ts`, `src/types/tt-constrained-typecheck.ts`

1. Update `unifyTerms` to handle Sort:
   ```typescript
   case 'Sort':
     if (t2.tag !== 'Sort') return failure;
     const levelResult = unifyLevels(t1.level, t2.level);
     // Convert level subst to term subst or generate constraints
   ```

2. Extend constraint types:
   ```typescript
   | { tag: 'LevelEq'; lhs: Level; rhs: Level }
   ```

3. Update constraint solver to handle level constraints

### Phase 6: Parser Updates
**Files:** `src/parser/tt-parser.ts`

1. Add new token: `SORT` (explicit Sort keyword, optional)

2. Update `parseType()` to handle level parameters:
   ```
   Type      → Sort 1
   Type u    → Sort (succ (param u))
   Type_3    → Sort 4 (concrete)
   Sort u    → Sort (param u)
   Sort 0    → Sort 0
   ```

3. Add level expression parsing for advanced cases:
   ```
   Sort (max u v)
   Sort (succ u)
   ```

4. (Future) Add `universe u v` declaration parsing

### Phase 7: Elaboration Updates
**Files:** `src/types/tt-elab.ts`

1. Sort elaboration now just copies Level (already correct type)
2. Track level parameters in elaboration context
3. Generate fresh level mvars for implicit level arguments

### Phase 8: Inductive Type Updates
**Files:** `src/types/tt-inductive-check.ts`

1. Update `getInductiveUniverseLevel` to return `Level | null`
2. Update universe constraint checking:
   - Compare levels symbolically when params present
   - Generate level constraints for polymorphic inductives

---

## Critical Files Summary

| File | Changes |
|------|---------|
| `src/types/tt-level.ts` | NEW - Level type and operations |
| `src/types/tt-level-unify.ts` | NEW - Level unification |
| `src/types/tt-kernel.ts` | Sort.level: number → Level |
| `src/types/tt-core.ts` | Sort.level: number → Level |
| `src/types/tt-typecheck.ts` | Pi universe = imax, Sort : Sort(succ) |
| `src/types/tt-typecheck-inference.ts` | Same as above |
| `src/types/tt-unify.ts` | Integrate level unification |
| `src/types/tt-constrained-typecheck.ts` | Add LevelEq constraints |
| `src/parser/tt-parser.ts` | Parse `Type u`, `Sort u` |
| `src/types/tt-elab.ts` | Handle level params |
| `src/types/tt-inductive-check.ts` | Symbolic level comparison |

---

## Testing Strategy

### Unit Tests (per phase)
- **Phase 1:** Level operations, simplification, equality, pretty-printing
- **Phase 4:** Level unification cases (success, failure, stuck, occurs check)
- **Phase 6:** Parser tests for `Type u`, `Sort (max u v)`, etc.

### Integration Tests
- Type inference with level params: `id : (A : Type u) -> A -> A`
- Universe polymorphic definitions typecheck correctly
- Impredicativity preserved: `(A : Type) -> Prop` has type `Prop`
- Inductive types with level constraints

### Regression Tests
- ALL existing tests must pass (concrete levels work as before)
- Impredicativity behavior unchanged

---

## Risks and Mitigations

| Risk | Mitigation |
|------|------------|
| Breaking existing tests | Backward-compat `mkType(n: number)` helper |
| imax semantics wrong | Extensive impredicativity tests |
| Level constraint solving incomplete | Start simple (concrete only), add symbolic incrementally |
| Performance regression | Cache simplified levels, profile |
| Parser ambiguity | Start with explicit `Sort u`, add `Type u` sugar after |

---

## Execution Order

1. **Phase 1** - Create `tt-level.ts` with full test coverage
2. **Phase 2** - Update kernel types, fix all type errors
3. **Phase 3** - Update type checker, verify existing tests pass
4. **Phase 4** - Add level unification
5. **Phase 5** - Integrate into term unification
6. **Phase 6** - Parser updates
7. **Phase 7** - Elaboration updates
8. **Phase 8** - Inductive type updates

Run full test suite after EACH phase. Do not proceed if tests fail.
