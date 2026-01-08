# LeanUI Engine Development Plan

**Master Plan for Type Theory Engine Development**

This document integrates all feature and architecture plans into a single ordered sequence. Execute phases in order. Each phase unlocks capabilities needed by subsequent phases.

---

## Dependency Graph

```
                    ┌─────────────────────────────────────────────────┐
                    │              PHASE 0: TESTING                    │
                    │  (No dependencies - DO THIS FIRST)              │
                    └─────────────────────────────────────────────────┘
                                          │
                                          ▼
                    ┌─────────────────────────────────────────────────┐
                    │         PHASE 1: SAFETY NETS                     │
                    │  (Fuel, boundaries, branding)                   │
                    └─────────────────────────────────────────────────┘
                                          │
                                          ▼
                    ┌─────────────────────────────────────────────────┐
                    │      PHASE 2: NAMED/IMPLICIT ARGUMENTS          │
                    │  (Foundation for all other features)            │
                    └─────────────────────────────────────────────────┘
                           │              │              │
              ┌────────────┘              │              └────────────┐
              ▼                           ▼                           ▼
   ┌──────────────────┐      ┌──────────────────────┐    ┌──────────────────┐
   │ PHASE 3: LEVELS  │      │ PHASE 4: MULTI-VAR   │    │   [SIDE QUEST]   │
   │ (Universe poly)  │      │ (Can start after P2) │    │   Architecture   │
   └──────────────────┘      └──────────────────────┘    │   Steps 4-9      │
              │                           │               └──────────────────┘
              └───────────┬───────────────┘
                          ▼
              ┌──────────────────────────┐
              │  PHASE 5: RECORDS        │
              │  (Structures)            │
              └──────────────────────────┘
                          │
                          ▼
              ┌──────────────────────────┐
              │  PHASE 6: KERNEL         │
              │  EXTRACTION              │
              │  (Architecture 10-12)    │
              └──────────────────────────┘
                          │
                          ▼
              ┌──────────────────────────┐
              │  PHASE 7: FORMAL         │
              │  VERIFICATION (Optional) │
              └──────────────────────────┘
```

---

## Phase 0: Testing Foundation

**Why First**: Tests give us confidence to refactor and expand. Without tests, every change is a risk.

**Goal**: Get test infrastructure healthy and expand coverage to critical modules.

### Step 0.1: Fix Test Infrastructure

**What**: Standardize all test files on vitest.

**Do**:
1. Change `import { describe, it, expect } from 'bun:test'` → `import { describe, it, expect } from 'vitest'` in:
   - `tt-typecheck.test.ts`
   - `tt-unify.test.ts`
   - `ttk-recursion-check.test.ts`
2. Run `npx vitest run` - all 33 files should load

**Success**:
- [ ] `npx vitest run` shows 33 test files loading (not 2)
- [ ] Only 4 actual failures (known Vec issues), not 31 framework errors

### Step 0.2: Add Kernel Tests

**What**: Create `tt-kernel.test.ts` covering core kernel operations.

**Do**:
1. Test `mkVar`, `mkPi`, `mkLambda`, `mkApp`, `mkConst`, `mkHole`
2. Test `subst` (substitution) - the most critical operation
3. Test `shift` (De Bruijn index adjustment)
4. Test `prettyPrint` with various contexts

**Success**:
- [ ] `tt-kernel.test.ts` exists with 30+ test cases
- [ ] Substitution edge cases covered (nested binders, index adjustment)
- [ ] All tests pass

### Step 0.3: Add Block Checker Integration Tests

**What**: Create `block-checker.test.ts` covering the full pipeline.

**Do**:
1. Test valid Nat/List/Vec definitions parse and type-check
2. Test error reporting (parse errors, type errors) with correct positions
3. Test multi-block dependencies (forward references)
4. Test edge cases (empty blocks, comments only)

**Success**:
- [ ] `block-checker.test.ts` exists with 20+ test cases
- [ ] Integration tests cover happy path and error paths
- [ ] Source position mapping verified

### Step 0.4: Document Known Failures

**What**: Mark the 4 failing Vec tests as `it.skip` with documentation.

**Do**:
1. Add comments explaining why each fails (indexed type unification limits)
2. Use `it.skip` so CI passes
3. Create tracking issue or TODO for fixing

**Success**:
- [ ] `npx vitest run` shows 0 failures
- [ ] Known limitations documented in test file

---

**CHECKPOINT**: After Phase 0, you have a green test suite and confidence to proceed.

---

## Phase 1: Architectural Safety Nets

**Why Now**: These quick changes prevent classes of bugs and enable safer refactoring.

**Parallel Note**: Can be done alongside Phase 0 testing work.

### Step 1.1: Add Fuel to WHNF

**What**: Add termination bound to `whnf` function.

**Files**: `tt-typecheck.ts`

**Do**:
```typescript
export function whnf(
  term: TTKTerm,
  ctx: TTKContext = [],
  definitions?: DefinitionsMap,
  fuel: number = 10000
): TTKTerm {
  if (fuel <= 0) throw new Error('WHNF: reduction limit exceeded');
  // ... pass fuel - 1 to recursive calls
}
```

**Success**:
- [ ] `whnf` has fuel parameter
- [ ] Recursive calls decrement fuel
- [ ] Test exists for fuel exhaustion
- [ ] All existing tests pass

### Step 1.2: Break Illegal Kernel Import

**What**: Remove TPattern import from kernel; define TTKPattern independently.

**Files**: `tt-kernel.ts`, `tt-pattern-match.ts`

**Do**:
1. Remove `import type { TPattern } from './tt-core'` from `tt-kernel.ts`
2. Add to `tt-kernel.ts`:
   ```typescript
   export type TTKPattern =
     | { tag: 'PVar'; name: string }  // Wildcards are PVar with _wN names
     | { tag: 'PCtor'; name: string; args: TTKPattern[] };
   ```
3. Update `TTKClause` to use `TTKPattern`
4. Add pattern elaboration `TPattern` → `TTKPattern` in `tt-elab.ts`

Note: PWild was removed from TTKPattern. Wildcards are now parsed as PVar with
unique names (_w0, _w1, etc.) by the parser.

**Success**:
- [ ] `tt-kernel.ts` has zero imports from `tt-core.ts`
- [ ] `TTKPattern` defined in kernel
- [ ] All tests pass

### Step 1.3: Add CheckedTerm Branding

**What**: Create branded type to distinguish type-checked terms.

**Files**: `tt-kernel.ts`, `tt-typecheck.ts`

**Do**:
```typescript
// tt-kernel.ts
declare const checkedBrand: unique symbol;
export type CheckedTerm = TTKTerm & { [checkedBrand]: true };

// tt-typecheck.ts
export function inferType(term: TTKTerm, ctx: TTKContext): CheckedTerm {
  // ... type checking logic ...
  return result as CheckedTerm;
}
```

**Success**:
- [ ] `CheckedTerm` type exists
- [ ] `inferType` returns `CheckedTerm`
- [ ] Can't accidentally pass unchecked term where checked expected

---

**CHECKPOINT**: After Phase 1, type checker is safer (terminates, clean boundaries).

---

## Phase 2: Named and Implicit Arguments

**Why Now**: This is the foundation for Levels, Multi-var, and Records. Everything else depends on it.

**Source**: `NAMED_ARGS_PLAN.md` (detailed implementation guide)

### Step 2.1: Extend Surface Syntax Types

**Files**: `tt-core.ts`

**Do**:
1. Add `BinderInfo = 'explicit' | 'implicit'` to `BinderKind`
2. Add `TArg = Positional | Named` type for call-site arguments
3. Add `Call` node to `TTerm`: `{ tag: 'Call'; fn: TTerm; args: TArg[] }`
4. Add `TPatternArg` for pattern arguments

**Success**:
- [ ] Types compile
- [ ] Existing tests pass (backward compatible)

### Step 2.2: Parser - Implicit Binders

**Files**: `tt-parser.ts`

**Do**:
1. Parse `{x : A} -> B` as implicit Pi binder
2. Parse `\ {x : A} => e` as implicit lambda (if needed)
3. Reuse existing `LBRACE`/`RBRACE` tokens

**Success**:
- [ ] `{A : Type} -> A -> A` parses correctly
- [ ] Parser tests added

### Step 2.3: Parser - Named Arguments

**Files**: `tt-parser.ts`

**Do**:
1. Parse `f {x = e}` as named argument application
2. Parse `f {x}` as shorthand for `f {x = x}`
3. Build `Call` node with mixed args

**Success**:
- [ ] `foo {y = 1} 2` parses as Call with named and positional args
- [ ] Parser tests added

### Step 2.4: Elaboration Algorithm

**Files**: `tt-elab.ts`

**Do**:
1. Implement call-site elaboration (see NAMED_ARGS_PLAN.md Section "Elaboration Algorithm")
2. Resolve named args to positions
3. Fill implicit args with fresh metavars
4. Convert `Call` to chain of kernel `App` nodes

**Success**:
- [ ] `id 5` where `id : {A : Type} -> A -> A` elaborates to `App(App(id, ?A), 5)`
- [ ] Named args work: `foo {y = 1} 2` resolves correctly
- [ ] Error on unknown param name, duplicate args

### Step 2.5: Pattern Syntax for Implicits

**Files**: `tt-parser.ts`, `tt-pattern-match.ts`

**Do**:
1. Parse `{n}` and `{n = pat}` in pattern position
2. Patterns must be in declaration order
3. Elaborate implicit patterns to regular bindings

**Success**:
- [ ] `qux {n} a b = ...` parses and elaborates correctly
- [ ] Tests for pattern implicit args

### Step 2.6: Type Query Updates

**Files**: `tt-type-query.ts`

**Do**:
1. Handle `Call` nodes in type queries
2. Report correct types for named/implicit arguments

**Success**:
- [ ] Hovering over `{x = e}` shows correct type
- [ ] Type queries work in implicit patterns

---

**CHECKPOINT**: After Phase 2, you have working implicit and named arguments.

---

## Phase 3: Universe Levels

**Depends On**: Phase 2 (implicit level parameters use implicit arg syntax)

**Source**: `LEVELS_PLAN.md` (detailed implementation guide)

### Step 3.1: Level Type Infrastructure

**Files**: NEW `tt-level.ts`, NEW `tt-level.test.ts`

**Do**:
1. Create `Level` type: `LZero | LSucc | LMax | LIMax | LParam | LMVar`
2. Implement helpers: `mkLZero`, `mkLSucc`, `mkLMax`, `mkLIMax`, `mkLParam`, `mkLMVar`
3. Implement `simplifyLevel`, `levelsEqual`, `prettyPrintLevel`
4. Write comprehensive tests

**Success**:
- [ ] `tt-level.ts` exists with full Level type
- [ ] `tt-level.test.ts` has 30+ tests
- [ ] Level simplification works (`max(0, u) = u`, etc.)

### Step 3.2: Kernel Sort Update

**Files**: `tt-kernel.ts`, `tt-core.ts`

**Do**:
1. Change `Sort.level` from `number` to `Level`
2. Update `mkProp()` → `{ tag: 'Sort', level: mkLZero() }`
3. Update `mkType(n)` for backward compat
4. Add `mkSort(level: Level)` for explicit level
5. Update `prettyPrint` for Level

**Success**:
- [ ] `Sort` uses `Level` type
- [ ] All existing tests pass (backward compat)
- [ ] `Sort u` pretty-prints correctly

### Step 3.3: Type Checker Level Rules

**Files**: `tt-typecheck.ts`

**Do**:
1. Update Sort rule: `Sort l : Sort (succ l)`
2. Update Pi rule: result is `imax(domain_level, body_level)`
3. Handle level comparison in `convertible`

**Success**:
- [ ] `(A : Type) -> Prop` has type `Prop` (impredicativity preserved)
- [ ] `(A : Type) -> Type` has type `Type 1`
- [ ] All existing tests pass

### Step 3.4: Level Unification

**Files**: NEW `tt-level-unify.ts`, NEW `tt-level-unify.test.ts`

**Do**:
1. Create `LevelUnifyResult = success | failure | stuck`
2. Implement `unifyLevels(l1, l2)`
3. Handle: structural equality, mvar solving, succ/max decomposition

**Success**:
- [ ] Level unification works for concrete levels
- [ ] Level mvars can be solved
- [ ] Tests cover all cases

### Step 3.5: Parser Level Syntax

**Files**: `tt-parser.ts`

**Do**:
1. Parse `Type u` as `Sort (succ (param u))`
2. Parse `Sort u` as `Sort (param u)`
3. Parse `Type_3` as `Sort 4` (concrete)
4. (Future) Parse `Sort (max u v)`

**Success**:
- [ ] `Type u` parses correctly
- [ ] Parser tests added

### Step 3.6: Integration

**Files**: `tt-unify.ts`, `tt-elab.ts`

**Do**:
1. Integrate level unification into term unification
2. Handle level params in elaboration context
3. Generate fresh level mvars for universe-polymorphic definitions

**Success**:
- [ ] `id : (A : Type u) -> A -> A` type-checks
- [ ] Level inference works at call sites

---

**CHECKPOINT**: After Phase 3, you have universe-polymorphic definitions.

---

## Phase 4: Multi-Variable Binders

**Depends On**: Phase 2 (implicit multi-var binders like `{A B : Type}`)

**Can Run In Parallel With**: Phase 3 (Levels) - no hard dependency

**Source**: `MULTI_ARGS_PLAN.md` (detailed implementation guide)

### Step 4.1: Add MultiVarBinder to TT

**Files**: `tt-core.ts`

**Do**:
1. Add `MultiVarBinder` variant to `TTerm`:
   ```typescript
   | { tag: 'MultiVarBinder'; names: string[]; binderKind: BinderKind; domain: TTerm; body: TTerm }
   ```
2. Add `mkMultiVarBinder` helper
3. Update `prettyPrint`

**Success**:
- [ ] Type compiles
- [ ] Pretty print shows `(x y : T)`

### Step 4.2: Parser Multi-Name Syntax

**Files**: `tt-parser.ts`

**Do**:
1. In binder parsing, collect identifiers until `:`
2. If multiple names, create `MultiVarBinder`
3. Handle both `(x y : T)` and `{x y : T}`

**Success**:
- [ ] `(x y : Nat) -> Nat` parses as MultiVarBinder
- [ ] `{A B : Type} -> A` parses correctly
- [ ] Parser tests added

### Step 4.3: Elaboration Unwinding

**Files**: `tt-elab.ts`

**Do**:
1. Add `unwindMultiVarBinders(term: TTerm): TTerm`
2. Transform `MultiVarBinder(['x','y'], domain, body)` → nested single Binders
3. Call unwinding BEFORE other elaboration steps

**Success**:
- [ ] `(x y : Nat) -> Nat` elaborates to `Pi(Nat, Pi(Nat, Nat))`
- [ ] De Bruijn indices correct in body
- [ ] All tests pass

### Step 4.4: Type Query Support

**Files**: `tt-type-query.ts`, `tt-source-query.ts`

**Do**:
1. Track source ranges for each name in MultiVarBinder
2. Type query at `x` in `(x y : Nat)` returns `Nat`
3. Type query at `y` in `(x y : Nat)` returns `Nat`

**Success**:
- [ ] Type queries work for each name in multi-var binder
- [ ] Source ranges correct

---

**CHECKPOINT**: After Phase 4, you have convenient multi-variable binder syntax.

---

## Phase 5: Records (Structures)

**Depends On**: Phase 2 (implicit params), Phase 3 (universe levels for `Type u`)

**Source**: `STRUCTURES_PLAN.md` (detailed implementation guide)

### Step 5.1: Parser Support

**Files**: `tt-parser.ts`

**Do**:
1. Add `STRUCTURE`, `EXTENDS` tokens
2. Add `'structure'` to ParsedDeclaration kinds
3. Implement `parseStructureDeclaration()`:
   ```
   structure Name (params) extends Parents where
     field1 : Type1
     field2 : Type2
   ```

**Success**:
- [ ] Simple structures parse
- [ ] Parameters (explicit and implicit) parse
- [ ] `extends` clause parses
- [ ] Parser tests added

### Step 5.2: Field Dependency Checking

**Files**: NEW `tt-typecheck-record.ts`

**Do**:
1. Implement `checkRecordDeclaration(record, env)`
2. Check each field type in growing context (params + earlier fields)
3. Error if field references later field

**Success**:
- [ ] Valid dependent fields type-check
- [ ] Forward reference errors detected
- [ ] Error messages point to correct field

### Step 5.3: Projection Generation

**Files**: NEW `tt-record-projections.ts`

**Do**:
1. For each field, generate `Record.field : Record -> FieldType`
2. Handle dependencies: `Sigma.snd : (s : Sigma A B) -> B (Sigma.fst s)`
3. Register projections in environment

**Success**:
- [ ] `Point.x : Point -> Nat` generated
- [ ] Dependent projections have correct types
- [ ] Projections in scope for subsequent code

### Step 5.4: Constructor Generation

**Files**: `tt-record-projections.ts`

**Do**:
1. Generate `Record.mk : (params) -> (fields) -> Record params`
2. Handle implicit parameters

**Success**:
- [ ] `Point.mk : Nat -> Nat -> Point` generated
- [ ] `Pair.mk : {A : Type} -> {B : Type} -> A -> B -> Pair A B` generated

### Step 5.5: Block Checker Integration

**Files**: `block-checker.ts`

**Do**:
1. Add `'Record'` block type
2. Wire up: parse → inline extensions → elaborate → type-check → register
3. Handle extension errors (unknown parent, field clash, cycles)

**Success**:
- [ ] `structure Point where x : Nat; y : Nat` works end-to-end
- [ ] Extension hierarchy (Magma → Semigroup → Monoid) works
- [ ] Errors reported with correct source positions

### Step 5.6: Type Query Support

**Files**: `tt-type-query.ts`

**Do**:
1. Type queries for record name, params, fields
2. Growing context for field type queries

**Success**:
- [ ] Hovering over field name shows type
- [ ] Hovering over record name shows record type

---

**CHECKPOINT**: After Phase 5, you have working record/structure definitions.

---

## Phase 6: Architectural Hardening

**Can Start After**: Phase 2 (many steps don't depend on features)

**This Is A Side Quest**: Can be interleaved with feature phases.

### Step 6.1: Document Typing Rules

**Files**: `tt-typecheck.ts`

**Do**: Add formal rule comments above each case in `inferType`/`checkType`.

**Example**:
```typescript
/**
 * Rule APP:
 *   Γ ⊢ f : Π(x:A).B    Γ ⊢ a : A
 *   ─────────────────────────────
 *          Γ ⊢ f a : B[a/x]
 */
case 'App': { ... }
```

**Success**:
- [ ] Every case has documented rule
- [ ] Preconditions and invariants stated

### Step 6.2: Create Context Module

**Files**: NEW `context.ts`

**Do**:
1. Create `Context` namespace with: `empty`, `extend`, `lookup`, `lookupByName`, `names`
2. Delete duplicate implementations
3. All context ops go through this module

**Success**:
- [ ] Single source of truth for context operations
- [ ] No inline context manipulation elsewhere

### Step 6.3: Add Metatheory Property Tests

**Files**: NEW `tt-metatheory.test.ts`

**Do**:
1. Install `fast-check`
2. Create arbitrary well-typed term generator
3. Test: substitution preserves typing
4. Test: weakening preserves typing
5. Test: WHNF preserves type
6. Test: conversion symmetry and transitivity

**Success**:
- [ ] Property tests exist and pass
- [ ] 100+ random cases per property

### Step 6.4: Convert Exceptions to Results

**Files**: `tt-typecheck.ts`, `tt-pattern-match.ts`, `block-checker.ts`

**Do**:
1. Define `TypeCheckResult<T> = { ok: true; value: T } | { ok: false; error: TypeCheckError }`
2. Convert `inferType`, `checkType` to return Results
3. No `throw` in kernel code

**Success**:
- [ ] Kernel functions return Results
- [ ] Callers handle Results properly

### Step 6.5: Implement Generic Term Fold

**Files**: `tt-kernel.ts`

**Do**:
1. Create `foldTerm<R>(term, visitor, depth)` generic traversal
2. Reimplement `subst`, `shift` using fold
3. Delete duplicate traversal code

**Success**:
- [ ] Single traversal abstraction
- [ ] Net code reduction

### Step 6.6: Add Branded Index Types

**Files**: NEW `indices.ts`, `tt-kernel.ts`

**Do**:
1. Create `DeBruijnIndex`, `DeBruijnLevel` branded types
2. Add conversion functions `Index.toLevel`, `Level.toIndex`
3. Update key function signatures

**Success**:
- [ ] Type system prevents index/level confusion
- [ ] Key functions use branded types

---

## Phase 7: Kernel Extraction

**Depends On**: Phases 1-5 complete, Phase 6 mostly complete

### Step 7.1: Create Kernel Directory

**Do**:
1. Create `src/kernel/` directory
2. Move minimal code: `term.ts`, `subst.ts`, `whnf.ts`, `typecheck.ts`, `conversion.ts`
3. Kernel has ZERO imports from outside `kernel/`

**Success**:
- [ ] `src/kernel/` exists
- [ ] `src/kernel/index.ts` exports only kernel API
- [ ] Kernel < 1,000 lines total

### Step 7.2: Write Formal Specification

**Files**: NEW `SPECIFICATION.md`

**Do**:
1. Document complete type theory: syntax, typing rules, reduction rules
2. Each rule has name matching code
3. Serve as verification contract

**Success**:
- [ ] Complete specification document
- [ ] Rules map 1-1 to code

### Step 7.3: Elaborate Match Away

**Files**: `tt-elab.ts`, `tt-kernel.ts`

**Do**:
1. Remove `Match` from kernel terms
2. Pattern matching elaborates to eliminators (recursors)
3. `tt-pattern-match.ts` becomes elaboration-only

**Success**:
- [ ] Kernel has no `Match` variant
- [ ] Kernel < 600 lines
- [ ] All tests pass

---

**CHECKPOINT**: After Phase 7, you have a minimal, extractable kernel.

---

## Phase 8: Formal Verification (Optional/Future)

**Depends On**: Phase 7 complete

### Step 8.1: Rewrite Kernel in Lean 4/Agda

**Do**:
1. Port ~500 lines kernel to dependently-typed language
2. Define types to match `SPECIFICATION.md`

### Step 8.2: Prove Fundamental Lemmas

**Do**:
1. Prove substitution lemma
2. Prove weakening
3. Prove subject reduction
4. Prove type safety (progress + preservation)

### Step 8.3: Certified Extraction (Optional)

**Do**:
1. Extract verified kernel back to TypeScript
2. Establish trust chain

---

## Summary Timeline

```
PHASE 0: Testing Foundation           [3-5 days]
PHASE 1: Safety Nets                  [1-2 days]
PHASE 2: Named/Implicit Arguments     [2-3 weeks]
PHASE 3: Universe Levels              [2-3 weeks] (can overlap with P4)
PHASE 4: Multi-var Binders            [1 week]
PHASE 5: Records                      [3-4 weeks]
PHASE 6: Architectural Hardening      [2-3 weeks] (side quest, interleaved)
PHASE 7: Kernel Extraction            [3-4 weeks]
PHASE 8: Formal Verification          [6-12 months] (optional)
```

**Total to feature-complete engine**: ~3-4 months
**Total to provable kernel**: +6-12 months

---

## Parallel Tracks

These can be worked on simultaneously by different people or as context-switching breaks:

| Track | Phases | Notes |
|-------|--------|-------|
| **Features** | 2 → 3 → 5 | Main development path |
| **Testing** | 0 (ongoing) | Add tests as features land |
| **Architecture** | 1, 6 | Can interleave with features |
| **Multi-var** | 4 | Independent after Phase 2 |

---

## Side Quests

These can be done anytime after their dependencies are met:

| Quest | After | Effort | Value |
|-------|-------|--------|-------|
| Add more parser tests | Phase 0 | Low | High |
| Document typing rules | Phase 1 | Medium | High |
| Metatheory property tests | Phase 0 | Medium | Very High |
| Branded index types | Phase 1 | Low | Medium |
| Generic term fold | Phase 1 | Medium | Medium |
| Performance benchmarks | Phase 0 | Low | Medium |

---

## Quick Reference: What Depends on What

| Feature | Requires |
|---------|----------|
| Named/Implicit Args | Nothing |
| Universe Levels | Named Args |
| Multi-var Binders | Named Args |
| Records | Named Args + Levels |
| Kernel Extraction | All features + Architecture |

---

## Original Source Documents

This plan integrates:
- `TEST_EXPANSION_PLAN.md` - Testing strategy
- `ARCHITECTURAL_REVIEW.md` - Kernel provability analysis
- `NAMED_ARGS_PLAN.md` - Implicit/named argument design
- `LEVELS_PLAN.md` - Universe level polymorphism
- `MULTI_ARGS_PLAN.md` - Multi-variable binder syntax
- `STRUCTURES_PLAN.md` - Record/structure implementation

These documents contain detailed implementation guidance for each phase.
