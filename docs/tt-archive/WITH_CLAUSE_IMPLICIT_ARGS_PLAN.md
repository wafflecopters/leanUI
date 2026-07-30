# With-Clause Implicit Arguments: Bug Analysis & Plan

**Date**: 2026-02-03
**Status**: Planning Phase
**Failing Tests**: 14 tests (baseline after reverting experimental changes)

## Executive Summary

With-clauses containing implicit parameters and recursive scrutinees fail with "Too many positional arguments" error. Root cause: `resolveAuxScrutineeTypes()` converts kernel types with implicit arguments to surface syntax using ALL positional arguments, which then fails re-elaboration.

## 1. System Overview: With-Clause Compilation Pipeline

### 1.1 High-Level Flow

```
Source Code (with-clause syntax)
  ↓ Parser
TT Surface Term
  ↓ with-desugar.ts: desugarWithClauses()
Main Function + Auxiliary Functions (ParsedDeclaration[])
  ↓ compile.ts: compileBlocks()
  ├─ resolveAuxScrutineeTypes() ← PROBLEM OCCURS HERE
  ├─ processTermDeclaration()
  │   ├─ Elaborate type (surface → kernel)
  │   └─ checkTermDeclaration()
  │       ├─ Extract namedArgMap, totalArity
  │       ├─ Elaborate value (surface → kernel)
  │       └─ Type check value against type
  └─ Register definitions
```

### 1.2 Key Data Structures

#### ParsedDeclaration (parser.ts)
```typescript
interface ParsedDeclaration {
  type?: TTerm;  // Surface type signature
  value?: TTerm; // Surface value (Match with clauses)
  withScrutineeExprs?: TTerm[];  // Original scrutinee expressions
  withScrutineeCount?: number;   // Number of scrutinee positions
}
```

#### TTerm vs TTKTerm
- **TTerm (surface)**: May contain `MultiBinder`, `named` flags, syntactic sugar
- **TTKTerm (kernel)**: Fully elaborated, all binders are singular, no named flags

#### namedArgMap & totalArity
- **namedArgMap**: `Map<string, number>` - Maps parameter names to positions for implicit params
- **totalArity**: `number` - Total count of parameters (including both implicit and explicit)
- **Source**: Extracted from surface type signature via `extractNamedArgMap()` and `countParameters()`

## 2. The Bug: Detailed Analysis

### 2.1 Failing Test Case

```lean
inductive Leq : Nat -> Nat -> Type where
  LeqZero : {n : Nat} -> Leq Zero n
  LeqSucc : {n m : Nat} -> Leq n m -> Leq (Succ n) (Succ m)

leqCanonical : {a b : Nat} -> (p q : Leq a b) -> Equal p q
leqCanonical LeqZero LeqZero = refl
leqCanonical (LeqSucc pleq) (LeqSucc qleq) with leqCanonical pleq qleq
  | refl => refl
```

**Expected**: Compiles successfully
**Actual**: "Too many positional arguments: 1 extra argument(s)"

### 2.2 What Happens Step-by-Step

#### Step 1: With-Desugaring (with-desugar.ts)
Creates auxiliary function:
```lean
leqCanonical-with-1 : {a b : Nat} -> (p q : Leq a b) -> ?_scrut0_type -> Equal p q
leqCanonical-with-1 x y refl = refl
```

The type contains a Hole `?_scrut0_type` because:
- `computeAuxiliaryType()` doesn't know the scrutinee's type yet
- For recursive call `leqCanonical pleq qleq`, it can't infer the type without the definitions

#### Step 2: resolveAuxScrutineeTypes() (compile.ts:5053)
Goal: Replace `?_scrut0_type` with actual scrutinee type

Process:
1. **Infer scrutinee type**: `inferScrutineeExprType(leqCanonical pleq qleq)`
   - Looks up `leqCanonical` in definitions
   - Walks Pi binders, substituting `pleq`, `qleq`
   - Result: `Equal (Leq n m) pleq qleq` (kernel term)

2. **Resolve implicit Holes**: `resolveImplicitHoles()`
   - Substitutes `{?Hole}` implicit args with variable types
   - Result: `Equal (Leq a b) p q` (kernel term)

3. **Convert to surface**: `kernelTypeToSurface()`
   ```typescript
   case 'App': return mkAppTT(kernelTypeToSurface(t.fn), kernelTypeToSurface(t.arg));
   ```
   - Converts `Equal (Leq a b) p q` (kernel) → `Equal (Leq a b) p q` (surface)
   - **PROBLEM**: This produces ALL POSITIONAL arguments!

4. **Replace Hole in surface type**:
   ```typescript
   auxDecl.type = replaceHoleInSurfaceTerm(auxDecl.type, '_scrut0_type', surfaceScrutType);
   ```
   Result: `{a b : Nat} -> (p q : Leq a b) -> Equal (Leq a b) p q -> Equal p q`

#### Step 3: processTermDeclaration() Re-Elaboration
When elaborating the type:
```typescript
kernelType = elabToKernelWithMap(auxDecl.type, ...);
```

Encounters `Equal (Leq a b) p q`:
- Looks up `Equal`'s signature: `{A : Type} -> A -> A -> Type`
- `namedArgMap = {A: 0}`, `totalArity = 3`
- Sees 3 positional arguments: `(Leq a b)`, `p`, `q`
- Position 0 is implicit (A), should be omitted or in `{...}` syntax
- **ERROR**: "Too many positional arguments: 1 extra argument(s)"

### 2.3 Root Cause Summary

**The fundamental problem**: `kernelTypeToSurface()` performs a structural conversion that loses implicit argument information. Kernel terms have ALL arguments positionally applied (implicit args are just regular applications), but surface syntax requires implicit args to be omitted or marked with `{...}`.

When `Equal (Leq a b) p q` (kernel) is converted to surface:
- Kernel: All 3 args are present (implicit args filled in)
- Surface (correct): Should be `Equal p q` (omit implicit A) or `Equal {Leq a b} p q` (explicit implicit)
- Surface (actual): `Equal (Leq a b) p q` (3 positional args) ← **WRONG**

## 3. Surface Area: What Needs to Work

### 3.1 Current Functionality (Must Not Break)

1. **Simple with-clauses** (working)
   ```lean
   test : {x : Bool} -> Bool -> Bool
   test y with not y
     | True => True
     | False => False
   ```

2. **With-clauses on variables** (working)
   ```lean
   simple : {n : Nat} -> Nat -> Equal n n
   simple x with x
     | Zero => refl
   ```

3. **Regular functions with implicit params** (working)
   ```lean
   leqCanonical : {a b : Nat} -> (p q : Leq a b) -> Equal p q
   leqCanonical LeqZero LeqZero = refl
   leqCanonical (LeqSucc pleq) (LeqSucc qleq) = refl  -- no with-clause
   ```

### 3.2 Broken Functionality (Must Fix)

1. **Recursive scrutinee with implicit params** (14 failing tests)
   ```lean
   leqCanonical (LeqSucc pleq) (LeqSucc qleq) with leqCanonical pleq qleq
     | refl => refl
   ```

2. **Complex scrutinee expressions with implicit params**
   ```lean
   f : {A : Type} -> A -> Equal A A
   f x with someFunction x
     | result => ...
   ```

### 3.3 Edge Cases to Consider

1. **Multiple implicit params**
   ```lean
   Equal : {A : Type} -> {B : Type} -> A -> B -> Type
   ```

2. **Mixed implicit/explicit**
   ```lean
   foo : {n : Nat} -> (x : Nat) -> {m : Nat} -> (y : Nat) -> Result
   ```

3. **Nested with-clauses**
   ```lean
   f x with g x
     | y with h y
       | z => ...
   ```

## 4. Attempted Solutions & Why They Failed

### 4.1 Approach 1: Cache Elaborated Kernel Type
**Idea**: Elaborate the type once after resolution, cache it, skip re-elaboration.

**Implementation**:
- Added `cachedKernelType` field to `ParsedDeclaration`
- In `resolveAuxScrutineeTypes`: elaborate resolved type and cache it
- In `processTermDeclaration`: use cached type if available

**Failure**: Broke regular pattern matching (isolate-leq-bug.test.ts). Caused implicit argument conflicts in non-auxiliary functions. The caching approach was too invasive.

### 4.2 Approach 2: Pass totalArity to elabToKernelWithMap
**Idea**: Fix pattern count mismatch by passing totalArity through elaboration.

**Implementation**:
- Added `totalArity` as 7th parameter to `elabToKernelWithMap` at checkTermDeclaration call

**Failure**: Didn't address root cause (type elaboration failing). Pattern elaboration needs totalArity from the ELABORATED type, not the surface type with Holes.

## 5. Potential Solutions (Ordered by Viability)

### 5.1 Solution A: Smart kernelTypeToSurface (RECOMMENDED)

**Core Idea**: Make `kernelTypeToSurface()` produce correct surface syntax that can be re-elaborated.

**Approach**:
1. When converting applications, check if the head function has implicit params
2. Omit or mark arguments in implicit positions appropriately

**Implementation Sketch**:
```typescript
function kernelTypeToSurface(t: TTKTerm, definitions: DefinitionsMap): TTerm {
  switch (t.tag) {
    case 'App':
      // Get the head function's namedArgMap if available
      const head = getAppHead(t);
      if (head.tag === 'Const') {
        const def = definitions.get(head.name);
        if (def?.namedArgMap && def.namedArgMap.size > 0) {
          // Convert to surface with correct implicit syntax
          return convertAppWithImplicits(t, def.namedArgMap, def.totalArity);
        }
      }
      return mkAppTT(kernelTypeToSurface(t.fn), kernelTypeToSurface(t.arg));
    // ... other cases
  }
}

function convertAppWithImplicits(app: TTKTerm, namedArgMap: NamedArgMap, totalArity: number): TTerm {
  // Collect all arguments
  const args = collectArgs(app);

  // For each arg, check if it's in an implicit position
  const surfaceArgs = args.map((arg, i) => {
    if (isImplicitPosition(i, namedArgMap)) {
      // Option 1: Omit implicit args entirely (if they can be inferred)
      // Option 2: Use explicit implicit syntax {arg}
      return mkExplicitImplicitTT(kernelTypeToSurface(arg));
    }
    return kernelTypeToSurface(arg);
  });

  return buildApp(head, surfaceArgs.filter(notOmitted));
}
```

**Pros**:
- Surgical fix - only changes `kernelTypeToSurface`
- Preserves existing architecture
- Can handle all implicit argument patterns

**Cons**:
- Needs access to `definitions` (must pass through)
- Must decide: omit or use `{...}` syntax?
- Complex logic for nested applications

**Risk**: Medium - New logic in conversion, but isolated

### 5.2 Solution B: Don't Convert, Keep Kernel Type

**Core Idea**: Store the resolved kernel type directly, don't convert back to surface.

**Approach**:
1. In `resolveAuxScrutineeTypes`: Elaborate type with Holes to kernel
2. Substitute Holes in kernel type directly (kernel-to-kernel)
3. Store resolved kernel type on auxiliary decl
4. Skip type elaboration in `processTermDeclaration` for auxiliaries

**Implementation Sketch**:
```typescript
function resolveAuxScrutineeTypes(...) {
  for (const auxDecl of auxiliaryDecls) {
    // Elaborate original type (with Holes) to kernel
    let kernelType = elabToKernelWithMap(auxDecl.type, ...);

    // For each scrutinee, substitute Hole in kernel type
    for (let i = 0; i < auxDecl.withScrutineeExprs.length; i++) {
      const scrutType = inferScrutineeExprType(...);  // Returns kernel
      kernelType = substituteHoleInKernel(kernelType, `_scrut${i}_type`, scrutType);
    }

    // Store resolved kernel type
    auxDecl.resolvedKernelType = kernelType;
  }
}
```

**Pros**:
- Avoids surface syntax issues entirely
- Clean separation: kernel stays kernel
- Direct substitution, no conversion

**Cons**:
- Architecture change: ParsedDeclaration holds kernel type
- Need to update all code expecting surface type
- `substituteHoleInKernel` might have de Bruijn index issues

**Risk**: Medium-High - Architectural change, may break other parts

### 5.3 Solution C: Don't Resolve Scrutinee Types Early

**Core Idea**: Leave Holes in the type, let type checker solve them.

**Approach**:
1. Remove `resolveAuxScrutineeTypes` entirely
2. Let `_scrut0_type` Holes elaborate to kernel Holes
3. During type checking, solve Holes via unification

**Implementation**:
- When checking auxiliary clause patterns, unify scrutinee with pattern to solve Hole

**Pros**:
- Simplest code change (deletion!)
- Leverages existing meta solving infrastructure
- Most "correct" from type theory perspective

**Cons**:
- May not work: Hole might not have enough info to solve
- Type checker might not trigger unification at right time
- Pattern matching might need scrutinee type before checking

**Risk**: High - Unknown if this approach can work at all

### 5.4 Solution D: Hybrid: Surface Conversion with Lookup

**Core Idea**: Pass namedArgMap info to `kernelTypeToSurface` for each const.

**Approach**:
```typescript
type NamedArgInfoLookup = (name: string) => {namedArgMap: NamedArgMap, totalArity: number} | undefined;

function kernelTypeToSurface(t: TTKTerm, lookup: NamedArgInfoLookup): TTerm {
  // When converting App of Const, use lookup to get namedArgMap
  // Generate correct surface syntax based on that info
}
```

**Pros**:
- Targeted fix to conversion
- Reuses existing lookup infrastructure

**Cons**:
- Every call to `kernelTypeToSurface` needs definitions lookup
- Must thread through multiple function calls

**Risk**: Low-Medium - Incremental change

## 6. Recommended Path Forward

### Phase 1: Prototype Solution A (Smart kernelTypeToSurface)

**Why**: Most surgical, preserves architecture, handles the specific problem.

**Steps**:
1. Modify `kernelTypeToSurface` signature to accept `definitions` or `NamedArgInfoLookup`
2. Implement `convertAppWithImplicits` helper
3. Decide: Omit implicit args or use `{...}` syntax? (Try omission first)
4. Update `resolveAuxScrutineeTypes` call site to pass definitions
5. Test on failing cases

**Success Criteria**:
- `leqCanonical` with-clause test passes
- No regressions on existing tests
- Code remains readable

**If This Fails**: Try Solution D (hybrid with lookup)

### Phase 2: Comprehensive Testing

**Test Matrix**:
```
| Scrutinee Type | Implicit Params | Status |
|----------------|-----------------|--------|
| Variable       | Yes             | ✓      |
| Variable       | No              | ✓      |
| Function call  | No              | ✓      |
| Function call  | Yes (single)    | ✗ FIX  |
| Function call  | Yes (multiple)  | ✗ FIX  |
| Nested app     | Yes             | ? TEST |
```

### Phase 3: Cleanup & Document

1. Remove unused helper functions
2. Add comprehensive comments to `resolveAuxScrutineeTypes`
3. Update SYSTEM_OVERVIEW.md with with-clause details
4. Document the implicit argument handling in conversion

## 7. Open Questions

1. **Should we omit implicit args or use explicit implicit syntax?**
   - Omission: `Equal p q` (simpler, may not always work)
   - Explicit: `Equal {Leq a b} p q` (always works, harder to implement)

2. **What about partial application?**
   - `map {f} xs` where f is implicit but xs is explicit
   - Need to handle mixed implicit/explicit carefully

3. **Do we need to update surface type for tests/display?**
   - Currently tests check `auxDecl.surfaceType` has no Holes
   - If we keep kernel type only, need to update tests

4. **Performance impact of definitions lookup?**
   - `kernelTypeToSurface` is called during resolution
   - Adding definitions lookup may slow down compilation

## 8. Success Metrics

**Definition of Done**:
- [ ] All 14 failing tests pass
- [ ] No new test failures
- [ ] `npm test` succeeds
- [ ] `npx tsc --noEmit` succeeds
- [ ] Code is documented and understandable

**Quality Checks**:
- [ ] Solution handles edge cases (multiple implicits, mixed implicit/explicit)
- [ ] No performance regressions (compile time similar)
- [ ] Architecture remains clean (no hacky special cases)
- [ ] Future maintainability: solution is general, not specific to leqCanonical

## 9. Risks & Mitigation

| Risk | Probability | Impact | Mitigation |
|------|------------|--------|------------|
| Solution breaks other tests | Medium | High | Incremental testing, revert if >5 regressions |
| Performance degradation | Low | Medium | Benchmark before/after |
| Incomplete fix (some edge cases fail) | Medium | Medium | Comprehensive test matrix |
| Architectural mess | Low | High | Code review, stick to plan |

## Appendix A: Code Locations Reference

### Key Files
- `src/compiler/with-desugar.ts`: With-clause desugaring (`desugarWithClauses`)
- `src/compiler/compile.ts`: Main compilation (`resolveAuxScrutineeTypes`, `processTermDeclaration`)
- `src/compiler/elab.ts`: Pattern reordering (`reorderPatterns`, `extractNamedArgMap`, `countParameters`)
- `src/compiler/kernel.ts`: Kernel term types (TTKTerm)
- `src/compiler/surface.ts`: Surface term types (TTerm)

### Key Functions
- `resolveAuxScrutineeTypes` (compile.ts:5053): Where the bug manifests
- `kernelTypeToSurface` (compile.ts:5145): Needs fix
- `inferScrutineeExprType` (compile.ts:5089): Infers scrutinee type
- `resolveImplicitHoles` (compile.ts:4920): Resolves implicit arg Holes
- `replaceHoleInSurfaceTerm` (compile.ts:5170): Substitutes Hole in surface

### Test Files
- `src/compiler/with-implicit-bug.test.ts`: Main failing test (leqCanonical)
- `src/compiler/isolate-leq-bug.test.ts`: Edge cases
- `src/compiler/with-desugar-implicit.test.ts`: Other implicit param tests
- `src/test-programs/tt-programs/with/*.tt`: Integration tests
