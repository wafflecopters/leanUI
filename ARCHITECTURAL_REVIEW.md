# Architectural Review: LeanUI Type Theory Implementation

**Version 3.0** | **Perspective**: Kent Beck (Clean Code) + Type Theory Correctness Czar

---

## Executive Summary

This review examines whether LeanUI's type theory implementation could form the basis of a **provably correct** proof assistant. We analyze the parser → elaborator → checker pipeline through two lenses: clean architecture and formal verification readiness.

### Verdict

| Criterion | Status | Assessment |
|-----------|--------|------------|
| **Algorithmic Foundation** | ✅ Solid | De Bruijn indices, bidirectional typing, PMWK unification |
| **Kernel Boundary** | ❌ Undefined | TCB spans 4 files, ~4,000 lines—6x too large |
| **Provability** | ❌ Not Ready | Missing: termination proofs, documented rules, metatheory tests |
| **Path to Provability** | ✅ Achievable | With focused refactoring: 3-6 months to high confidence |

**Bottom Line**: Strong algorithms wrapped in unclear boundaries. The code works correctly but cannot be proven correct in its current form.

---

## 1. The Good: Algorithmic Foundations

### 1.1 De Bruijn Indices ✓

```typescript
// tt-kernel.ts:48-49
export type TTKTerm =
  | { tag: 'Var'; index: number }  // Correct: De Bruijn, not named
```

**Why this matters**: De Bruijn indices eliminate α-equivalence (variable renaming) issues. Substitution becomes mechanical. This is what Coq, Lean, and Agda do. **No change needed.**

### 1.2 Bidirectional Type Checking ✓

```typescript
// tt-typecheck.ts - Two modes, correctly separated
export function inferType(term: TTKTerm, ctx: TTKContext): TTKTerm { ... }
export function checkType(term: TTKTerm, expected: TTKTerm, ctx: TTKContext): void { ... }
```

**Why this matters**: Synthesis (infer) + Checking modes enable type annotations to guide inference, essential for dependent types. Follows Pierce's "Local Type Inference." **No change needed.**

### 1.3 Pattern Matching Without K ✓

```typescript
// tt-unify.ts:1-21 - Explicit citation
/**
 * This implements the unification algorithm from "Pattern Matching Without K"
 * by Jesper Cockx, Dominique Devriese, and Frank Piessens (ICFP 2014).
 */

// Three-way result type (exactly what the paper specifies)
export type UnifyResult =
  | { tag: 'success'; substitution: Substitution }
  | { tag: 'failure'; reason: string }  // Provably impossible
  | { tag: 'stuck'; reason: string };   // Need more info
```

**Why this matters**: This peer-reviewed algorithm has formal proofs. The three-way result correctly distinguishes "proven impossible" from "can't decide yet." **Excellent choice.**

---

## 2. The Bad: Architectural Problems

### 2.1 Problem: No Kernel Boundary

**Current state**: "Kernel" code is spread across 4 files with unclear responsibilities:

| File | Lines | Contains Kernel? | Verdict |
|------|-------|-----------------|---------|
| tt-kernel.ts | 714 | Yes: terms, subst | Also has pretty-printing (not kernel) |
| tt-typecheck.ts | 923 | Yes: inference | Also has pattern match dispatch |
| tt-unify.ts | 1,017 | Debatable | Could be elaboration, not kernel |
| tt-pattern-match.ts | 1,282 | Partially | Should be elaborated away |

**Impact**: Cannot answer "what code do we need to trust?" A provable kernel needs a single-digit number of files with <1,000 lines total.

**The Kernel Question**: Should pattern matching and unification be in the kernel?

| Design Choice | Kernel | Pros | Cons |
|---------------|--------|------|------|
| **Match + Unify in kernel** | ~3,000 lines | Natural implementation | Larger TCB |
| **Elaborate Match to eliminators** | ~700 lines | Minimal kernel | Complex elaboration |
| **Hybrid (unify in, match out)** | ~1,700 lines | Balanced | Two boundaries |

**Recommendation**: Elaborate pattern matching to eliminators (like Coq). Keep unification outside kernel as an elaboration-time solver.

### 2.2 Problem: Kernel Imports Surface Types

```typescript
// tt-kernel.ts:40-41 - VIOLATION
import type { TPattern } from './tt-core';

// This means the "kernel" depends on "surface" code
// Dependency should flow: surface → elaboration → kernel
```

**Why this is bad**: The kernel's correctness should be independent of surface syntax choices. If TPattern changes, kernel could break.

**Fix**:
```typescript
// tt-kernel.ts - Define kernel pattern type independently
export type TTKPattern =
  | { tag: 'PVar'; name: string }
  | { tag: 'PWild' }
  | { tag: 'PCtor'; name: string; args: TTKPattern[] };

// Elaboration converts TPattern → TTKPattern
```

### 2.3 Problem: TT ≈ TTK (No Real Elaboration)

The surface syntax (TT) and kernel syntax (TTK) are nearly identical:

```typescript
// tt-core.ts
export type TTerm = { tag: 'Var'; index: number } | { tag: 'App'; ... } | ...

// tt-kernel.ts
export type TTKTerm = { tag: 'Var'; index: number } | { tag: 'App'; ... } | ...
```

**Why have two layers?** To allow surface conveniences that get elaborated away:
- Implicit arguments (`{x : A}` becomes explicit)
- Pattern synonyms (expand at elaboration time)
- Operator syntax (desugar to applications)
- Record syntax (elaborate to sigma types)

**Current state**: TT has none of these conveniences, so elaboration is trivial copying.

**Options**:
1. **Enrich TT**: Add implicit args, operators, records → meaningful elaboration
2. **Simplify TTK**: Remove Match, use eliminators only → TT becomes richer by contrast
3. **Merge TT/TTK**: If they're identical anyway, remove the indirection

**Recommendation**: Option 2. A simpler kernel is easier to verify.

### 2.4 Problem: Inconsistent Error Handling

```typescript
// tt-typecheck.ts - Uses exceptions
throw new TypeCheckError('Type mismatch: ...');

// tt-unify.ts - Uses result types
return { tag: 'failure', reason: 'Conflict: ...' };
```

**Why result types are better**:
- Explicit in function signature (no hidden control flow)
- Forces caller to handle failures
- Easier to test and reason about
- Required for formal verification (exceptions aren't pure)

**Migration plan**:
```typescript
// Step 1: Define unified result type
type TypeCheckResult<T> =
  | { ok: true; value: T }
  | { ok: false; error: TypeCheckError };

// Step 2: Convert inferType
export function inferType(term: TTKTerm, ctx: TTKContext): TypeCheckResult<TTKTerm>

// Step 3: Convert checkType
export function checkType(term: TTKTerm, expected: TTKTerm, ctx: TTKContext): TypeCheckResult<void>
```

---

## 3. The Ugly: Provability Blockers

### 3.1 Blocker: No Termination Argument

```typescript
// tt-typecheck.ts:130 - whnf can loop forever
export function whnf(term: TTKTerm, ctx: TTKContext, definitions?: DefinitionsMap): TTKTerm {
  switch (term.tag) {
    case 'App': {
      const fn = whnf(term.fn, ctx, definitions);  // Recursive call
      if (fn.tag === 'Binder' && fn.binderKind.tag === 'BLam') {
        return whnf(subst(0, term.arg, fn.body), ctx, definitions);  // Another!
      }
      // ...
    }
  }
}
```

**Risk**: Malformed input could cause infinite loops. Type checking must be decidable.

**Fix** (choose one):

```typescript
// Option A: Explicit fuel
function whnf(term: TTKTerm, ctx: Context, fuel: number = 10000): TTKTerm {
  if (fuel <= 0) throw new Error('Reduction limit exceeded');
  // ... use fuel - 1 in recursive calls
}

// Option B: Structural recursion (requires proof)
// Prove: each recursive call operates on a "smaller" term by some measure
// This is what Coq/Lean require for recursive functions
```

### 3.2 Blocker: Typing Rules Not Documented

The type checker implements rules implicitly. A provable kernel requires explicit rules:

```typescript
// CURRENT (implicit)
case 'Var': {
  const type = lookupVar(ctx, term.index);
  if (!type) throw new TypeCheckError(`Unbound variable: ${term.index}`);
  return type;
}

// REQUIRED FOR PROVABILITY
/**
 * Rule VAR:
 *
 *    Γ(i) = A
 *   ───────────
 *   Γ ⊢ Var(i) : A
 *
 * Precondition: i < |Γ|
 * Invariant: lookupVar returns the shifted type
 */
case 'Var': {
  const type = lookupVar(ctx, term.index);
  if (!type) throw new TypeCheckError(`VAR rule failed: index ${term.index} out of bounds`);
  return type;
}
```

**Every typing rule needs**:
1. Formal rule in comment (with inference line)
2. Explicit preconditions
3. Explicit invariants maintained

### 3.3 Blocker: No Metatheory Tests

The following properties are **necessary for soundness** but **untested**:

| Property | Description | Test |
|----------|-------------|------|
| **Substitution Lemma** | If Γ,x:A ⊢ t:B and Γ ⊢ s:A, then Γ ⊢ t[s/x]:B[s/x] | Property test |
| **Weakening** | If Γ ⊢ t:A, then Γ,x:B ⊢ t':A' (with shifting) | Property test |
| **Subject Reduction** | If Γ ⊢ t:A and t → t', then Γ ⊢ t':A | Property test |
| **Conversion Transitivity** | If A ≡ B and B ≡ C, then A ≡ C | Unit tests |
| **Conversion Symmetry** | If A ≡ B, then B ≡ A | Unit tests |

**Implementation** (using fast-check):
```typescript
import * as fc from 'fast-check';

// Need: Arbitrary well-typed term generator
const arbitraryWellTypedTerm: fc.Arbitrary<{ term: TTKTerm; type: TTKTerm; ctx: TTKContext }>;

describe('Metatheory', () => {
  it('substitution preserves typing', () => {
    fc.assert(fc.property(
      arbitraryWellTypedTerm,  // Γ, x:A ⊢ t : B
      arbitraryWellTypedTerm,  // Γ ⊢ s : A (where types match)
      ({ term: t, type: B, ctx }, { term: s }) => {
        const substituted = subst(0, s, t);
        const resultType = inferType(substituted, ctx.slice(1));
        // Should not throw, and type should be B[s/x]
      }
    ));
  });

  it('whnf preserves type', () => {
    fc.assert(fc.property(arbitraryWellTypedTerm, ({ term, type, ctx }) => {
      const reduced = whnf(term, ctx);
      const reducedType = inferType(reduced, ctx);
      expect(convertible(reducedType, type, ctx)).toBe(true);
    }));
  });
});
```

### 3.4 Blocker: Checked vs Unchecked Terms Indistinguishable

```typescript
// DANGEROUS: Both are TTKTerm, no type-level distinction
const checked: TTKTerm = inferType(term, ctx);  // Type-checked!
const unchecked: TTKTerm = { tag: 'Var', index: 999 };  // Garbage!

// Can pass either to functions expecting valid terms
function extractProof(term: TTKTerm): Proof { ... }  // Which is it?
```

**Fix**: Branded or wrapper types

```typescript
// Option A: Branded (lightweight, TypeScript-specific)
type CheckedTerm = TTKTerm & { readonly __brand: 'checked' };

function inferType(term: TTKTerm, ctx: TTKContext): CheckedTerm {
  // ... type checking logic ...
  return result as CheckedTerm;  // Brand applied after checking
}

// Option B: Wrapper (stronger, cross-language)
interface TypedTerm {
  term: TTKTerm;
  type: TTKTerm;
  ctx: TTKContext;
}

function inferType(term: TTKTerm, ctx: TTKContext): TypedTerm {
  const type = /* ... inference ... */;
  return { term, type, ctx };
}
```

---

## 4. DRY Violations and FP Improvements

### 4.1 Duplicated Term Traversal

Term traversal is reimplemented 4+ times:

```typescript
// tt-kernel.ts - substHelper traverses
function substHelper(target: number, repl: TTKTerm, term: TTKTerm, depth: number): TTKTerm {
  switch (term.tag) {
    case 'Var': ...
    case 'App': return { tag: 'App', fn: substHelper(...), arg: substHelper(...) };
    // ... every case
  }
}

// tt-kernel.ts - shift traverses the same way
function shift(amount: number, term: TTKTerm, cutoff: number): TTKTerm {
  switch (term.tag) {
    case 'Var': ...
    case 'App': return { tag: 'App', fn: shift(...), arg: shift(...) };
    // ... same structure!
  }
}

// tt-type-query.ts - another traversal
// tt-source-query.ts - yet another
```

**Solution**: Generic fold

```typescript
// tt-kernel.ts - Single traversal abstraction
interface TermVisitor<R> {
  visitVar(index: number, depth: number): R;
  visitSort(level: number): R;
  visitApp(fn: R, arg: R): R;
  visitBinder(name: string, kind: TTKBinderKind, domain: R, body: R): R;
  visitConst(name: string, type: R): R;
  visitHole(id: string, type: R, ctx: TTKContext): R;
  visitMatch(scrutinee: R, clauses: { patterns: TPattern[]; rhs: R }[]): R;
}

function foldTerm<R>(term: TTKTerm, visitor: TermVisitor<R>, depth: number = 0): R {
  switch (term.tag) {
    case 'Var': return visitor.visitVar(term.index, depth);
    case 'Sort': return visitor.visitSort(term.level);
    case 'App': return visitor.visitApp(
      foldTerm(term.fn, visitor, depth),
      foldTerm(term.arg, visitor, depth)
    );
    // ... etc
  }
}

// Now subst is just:
function subst(target: number, repl: TTKTerm, term: TTKTerm): TTKTerm {
  return foldTerm(term, {
    visitVar: (i, d) => i === target + d ? shift(d, repl) : mkVar(i > target + d ? i - 1 : i),
    visitSort: (l) => mkSort(l),
    visitApp: (fn, arg) => mkApp(fn, arg),
    // ... compositional!
  });
}
```

### 4.2 Context Operations Scattered

Context manipulation appears in multiple forms:

```typescript
// tt-typecheck.ts:65-75
export function extendContext(ctx: TTKContext, name: string, type: TTKTerm): TTKContext {
  const shiftedType = shiftTermBy(type, 1, 0);
  const shiftedCtx = ctx.map(binding => ({
    name: binding.name,
    type: shiftTermBy(binding.type, 1, 0),
  }));
  return [{ name, type: shiftedType }, ...shiftedCtx];
}

// tt-pattern-match.ts - inline variant
const extendedCtx = [{ name, type: shiftedType }, ...ctx];

// Different semantics? Same? Hard to tell.
```

**Solution**: Canonical context module

```typescript
// kernel/context.ts
export namespace Context {
  export const empty: TTKContext = [];

  export function extend(ctx: TTKContext, name: string, type: TTKTerm): TTKContext {
    // Single source of truth for this operation
    const shiftedType = shift(1, type, 0);
    const shiftedCtx = ctx.map(b => ({ name: b.name, type: shift(1, b.type, 0) }));
    return [{ name, type: shiftedType }, ...shiftedCtx];
  }

  export function lookup(ctx: TTKContext, index: number): TTKTerm | null {
    return index >= 0 && index < ctx.length ? ctx[index].type : null;
  }

  export function lookupByName(ctx: TTKContext, name: string): { index: number; type: TTKTerm } | null {
    const idx = ctx.findIndex(b => b.name === name);
    return idx >= 0 ? { index: idx, type: ctx[idx].type } : null;
  }

  export function names(ctx: TTKContext): string[] {
    return ctx.map(b => b.name);
  }

  export function length(ctx: TTKContext): number {
    return ctx.length;
  }
}
```

### 4.3 Missing Branded Types for Indices

De Bruijn indices and levels are both `number`, easily confused:

```typescript
// What's the difference?
const idx: number = 3;   // Is this an index (relative to binder)?
const lvl: number = 3;   // Or a level (absolute depth)?

// They're used differently!
// Index: Var(0) refers to innermost binder
// Level: Level 0 is the outermost binder

// Current function signature - unclear
function shift(amount: number, term: TTKTerm, cutoff: number): TTKTerm
// Is cutoff an index or a level?
```

**Fix**:
```typescript
// kernel/indices.ts
export type DeBruijnIndex = number & { readonly __brand: 'DeBruijnIndex' };
export type DeBruijnLevel = number & { readonly __brand: 'DeBruijnLevel' };
export type ShiftAmount = number & { readonly __brand: 'ShiftAmount' };

export const Index = {
  of: (n: number): DeBruijnIndex => n as DeBruijnIndex,
  toLevel: (idx: DeBruijnIndex, ctxLen: number): DeBruijnLevel => (ctxLen - 1 - idx) as DeBruijnLevel,
};

export const Level = {
  of: (n: number): DeBruijnLevel => n as DeBruijnLevel,
  toIndex: (lvl: DeBruijnLevel, ctxLen: number): DeBruijnIndex => (ctxLen - 1 - lvl) as DeBruijnIndex,
};

// Now type-safe:
function shift(amount: ShiftAmount, term: TTKTerm, cutoff: DeBruijnIndex): TTKTerm
```

---

## 5. Risk Assessment

### 5.1 Soundness Risks

| Risk | Severity | Likelihood | Mitigation |
|------|----------|------------|------------|
| **Infinite loop in whnf** | High | Medium | Add fuel parameter |
| **Universe inconsistency (Type:Type)** | Critical | Low | Already handled correctly |
| **Substitution bug** | High | Low | Add property tests |
| **Index/level confusion** | Medium | Medium | Add branded types |
| **Unchecked term escapes** | High | Medium | Add CheckedTerm wrapper |

### 5.2 Technical Debt

| Debt | Impact | Effort to Fix |
|------|--------|---------------|
| TT ≈ TTK duplication | Low (works fine) | High (architectural) |
| Pattern import in kernel | Medium (boundary violation) | Low (copy type def) |
| Exception vs Result inconsistency | Medium (testing harder) | Medium (gradual migration) |
| No metatheory tests | High (unknown correctness) | Medium (property tests) |

### 5.3 What Could Go Wrong

1. **Soundness bug discovered late**: Without metatheory tests, a subtle bug in substitution or conversion could go unnoticed until a user derives `False`.

2. **Performance cliff**: Without fuel/termination bounds, adversarial input could hang the type checker.

3. **Refactoring breaks soundness**: Without explicit typing rules documented, a well-intentioned refactor could subtly break a rule's invariants.

---

## 6. THE PLAN: Ordered Steps to a Provable Kernel

**Execute these steps in order. Do not skip steps. Each step unlocks the next.**

---

### Step 1: ADD FUEL TO WHNF

**What**: Add a `fuel` parameter to the `whnf` function that decrements on each recursive call. Throw an error when fuel hits zero.

**Why**: Without this, malformed input can hang the type checker forever. This is a soundness and availability risk. Every other step assumes the type checker terminates.

**Files**: `tt-typecheck.ts`

**Success**:
- [ ] `whnf` has signature `whnf(term, ctx, definitions?, fuel = 10000)`
- [ ] All recursive calls pass `fuel - 1`
- [ ] Test exists: deeply nested term exhausts fuel and throws
- [ ] All existing tests still pass

---

### Step 2: BREAK THE ILLEGAL IMPORT

**What**: Remove `import type { TPattern } from './tt-core'` from `tt-kernel.ts`. Define `TTKPattern` independently in the kernel.

**Why**: The kernel must have zero dependencies on surface code. This import means surface changes can break the kernel. It's a boundary violation.

**Files**: `tt-kernel.ts`, `tt-pattern-match.ts` (update imports)

**Success**:
- [ ] `tt-kernel.ts` has no imports from `tt-core.ts`
- [ ] `TTKPattern` is defined in `tt-kernel.ts`
- [ ] `TTKClause` uses `TTKPattern`, not `TPattern`
- [ ] Elaboration converts `TPattern` → `TTKPattern`
- [ ] All tests pass

---

### Step 3: ADD CHECKED TERM BRANDING

**What**: Create a branded type `CheckedTerm` that can only be produced by successful type checking. Functions that require verified terms take `CheckedTerm`, not `TTKTerm`.

**Why**: Currently, nothing prevents passing garbage terms to functions expecting well-typed terms. This is a type-level bug waiting to happen.

**Files**: `tt-kernel.ts`, `tt-typecheck.ts`

**Success**:
- [ ] `CheckedTerm` type exists: `TTKTerm & { readonly __checked: unique symbol }`
- [ ] `inferType` returns `CheckedTerm`
- [ ] `checkType` returns `CheckedTerm`
- [ ] At least one function signature changed to require `CheckedTerm`
- [ ] Compiler rejects passing raw `TTKTerm` where `CheckedTerm` expected

---

### Step 4: DOCUMENT EVERY TYPING RULE

**What**: Add a comment above each case in `inferType` and `checkType` showing the formal typing rule being implemented. Use standard notation with inference lines.

**Why**: Without documented rules, we can't verify the implementation matches the theory. This is prerequisite for any formal reasoning.

**Files**: `tt-typecheck.ts`

**Success**:
- [ ] Every `case` in `inferType` has a rule comment
- [ ] Every `case` in `checkType` has a rule comment
- [ ] Rules use standard notation: premises above line, conclusion below
- [ ] Preconditions and invariants are stated
- [ ] A reviewer can verify code matches rules by inspection

**Example**:
```typescript
/**
 * Rule APP:
 *   Γ ⊢ f : Π(x:A).B    Γ ⊢ a : A
 *   ─────────────────────────────
 *          Γ ⊢ f a : B[a/x]
 *
 * Precondition: f and a are well-formed in Γ
 * Invariant: result type has a substituted correctly
 */
case 'App': { ... }
```

---

### Step 5: CREATE CONTEXT MODULE

**What**: Create a single `Context` namespace/module with all context operations: `empty`, `extend`, `lookup`, `lookupByName`, `names`, `length`. Delete duplicate implementations elsewhere.

**Why**: Context operations are scattered and inconsistent. A single source of truth prevents subtle bugs from different extend/lookup semantics.

**Files**: New `src/types/context.ts`, update all importers

**Success**:
- [ ] `context.ts` exists with `Context` namespace
- [ ] All context operations go through this module
- [ ] No inline context manipulation remains (search for `[{ name,` patterns)
- [ ] All tests pass

---

### Step 6: ADD METATHEORY PROPERTY TESTS

**What**: Install `fast-check`. Create `tt-metatheory.test.ts` with property tests for: substitution preserves typing, weakening preserves typing, WHNF preserves typing, conversion is symmetric and transitive.

**Why**: These properties are *necessary* for soundness but *untested*. A bug here means users can prove `False`. Property tests catch edge cases unit tests miss.

**Files**: New `src/types/tt-metatheory.test.ts`, `package.json`

**Success**:
- [ ] `fast-check` is installed
- [ ] Arbitrary well-typed term generator exists
- [ ] Test: substitution lemma (100+ random cases)
- [ ] Test: weakening lemma (100+ random cases)
- [ ] Test: WHNF preserves type (100+ random cases)
- [ ] Test: conversion symmetry
- [ ] Test: conversion transitivity
- [ ] All property tests pass

---

### Step 7: CONVERT EXCEPTIONS TO RESULTS

**What**: Change `inferType` and `checkType` to return `Result<T, TypeCheckError>` instead of throwing. Propagate through callers.

**Why**: Exceptions hide control flow and make testing harder. Result types make failure explicit in the type signature. Required for any formal reasoning about the code.

**Files**: `tt-typecheck.ts`, `tt-pattern-match.ts`, `block-checker.ts`

**Success**:
- [ ] `TypeCheckResult<T> = { ok: true; value: T } | { ok: false; error: TypeCheckError }`
- [ ] `inferType` returns `TypeCheckResult<CheckedTerm>`
- [ ] `checkType` returns `TypeCheckResult<void>`
- [ ] No `throw new TypeCheckError` in kernel code
- [ ] All callers handle Result properly
- [ ] All tests updated and passing

---

### Step 8: IMPLEMENT GENERIC TERM FOLD

**What**: Create a generic `foldTerm<R>` function that traverses terms once. Reimplement `subst`, `shift`, and other traversals using it.

**Why**: Term traversal is copy-pasted 4+ times. Each copy is a bug risk. A single fold ensures consistency and reduces code by ~200 lines.

**Files**: `tt-kernel.ts`

**Success**:
- [ ] `foldTerm<R>(term, visitor, depth)` exists
- [ ] `TermVisitor<R>` interface defined
- [ ] `subst` reimplemented using `foldTerm`
- [ ] `shift` reimplemented using `foldTerm`
- [ ] Old traversal code deleted
- [ ] All tests pass
- [ ] Net code reduction of 100+ lines

---

### Step 9: ADD BRANDED INDEX TYPES

**What**: Create `DeBruijnIndex` and `DeBruijnLevel` branded types. Update function signatures to use them. Add conversion functions.

**Why**: Indices and levels are both `number` but have different semantics. Mixing them up causes subtle bugs. The type system should prevent this.

**Files**: New `src/types/indices.ts`, `tt-kernel.ts`, `tt-typecheck.ts`

**Success**:
- [ ] `DeBruijnIndex = number & { __brand: 'index' }`
- [ ] `DeBruijnLevel = number & { __brand: 'level' }`
- [ ] `Index.of()`, `Level.of()`, `Index.toLevel()`, `Level.toIndex()` exist
- [ ] `shift`, `subst` use branded types
- [ ] Compiler catches at least one real bug (or we're confident there are none)

---

### Step 10: CREATE KERNEL DIRECTORY

**What**: Create `src/kernel/` directory. Move minimal kernel code there: `term.ts`, `subst.ts`, `whnf.ts`, `typecheck.ts`, `conversion.ts`. The kernel has NO imports from outside `kernel/`.

**Why**: The kernel boundary must be explicit. "What do we trust?" should be answerable by "the files in `kernel/`". Current code has no clear boundary.

**Files**: New directory structure, move and refactor code

**Success**:
- [ ] `src/kernel/` directory exists
- [ ] `src/kernel/index.ts` exports only kernel API
- [ ] Kernel has 0 imports from outside kernel
- [ ] Kernel is <1,000 lines total
- [ ] Non-kernel code imports from `kernel/index.ts` only
- [ ] All tests pass

---

### Step 11: WRITE FORMAL SPECIFICATION

**What**: Create `SPECIFICATION.md` documenting the complete type theory: syntax, typing rules, reduction rules, conversion rules. Each rule has a name that maps to code.

**Why**: This is the contract. The code implements the spec. Without a spec, "correct" has no meaning. This document is what we'd prove the implementation matches.

**Files**: New `SPECIFICATION.md`

**Success**:
- [ ] Document defines syntax (BNF or similar)
- [ ] All typing rules listed with names
- [ ] All reduction rules listed (β, δ, ι, ζ)
- [ ] Conversion rules defined
- [ ] Each rule name appears in code comments
- [ ] A type theorist can read the spec and understand the system

---

### Step 12: ELABORATE PATTERN MATCHING AWAY

**What**: Change pattern matching to elaborate to eliminators (recursors) at elaboration time. Remove `Match` from kernel terms.

**Why**: Pattern matching is 1,282 lines of complex code. Eliminators are the "correct" primitive—simpler, easier to verify. This cuts kernel size by ~40%.

**Files**: `tt-elab.ts` (major changes), `tt-kernel.ts` (remove Match), `tt-pattern-match.ts` (becomes elaboration-only)

**Success**:
- [ ] `TTKTerm` has no `Match` variant
- [ ] Kernel is <600 lines
- [ ] Eliminators (`nat_rec`, `list_rec`, etc.) are the only recursion primitive in kernel
- [ ] Pattern matching still works (via elaboration)
- [ ] All tests pass

---

### CHECKPOINT: High Confidence

After Step 12, you have:
- Terminating type checker (fuel)
- Clean kernel boundary (<600 lines, no external deps)
- Documented typing rules
- Property-tested metatheory
- Type-safe interfaces (branded types, Results)

**This is "high confidence" but not "proven".**

---

### Step 13: FORMAL VERIFICATION (OPTIONAL)

**What**: Rewrite the kernel in Lean 4 or Agda. Prove: substitution lemma, weakening, subject reduction, progress, preservation.

**Why**: Machine-checked proofs are the gold standard. No human error possible. This is what Coq (partially) has with MetaCoq.

**Success**:
- [ ] Kernel exists in Lean 4/Agda (~500 lines)
- [ ] Substitution lemma proven
- [ ] Weakening proven
- [ ] Subject reduction proven
- [ ] Type safety (progress + preservation) proven
- [ ] (Optional) Extract verified code back to TypeScript

---

## Summary: The Path

```
NOW ────────────────────────────────────────────────────────> PROVABLE

Step 1-3:   Safety nets (fuel, boundaries, branding)     [1 day]
Step 4-5:   Documentation & DRY (rules, context)         [2-3 days]
Step 6-7:   Verification groundwork (tests, Results)     [1 week]
Step 8-9:   Code quality (fold, branded indices)         [1 week]
Step 10-11: Kernel extraction (directory, spec)          [2-3 weeks]
Step 12:    Kernel minimization (eliminate Match)        [3-4 weeks]
            ──────────────────────────────────────────────
            HIGH CONFIDENCE ACHIEVED (~2-3 months)

Step 13:    Formal verification                          [6-12 months]
            ──────────────────────────────────────────────
            PROVEN CORRECT
```

---

## 7. Architectural Decision Record

### ADR-1: Should Unification Be in the Kernel?

**Status**: Needs decision

**Context**: Unification is currently in the TCB. It's 1,017 lines. Including it makes the kernel harder to verify.

**Options**:
1. **Keep in kernel**: Necessary for dependent pattern matching
2. **Move to elaboration**: Generate proof terms that kernel verifies
3. **Hybrid**: Simple unification in kernel, complex cases outside

**Recommendation**: Option 3. Keep structural unification (checking that two terms are definitionally equal). Move solving/inference to elaboration, generating explicit proof witnesses.

### ADR-2: Should Pattern Matching Be in the Kernel?

**Status**: Needs decision

**Context**: Pattern matching is 1,282 lines. It's complex and hard to verify.

**Options**:
1. **Keep Match in kernel**: Current approach
2. **Elaborate to eliminators**: Match becomes syntactic sugar for induction principles
3. **Case trees in kernel**: Simpler than full pattern matching

**Recommendation**: Option 2 long-term, Option 3 medium-term. Eliminators are the "correct" kernel primitive. Case trees are a pragmatic intermediate step.

### ADR-3: Merge TT and TTK?

**Status**: Needs decision

**Context**: TT and TTK are nearly identical. The two-layer architecture provides no current benefit.

**Options**:
1. **Merge into one type**: Less code, simpler
2. **Differentiate TT**: Add surface conveniences (implicits, operators)
3. **Simplify TTK**: Remove Match, use eliminators

**Recommendation**: Option 2 or 3. If we want a polished surface language, differentiate TT. If we want a provable kernel, simplify TTK.

---

## 8. Conclusion

### The Good News

- Algorithmic foundation is excellent (De Bruijn, bidirectional, PMWK)
- Core logic appears correct (passes substantial test suite)
- Code is readable and reasonably well-organized

### The Bad News

- Kernel boundary is undefined (4 files, ~4,000 lines)
- No termination guarantees
- No documented typing rules
- No metatheory tests
- Checked/unchecked terms are indistinguishable

### The Path Forward

**To achieve "high confidence but not proven"** (3-4 months):
1. Add fuel to whnf
2. Document typing rules
3. Add metatheory property tests
4. Create CheckedTerm branded type
5. Extract kernel to dedicated directory

**To achieve "provably correct"** (6-12 months additional):
1. Elaborate pattern matching away
2. Rewrite kernel in Lean 4 or Agda
3. Prove fundamental lemmas
4. (Optional) Extract verified kernel to TypeScript

### Final Verdict

**Is the kernel tight enough to prove?** No.

**Could it become tight enough?** Yes, with 3-6 months of focused work.

**Is it worth it?** Depends on goals. For a teaching tool, current state is fine. For a proof assistant people trust with important proofs, verification is essential.

---

## Appendices

### Appendix A: Core Typing Rules

These rules must map 1-1 to code:

```
────────────────────────── SORT
Γ ⊢ Type_i : Type_{i+1}

      Γ(i) = A
────────────────────────── VAR
     Γ ⊢ Var(i) : A

Γ ⊢ A : Type_i    Γ, x:A ⊢ B : Type_j
────────────────────────────────────── PI
     Γ ⊢ Π(x:A).B : Type_{max(i,j)}

       Γ, x:A ⊢ e : B
────────────────────────────────────── LAM
   Γ ⊢ λ(x:A).e : Π(x:A).B

Γ ⊢ f : Π(x:A).B    Γ ⊢ a : A
───────────────────────────── APP
       Γ ⊢ f a : B[a/x]

Γ ⊢ e : A    Γ ⊢ A ≡ B : Type_i
─────────────────────────────── CONV
           Γ ⊢ e : B
```

### Appendix B: Kernel Size Comparison

| System | Language | Kernel LOC | Verified? |
|--------|----------|------------|-----------|
| Coq | OCaml | ~10,000 | Partial (MetaCoq) |
| Lean 4 | C++ | ~15,000 | No |
| Agda | Haskell | ~20,000 | No |
| Mini-TT | Haskell | ~500 | Yes (paper) |
| **LeanUI (current)** | TypeScript | **~4,000** | No |
| **LeanUI (target)** | TypeScript | **~650** | Possible |

### Appendix C: File Dependency Graph (Current)

```
tt-parser.ts
    ↓
tt-core.ts (TT surface)
    ↓
tt-elab.ts
    ↓
tt-kernel.ts ←── imports TPattern (WRONG!)
    ↓
tt-typecheck.ts
    ↓
tt-unify.ts
    ↓
tt-pattern-match.ts
    ↓
ttk-totality-check.ts
ttk-recursion-check.ts
```

### Appendix D: File Dependency Graph (Target)

```
surface/
  tt-parser.ts
  tt-core.ts
      ↓
elaboration/
  tt-elab.ts
  tt-pattern-elab.ts (elaborate Match to eliminators)
  tt-unify.ts (solving/inference)
      ↓
kernel/
  term.ts          # ~100 lines
  subst.ts         # ~100 lines
  whnf.ts          # ~150 lines
  typecheck.ts     # ~200 lines
  conversion.ts    # ~100 lines
  index.ts         # exports only
      ↓
checking/
  totality.ts
  termination.ts
```

### Appendix E: Test Gap Analysis

| Module | Unit Tests | Property Tests | Integration Tests |
|--------|------------|----------------|-------------------|
| tt-kernel.ts | ❌ None | ❌ None | ⚠️ Indirect |
| tt-typecheck.ts | ✅ Yes | ❌ None | ✅ Yes |
| tt-unify.ts | ✅ Yes | ❌ None | ✅ Yes |
| tt-pattern-match.ts | ✅ Yes | ❌ None | ✅ Yes |
| block-checker.ts | ❌ None | ❌ None | ⚠️ Indirect |

**Critical gap**: No property tests for metatheoretic properties anywhere.
