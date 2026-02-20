# Pattern Unification Plan

## 1. Background: Why We Need This

### The Motivating Example

Our PeanoNat proofs require explicit motive annotations:

```
pzrP : (N : PeanoNat) -> PeanoNat.carrier N -> Type
pzrP N n = Equal (plus N n (PeanoNat.zero N)) n

plusZeroRight N = (PeanoNat.ind N {P := pzrP N}
  (plusZeroEq N (PeanoNat.zero N))
  (\ih => trans (plusSuccEq N _ (PeanoNat.zero N)) (cong (PeanoNat.succ N) ih)))
```

Without `{P := pzrP N}`, the elaborator encounters:

```
?P n = Equal (plus N n (PeanoNat.zero N)) n
```

where `?P` is applied to bound variable `n`. This is a **higher-order unification** problem. Our current system can't solve it — it uses a constant-function heuristic that ignores all arguments:

```
?P n = t  →  ?P := \_ => t    (only works when n ∉ FV(t))
```

But here `n` DOES appear in `t`, so the constant-function heuristic produces a wrong solution (or the constraint gets stuck).

The correct solution is `?P := \n => Equal (plus N n (PeanoNat.zero N)) n`, which **pattern unification** can compute.

### What Is Pattern Unification?

Miller's pattern fragment (1991) restricts higher-order unification to the case where metavariable arguments are **pairwise distinct bound variables**:

```
?M x₁ x₂ ... xₙ = t     where xᵢ are pairwise distinct bound vars
```

In this fragment:
- Solutions are **unique** (most general unifier exists)
- Solvability is **decidable** in linear time
- The algorithm is simple: **invert** the spine to build a renaming, apply it to `t`

This is the exact fragment used by Lean, Agda, Idris, and Coq for practical type inference. It handles the vast majority of real-world motive inference problems.

## 2. The Algorithm

### Core: Spine Inversion

Given `?M x₁ ... xₙ = t`:

1. **Check spine is pattern**: each xᵢ must be a `Var`, and all must be **pairwise distinct**
2. **Build partial renaming** σ: maps each xᵢ's de Bruijn index to position `i` (its lambda-bound index in the solution)
3. **Apply renaming to `t`**: traverse `t`, replacing each `Var(j)` with `Var(σ(j))`. If any free variable in `t` is NOT in σ's domain → **scope escape error** (no solution exists in this fragment)
4. **Occurs check**: if `?M` appears in `t` → **cyclic** (no solution)
5. **Construct solution**: `?M := λ x₁. λ x₂. ... λ xₙ. σ(t)`

### Worked Example

```
?P n = Equal (plus N n zero) n
```

Here `?P` has 1 argument: `n` (which is `Var(0)` in context `[N, ..., n]`).

- Spine: `[Var(0)]` — a single distinct bound variable ✓
- Partial renaming σ: `{ 0 → 0 }` (Var(0) in the outer context maps to Var(0) under the lambda)
- Apply σ to RHS: `Equal (plus N' n' zero') n'` where primed vars are the renamed versions
  - `n` = Var(0) → σ(0) = 0 ✓
  - `N` = Var(k) for some k > 0 → k not in σ's domain...

Wait — this needs more care. The RHS references `N`, `zero`, `plus`, etc. which are free variables NOT in the spine. These are **constants or outer-scope variables** that exist at a higher level than the lambda binding. The renaming needs to handle this by shifting.

Let me be more precise about the de Bruijn arithmetic:

**Context** (outside the meta application): `[..., N : PeanoNat, n : carrier N]`
- `n` is at index 0
- `N` is at index 1

**The constraint**: `App(Meta(?P), Var(0)) = Equal(App(App(plus, Var(1)), Var(0)), App(zero, Var(1)), Var(0))`

**Spine**: `[Var(0)]` — the argument to `?P` is `n` (Var 0)

**Building the renaming**: The meta `?P` lives in a context `[..., N : PeanoNat]` (one level above `n`). Its solution will be a lambda `\n => body` where `body` is in context `[..., N : PeanoNat, n : carrier N]`.

- Var(0) in spine → position 0 in the lambda. So `n` (Var 0) maps to Var(0) under the lambda.
- Variables in the RHS with index > 0 need to be shifted: since we're wrapping in 1 lambda, outer vars shift up by `numArgs - (original_depth - meta_depth)`. Actually, more precisely:

The standard approach (as in elaboration-zoo):
- The meta `?P` was created in a context of length `L` (the "meta context")
- The spine has `n` args: `x₁...xₙ`
- Build a **partial renaming** `ρ: Lvl → Lvl` mapping each spine arg's level to position 0..n-1
- For the RHS, any variable at level `l`:
  - If `l` is in ρ's domain → rename to `ρ(l)`
  - If `l < L` (in the meta's original context) → it's a free variable of the solution, keep it (but may need shifting)
  - Otherwise → **scope escape**: variable not available to the meta

In our de Bruijn representation, this translates to:
- Spine args at indices `i₁, i₂, ...` (relative to the constraint's context)
- Build renaming: `iⱼ → j` (0-indexed position in the lambda telescope)
- For other free vars: check they're accessible (index in range), shift appropriately

### Practical Implementation Strategy

Rather than fully switching to levels (which would be a large refactor), we can implement pattern unification directly on de Bruijn indices:

```typescript
function tryPatternUnify(
  metaId: string,
  spine: TTKTerm[],     // args applied to the meta
  rhs: TTKTerm,         // the other side of the equation
  metaCtxLength: number // length of meta's creation context
): TTKTerm | null {
  // 1. Check each spine arg is a Var with distinct indices
  const varIndices: number[] = [];
  for (const arg of spine) {
    if (arg.tag !== 'Var') return null;  // not a pattern
    if (varIndices.includes(arg.index)) return null;  // non-linear
    varIndices.push(arg.index);
  }

  // 2. Build renaming: varIndices[j] → j
  //    (under the lambda telescope, position j binds what was varIndices[j])
  const renaming = new Map<number, number>();
  for (let j = 0; j < varIndices.length; j++) {
    renaming.set(varIndices[j], j);
  }

  // 3. Apply renaming to rhs + occurs check
  const numArgs = spine.length;
  const renamed = applyRenaming(rhs, renaming, numArgs, metaId);
  if (renamed === null) return null;  // scope escape or occurs check failure

  // 4. Wrap in lambdas
  let solution = renamed;
  for (let i = numArgs - 1; i >= 0; i--) {
    solution = mkLambda(mkSort(mkULit(0)), solution, `_x${i}`);
  }

  return solution;
}
```

The `applyRenaming` function traverses the term:
- `Var(i)` where `i < numArgs` (bound by lambda) → keep as-is (already correct)
- `Var(i)` where `renaming.has(i)` → `Var(renaming.get(i)!)`
- `Var(i)` where `i` is a free variable not in renaming → **scope escape** → return null
- `Meta(id)` where id === metaId → **occurs check failure** → return null
- Under binders: shift the renaming keys up by 1

Actually, let me reconsider. The de Bruijn indices in the constraint's context and in the meta's context differ. Let me think through this more carefully.

**Key insight**: When we have `App(App(Meta(?M), x₁), x₂) = t` at some context depth `d`, and the meta `?M` was created at context depth `m`:

- The spine args `x₁, x₂` are de Bruijn indices relative to depth `d`
- The RHS `t` has free variables at indices relative to depth `d`
- The solution `?M := \x₁.\x₂. body` needs `body` to have free variables relative to depth `m + numArgs` (the meta's context extended by the lambda binders)

The renaming works as follows:
- Spine arg `Var(i)` at depth `d` → should become `Var(j)` at depth `m + numArgs` where `j` is the lambda binder position
- For a free variable `Var(k)` in `t` at depth `d`:
  - If it's one of the spine vars → rename to the corresponding lambda binder
  - If `k >= d` → it's a free variable above the entire context → needs to be preserved as `Var(k - d + m + numArgs)`
  - If `k < d` and `k` is not a spine var:
    - If `k` corresponds to something in the meta's context (i.e., `k` is accessible from the meta) → preserve with appropriate shift
    - Otherwise → scope escape

**Simpler approach**: Since our metas store their creation context and constraints are normalized to the meta's context depth (via `normalizeConstraintDepth`), by the time we see the constraint in `solveConstraints`, the indices should already be relative to a consistent depth. This means:

After normalization, the constraint `?M x₁ ... xₙ = t` has all indices relative to the meta's context. The spine args are Var indices in that context. The renaming maps those indices to positions 0..n-1 under the lambda telescope.

For a Var(k) in the normalized RHS:
- If k is in the renaming (i.e., k is one of the spine var indices) → Var(renaming[k])
- If k is NOT in the renaming:
  - k must be accessible from the meta's context (k < metaCtxLength)
  - Shift k up by numArgs (since the solution is under numArgs lambdas): Var(k + numArgs)
  - But wait — we also need to account for the fact that the spine vars "consume" certain context positions...

Actually, the simplest correct approach is the **elaboration-zoo style** using explicit shifting:

```
Given ?M x₁ ... xₙ = t  (all indices relative to meta's context of depth L)

Renaming: for each position j (0..n-1), spine arg xⱼ has index iⱼ
  Map: iⱼ → j

For Var(k) in t at depth d (d starts at 0 for the top level, +1 under each binder in t):
  Real index relative to constraint context: k - d (if k >= d, it's a free var)
  If k < d: it's bound within t itself → keep as Var(k) (no renaming needed)
  If k >= d:
    Let freeIdx = k - d  (free variable index in the constraint context)
    If freeIdx is in the renaming → Var(d + renaming[freeIdx])
    If freeIdx < L and freeIdx is NOT any spine var → Var(d + numArgs + freeIdx)
      (shift past the lambda binders, but we need to skip the spine-var positions...)
```

Hmm, this is getting complicated because the spine vars "occupy" some of the original context positions but get remapped. Let me just follow the elaboration-zoo approach directly.

**Elaboration-zoo approach** (using levels instead of de Bruijn):

Actually, I think the cleanest approach for our de Bruijn system is:

1. We have constraint `?M x₁ ... xₙ = t` (normalized to meta context of length `L`)
2. Check spine is pattern: all xᵢ are distinct Vars
3. The solution will be `λ ... λ. body` with `n` lambdas
4. To compute `body`: traverse `t`, and for each free `Var(k)` (relative to the traversal depth):
   - Compute its "context index": `k - depth` (where `depth` is the number of binders we've entered in `t`)
   - Look up in renaming: if it maps to position `j` → `Var(depth + j)`
   - Otherwise: it must be "liftable" into the solution's context. Under the n lambdas, the original context vars are shifted up by n. So → `Var(depth + n + (k - depth))` = `Var(k + n)`

   Wait, but the spine vars are at certain indices in the original context, and in the solution those positions are "replaced" by the lambda binders. So we can't just shift by n — we need to account for the gap.

OK let me think about this differently. The **correct** de Bruijn approach:

The meta `?M` lives in context `Γ` of length `L`. The solution is `\x₁...\xₙ. body` where `body` lives in context `Γ, x₁, ..., xₙ` of length `L + n`.

In the constraint `?M x₁ ... xₙ = t`, all terms are at the same depth (the constraint context, which after normalization is `Γ` itself, length L). The spine args `xᵢ = Var(iᵢ)` where `iᵢ < L`.

To build `body` from `t`:
- Free variables in `t` that are spine vars (`Var(iⱼ)`) get replaced by `Var(n - 1 - j)` (the j-th lambda binder, in de Bruijn where the innermost binder is 0)

Wait, actually the lambda binder order matters. If `?M x₁ x₂ x₃`, then the solution is `\x₁. \x₂. \x₃. body`. In de Bruijn:
- `x₃` is Var(0) inside body
- `x₂` is Var(1) inside body
- `x₁` is Var(2) inside body

And original context variables `Var(k)` that are NOT spine vars become `Var(k + n)` inside body (shifted past all n lambdas).

So the renaming for a free variable `Var(k)` in `t`:
- If `k = iⱼ` (it's the j-th spine arg): → `Var(n - 1 - j)`
- Otherwise: → `Var(k + n)` (shifted past lambdas)
- **Scope check**: `k` must be < L (in the meta's context)

And for bound variables (k that refer to binders within `t` itself), we need to adjust for the traversal depth. When we've entered `d` binders in `t`, a `Var(k)` where `k < d` is locally bound and stays as-is. For `k >= d`, the free index is `k - d`, we apply the renaming above, then add `d` back.

So the complete transformation for `Var(k)` at traversal depth `d`:
- If `k < d`: keep `Var(k)` (locally bound in t)
- If `k >= d`:
  - Let `freeIdx = k - d`
  - If `freeIdx = iⱼ`: → `Var(d + n - 1 - j)`
  - Else if `freeIdx < L`: → `Var(d + n + freeIdx)` ...

  Hmm wait, this isn't right either. The issue is that the original context positions that ARE spine vars get "removed" from the outer context in the solution and replaced by lambda binders. So `Var(k + n)` double-counts.

  Actually, I think I'm overcomplicating this. Let's reconsider.

  The meta's solution is semantically: given arguments `x₁...xₙ`, return `t[x₁/Var(i₁), ..., xₙ/Var(iₙ)]`. In de Bruijn terms, under the n lambdas, the original context Γ is shifted up by n (each Var in Γ gains +n), and the lambda parameters are at indices 0..n-1.

  So for a free variable `Var(freeIdx)` in the constraint RHS:
  - If it's a spine var `iⱼ` → replace with the lambda parameter: `Var(n - 1 - j)`
  - Otherwise → shift it: `Var(freeIdx + n)`

  **This IS correct** because:
  - The lambda parameters occupy indices 0..n-1
  - The original context occupies indices n..n+L-1
  - Var(freeIdx) in the original context becomes Var(freeIdx + n) ✓
  - Spine var iⱼ, instead of being at index iⱼ+n, gets "redirected" to lambda param at n-1-j ✓

  The only subtlety: this means the solution's body references both lambda-bound vars (0..n-1) and context vars (n..n+L-1). Under the n lambdas, the context vars are at shifted positions, which is exactly right.

  **Scope check**: Any free variable in `t` must either be a spine var or must have index < L. Variables with index >= L are out of scope.

  **Occurs check**: `Meta(?M)` must not appear in `t`.

Let me re-express the algorithm cleanly:

```typescript
function applyRenaming(
  term: TTKTerm,
  renaming: Map<number, number>,  // spine var index → lambda position (0 = outermost lambda)
  numArgs: number,                 // number of lambda binders
  metaId: string,                  // for occurs check
  metaCtxLength: number,           // L
  depth: number = 0               // binders entered in term
): TTKTerm | null {
  switch (term.tag) {
    case 'Var': {
      if (term.index < depth) return term;  // locally bound
      const freeIdx = term.index - depth;
      if (renaming.has(freeIdx)) {
        return mkVar(depth + (numArgs - 1 - renaming.get(freeIdx)!));
      }
      if (freeIdx >= metaCtxLength) return null;  // scope escape
      return mkVar(term.index + numArgs);  // = depth + freeIdx + numArgs
    }
    case 'Meta':
      if (term.id === metaId) return null;  // occurs check
      return term;
    case 'App': {
      const fn = applyRenaming(term.fn, renaming, numArgs, metaId, metaCtxLength, depth);
      if (!fn) return null;
      const arg = applyRenaming(term.arg, renaming, numArgs, metaId, metaCtxLength, depth);
      if (!arg) return null;
      return { tag: 'App', fn, arg };
    }
    case 'Binder': {
      const domain = applyRenaming(term.domain, renaming, numArgs, metaId, metaCtxLength, depth);
      if (!domain) return null;
      const body = applyRenaming(term.body, renaming, numArgs, metaId, metaCtxLength, depth + 1);
      if (!body) return null;
      // handle BLet defVal too
      return { ...term, domain, body };
    }
    // ... other cases
  }
}
```

Then the solution is:
```typescript
let solution = renamedBody;
for (let i = numArgs - 1; i >= 0; i--) {
  solution = mkLambda(domainType, solution, `_x${i}`);
}
```

## 3. Where to Integrate

### Location 1: `unifyTerms` in `unify.ts` (FLEX-RIGID section, lines 816-845)

Currently:
```typescript
const metaAppA = extractMetaApp(a);
if (metaAppA) {
  const numArgs = metaAppA.args.length;
  let solution = shiftTerm(b, numArgs, 0);
  for (let i = 0; i < numArgs; i++) {
    solution = mkLambda(mkSort(mkULit(0)), solution, '_');
  }
  return { success: true, ..., metaConstraints: [{ meta: metaAppA.meta, rhs: solution }] };
}
```

**Change to**: Try pattern unification first. If the spine is a valid pattern and renaming succeeds, use that solution. If not (spine has non-Var args, or repeated vars, or scope escape), fall back to the existing constant-function heuristic.

```typescript
const metaAppA = extractMetaApp(a);
if (metaAppA) {
  // Try pattern unification first
  const patternSolution = tryPatternUnify(metaAppA.meta, metaAppA.args, b, options);
  if (patternSolution !== null) {
    return { success: true, ..., metaConstraints: [{ meta: metaAppA.meta, rhs: patternSolution }] };
  }
  // Fall back to constant-function heuristic
  const numArgs = metaAppA.args.length;
  let solution = shiftTerm(b, numArgs, 0);
  // ... existing code ...
}
```

### Location 2: Bare `Meta` handling (lines 437-455)

Currently, bare Metas (not applied to args) just defer as constraints. This is correct — no change needed here (a bare Meta is the 0-arg pattern case, which is just direct assignment).

### Location 3: `solveConstraints` in `meta.ts` (line 746+)

Currently, when a meta has no solution, it tries `canSolveMetaInContext` and assigns directly. For pattern unification, the constraint may come in as `?M = t` (after the flex-rigid code already extracted the solution with lambdas). But we should also handle the case where constraints arrive at `solveConstraints` with meta-applied forms.

Actually, since the flex-rigid section in `unifyTerms` already produces the lambda-wrapped solution, `solveConstraints` should work as-is — it receives `{ meta: "?P", rhs: \n. Equal(...) }` and assigns it.

## 4. Implementation Plan

### Phase 1: Core Pattern Unification (MVP)

**Goal**: Solve `?M x₁ ... xₙ = t` when spine is pairwise distinct bound vars.

Files to modify:
- **`src/compiler/unify.ts`**: Add `tryPatternUnify` and `applyPatternRenaming` functions. Modify FLEX-RIGID section to try pattern unification first, fall back to constant-function.

Implementation:

```typescript
/**
 * Try to solve a flex-rigid equation by pattern unification.
 *
 * Given ?M x₁ ... xₙ = t where each xᵢ is Var(iᵢ) and all iᵢ are
 * pairwise distinct, compute ?M := \x₁...\xₙ. rename(t).
 *
 * Returns the solution term (already wrapped in lambdas), or null if
 * pattern unification doesn't apply (non-pattern spine, scope escape,
 * or occurs check failure).
 */
function tryPatternUnify(
  metaId: string,
  spine: TTKTerm[],
  rhs: TTKTerm,
  _options: UnifyOptions
): TTKTerm | null {
  // 1. Check spine is a pattern: all args must be distinct Vars
  const varIndices: number[] = [];
  for (const arg of spine) {
    // After WHNF, spine args should be Vars for pattern fragment
    if (arg.tag !== 'Var') return null;
    if (varIndices.includes(arg.index)) return null; // non-linear
    varIndices.push(arg.index);
  }

  const numArgs = spine.length;

  // 2. Build renaming: varIndices[j] → j (position in lambda telescope)
  const renaming = new Map<number, number>();
  for (let j = 0; j < numArgs; j++) {
    renaming.set(varIndices[j], j);
  }

  // 3. Apply renaming to rhs with occurs check
  const renamed = applyPatternRenaming(rhs, renaming, numArgs, metaId, 0);
  if (renamed === null) return null;

  // 4. Wrap in lambdas (outermost first)
  let solution = renamed;
  for (let i = numArgs - 1; i >= 0; i--) {
    solution = mkLambda(mkSort(mkULit(0)), solution, '_');
  }

  return solution;
}

/**
 * Apply a pattern renaming to a term.
 *
 * For free variables: spine vars get redirected to lambda parameters,
 * other free vars get shifted past the lambda telescope.
 * Returns null on scope escape or occurs check failure.
 */
function applyPatternRenaming(
  term: TTKTerm,
  renaming: Map<number, number>,
  numArgs: number,
  metaId: string,
  depth: number
): TTKTerm | null {
  switch (term.tag) {
    case 'Var': {
      if (term.index < depth) return term; // locally bound in rhs
      const freeIdx = term.index - depth;
      const lambdaPos = renaming.get(freeIdx);
      if (lambdaPos !== undefined) {
        // Spine var → lambda parameter
        // Lambda params: outermost = numArgs-1, innermost = 0
        return mkVar(depth + numArgs - 1 - lambdaPos);
      }
      // Not a spine var: shift past lambdas
      // This is a free var that stays free in the solution
      return mkVar(term.index + numArgs);
    }

    case 'Meta':
      if (term.id === metaId) return null; // occurs check
      return term; // other metas are fine

    case 'Const':
    case 'Sort':
    case 'Hole':
    case 'ULevel':
    case 'ULit':
    case 'UOmega':
      return term; // no free vars to rename

    case 'App': {
      const fn = applyPatternRenaming(term.fn, renaming, numArgs, metaId, depth);
      if (fn === null) return null;
      const arg = applyPatternRenaming(term.arg, renaming, numArgs, metaId, depth);
      if (arg === null) return null;
      if (fn === term.fn && arg === term.arg) return term;
      return { tag: 'App', fn, arg };
    }

    case 'Binder': {
      const domain = applyPatternRenaming(term.domain, renaming, numArgs, metaId, depth);
      if (domain === null) return null;
      const body = applyPatternRenaming(term.body, renaming, numArgs, metaId, depth + 1);
      if (body === null) return null;
      let binderKind = term.binderKind;
      if (binderKind.tag === 'BLet') {
        const defVal = applyPatternRenaming(binderKind.defVal, renaming, numArgs, metaId, depth);
        if (defVal === null) return null;
        if (defVal !== binderKind.defVal) {
          binderKind = { ...binderKind, defVal };
        }
      }
      if (domain === term.domain && body === term.body && binderKind === term.binderKind) return term;
      return { ...term, domain, body, binderKind };
    }

    case 'Annot': {
      const t = applyPatternRenaming(term.term, renaming, numArgs, metaId, depth);
      if (t === null) return null;
      const ty = applyPatternRenaming(term.type, renaming, numArgs, metaId, depth);
      if (ty === null) return null;
      return { tag: 'Annot', term: t, type: ty };
    }

    case 'Match': {
      const scrutinee = applyPatternRenaming(term.scrutinee, renaming, numArgs, metaId, depth);
      if (scrutinee === null) return null;
      const clauses = [];
      for (const c of term.clauses) {
        // Pattern variables bind, increasing depth
        const patVarCount = countPatternVars(c.patterns);
        const clauseRhs = applyPatternRenaming(c.rhs, renaming, numArgs, metaId, depth + patVarCount);
        if (clauseRhs === null) return null;
        clauses.push({ ...c, rhs: clauseRhs });
      }
      return { tag: 'Match', scrutinee, clauses };
    }
  }
}
```

### Phase 2: Handle Interaction with WHNF

The RHS `t` should be in **WHNF** before pattern unification, which is already the case (unifyTerms calls WHNF on both sides). However, the spine args might not be bare Vars after WHNF — e.g., if a spine arg is `Const("zero")` after δ-reduction. Only bare `Var` args are in the pattern fragment.

**Important**: Our flex-rigid code runs AFTER whnf. So `a` is in WHNF. When `a = App(App(Meta(?P), Var(0)), Var(1))`, extractMetaApp gives spine `[Var(0), Var(1)]` — these are already in WHNF since Vars don't reduce. Good.

### Phase 3: Handle Depth Normalization

**Critical issue**: The constraint equation has indices relative to the current unification context, but the meta was created at a potentially different context depth. The flex-rigid code currently "fixes" this by shifting `b` up by `numArgs` (constant-function heuristic just wraps everything). For pattern unification, we need to be more careful.

Looking at the code:
```typescript
const metaAppA = extractMetaApp(a);
// a is WHNF of lhs
// b is WHNF of rhs
```

Both `a` and `b` are at the same context depth (the unification happens within the type checker at a specific context depth). The meta in `a` was created earlier at a (potentially) shallower depth, but the `Meta(?P)` applied to `Var(0)` means the args are at the CURRENT depth.

When we solve `?P := \x. body`, the body needs to make sense in the meta's original context extended by the lambda binder. The `rhs` (term `b`) has free vars at the current depth. Vars that are spine args get remapped to lambda params. Other free vars need to reference the meta's context.

If the meta's context depth is `L` and the current context depth is `D`:
- Spine args are Var indices at depth D
- Other free vars in `b` at depth D need to be accessible at depth L + numArgs
- A free Var(k) at depth D corresponds to context position D-1-k
- At depth L + numArgs, the same context position is Var(L + numArgs - 1 - (D - 1 - k)) = Var(L + numArgs - D + k)

Hmm, this is complex. But in practice, the `adjustMetaConstraintDepth` function and `normalizeConstraintDepth` handle depth differences. And in `unifyTerms`, both sides are at the same depth.

**Key simplification**: In the flex-rigid case in `unifyTerms`, both `a` (the meta application) and `b` (the rigid term) are at the same depth. The spine args' indices are relative to this shared depth. The pattern unification produces a solution where:
- Lambda params bind the spine vars
- Other free vars keep their original indices, shifted by numArgs

This solution is then stored as a `metaConstraint` and processed by `solveConstraints`. The constraint solver handles depth normalization via `normalizeConstraintDepth`.

**I think the approach in Phase 1 is correct as stated**, because `shiftTerm(b, numArgs, 0)` in the existing constant-function heuristic does exactly the same shift for free variables — it shifts ALL free vars by numArgs. Pattern unification does the same shift for non-spine free vars, and remaps spine vars to lambda params instead.

### Phase 4: Tests

See Section 5 below for the full test plan.

### Phase 5: Extensions (Future)

After the core is working:

1. **Pruning**: When `?M x y = t` and `t` doesn't mention `y`, we can't solve (y is in the spine but not in RHS... wait, that's fine — y just won't be used in the body). Actually pruning is for the case where `?M x (f y) = t` — `f y` is not a bare Var so we're outside the pattern fragment, but we can create `?M' x = ?M x _` that drops the problematic arg. We'll defer this.

2. **Intersection**: When we have `?M x y = ?M y x` (flex-flex with same meta), the solution must ignore both args (or only use the intersection). Defer this.

3. **Non-pattern spine relaxation**: When a spine arg is `Const("something")` or `App(...)`, it's outside the pattern fragment. We could try the constant-function heuristic as fallback (which we already do). Future: partial pattern unification for the Var args, constant for non-Var args.

## 5. Test Plan

### 5.1 Core Pattern Unification Tests

**Test: Basic motive inference (the motivating example)**
```
@test success
@name "Pattern unif: motive inference for ind"
```
Remove `{P := pzrP N}` from `plusZeroRight` and check it still compiles. This is the ultimate test — if this works, pattern unification is solving `?P n = Equal (plus N n zero) n`.

**Test: Identity function motive**
```
-- ?P x = Nat  →  ?P := \_ => Nat  (constant function — should still work)
```

**Test: Projection motive**
```
-- ?P x = x  →  ?P := \x => x  (identity)
```

**Test: Dependent pair motive**
```
-- ?P x = Equal (f x) (g x)  →  ?P := \x => Equal (f x) (g x)
```

### 5.2 Scope and Occurs Check Tests

**Test: Scope escape (should fail or defer)**
```
-- ?M x = y  where y is not in the spine
-- Should fall back to constant-function (which handles this by shifting)
```

Actually, the constant-function heuristic handles scope "escape" by just ignoring the spine entirely. So if pattern unification fails due to scope escape, we fall back to constant-function which may or may not work (it works when the solution genuinely doesn't depend on the spine args).

**Test: Occurs check**
```
-- ?M x = f (?M x)  →  should fail (cyclic)
```

### 5.3 Non-Pattern Spine (Fallback)

**Test: Non-var spine arg falls back to constant-function**
```
-- ?M Zero = Nat  →  pattern unif fails (Zero isn't a Var)
-- Falls back to: ?M := \_ => Nat (constant function)
```

**Test: Repeated spine arg falls back**
```
-- ?M x x = Nat  →  non-linear, falls back to constant-function
```

### 5.4 Realistic Dependent Type Tests

**Test: plusZeroRight without explicit motive**
The big one — can the elaborator infer `P := \n => Equal (plus N n zero) n`?

**Test: Simple `map` function motive**
```
map : {A B : Type} -> (A -> B) -> List A -> List B
-- Internally needs ?P n = List B
```

**Test: Vector length index**
```
-- replicate : {A : Type} -> (n : Nat) -> A -> Vec A n
-- Uses: ?P k = Vec A (Succ k)
```

### 5.5 Edge Cases from the Literature

**Test: Solution must use all spine args**
```
-- ?M x y = Pair x y  →  ?M := \x.\y. Pair x y
```

**Test: Solution uses only some spine args**
```
-- ?M x y = x  →  ?M := \x.\y. x  (y unused but that's fine)
```

**Test: Free variables in solution**
```
-- Given f : Nat -> Nat in context
-- ?M x = f x  →  ?M := \x. f x  (f is free, shifted correctly)
```

**Test: Nested binders in RHS**
```
-- ?M x = \y => Equal x y  →  ?M := \x. \y. Equal x y
```

**Test: Multiple metas in same constraint set**
```
-- ?M x = Succ (?N x)  →  both metas have the same spine pattern
-- Should propagate: solve ?M in terms of ?N, then solve ?N independently
```

## 6. Verification Strategy

1. First, write the tests as `.tt` files
2. Verify they currently fail (or succeed for wrong reasons)
3. Implement `tryPatternUnify` and `applyPatternRenaming`
4. Modify FLEX-RIGID to call `tryPatternUnify` first
5. Run the new tests — should pass
6. Run the FULL test suite — must not regress
7. Try removing `{P := pzrP N}` from the PeanoNat proofs — the ultimate validation
8. `npx tsc --noEmit && npm test`

## 7. Risks and Mitigations

**Risk**: Pattern unification produces solutions that don't type-check.
**Mitigation**: Solutions are stored as metaConstraints and processed by `solveConstraints`, which validates them. Also, the type checker will catch ill-typed solutions during the CONV rule.

**Risk**: Interaction with existing constant-function heuristic — some tests may rely on the current behavior.
**Mitigation**: Pattern unification is strictly MORE PRECISE than constant-function. It agrees with constant-function when the solution genuinely doesn't depend on spine args, and gives correct solutions when it does. The fallback ensures we don't lose any current behavior.

**Risk**: De Bruijn index arithmetic errors.
**Mitigation**: Extensive tests with specific examples. Test the renaming function in isolation with unit tests in `meta.test.ts`.

**Risk**: Performance — pattern unification adds a spine check before every flex-rigid.
**Mitigation**: The spine check is O(n²) in the number of args (checking distinctness), which is negligible for typical arities (< 10).

## 8. References

- Dale Miller. "Unification Under a Mixed Prefix" (1992) — original pattern fragment
- Andreas Abel & Brigitte Pientka. "Higher-Order Dynamic Pattern Unification for Dependent Types and Records" (2011) — extensions with pruning, intersection
- Andras Kovacs. elaboration-zoo 03-holes — minimal implementation reference
- Adam Gundry. "Type Inference, Haskell and Dependent Types" (PhD thesis, 2013) — practical algorithms
- Francesco Mazzoli & Andreas Abel. "Type Checking Through Unification" (2016)
