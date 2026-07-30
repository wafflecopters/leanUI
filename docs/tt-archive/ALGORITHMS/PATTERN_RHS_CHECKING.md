# RHS Elaboration: Bidirectional Type Checking with Meta-Variables

## Overview

After LHS elaboration, we have:
- A refined context Γ with all pattern-bound variables and their types
- Solved meta-variables from pattern unification
- The expected return type of the clause

The RHS is then **checked** against the expected return type using standard bidirectional type checking, extended to handle meta-variables (holes).

## Running Example

```tt
nth : (A : Type) -> (n : Nat) -> Vec A n -> Fin n -> A
nth A _ (VCons _ (Succ _) h tail) (FSucc _ f) = nth _ _ tail f
```

**After LHS elaboration:**

```
Γ = [A : Type, n : Nat, h : A, tail : Vec A n, f : Fin n]

Expected return type: A

RHS to elaborate: nth _ _ tail f
```

Note: The LHS metas (_w5, _w6, etc.) are solved — they determined that the second argument is `Succ (Succ n)`, etc. Now we're elaborating the RHS which has its own holes `_`.

---

## Bidirectional Type Checking

Two main judgments:

```
Γ ⊢ e ⇐ T    (check: e has type T)
Γ ⊢ e ⇒ T    (infer: e synthesizes type T)
```

### Mode Selection

- **Infer** for: variables, constants, applications, annotated terms
- **Check** for: lambdas, let-expressions, holes (sometimes)

---

## Core Rules

### Variables (Infer)

```typescript
function inferVar(ctx: Signature, index: number): TTKTerm {
  return ctx[ctx.length - 1 - index].type;
}
```

```
────────────────────── (Var)
Γ, x : T, Γ' ⊢ x ⇒ T
```

### Constants (Infer)

Look up the constant's type in the global signature.

```typescript
function inferConst(name: string, globalSig: GlobalSignature): TTKTerm {
  return globalSig.get(name)!.type;
}
```

### Application (Infer)

```typescript
function inferApp(ctx: Signature, fn: Term, arg: Term, env: WorkEnv): [TTKTerm, TTKTerm, WorkEnv] {
  // Infer function type
  const [fnType, fnElab, env1] = infer(ctx, fn, env);
  
  // fnType should be a Pi type (or a meta that we constrain to be Pi)
  const [dom, cod] = ensurePi(fnType, env1);
  
  // Check argument against domain
  const [argElab, env2] = check(ctx, arg, dom, env1);
  
  // Substitute argument into codomain
  const resultType = subst(0, argElab, cod);
  
  return [resultType, mkApp(fnElab, argElab), env2];
}
```

```
Γ ⊢ f ⇒ (x : A) -> B    Γ ⊢ e ⇐ A
─────────────────────────────────── (App)
       Γ ⊢ f e ⇒ B[x := e]
```

### Lambda (Check)

```typescript
function checkLam(ctx: Signature, name: string, body: Term, expectedType: TTKTerm, env: WorkEnv): [TTKTerm, WorkEnv] {
  // expectedType should be a Pi type
  const [dom, cod] = ensurePi(expectedType, env);
  
  // Extend context with the parameter
  const extCtx = [...ctx, {name, type: dom}];
  
  // Check body against codomain
  const [bodyElab, env1] = check(extCtx, body, cod, env);
  
  return [mkLam(name, dom, bodyElab), env1];
}
```

```
Γ, x : A ⊢ e ⇐ B
─────────────────────────── (Lam)
Γ ⊢ λx. e ⇐ (x : A) -> B
```

### Hole / Meta-Variable (Check)

When we encounter a hole `_` in checking mode:

```typescript
function checkHole(ctx: Signature, expectedType: TTKTerm, env: WorkEnv): [TTKTerm, WorkEnv] {
  // Create a fresh meta-variable
  const metaId = freshMeta(env);
  
  // The meta's telescope is the current context
  const meta: MetaVar = {
    ctx: [...ctx],
    type: expectedType,
    solution: null
  };
  
  env.metaVars.set(metaId, meta);
  
  // Return a meta-application: ?m applied to all context variables
  // This is how we represent "?m in context Γ"
  const metaTerm = mkMetaApp(metaId, ctx.length);
  
  return [metaTerm, env];
}
```

The `mkMetaApp` creates a term like `?m #(n-1) #(n-2) ... #0` — the meta applied to all variables in scope. This is called a "flexible term" and is important for higher-order unification.

For first-order (our case), we can simplify and just record that the meta was created in this context.

### Infer-Check Subsumption

When we infer a type but need to check:

```typescript
function check(ctx: Signature, term: Term, expectedType: TTKTerm, env: WorkEnv): [TTKTerm, WorkEnv] {
  // Try to use checking mode for certain term forms
  if (term.tag === 'Lam') {
    return checkLam(ctx, term.name, term.body, expectedType, env);
  }
  if (term.tag === 'Hole') {
    return checkHole(ctx, expectedType, env);
  }
  
  // Otherwise, infer and unify
  const [inferredType, elab, env1] = infer(ctx, term, env);
  const env2 = unify(ctx, inferredType, expectedType, env1);
  
  return [elab, env2];
}
```

```
Γ ⊢ e ⇒ T'    T' ≡ T
───────────────────── (Sub)
     Γ ⊢ e ⇐ T
```

---

## Unification with Meta-Variables

When we unify two types and one contains a meta:

```typescript
function unify(ctx: Signature, t1: TTKTerm, t2: TTKTerm, env: WorkEnv): WorkEnv {
  // Normalize/reduce both sides first
  const t1n = normalize(t1, env);
  const t2n = normalize(t2, env);
  
  // If either is a meta, try to solve
  if (t1n.tag === 'Meta') {
    return solveMeta(ctx, t1n.id, t2n, env);
  }
  if (t2n.tag === 'Meta') {
    return solveMeta(ctx, t2n.id, t1n, env);
  }
  
  // Otherwise structural unification
  if (t1n.tag === 'Var' && t2n.tag === 'Var') {
    if (t1n.index !== t2n.index) throw new Error('Unification failed');
    return env;
  }
  
  if (t1n.tag === 'App' && t2n.tag === 'App') {
    const env1 = unify(ctx, t1n.fn, t2n.fn, env);
    return unify(ctx, t1n.arg, t2n.arg, env1);
  }
  
  if (t1n.tag === 'Binder' && t2n.tag === 'Binder' && t1n.binderKind.tag === t2n.binderKind.tag) {
    const env1 = unify(ctx, t1n.domain, t2n.domain, env);
    const extCtx = [...ctx, {name: t1n.name, type: t1n.domain}];
    return unify(extCtx, t1n.body, t2n.body, env1);
  }
  
  // ... other cases
  
  throw new Error(`Cannot unify ${t1n} with ${t2n}`);
}
```

### Solving a Meta

```typescript
function solveMeta(ctx: Signature, metaId: string, solution: TTKTerm, env: WorkEnv): WorkEnv {
  const meta = env.metaVars.get(metaId)!;
  
  // Occurs check: solution must not contain metaId
  if (containsMeta(solution, metaId)) {
    throw new Error(`Occurs check failed: ${metaId} in ${solution}`);
  }
  
  // Scope check: solution must only reference variables in meta's telescope
  const maxIdx = maxFreeVarIndex(solution);
  if (maxIdx >= meta.ctx.length) {
    // Can't solve yet — add as constraint
    env.constraints.push({ctx: [...ctx], meta: metaId, rhs: solution});
    return env;
  }
  
  // Solve!
  meta.solution = solution;
  
  // Substitute this solution into all other metas and constraints
  return propagateSolution(metaId, solution, env);
}
```

---

## Trace: Elaborating `nth _ _ tail f`

**Initial state:**
```
Γ = [A : Type, n : Nat, h : A, tail : Vec A n, f : Fin n]
Expected type: A
Term: nth _ _ tail f
```

### Step 1: Infer `nth`

Look up `nth` in global signature:
```
nth : (A : Type) -> (n : Nat) -> Vec A n -> Fin n -> A
```

### Step 2: Apply to first `_`

```
nth _ : ?

Expected domain: Type
Argument: _ (hole)
```

Create meta `?r0` with:
- ctx = [A, n, h, tail, f]
- type = Type
- solution = null

After application:
```
nth ?r0 : (n' : Nat) -> Vec ?r0 n' -> Fin n' -> ?r0
```

### Step 3: Apply to second `_`

```
nth ?r0 _ : ?

Expected domain: Nat
Argument: _ (hole)
```

Create meta `?r1` with:
- ctx = [A, n, h, tail, f]
- type = Nat
- solution = null

After application:
```
nth ?r0 ?r1 : Vec ?r0 ?r1 -> Fin ?r1 -> ?r0
```

### Step 4: Apply to `tail`

```
nth ?r0 ?r1 tail : ?

Expected domain: Vec ?r0 ?r1
Argument: tail
```

Infer type of `tail`: `Vec A n` (from context, index #1)

Unify: `Vec ?r0 ?r1 = Vec A n`
- By injectivity: `?r0 = A` and `?r1 = n`

**Solve ?r0 := A** (which is `#4` in ctx of length 5)
**Solve ?r1 := n** (which is `#3` in ctx of length 5)

After application:
```
nth A n tail : Fin n -> A
```

### Step 5: Apply to `f`

```
nth A n tail f : ?

Expected domain: Fin n
Argument: f
```

Infer type of `f`: `Fin n` (from context, index #0)

Unify: `Fin n = Fin n` ✓

After application:
```
nth A n tail f : A
```

### Step 6: Check against expected type

```
Inferred: A
Expected: A
```

Unify: `A = A` ✓

### Final elaborated RHS:

```
nth A n tail f
```

Where:
- `A` is `#4`
- `n` is `#3`
- `tail` is `#1`
- `f` is `#0`

In de Bruijn indices: `nth #4 #3 #1 #0`

---

## Full Algorithm

```typescript
function elaborateRHS(
  ctx: Signature,           // Context from LHS elaboration
  expectedType: TTKTerm,    // Return type of the clause
  rhs: Term,                // Raw RHS term
  env: WorkEnv              // Metas and constraints from LHS
): [TTKTerm, WorkEnv] {
  
  // Check the RHS against the expected return type
  const [elabRHS, env1] = check(ctx, rhs, expectedType, env);
  
  // Solve any remaining constraints
  const env2 = solveConstraints(env1);
  
  // Check for unsolved metas (error if any)
  for (const [id, meta] of env2.metaVars) {
    if (meta.solution === null) {
      throw new Error(`Unsolved meta-variable: ${id}`);
    }
  }
  
  // Substitute all meta solutions into the elaborated term
  const finalRHS = substituteMetas(elabRHS, env2.metaVars);
  
  return [finalRHS, env2];
}
```

---

## Key Differences from LHS Elaboration

| Aspect | LHS | RHS |
|--------|-----|-----|
| Mode | Pattern matching against type | Type checking expressions |
| Variable binding | Patterns introduce variables | Variables are looked up |
| Holes | Must be determined by pattern structure | Can be inferred from usage |
| Unification source | Constructor return types vs expected types | Inferred types vs expected types |
| Constraint solving | May need re-lifting | Usually solved immediately |

---

## Summary

1. **Start** with context and expected type from LHS elaboration
2. **Check** the RHS against the expected return type
3. **Create metas** for holes in the RHS
4. **Unify** inferred types with expected types during application
5. **Solve metas** when unification determines their values
6. **Substitute** solved metas into the final elaborated term
7. **Error** if any metas remain unsolved