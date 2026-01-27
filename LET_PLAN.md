# Let-Checking Plan

## Background: "Let Should Not Be Generalised"

The famous paper by Vytiniotis, Peyton Jones, et al. (TLDI 2010) argues:

1. **Let-generalisation** (automatically polymorphizing let-bound variables à la ML) imposes **disproportionate complexity** for advanced type systems (GADTs, type families, dependent types)
2. The feature is **rarely used** in practice
3. **Recommendation**: eliminate implicit let-generalisation entirely

For a dependently typed system like ours, this is the obvious choice. Let-bound variables are **monomorphic** — they have exactly the type of their definition. No generalisation, no instantiation machinery, no complexity.

Source: [Let Should Not Be Generalised](https://simon.peytonjones.org/let-generalised/)

---

## Our Let Semantics

```
let x : A := v in body   -- explicit type
let x := v in body       -- inferred type (domain is Hole)
```

- `x` has type `A` (or inferred type of `v`) in `body`
- `x` may be unfolded to `v` during reduction (ζ-reduction)
- **No polymorphism, no generalisation** — just monomorphic type inference

---

## What's Already Done

| Component | Status | Location |
|-----------|--------|----------|
| `TTKBinderKind::BLet` with `defVal` | ✅ | `kernel.ts:47-50` |
| `inBinderLetName/Domain/Value/Body` | ✅ | `term.ts:1507-1557` |
| `isBinderLetTerm` type guard | ✅ | `term.ts:966` |
| ζ-reduction in WHNF | ✅ | `whnf.ts:303-305` |
| Let in substitution | ✅ | `subst.ts:61-66` |
| Let in unification | ✅ | `unify.ts:618-621` |
| Let in zonking | ✅ | `term.ts:801-803` |
| Let in definitional equality | ✅ | `whnf.ts:188-190` |
| `getTermDescription` for let | ✅ | `checker.ts:91` |

---

## What's Missing

One case in `inferBinderType` (checker.ts, after line 175):

```typescript
if (env.isBinderLetTerm()) {
  // ────────────────────────────────────────────────────────────────
  // (LET) - Let binding with optional type inference (no generalisation)
  //
  //   Γ ⊢ A ⇐ Type_i            (type annotation, or Hole→Meta)
  //   Γ ⊢ v ⇐ A                 (value checked against A; solves Meta if inferred)
  //   Γ, x : A ⊢ body ⇒ B       (infer body type in extended context)
  //   ─────────────────────────────────────────────────────────────────
  //   Γ ⊢ let x : A := v in body ⇒ B
  //
  // When A is a Hole, checkType creates a Meta. Checking v against
  // that Meta infers v's type and solves the Meta. No generalisation.
  // ────────────────────────────────────────────────────────────────

  // 1. Check type annotation against Sort (Hole → Meta for inference)
  const { env: env1, sort: domainSort } = env.typeSortFresh();
  const domEnv = checkType(env1.atValueAndPathOfEnv(env).inBinderLetDomain(), domainSort);
  const elaboratedDomain = domEnv.elaboratedTerm ?? env.value.domain;

  // 2. Check value against the (possibly meta) type — this solves inference
  const valEnv = checkType(domEnv.atValueAndPathOfEnv(env).inBinderLetValue(), elaboratedDomain);
  const elaboratedValue = valEnv.elaboratedTerm ?? env.value.binderKind.defVal;

  // 3. Infer body type with x : A in context
  const bodyEnv = inferType(valEnv.atValueAndPathOfEnv(env).inBinderLetBodyWithDomain(elaboratedDomain));

  // 4. Build elaborated let term
  const elaboratedLet: TTKTerm = {
    tag: 'Binder',
    name: env.value.name,
    binderKind: { tag: 'BLet', defVal: elaboratedValue },
    domain: elaboratedDomain,
    body: bodyEnv.elaboratedTerm ?? env.value.body
  };

  // Return body type (the type of the whole let expression)
  return bodyEnv.withValue(bodyEnv.value).withElaboratedTerm(elaboratedLet);
}
```

---

## Minor Addition Needed

Add `inBinderLetBodyWithDomain` method to `TCEnv` (in term.ts), analogous to `inBinderLambdaBodyWithDomain`:

```typescript
inBinderLetBodyWithDomain(
  this: TCEnv<TTKTerm & { tag: 'Binder' } & { binderKind: { tag: 'BLet' } }>,
  domain: TTKTerm
): TCEnv<TTKTerm> {
  return new TCEnv(
    [...this.context, { name: this.value.name, type: domain }],
    this.definitions,
    this.metaVars,
    this.constraints,
    [...this.indexPath, BinderPartSegment.Body],
    [...this.valueStack, this.value],
    this.value.body,
    this.levelMetas
  );
}
```

---

## Summary

| Task | Effort |
|------|--------|
| Add `inBinderLetBodyWithDomain` to TCEnv | ~10 lines |
| Add let case to `inferBinderType` | ~25 lines |
| **Total** | ~35 lines |

The infrastructure does 95% of the work. Type inference comes for free: when `domain` is a Hole, `checkType` converts it to a Meta, and checking the value against that Meta solves it. No special inference logic needed — just the standard bidirectional flow.
