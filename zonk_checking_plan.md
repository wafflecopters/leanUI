# Zonk Recheck: 10 Remaining Failures

## What This Is

We added a `recheckZonkedTerms` flag that, after normal type-checking + zonking, re-checks the zonked term in a **fresh TCEnv** (no metas). If metas are generated or the check fails, it throws. This validates that zonked output is self-consistent.

**Result: 163/173 pass.** 10 fail across two categories.

**Note:** Match values (pattern-match compilation output) are NOT rechecked because the checker has no `Match` case — Match nodes are trusted compilation output.

---

## Category 1: Universe-Level Nodes in Zonked Terms (4 failures)

### The Problem

`USucc`, `UMax`, `UIMax` are represented as `Const` nodes in TTK:

```typescript
// kernel.ts
mkLSucc(level) → App(Const('USucc'), level)
mkLMax(l, r)   → App(App(Const('UMax'), l), r)
```

When `recheckZonkedTerm` creates a fresh env and calls `inferType`, it hits `Const('USucc')` and does `getTypeDefinitionAssert('USucc')` — which fails because these are built-in level constructors, not user-defined terms. They were never added to the definitions map.

### Failing Tests

| Test | Error |
|------|-------|
| `equality-proofs/replace.tt` | `inferType threw: Type definition not found: USucc` |
| `universe-levels/replace0-non-poly.tt` | `'Equal0' expects Type but was applied to Type 1` |
| `universe-check/dpair-single-uvar-fail.tt` | `'DPair3' expects (A -> Type u) but was applied to (A -> Type v)` |
| `records/named-arg-ulevel.tt` | `'DPair' expects (Nat -> Type) but was applied to Type` |

### Fix

The zonked signature contains universe-level expressions (`Sort` containing `App(Const('USucc'), ...)`) that the checker can't handle because `USucc`/`UMax` aren't real definitions.

**Option A**: In `recheckZonkedTerm`, pre-populate the fresh env's definitions with synthetic entries for `USucc`, `UMax`, `UIMax` so `inferType` can look them up. Their types would be `ULevel -> ULevel` and `ULevel -> ULevel -> ULevel`.

**Option B**: Make `inferType` recognize `USucc`/`UMax`/`UIMax` as built-in constants (special case in checker.ts around line 266).

**Option C**: Before rechecking, normalize universe-level expressions inside `Sort` nodes to concrete levels. If the zonked term still has symbolic level expressions (USucc/UMax with level variables), that itself might be the bug — maybe zonking should fully resolve these.

Option A is probably simplest. Option C is worth investigating because if a zonked term still has `USucc(#0)` where `#0` is a level variable, that may indicate incomplete level solving.

### Key Files

- `src/compiler/kernel.ts:250-261` — where USucc/UMax are constructed
- `src/compiler/checker.ts:258-268` — where `inferType` fails on unknown Const
- `src/compiler/compile.ts:recheckZonkedTerm` — where the fresh env is created

---

## Category 2: With-Clause `_scrut0_type` Metas (6 failures)

### The Problem

When a with-clause's scrutinee is a complex expression (not a bare variable), `computeAuxiliaryType` in `with-desugar.ts` creates a placeholder hole for the scrutinee's type:

```typescript
// with-desugar.ts:551, 560
scrutineeTypes.push(mkHoleTT(`_scrut${i}_type`, mkPropTT()));
```

This hole has placeholder type `Prop`. During elaboration it becomes a meta. The meta's universe level (`Sort ?l`) is **not always solved** during type-checking of the auxiliary function. So the zonked signature still contains `_scrut0_type: Sort ?l4`.

The auxiliary functions are processed with `allowUnsolvedSigMetas: true` (compile.ts:3020), which lets the normal pipeline succeed. But the recheck catches it.

### Failing Tests

All are in `with/`:

| Test | Auxiliary | Meta |
|------|-----------|------|
| `with-min-max.tt` | `min-with-32` | `_scrut0_type: Sort ?l4` |
| `with-named-pattern-args.tt` | `apply-with-41` | `_scrut0_type: Sort ?l10` |
| `with-nested-implicit.tt` | `filter-with-50-with-51` | `_scrut0_type: Sort ?l10` |
| `with-frozen-patterns.tt` | `filter-with-63-with-64` | `_scrut0_type: Sort ?l10` |
| `with-on-function-app.tt` | `doubleIsZero-with-74` | `_scrut0_type: Sort ?l2` |
| `with-on-nested-function-app.tt` | `isNonZero-with-77` | `_scrut0_type: Sort ?l2` |

### Fix

The scrutinee's type is known at the call site — it was inferred during the with-desugaring process. Instead of creating a blind `mkHoleTT('_scrut0_type', Prop)`, pass the **actual inferred scrutinee type** into `computeAuxiliaryType`.

Look at `with-desugar.ts` around lines 540-562 where `scrutineeTypes` is built. The scrutinee expressions are available (they're in `withExprs`). Their types should be inferrable from context. If `computeAuxiliaryType` received the inferred types, it could use them directly instead of creating holes.

### Key Files

- `src/compiler/with-desugar.ts:501-562` — `computeAuxiliaryType`, where holes are created
- `src/compiler/with-desugar.ts:240` — where the overall with-desugaring orchestrates
- `src/compiler/compile.ts:3020` — where aux decls are processed with `allowUnsolvedSigMetas: true`

---

## How to Enable and Test

```typescript
// In tt-runner.test.ts line 150:
const results = compileSource(fullSource, { recheckZonkedTerms: true });
```

Run: `npx vitest run src/test-programs/tt-runner.test.ts --reporter=verbose`

The flag threads through: `compileSource` → `compileTTFromText` → `process*Declaration` → `check*Declaration` → recheck points.

Recheck points (in compile.ts and inductive.ts):
- After zonking each constructor type (inductive.ts)
- After zonking a term's signature (compile.ts)
- After zonking a simple (non-match) value (compile.ts)
