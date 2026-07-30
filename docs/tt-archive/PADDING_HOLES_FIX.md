# Padding Holes Fix: UIP and Constructor Pattern Implicit Arguments

## Summary

Fixed two related issues with constructor patterns that have implicit arguments:

1. **UIP Implicit Argument Conflict** - Constructor patterns with implicit args (like `refl`) caused conflicts when appearing multiple times
2. **Hole Zonking** - Padding holes weren't being properly zonked, appearing as unsolved in output

## Problem 1: UIP Implicit Argument Conflict

### Symptoms
```
uip : {A : Type} -> {x y : A} -> (p q : Equal x y) -> Equal p q
uip refl refl = refl
```

Would fail with:
```
Implicit argument conflict for ?m10:
  inferred (refl 0 ?0 ?2)
  but required to be (refl 0 ?2 ?2)
```

### Root Cause

When constructor patterns have implicit arguments, the pattern matching system pads them with wildcards (prefix `_pad`). Originally, ALL wildcards created pattern variables:

```typescript
// OLD: All wildcards create pattern variables
const { env: newWorkEnv, name } = addMetaVarInTCEnv(env, binderType)
env = newWorkEnv.extendTTKContext(pattern.name, binderType)
env = env.withConstraint({ meta: name, rhs: mkVar(env.context.length - 1) })
elabStack.push(mkVar(env.context.length - 1))
```

This caused each occurrence of `refl` to create SEPARATE pattern variables for its implicit arguments, leading to conflicts during RHS type checking.

### Solution

Detect padding wildcards (starting with `_pad`) and use **Hole terms** instead of pattern variables:

```typescript
// NEW: Padding wildcards use holes that can be shared
const isPaddingWildcard = pattern.name.startsWith('_pad');

if (isPaddingWildcard) {
  const holeId = `${pattern.name}_${env.context.length}`;
  const holeTerm: TTKTerm = { tag: 'Hole', id: holeId };

  env = registerHolesInTermAsMetas(env, holeTerm);
  env = env.extendTTKContext(pattern.name, binderType);
  env = env.withConstraint({ meta: `hole:${holeId}`, rhs: mkVar(env.context.length - 1) });

  elabStack.push(holeTerm)
}
```

**Key insight**: Holes can be filled with unified values during pattern matching, while pattern variables create independent bindings. This allows multiple `refl` patterns to share the same implicit argument values.

## Problem 2: Hole Zonking

### Symptoms

After fixing Problem 1, patterns worked correctly but pretty-printed output showed:
```
refl {A:=?_pad0_3} {a:=?_pad1_4}
```

The holes appeared unsolved even though pattern matching succeeded.

### Root Cause

The `registerHolesInTermAsMetas` function creates TWO meta entries per hole:
- Plain ID: `_pad0_3` (used by zonking)
- Prefixed ID: `hole:_pad0_3` (used by unification/constraints)

When constraints are solved:
1. Unification generates constraints with "hole:" prefix
2. Solution gets stored under the prefixed ID
3. Zonking looks up the plain ID and finds it unsolved

### Solution Part 1: Link Holes to Context Variables

Add a constraint that links the hole to the context variable:

```typescript
env = env.withConstraint({ meta: `hole:${holeId}`, rhs: mkVar(env.context.length - 1) });
```

When the context variable gets unified/substituted during pattern matching, the constraint solver resolves the hole.

### Solution Part 2: Copy Solutions to Plain IDs

Modified `solveConstraints` in `meta.ts` to copy solutions from prefixed IDs to plain IDs:

```typescript
newMetaVars.set(normConstraint.meta, { ...meta, solution: normConstraint.rhs, ctx: effectiveContext });

// If this is a "hole:" prefixed constraint, also copy the solution to the plain ID
if (normConstraint.meta.startsWith('hole:')) {
  const plainId = normConstraint.meta.slice(5);
  const plainMeta = newMetaVars.get(plainId);
  if (plainMeta && !plainMeta.solution) {
    newMetaVars.set(plainId, { ...plainMeta, solution: normConstraint.rhs, ctx: effectiveContext });
  }
}
```

Now zonking finds the solution under the plain ID.

## Files Modified

### `src/compiler/patterns.ts`

**Lines 1178-1197**: Detect padding wildcards and create holes with constraints
```typescript
if (pattern.tag === 'PWild') {
  const isPaddingWildcard = pattern.name.startsWith('_pad');

  if (isPaddingWildcard) {
    // Create hole + constraint linking to context var
    const holeId = `${pattern.name}_${env.context.length}`;
    const holeTerm: TTKTerm = { tag: 'Hole', id: holeId };

    env = registerHolesInTermAsMetas(env, holeTerm);
    env = env.extendTTKContext(pattern.name, binderType);
    env = env.withConstraint({ meta: `hole:${holeId}`, rhs: mkVar(env.context.length - 1) });

    checkStack.push({ type: binderBody, ctxLength: env.context.length })
    elabStack.push(holeTerm)
  } else {
    // User wildcards: original behavior
    ...
  }
}
```

**Lines 1483-1487**: Zonk elaborated patterns before converting to de Bruijn indices
```typescript
// Zonk the elaborated patterns to resolve any padding wildcard holes
const zonkedElabStack = elabStack.map(term => result.zonkTerm(term));

// Convert elabStack to de Bruijn indices
const elabArgs = zonkedElabStack.map(term => levelsToDeBruijn(term, finalContextLength));
```

### `src/compiler/meta.ts`

**Lines 497-506**: Copy solutions from prefixed IDs to plain IDs
```typescript
newMetaVars.set(normConstraint.meta, { ...meta, solution: normConstraint.rhs, ctx: effectiveContext });

// Copy solution to plain ID for holes
if (normConstraint.meta.startsWith('hole:')) {
  const plainId = normConstraint.meta.slice(5);
  const plainMeta = newMetaVars.get(plainId);
  if (plainMeta && !plainMeta.solution) {
    newMetaVars.set(plainId, { ...plainMeta, solution: normConstraint.rhs, ctx: effectiveContext });
  }
}
```

## Test Coverage

### `src/compiler/uip-implicit-conflict.test.ts`

15 systematic test cases covering:
- Single refl patterns (sym, trans)
- Multiple refl patterns on same type
- UIP with and without axiom K
- Different numbers of implicit arguments
- Edge cases with mixed patterns

### Test Results

- ✅ 234/234 tt-runner tests pass
- ✅ 14/14 UIP tests pass (1 skipped)
- ✅ 1424/1424 total tests pass (1 skipped, 2 todo)
- ✅ TypeScript compiles without errors

## Architecture

The fix maintains clean separation of concerns in the type checking pipeline:

```
1. Pattern Parsing → Padding → Pattern Elaboration
   └─ Padding wildcards create holes (not pattern vars)

2. LHS Unification → Constraint Generation
   └─ Context vars get substituted
   └─ Constraints link holes to context vars

3. Constraint Solving
   └─ Constraints for "hole:" prefixed IDs get solved
   └─ Solutions copied to plain IDs

4. Zonking
   └─ Looks up plain IDs and finds solutions
   └─ Replaces holes with their values

5. Pretty Printing
   └─ Shows zonked terms (no unsolved holes)
```

## Why This Works

1. **Holes are placeholders** that get filled during unification, unlike pattern variables which create independent bindings

2. **Constraint linking** ensures that when context variables get unified/substituted, the holes get solved

3. **Solution copying** ensures zonking can find hole solutions under their plain IDs

4. **Multiple occurrences share values** because they reference the same holes, preventing conflicts

## Examples

### UIP (now works with @assumeK)

```
@assumeK

uip : {A : Type} -> {x y : A} -> (p q : Equal x y) -> Equal p q
uip refl refl = refl
```

### Sym (now zonks correctly)

```
sym : {A : Type} -> {u v : A} -> Equal u v -> Equal v u
sym refl = refl

-- Pretty-printed output shows zonked implicit args:
-- (match scrutinee | refl {A:=A} {a:=u} => refl {A:=A} {a:=v})
```

## Related

- See `IMPLICITS-DESIGN.md` for implicit argument handling
- See `ALGORITHMS/pattern-matching.md` for pattern matching details
- Tests in `src/test-programs/pattern-without-k/` for axiom K behavior
