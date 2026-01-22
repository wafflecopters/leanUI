# Implicit Argument Elaboration

## Overview

This document describes how to elaborate implicit and named arguments, informed by how Agda, Lean 4, and Idris 2 handle these features.

The key insight: **implicit argument insertion is bidirectional**. The decision of *when* and *how many* implicits to insert depends on both the term being elaborated and the expected type (if any).

---

## Key Concepts from Real Systems

### Agda

1. **Eager insertion in LHS patterns**: Implicit arguments are inserted eagerly on the left-hand side of definitions. `f = e` and `f {x} {y} = e` are equivalent when `f : {A} -> {B} -> ...`.

2. **Trailing insertion in RHS when type is known**: Implicit arguments are inserted at the end of an application *if required by the expected type*.
   ```agda
   y1 : a == b → C a → C b
   y1 = subst C              -- {_} {_} inserted to match expected type
   ```

3. **No insertion without type signature**: If there's no expected type, trailing implicits are not inserted.
   ```agda
   y5 = subst C              -- only A argument inserted (before explicit C)
   ```

4. **`@` suppresses insertion**: `@f` gives explicit access to all arguments.

### Lean 4

1. **Regular implicits `{x : A}`**: A `_` placeholder is inserted whenever all parameters *before* it have been specified.

2. **Strict implicits `⦃x : A⦄` or `{{x : A}}`**: No placeholder inserted until at least one *subsequent* explicit parameter is provided.
   ```lean
   -- h : ∀ ⦃x : A⦄, x ∈ s → p x
   h        -- no insertion, h : ∀ ⦃x : A⦄, x ∈ s → p x
   h hs     -- insertion happens, result : p y
   ```

3. **`@` makes all arguments explicit**: `@f` disables implicit insertion entirely.

4. **Implicit lambda insertion**: When the expected type is `{A} -> B`, Lean automatically wraps the term in `fun {a} => ...`.

### Idris 2

1. **Implicits not added after non-given explicits**: On the LHS, implicit arguments are only inserted up to the last explicit argument that was provided.

2. **Unbound implicits**: Names starting with lowercase in type signatures are automatically bound as implicit with multiplicity 0 (erased).

3. **Auto implicits `{auto p : T}`**: Solved by proof search, not unification.

---

## Design Principles

Based on the above, here are the principles for a good implicit elaboration system:

### Principle 1: Bidirectional Guidance

- **Check mode** (expected type known): Insert implicits as needed to match the expected type.
- **Infer mode** (no expected type): Insert implicits only up to the first explicit argument encountered.

### Principle 2: The "Boundary" Rule

There's a conceptual boundary in the parameter list. Implicits are inserted:
- **Before the boundary**: Always (these are "leading" implicits)
- **After the boundary**: Only if the expected type demands it

The boundary is determined by:
- In **infer mode**: The last explicitly-provided argument
- In **check mode**: The full arity required by the expected type

### Principle 3: Named Arguments Pin Positions

A named argument `{A = x}` pins the slot for parameter `A`. This affects the boundary — if `A` is at position 5, the boundary is at least 5.

### Principle 4: Strict vs Regular Implicits (Optional)

If you want Lean-style strict implicits:
- Regular `{x}`: Insert when all prior parameters are filled
- Strict `{{x}}`: Insert only when a subsequent explicit is provided

---

## Data Structures

### Parameter Info (stored with each function)

```typescript
type Implicitness =
  | 'explicit'           // (x : A)
  | 'implicit'           // {x : A}
  | 'strictImplicit'     // {{x : A}} (optional feature)
  | 'instance'           // [x : A] (typeclass)
  | 'auto'               // {auto x : A} (proof search)

type ParamInfo = {
  name: string;
  implicitness: Implicitness;
  type: Term;
}

type FunctionInfo = {
  params: ParamInfo[];
  returnType: Term;
}
```

### Surface Syntax Arguments

```typescript
type SurfaceArg =
  | { tag: 'Explicit', value: Term }              // positional: f x
  | { tag: 'ImplicitPositional', value: Term }    // positional implicit: f {x}
  | { tag: 'ImplicitNamed', name: string, value: Term }  // named: f {A = x}
  | { tag: 'InstanceArg', value: Term }           // instance: f [inst]
```

---

## The Elaboration Algorithm

### Entry Point

```typescript
function elaborateApp(
  head: string,
  args: SurfaceArg[],
  expectedType: Term | null,   // null = infer mode
  mode: 'pattern' | 'term'
): { elaboratedArgs: Term[], resultType: Term } {

  const fnInfo = lookupFunctionInfo(head);
  const params = fnInfo.params;
  const arity = params.length;

  // Step 1: Create slots
  const slots: (Term | null)[] = new Array(arity).fill(null);

  // Step 2: Place named arguments
  placeNamedArgs(args, params, slots);

  // Step 3: Place positional arguments
  placePositionalArgs(args, params, slots);

  // Step 4: Determine the boundary
  const boundary = computeBoundary(slots, params, expectedType, mode);

  // Step 5: Fill implicit slots up to boundary
  fillImplicits(slots, params, boundary);

  // Step 6: Check for errors
  checkMissingExplicits(slots, params, boundary);

  // Step 7: Build result
  return buildResult(slots, params, boundary, fnInfo);
}
```

### Step 2: Place Named Arguments

```typescript
function placeNamedArgs(
  args: SurfaceArg[],
  params: ParamInfo[],
  slots: (Term | null)[]
): void {
  for (const arg of args) {
    if (arg.tag === 'ImplicitNamed') {
      const idx = params.findIndex(p => p.name === arg.name);
      if (idx === -1) {
        throw new Error(`Unknown parameter: ${arg.name}`);
      }
      if (slots[idx] !== null) {
        throw new Error(`Parameter ${arg.name} already filled`);
      }
      slots[idx] = arg.value;
    }
  }
}
```

### Step 3: Place Positional Arguments

```typescript
function placePositionalArgs(
  args: SurfaceArg[],
  params: ParamInfo[],
  slots: (Term | null)[]
): void {
  // Separate explicit and implicit positional args
  const explicitArgs = args.filter(a => a.tag === 'Explicit');
  const implicitArgs = args.filter(a => a.tag === 'ImplicitPositional');

  // Place explicit args in explicit slots (left to right)
  let explicitIdx = 0;
  for (let i = 0; i < params.length && explicitIdx < explicitArgs.length; i++) {
    if (params[i].implicitness === 'explicit' && slots[i] === null) {
      slots[i] = explicitArgs[explicitIdx].value;
      explicitIdx++;
    }
  }

  if (explicitIdx < explicitArgs.length) {
    throw new Error('Too many explicit arguments');
  }

  // Place implicit positional args in implicit slots (left to right)
  let implicitIdx = 0;
  for (let i = 0; i < params.length && implicitIdx < implicitArgs.length; i++) {
    if (params[i].implicitness === 'implicit' && slots[i] === null) {
      slots[i] = implicitArgs[implicitIdx].value;
      implicitIdx++;
    }
  }

  if (implicitIdx < implicitArgs.length) {
    throw new Error('Too many implicit positional arguments');
  }
}
```

### Step 4: Compute the Boundary

This is the crucial step that differs between systems.

```typescript
function computeBoundary(
  slots: (Term | null)[],
  params: ParamInfo[],
  expectedType: Term | null,
  mode: 'pattern' | 'term'
): number {
  // For patterns: always full arity
  if (mode === 'pattern') {
    return params.length;
  }

  // Find the rightmost filled slot
  let rightmostFilled = -1;
  for (let i = params.length - 1; i >= 0; i--) {
    if (slots[i] !== null) {
      rightmostFilled = i;
      break;
    }
  }

  // In infer mode: boundary is just after rightmost filled
  if (expectedType === null) {
    return rightmostFilled + 1;
  }

  // In check mode: boundary extends to match expected type
  // Count how many arguments the expected type consumes
  const expectedArity = countPiArgs(expectedType);
  const neededArity = params.length - expectedArity;

  // Boundary is the max of what we have and what we need
  return Math.max(rightmostFilled + 1, neededArity);
}

function countPiArgs(type: Term): number {
  let count = 0;
  while (type.tag === 'Pi') {
    count++;
    type = type.body;
  }
  return count;
}
```

### Step 5: Fill Implicit Slots

```typescript
function fillImplicits(
  slots: (Term | null)[],
  params: ParamInfo[],
  boundary: number
): void {
  for (let i = 0; i < boundary; i++) {
    if (slots[i] === null && params[i].implicitness !== 'explicit') {
      slots[i] = freshMeta(params[i].type);
    }
  }
}
```

### Step 6: Check for Missing Explicits

```typescript
function checkMissingExplicits(
  slots: (Term | null)[],
  params: ParamInfo[],
  boundary: number
): void {
  for (let i = 0; i < boundary; i++) {
    if (slots[i] === null && params[i].implicitness === 'explicit') {
      throw new Error(`Missing explicit argument for ${params[i].name}`);
    }
  }
}
```

### Step 7: Build Result

```typescript
function buildResult(
  slots: (Term | null)[],
  params: ParamInfo[],
  boundary: number,
  fnInfo: FunctionInfo
): { elaboratedArgs: Term[], resultType: Term } {
  const elaboratedArgs: Term[] = [];
  let resultType = fnInfo.returnType;

  for (let i = 0; i < boundary; i++) {
    elaboratedArgs.push(slots[i]!);
    // Substitute the arg into the result type
    resultType = subst(0, slots[i]!, resultType);
  }

  // If boundary < arity, resultType is still a function type
  return { elaboratedArgs, resultType };
}
```

---

## Examples

### Example 1: Infer mode, partial application

```tt
map : {A : Type} -> {B : Type} -> (A -> B) -> List A -> List B
```

User writes: `map f`

- Named args: none
- Positional explicit: `f` fills slot 2
- Rightmost filled: 2
- Boundary (infer mode): 3
- Fill implicits: slots 0, 1 get metas
- Result: `map ?A ?B f : List ?A -> List ?B`

### Example 2: Check mode, full application

```tt
map : {A : Type} -> {B : Type} -> (A -> B) -> List A -> List B
```

User writes: `map f` with expected type `List Nat -> List Bool`

- Named args: none
- Positional explicit: `f` fills slot 2
- Rightmost filled: 2
- Expected type has 1 Pi → need arity 3
- Boundary: max(3, 3) = 3
- Fill implicits: slots 0, 1 get metas
- Unify `List ?A -> List ?B` with `List Nat -> List Bool`
- Solve: ?A = Nat, ?B = Bool
- Result: `map Nat Bool f : List Nat -> List Bool`

### Example 3: Check mode, higher-order

```tt
id : {A : Type} -> A -> A
```

User writes: `id` with expected type `Nat -> Nat`

- No args provided
- Rightmost filled: -1
- Expected type has 1 Pi → need arity 1
- Boundary: 1
- Fill implicits: slot 0 gets meta
- Result type: `?A -> ?A`
- Unify with `Nat -> Nat` → ?A = Nat
- Result: `id Nat : Nat -> Nat`

### Example 4: Named args out of order

```tt
foo : {A : Type} -> (x : Nat) -> {B : Type} -> (y : Bool) -> A
```

User writes: `foo {B = Int} 42 {A = String} true`

- Named args: slot 0 = String, slot 2 = Int
- Positional explicit: slot 1 = 42, slot 3 = true
- Rightmost filled: 3
- Boundary: 4
- All slots filled
- Result: `foo String 42 Int true : String`

### Example 5: Pattern LHS

```tt
foo : {A : Type} -> (x : A) -> {B : Type} -> B -> A
foo x y = x
```

- Mode = pattern, so boundary = 4 (full arity)
- Positional explicit: slot 1 = x, slot 3 = y
- Fill implicits: slot 0, slot 2 get hole patterns
- Elaborated: `foo {_A} x {_B} y = x`

### Example 6: Strict implicits (Lean-style)

```tt
h : {{x : A}} -> x ∈ s -> p x
```

User writes: `h` (no args)

- With strict implicits: no explicit arg provided after `x`
- Boundary: 0 (don't insert the strict implicit)
- Result: `h : {{x : A}} -> x ∈ s -> p x` (no change)

User writes: `h proof`

- Positional explicit: slot 1 = proof
- Now there's an explicit after the strict implicit
- Boundary: 2
- Fill slot 0 with meta
- Result: `h ?x proof : p ?x`

---

## Pattern LHS vs Term RHS

| Aspect | Pattern LHS | Term RHS |
|--------|-------------|----------|
| Boundary | Always full arity | Determined by args + expected type |
| Unfilled implicits | Become hole patterns `_` | Become metas `?m` |
| Unfilled explicits | Error | Error (within boundary) or partial application |
| Expected type | From function signature | From context |

---

## Interaction with Type Checking

The elaboration of applications is interleaved with type checking:

1. **Look up head type**
2. **Elaborate arguments** (may create metas)
3. **Compute result type** by substituting elaborated args into function type
4. **If in check mode**: Unify result type with expected type (may solve metas)
5. **If metas remain unsolved**: They may be solved later by other constraints

This interleaving is crucial — the expected type guides how many implicits to insert, and unification with the expected type solves the inserted metas.

---

## Summary

1. **Named args**: Place in their designated slots
2. **Positional explicit args**: Fill explicit slots left-to-right
3. **Positional implicit args**: Fill implicit slots left-to-right
4. **Compute boundary**:
   - Patterns: full arity
   - Infer mode: rightmost filled + 1
   - Check mode: max(rightmost filled + 1, arity - expected Pi count)
5. **Fill implicits**: Insert metas/holes up to boundary
6. **Check explicits**: Error if explicit slots within boundary are empty
7. **Build result**: Arguments up to boundary, with partially-applied type

The bidirectional nature (using expected type to guide insertion) is what makes implicit arguments practical — without it, you'd need explicit `@` everywhere or aggressive insertion that breaks partial application.
