# Multi-Variable Binder Syntax Implementation Plan

## Overview

Add support for multi-variable binder syntax in Pi and Lambda expressions (NOT let bindings):

```
-- Lambda with multiple variables of same type
\ (x y : Nat) (z : Bool) => ...
-- Desugars to: \ (x : Nat) => \ (y : Nat) => \ (z : Bool) => ...

-- Pi with multiple variables of same type
foo : (A B : Type) -> (x y : A) -> A
-- Desugars to: (A : Type) -> (B : Type) -> (x : A) -> (y : A) -> A

-- Implicit binders with multiple variables
bar : {A B : Type} -> A -> B -> A
-- Desugars to: {A : Type} -> {B : Type} -> A -> B -> A
```

This is purely a **surface syntax sugar** - the kernel (TTK) always sees single-variable binders.

---

## Implementation Order Context

This feature is part of a larger roadmap. The implementation order is:

1. **Implicit/Named Arguments** (`NAMED_ARGS_PLAN.md`) - First priority
2. **Universe Levels** (`LEVELS_PLAN.md`) - Second priority
3. **Multi-Variable Binders** (this plan) - Third priority
4. **Records** - Fourth priority (plan TBD)

### Why This Order?

- **Implicit args before multi-var**: Multi-variable implicit binders (`{A B : Type}`) require the implicit binder infrastructure to already exist.
- **Multi-var as elaboration step**: The multi-variable expansion happens BEFORE named argument elaboration, allowing `{A B : Type}` to properly expand into separate implicit binders that the named arg system then handles.

---

## Design Decisions

### 1. Surface Syntax Only (TT)

Multi-variable binders exist ONLY in TT (surface syntax). During elaboration, they are "unwound" into chains of single-variable binders BEFORE any other elaboration steps (like named argument resolution).

```
TT: (x y : Nat) -> Body
      ↓ unwind (early elaboration step)
TT: (x : Nat) -> (y : Nat) -> Body
      ↓ full elaboration
TTK: Pi(Nat, Pi(Nat, Body'))
```

### 2. New TT Node: MultiVarBinder

Add a new surface term node to represent multi-variable binders:

```typescript
// In tt-core.ts
export type TTerm =
  // ... existing variants ...
  | {
      tag: 'MultiVarBinder';
      names: string[];           // e.g., ['x', 'y']
      binderKind: BinderKind;    // BPi or BLam (NOT BLet)
      domain: TTerm;             // Shared type for all variables
      body: TTerm;               // Body where all names are bound
    }
```

**Note**: `BLet` is explicitly NOT supported for multi-var binders. Let bindings require individual values:
```
let x = 1
let y = 2
-- NOT: let (x y) = ???
```

### 3. Parser Updates

The parser recognizes multi-name syntax in binder positions:

```
-- Current grammar:
binder ::= '(' name ':' type ')'
         | '{' name ':' type '}'

-- Extended grammar:
binder ::= '(' name+ ':' type ')'   -- one or more names
         | '{' name+ ':' type '}'   -- implicit version
```

When parsing `(x y : Nat)`, if we see multiple identifiers before the colon, produce `MultiVarBinder` instead of `Binder`.

### 4. Elaboration: Unwinding Step

Add an **early elaboration pass** that unwinds `MultiVarBinder` nodes:

```typescript
function unwindMultiVarBinders(term: TTerm): TTerm {
  // Recursively transform the term
  // When we see MultiVarBinder { names: ['x', 'y'], domain, body }:
  // - Create nested Binders: Binder('x', domain, Binder('y', domain', body'))
  // - Note: domain' has De Bruijn indices shifted appropriately
}
```

This pass runs BEFORE:
- Named argument elaboration
- Type checking
- Any other elaboration

After unwinding, the AST contains only regular `Binder` nodes.

---

## Implementation Phases

### Phase 1: Extend TT Types

**Files:** `src/types/tt-core.ts`

1. Add `MultiVarBinder` variant to `TTerm`
2. Add helper constructor:
   ```typescript
   export function mkMultiVarBinder(
     names: string[],
     binderKind: BinderKind,
     domain: TTerm,
     body: TTerm
   ): TTerm
   ```
3. Update `prettyPrint` to handle `MultiVarBinder`

### Phase 2: Parser Updates

**Files:** `src/parser/tt-parser.ts`

1. Modify binder parsing to detect multiple names:
   - After `(` or `{`, collect identifiers until we see `:`
   - If more than one identifier, create `MultiVarBinder`
   - If exactly one identifier, create regular `Binder`

2. Handle both explicit and implicit versions:
   ```
   (x y z : Nat)   → MultiVarBinder(['x','y','z'], BPi, Nat, ...)
   {A B : Type}    → MultiVarBinder(['A','B'], BPi{implicit}, Type, ...)
   \ (a b : Nat) => → MultiVarBinder(['a','b'], BLam, Nat, ...)
   ```

### Phase 3: Elaboration Unwinding

**Files:** `src/types/tt-elab.ts`

1. Create `unwindMultiVarBinders(term: TTerm): TTerm`:
   ```typescript
   function unwindMultiVarBinders(term: TTerm): TTerm {
     switch (term.tag) {
       case 'MultiVarBinder': {
         const { names, binderKind, domain, body } = term;
         // Build chain from right to left
         // (x y : T) -> B becomes (x : T) -> (y : T) -> B
         // Note: De Bruijn indices in domain don't need shifting
         // because domain doesn't reference the bound variables
         let result = unwindMultiVarBinders(body);
         for (let i = names.length - 1; i >= 0; i--) {
           result = {
             tag: 'Binder',
             name: names[i],
             binderKind,
             domain: unwindMultiVarBinders(domain),
             body: result
           };
         }
         return result;
       }
       // ... recurse on other cases ...
     }
   }
   ```

2. Call `unwindMultiVarBinders` as the FIRST step in `elaborate()`:
   ```typescript
   export function elaborate(term: TTerm, ...): TTKTerm {
     // Step 1: Unwind multi-var binders
     const unwound = unwindMultiVarBinders(term);

     // Step 2: Proceed with normal elaboration
     return elaborateUnwound(unwound, ...);
   }
   ```

### Phase 4: Type Query Support

**Files:** `src/types/tt-type-query.ts`, `src/types/tt-source-query.ts`

1. Update source range tracking:
   - `MultiVarBinder` covers the range of all names
   - Each individual name within has its own source range
   - When querying type at cursor position within a name, report that name's type

2. Extend `SourceNode` to track multi-var ranges:
   ```typescript
   // For (x y : Nat), we need to track:
   // - The whole binder: (x y : Nat)
   // - Each name: x at position P1, y at position P2
   // - The type: Nat at position P3
   ```

3. Type at cursor for `x` in `(x y : Nat)` should report `Nat`
4. Type at cursor for `y` in `(x y : Nat)` should report `Nat`

---

## Critical Files

| File | Changes |
|------|---------|
| `src/types/tt-core.ts` | Add `MultiVarBinder` variant |
| `src/parser/tt-parser.ts` | Parse `(x y : T)` and `{x y : T}` |
| `src/types/tt-elab.ts` | Add unwinding pass |
| `src/types/tt-type-query.ts` | Handle multi-var ranges |
| `src/types/tt-source-query.ts` | Track per-name source positions |

---

## Testing Strategy

### Parser Tests

```typescript
// Multiple explicit args
test('parses (x y : Nat)', () => {
  const result = parse('(x y : Nat) -> Nat');
  expect(result).toMatchObject({
    tag: 'MultiVarBinder',
    names: ['x', 'y'],
    binderKind: { tag: 'BPi' },
    // ...
  });
});

// Multiple implicit args
test('parses {A B : Type}', () => {
  const result = parse('{A B : Type} -> A');
  expect(result).toMatchObject({
    tag: 'MultiVarBinder',
    names: ['A', 'B'],
    binderKind: { tag: 'BPi', info: 'implicit' },
    // ...
  });
});

// Lambda with multiple args
test('parses \\ (x y : Nat) => body', () => {
  const result = parse('\\ (x y : Nat) => x');
  expect(result).toMatchObject({
    tag: 'MultiVarBinder',
    names: ['x', 'y'],
    binderKind: { tag: 'BLam' },
    // ...
  });
});

// Mixed
test('parses (A B : Type) -> (x y z : A) -> B', () => {
  // Should parse as nested MultiVarBinders
});
```

### Elaboration Tests

```typescript
test('unwinds (x y : Nat) -> Nat to nested Pi', () => {
  const input = parse('(x y : Nat) -> Nat');
  const unwound = unwindMultiVarBinders(input);

  expect(unwound).toEqual(
    mkPi('Nat', mkPi('Nat', 'Nat', 'y'), 'x')
  );
});

test('unwinds lambda (x y : Nat) => x', () => {
  const input = parse('\\ (x y : Nat) => x');
  const unwound = unwindMultiVarBinders(input);

  // Should become: \ (x : Nat) => \ (y : Nat) => x
  // where x is Var(1) in the body
});

test('unwinds implicit {A B : Type} -> A -> A', () => {
  // After unwinding, should be two separate implicit Pi binders
});
```

### Type Query Tests

```typescript
test('type query on first name in multi-var binder', () => {
  const code = '(x y : Nat) -> Nat';
  //            ^-- cursor here on 'x'
  const type = queryTypeAtPosition(code, /* position of 'x' */);
  expect(type).toBe('Nat');
});

test('type query on second name in multi-var binder', () => {
  const code = '(x y : Nat) -> Nat';
  //               ^-- cursor here on 'y'
  const type = queryTypeAtPosition(code, /* position of 'y' */);
  expect(type).toBe('Nat');
});
```

### Error Cases

```typescript
test('rejects let with multiple names', () => {
  // let (x y) = 1 in ... is not valid
  expect(() => parse('let (x y : Nat) = 1 in x')).toThrow();
});

test('rejects empty name list', () => {
  expect(() => parse('( : Nat) -> Nat')).toThrow();
});
```

---

## De Bruijn Index Considerations

When unwinding `(x y : Nat) -> Body`:

1. The domain `Nat` is evaluated in the OUTER context (before any bindings)
2. In the unwound form `(x : Nat) -> (y : Nat) -> Body`:
   - First `Nat` is in outer context
   - Second `Nat` is in context with `x` bound
   - But `Nat` has no free variables, so no shifting needed

3. If domain references outer variables: `(f : A -> B) -> (x y : A) -> ...`
   - `A` in `(x y : A)` references the outer `A` (before `f` is bound)
   - When unwound: each copy of `A` still references the same position
   - De Bruijn shifting handles this correctly

4. The body's indices:
   - In `(x y : Nat) -> x + y`, the body `x + y` has:
     - `x` as Var(1) (one binder up)
     - `y` as Var(0) (immediately bound)
   - After unwinding, the body is identical (same indices)

---

## Integration with Implicit Arguments

When implicit argument support is implemented (see `NAMED_ARGS_PLAN.md`), the flow becomes:

```
Source: {A B : Type} -> (x : A) -> A

Parse → MultiVarBinder(['A','B'], BPi{implicit}, Type,
          Binder('x', BPi{explicit}, A, A))

Unwind → Binder('A', BPi{implicit}, Type,
           Binder('B', BPi{implicit}, Type,
             Binder('x', BPi{explicit}, A, A)))

Elaborate → TTKPi(Type, TTKPi(Type, TTKPi(A, A)))
            (implicit flags tracked in elaboration context)
```

The key insight: unwinding happens BEFORE implicit argument elaboration, so each variable gets its own implicit binder that the named argument system can then work with.

---

## Execution Order

1. **Phase 1**: Extend TT types - add `MultiVarBinder`
2. **Phase 2**: Parser updates - parse multi-name binders
3. **Phase 3**: Elaboration unwinding - transform to single-var chain
4. **Phase 4**: Type query support - handle source ranges

Run full test suite after EACH phase. Do not proceed if tests fail.

---

## Future Considerations

### Record Fields
When records are implemented, multi-var syntax could extend to record fields:
```
structure Point where
  x y z : Float    -- Three fields of same type
```

This would use the same parsing infrastructure but generate record field declarations instead of binders.

### Pattern Matching
Multi-var patterns are NOT planned:
```
-- NOT supported:
\ (x y) => x + y   -- No type annotation = ambiguous
```

All multi-var binders require explicit type annotation with `:`.
