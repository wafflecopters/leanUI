# Named Arguments Implementation Plan

This document outlines the implementation of named arguments (NOT implicit arguments) for LeanUI.

## Overview

Named arguments allow users to explicitly specify which parameter a value corresponds to, regardless of position. This is purely syntactic sugar that gets elaborated away before type checking.

### Example

```
-- Definition with named parameters
id : { A : Type } -> A -> A
id {A} x = x

-- Application with named argument (both equivalent)
id { A := Nat } Zero
id Zero { A := Nat }   -- Same thing - named args can appear anywhere
```

After elaboration, both become:
```
id Nat Zero
```

---

## Part 1: Surface Syntax (TT) Changes

### 1.1 Extend `BinderKind` for Named Parameters

**File**: `src/compiler/surface.ts`

Add a new field to distinguish named binders from regular ones:

```typescript
export type BinderKind =
  | { tag: 'BPiTT'; named?: boolean }    // named: true for { A : Type }
  | { tag: 'BLamTT'; named?: boolean }   // named: true for pattern {A}
  | { tag: 'BLetTT'; defVal: TTerm }

// Alternatively, track named status in the Binder node itself
```

**Decision**: Add `named?: boolean` field to Binder and MultiBinder nodes rather than BinderKind, since this is about syntax presentation not semantic binding:

```typescript
export type TTerm =
  | ...
  | { tag: 'Binder'; name: string; binderKind: BinderKind; domain?: TTerm; body: TTerm; named?: boolean }
  | { tag: 'MultiBinder'; names: string[]; binderKind: BinderKind; domain: TTerm; body: TTerm; named?: boolean }
```

### 1.2 Add Named Argument in Application

**File**: `src/compiler/surface.ts`

For application sites, we need to represent named arguments. Two approaches:

**Option A**: Extend App to include optional name
```typescript
export type TTerm =
  | { tag: 'App'; fn: TTerm; arg: TTerm; argName?: string }  // argName: "A" for { A := ... }
```

**Option B**: Add a new term type for named argument application
```typescript
export type TTerm =
  | { tag: 'NamedApp'; fn: TTerm; name: string; arg: TTerm }  // { name := arg }
```

**Decision**: Option A is simpler and allows mixing named/positional in the same App spine.

### 1.3 Add Named Pattern Syntax

**File**: `src/compiler/surface.ts`

Patterns need to distinguish named patterns like `{A}`:

```typescript
export type TPattern =
  | { tag: 'PVar'; name: string; named?: boolean }   // named: true for {A} syntax
  | { tag: 'PWild'; named?: boolean }                // named: true for {_} syntax
  | { tag: 'PCtor'; name: string; args: TPattern[] }
```

---

## Part 2: Parser Changes

### 2.1 Parse Named Binders in Pi Types

**File**: `src/parser/parser.ts`

Current syntax:
```
(A : Type) -> B       -- positional
(a b : Type) -> B     -- multi-binder positional
```

New syntax:
```
{ A : Type } -> B       -- named single
{ A B : Type } -> B     -- named multi-binder
```

**Changes to `parseParenExpr`**:

Add a new function `parseBraceExpr` (triggered by `LBRACE` token):

```typescript
// In PREFIX_PARSELETS
'LBRACE': (p, _t, ctx, path) => p['parseBraceExpr'](ctx, path),

// New method
private parseBraceExpr(ctx: NameContext, path: IndexPath = []): TTerm {
  this.expect('LBRACE');

  // Collect names until ':'
  const nameTokens: Token[] = [];
  while (this.current().type === 'IDENT' || this.current().type === 'UNDERSCORE') {
    nameTokens.push(this.current());
    this.advance();
  }

  if (nameTokens.length === 0) {
    throw new ParseError('Expected at least one name in named binder', ...);
  }

  this.expect('COLON');
  const type = this.expr(0, ctx);
  this.expect('RBRACE');

  // Must be followed by '->'
  if (this.current().type !== 'ARROW') {
    throw new ParseError('Named binder must be followed by ->', ...);
  }
  this.advance();

  const names = nameTokens.map(t => t.type === 'UNDERSCORE' ? '_' : t.value);

  // Extend context
  let newCtx = ctx;
  for (const name of names) {
    newCtx = [name, ...newCtx];
  }

  const body = this.expr(ARROW_PRECEDENCE, newCtx);

  if (names.length === 1) {
    return mkPiTT(type, body, names[0], /* named */ true);
  } else {
    return {
      tag: 'MultiBinder',
      names,
      binderKind: { tag: 'BPiTT' },
      domain: type,
      body,
      named: true
    };
  }
}
```

### 2.2 Parse Named Arguments in Application

**File**: `src/parser/parser.ts`

New syntax for application:
```
f { A := x }        -- named argument
f a { B := y } c    -- mixed positional and named
```

**Changes to `expr()` method** (in the application loop):

When we see a `LBRACE` token during application parsing:

```typescript
// Inside the application loop in expr()
if (this.current().type === 'LBRACE') {
  // Parse named argument: { name := value }
  this.advance(); // consume '{'

  const nameToken = this.expect('IDENT');
  const argName = nameToken.value;

  this.expect('ASSIGN');  // ':='

  const argValue = this.expr(0, ctx);

  this.expect('RBRACE');

  // Create App with argName
  left = {
    tag: 'App',
    fn: left,
    arg: argValue,
    argName  // This marks it as a named argument
  };
  continue;
}
```

### 2.3 Parse Named Patterns

**File**: `src/parser/parser.ts`

New syntax for patterns:
```
foo {A} x = ...       -- named pattern variable
foo {_} x = ...       -- named wildcard
```

**Changes to pattern parsing**:

```typescript
private parsePattern(ctx: NameContext): { pattern: TPattern; newCtx: NameContext } {
  const token = this.current();

  // Check for named pattern: { name } or { _ }
  if (token.type === 'LBRACE') {
    this.advance();
    const innerToken = this.current();

    if (innerToken.type === 'IDENT') {
      const name = innerToken.value;
      this.advance();
      this.expect('RBRACE');
      return {
        pattern: { tag: 'PVar', name, named: true },
        newCtx: [name, ...ctx]
      };
    } else if (innerToken.type === 'UNDERSCORE') {
      this.advance();
      this.expect('RBRACE');
      return {
        pattern: { tag: 'PWild', named: true },
        newCtx: ctx
      };
    } else {
      throw new ParseError('Expected identifier or _ in named pattern', ...);
    }
  }

  // ... existing pattern parsing logic ...
}
```

---

## Part 3: Elaboration Changes

### 3.1 Build Named-to-Index Map

**File**: `src/compiler/elab.ts`

During elaboration of a signature with named binders, build a map from names to positions:

```typescript
export type NamedArgMap = Map<string, number>;

/**
 * Extract named argument positions from a type (Pi chain).
 * Returns a map from argument name to its 0-based position.
 */
export function extractNamedArgMap(type: TTerm): NamedArgMap {
  const map: NamedArgMap = new Map();
  let index = 0;
  let current = type;

  while (current.tag === 'Binder' && current.binderKind.tag === 'BPiTT') {
    if (current.named && current.name !== '_') {
      map.set(current.name, index);
    }
    index++;
    current = current.body;
  }

  // Handle MultiBinder
  while (current.tag === 'MultiBinder' && current.binderKind.tag === 'BPiTT') {
    if (current.named) {
      for (const name of current.names) {
        if (name !== '_') {
          map.set(name, index);
        }
        index++;
      }
    }
    current = current.body;
  }

  return map;
}
```

### 3.2 Elaborate Named Binders to Positional

**File**: `src/compiler/elab.ts`

Named binders elaborate to regular positional binders in TTK:

```typescript
// In elabToKernel, for Binder case:
case 'Binder': {
  const body = elabToKernel(term.body);

  // The 'named' flag is discarded - TTK doesn't track it
  // The name-to-index map is computed separately from the type

  let binderKind: TTKBinderKind;
  // ... existing logic, unchanged ...

  return {
    tag: 'Binder',
    name: term.name,
    binderKind,
    domain,
    body
    // No 'named' field in TTK
  };
}
```

### 3.3 Elaborate Named Applications to Positional

This is the complex part. When we encounter an App spine with named arguments, we need to:

1. Collect all apps in the spine
2. Look up the function's type to get its named argument map
3. Reorder named arguments to their correct positions
4. Fill in positional arguments in the remaining gaps

**File**: `src/compiler/elab.ts`

```typescript
/**
 * Represents an argument in an application spine.
 */
type SpineArg =
  | { kind: 'positional'; term: TTerm }
  | { kind: 'named'; name: string; term: TTerm };

/**
 * Collect an application spine from nested Apps.
 * Returns the function head and list of arguments.
 */
function collectAppSpine(term: TTerm): { head: TTerm; args: SpineArg[] } {
  const args: SpineArg[] = [];
  let current = term;

  while (current.tag === 'App') {
    if (current.argName) {
      args.unshift({ kind: 'named', name: current.argName, term: current.arg });
    } else {
      args.unshift({ kind: 'positional', term: current.arg });
    }
    current = current.fn;
  }

  return { head: current, args };
}

/**
 * Reorder application arguments, placing named args at correct positions.
 *
 * @param args - Mixed list of positional and named arguments
 * @param namedMap - Map from name to position index
 * @returns Ordered list of positional arguments (with possible trailing holes)
 */
function reorderArgs(
  args: SpineArg[],
  namedMap: NamedArgMap
): { ordered: TTerm[]; error?: string } {
  // Separate named and positional
  const named: Array<{ name: string; term: TTerm }> = [];
  const positional: TTerm[] = [];

  for (const arg of args) {
    if (arg.kind === 'named') {
      named.push({ name: arg.name, term: arg.term });
    } else {
      positional.push(arg.term);
    }
  }

  // Determine result size
  const namedIndices = named.map(n => {
    const idx = namedMap.get(n.name);
    if (idx === undefined) {
      return { error: `Unknown named argument: ${n.name}` };
    }
    return { idx, term: n.term };
  });

  // Check for errors
  for (const ni of namedIndices) {
    if ('error' in ni) return { ordered: [], error: ni.error };
  }

  // Find max position needed
  const maxNamedIdx = Math.max(-1, ...namedIndices.map(ni => (ni as any).idx));
  const resultSize = Math.max(maxNamedIdx + 1, positional.length + named.length);

  // Build result array
  const result: (TTerm | null)[] = new Array(resultSize).fill(null);

  // Place named arguments at their positions
  for (const ni of namedIndices) {
    const { idx, term } = ni as { idx: number; term: TTerm };
    if (result[idx] !== null) {
      return { ordered: [], error: `Duplicate argument at position ${idx}` };
    }
    result[idx] = term;
  }

  // Fill positional arguments in gaps from left to right
  let posIdx = 0;
  for (let i = 0; i < result.length && posIdx < positional.length; i++) {
    if (result[i] === null) {
      result[i] = positional[posIdx++];
    }
  }

  // Check for unfilled gaps that precede filled positions
  let lastFilled = -1;
  for (let i = result.length - 1; i >= 0; i--) {
    if (result[i] !== null) {
      lastFilled = i;
      break;
    }
  }

  for (let i = 0; i < lastFilled; i++) {
    if (result[i] === null) {
      return { ordered: [], error: `Missing argument at position ${i}` };
    }
  }

  // Trailing nulls are OK (partial application) - but we stop at lastFilled
  return { ordered: result.slice(0, lastFilled + 1).filter(t => t !== null) as TTerm[] };
}

/**
 * Elaborate an application, handling named arguments.
 */
function elabApp(
  term: TTerm,
  getNamedMap: (name: string) => NamedArgMap | undefined
): TTKTerm {
  // Check if this app spine has any named arguments
  const { head, args } = collectAppSpine(term);

  const hasNamed = args.some(a => a.kind === 'named');

  if (!hasNamed) {
    // Simple case: just elaborate normally
    return elabToKernel(term);
  }

  // We have named arguments - need to reorder
  // First, get the named map for the function
  let namedMap: NamedArgMap | undefined;

  if (head.tag === 'Const') {
    namedMap = getNamedMap(head.name);
  }

  if (!namedMap || namedMap.size === 0) {
    throw new Error(`Cannot use named arguments: ${head.tag === 'Const' ? head.name : 'expression'} has no named parameters`);
  }

  const { ordered, error } = reorderArgs(args, namedMap);
  if (error) {
    throw new Error(error);
  }

  // Build the elaborated application spine
  let result = elabToKernel(head);
  for (const arg of ordered) {
    result = {
      tag: 'App',
      fn: result,
      arg: elabToKernel(arg)
    };
  }

  return result;
}
```

### 3.4 Elaborate Named Patterns to Positional

Similar to applications, patterns with named syntax need reordering.

For a clause like:
```
foo {A} x = ...
```

Where `foo : { A : Type } -> Nat -> Nat`, the patterns need reordering to match the type's parameter order:

```typescript
/**
 * Reorder patterns to match function signature.
 * Named patterns go to their designated positions.
 */
function reorderPatterns(
  patterns: TPattern[],
  namedMap: NamedArgMap
): TPattern[] {
  // Similar logic to reorderArgs but for patterns
  const named: Array<{ name: string; pattern: TPattern }> = [];
  const positional: TPattern[] = [];

  for (const p of patterns) {
    if (p.tag === 'PVar' && p.named) {
      named.push({ name: p.name, pattern: p });
    } else if (p.tag === 'PWild' && p.named) {
      // Named wildcards don't have a name to look up - error?
      throw new Error('Named wildcard {_} cannot be reordered without knowing its parameter name');
    } else {
      positional.push(p);
    }
  }

  // Build result similar to reorderArgs
  // ...
}
```

---

## Part 4: Definition Storage Changes

### 4.1 Extend Definition Types

**File**: `src/compiler/term.ts`

Add the named argument map to definitions:

```typescript
export type TermDefinition = {
  name: string,
  type: TTKTerm,
  value?: TTKTerm,
  namedArgMap?: NamedArgMap,  // New: map from name to position
}

export type InductiveDefinition = {
  name: string,
  type: TTKTerm,
  constructors: Array<{
    name: string;
    type: TTKTerm;
    namedArgMap?: NamedArgMap;  // New: each constructor can have named args
  }>,
  indexPositions: number[],
  namedArgMap?: NamedArgMap,  // New: for the inductive type itself
}
```

### 4.2 Compute Maps During Definition Checking

When a definition is checked, compute its named arg map from its type:

```typescript
// In term.ts or where definitions are added
function addDefinitionWithNamedMap(
  definitions: DefinitionsMap,
  name: string,
  type: TTKTerm,
  surfaceType: TTerm,  // Need surface type to find 'named' markers
  value?: TTKTerm
): DefinitionsMap {
  const namedArgMap = extractNamedArgMap(surfaceType);

  const newMap = new Map(definitions.terms);
  newMap.set(name, {
    name,
    type,
    value,
    namedArgMap: namedArgMap.size > 0 ? namedArgMap : undefined
  });

  return { ...definitions, terms: newMap };
}
```

---

## Part 5: Language Spec Updates

**File**: `language-spec.md`

Add new sections:

```markdown
### Named Parameters in Pi Types

Named parameters allow arguments to be passed by name at call sites:

```
{ A : Type } -> A -> A        -- A is a named parameter
{ A B : Type } -> A -> B      -- Multiple named params with same type
(x : Nat) -> { A : Type } -> A -> x  -- Mix of positional and named
```

### Named Arguments in Applications

Pass arguments by name using `{ name := value }` syntax:

```
id { A := Nat } Zero          -- Pass Nat for A
id Zero { A := Nat }          -- Same thing - order doesn't matter
pair { A := Nat } { B := Bool } Zero True  -- Multiple named args
```

### Named Patterns in Definitions

Match named parameters with `{name}` syntax:

```
foo : { A : Type } -> A -> A
foo {A} x = x

bar : { A B : Type } -> A -> B -> A
bar {A} {B} a b = a
```
```

---

## Part 6: Implementation Order

### Phase 1: Parser Infrastructure
1. Add `named` field to TT types (Binder, MultiBinder, App, TPattern)
2. Update parser to recognize `LBRACE` in binder contexts
3. Implement `parseBraceExpr` for `{ A : Type } ->` syntax
4. Test parsing of named Pi types

### Phase 2: Named Application Parsing
5. Update application parsing to handle `{ name := value }` syntax
6. Test parsing of named argument applications

### Phase 3: Named Pattern Parsing
7. Update pattern parsing for `{name}` syntax
8. Test parsing of named patterns in definitions

### Phase 4: Elaboration Core
9. Implement `extractNamedArgMap` to build name-to-index maps
10. Implement `reorderArgs` for application elaboration
11. Update `elabToKernel` for App case to handle named args

### Phase 5: Definition Integration
12. Extend `TermDefinition` and `InductiveDefinition` with `namedArgMap`
13. Store named maps when definitions are added
14. Make maps accessible during elaboration

### Phase 6: Pattern Elaboration
15. Implement `reorderPatterns` for clause elaboration
16. Update pattern elaboration to use named maps

### Phase 7: Testing & Polish
17. Add comprehensive tests for all named argument scenarios
18. Update error messages for named argument errors
19. Update language spec documentation

---

## Part 7: Future Work - Implicit Arguments

Once named arguments are working, implicit arguments can be added as a natural extension:

### Implicit Argument Syntax

```
-- Implicit parameters (inferred at call site)
id : {A : Type} -> A -> A      -- Same {} syntax, but different semantics

-- Explicit override when needed
@id Nat Zero                   -- @ forces explicit passing
```

### Key Differences from Named Arguments

| Aspect | Named Arguments | Implicit Arguments |
|--------|----------------|-------------------|
| At definition | `{ A : Type } ->` | `{A : Type} ->` (same syntax) |
| At call site | Must pass `{ A := val }` | Inferred, or `@f val` to pass explicitly |
| Elaboration | Reorder only | Insert metavariables |
| Type checking | No inference | Requires unification |

### Implementation Additions Needed

1. **Marker in TTK**: Track which parameters are implicit (not just named)
2. **Meta insertion**: When applying to implicit function, insert metas for missing implicit args
3. **Unification**: Solve the inserted metas through type checking
4. **@ syntax**: Override to pass implicit args explicitly

### Roadmap

1. Named arguments (this document) - purely syntactic sugar
2. Implicit arguments - requires unification infrastructure
3. Instance arguments - like implicit but resolved via typeclass search

The named argument infrastructure (named maps, reordering) will be reused for implicit arguments. The main new work is:
- Deciding which args are implicit vs just named
- Inserting metavariables at application sites
- Propagating solutions back to the metas

---

## Summary

Named arguments are a surface-level feature that gets completely elaborated away:

**Before elaboration:**
```
id : { A : Type } -> A -> A
id {A} x = x
-- Call: id { A := Nat } Zero
```

**After elaboration (TTK):**
```
id : (A : Type) -> A -> A
id A x = x
-- Call: id Nat Zero
```

The key data structure is the `NamedArgMap` which maps parameter names to their positions. This map is:
- Computed from surface types during definition elaboration
- Stored with definitions
- Used during application/pattern elaboration to reorder arguments

No changes to the type checker (term.ts), kernel (kernel.ts), or any verification passes are needed - they only see positional arguments.
