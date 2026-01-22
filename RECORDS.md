# Records Implementation Plan

This document describes the plan for implementing records (structures) in LeanUI.

## Overview

Records are single-constructor inductive types with named fields and automatic projection functions. They support:
- Optional constructor name (defaults to `Mk#<RecordName>`)
- Dependent fields (each field can reference previous fields)
- Parameters (but not indices)
- Extension/inheritance via `extends` syntax
- Named and implicit arguments for fields
- Eta expansion for equality

## Current State

### Already Implemented

1. **Surface Representation** ([surface.ts:2789-2838](src/compiler/surface.ts#L2789-L2838))
   - `RecordField`, `RecordParam`, `RecordDef` interfaces
   - Helper functions: `mkProjection`, `mkRecordConstructor`, `mkRecordConstructorType`
   - `extends` field for inheritance

2. **Kernel Representation** ([kernel.ts:987-1013](src/compiler/kernel.ts#L987-L1013))
   - `TTKRecordField`, `TTKRecordParam`, `TTKRecordDef` interfaces
   - No `extends` - flattened at elaboration time

3. **Elaboration** ([elab.ts:1384-1535](src/compiler/elab.ts#L1384-L1535))
   - `inlineExtension()` - recursively flattens inherited fields
   - `elabRecordToKernel()` - converts TT to TTK
   - `RecordExtensionError` for clash detection

### Not Yet Implemented

1. **Parsing** - No record syntax in parser
2. **Constructor naming** - Currently hardcoded to `Name.mk`
3. **Namespace system** - Projections need namespace registration
4. **Type checking** - Records need validation
5. **Projection generation** - Need to generate and register projection functions
6. **Eta rule** - For record equality
7. **Implicit/named arguments** - For field types

---

## Design Decisions

### 1. Constructor Name

The constructor can be optionally named:
```
record Point where
  x : Nat
  y : Nat
-- Constructor: Mk#Point : Nat → Nat → Point

record Point where
  constructor MkPoint
  x : Nat
  y : Nat
-- Constructor: MkPoint : Nat → Nat → Point
```

**Surface representation change:**
```typescript
export interface RecordDef {
  name: string;
  constructorName?: string;  // NEW: Optional, defaults to Mk#{name}
  type: TTerm;
  params: RecordParam[];
  fields: RecordField[];
  extends?: string[];
}
```

**Default constructor name:** `Mk#${recordName}` (using `#` to avoid collision with user names)

### 2. Namespace System for Projections

Projections should be registered under the record's namespace to avoid polluting the global namespace.

**Option A: Flat naming with dot notation**
- Register as `Point.x`, `Point.y` in the global `terms` map
- Simple but clutters the global namespace

**Option B: Namespace chain on definitions** (PREFERRED)
```typescript
export type TermDefinition = {
  name: string,
  namespaces: string[],  // NEW: e.g., ['Point'] for Point.x
  type: TTKTerm,
  value?: TTKTerm,
  namedArgMap?: NamedArgMap,
}
```
- Lookup: `Point.x` resolves by searching for name `x` with namespace `['Point']`
- Avoids polluting the flat namespace
- Allows future nested namespaces

**Resolution algorithm:**
1. Parse `Point.x` → prefix `['Point']`, name `x`
2. Look for definition with `name: 'x', namespaces: ['Point']`
3. Fallback: look for definition with `name: 'Point.x'` (for compatibility)

### 3. Field Scoping (Dependent Records)

Each field type is checked in a context where:
- All parameters are bound
- All previous fields are bound

```
record Sigma (A : Type) where
  fst : A
  snd : B fst  -- 'fst' is in scope here
```

**De Bruijn indexing:**
- In field `fst`: `A` is at index 0
- In field `snd`: `fst` is at index 0, `A` is at index 1

**Implementation:** When checking field `i`, extend context with:
- Parameters (indices `i+numParams-1` to `i`)
- Previous fields 0..i-1 (indices `i-1` to `0`)

### 4. Projection Function Generation

For each field, generate a projection function:

```typescript
// Record: Point (A : Type) with x : A, y : A
// Projection for x:
// Point.x : (A : Type) → Point A → A
// Point.x = λ(A : Type) (p : Point A) => match p with | Mk#Point x _ => x
```

**Structure:**
1. Bind all parameters
2. Bind the record instance
3. Match on the single constructor
4. Return the appropriate field

**Registration:** Add to `DefinitionsMap.terms` with namespace chain.

### 5. Extends Mechanism

Already implemented via `inlineExtension()`. Key points:
- Fields from extended records are prepended
- Field name clashes are errors
- Parameters must match (TODO: verify compatibility)

**Parameter compatibility for extends:**
```
record A (X : Type) where ...
record B (Y : Type) extends A where ...  -- Y must unify with X
```

This needs more design work - for now, assume parameter lists must exactly match.

### 6. Eta Rule

Two record values are equal if all their fields are equal:
```
p : Point
q : Point
p = q  iff  p.x = q.x ∧ p.y = q.y
```

**Implementation:** In the unifier/normalizer:
- When comparing two record-typed values, eta-expand to field comparisons
- `p = q` becomes `Mk#Point p.x p.y = Mk#Point q.x q.y`
- Then structurally compare

### 7. Implicit and Named Arguments

Fields can be implicit or explicit, like Pi binders:
```
record Sigma where
  {A : Type}     -- implicit
  fst : A
  snd : B fst
```

**Surface representation change:**
```typescript
export interface RecordField {
  name: string;
  type: TTerm;
  implicit?: boolean;  // NEW: true for implicit fields
}
```

**Constructor type:** Implicit fields become implicit arguments:
```
Mk#Sigma : {A : Type} → (fst : A) → (snd : B fst) → Sigma
```

**Named arguments:** Can use field names as named arguments in constructor calls:
```
Mk#Point (y := 3) (x := 2)  -- reorders to Mk#Point 2 3
```

This reuses existing `namedArgMap` infrastructure.

---

## Implementation Plan

### Phase 1: Parser Support

**File:** [parser.ts](src/parser/parser.ts)

1. Add `RECORD` keyword to tokenizer
2. Add `parseRecordDeclaration()` function:
   ```
   record Name (params) where
     [constructor CtorName]
     field1 : Type1
     field2 : Type2
     ...
   ```
3. Return `ParsedDeclaration` with `kind: 'record'`

**Syntax:**
```
record ::= 'record' NAME params 'where' record-body
params ::= '(' NAME ':' type ')' | '{' NAME ':' type '}'  -- can be empty
record-body ::= constructor-decl? field*
constructor-decl ::= 'constructor' NAME
field ::= NAME ':' type
```

### Phase 2: Surface → Kernel Pipeline

**Files:** [surface.ts](src/compiler/surface.ts), [elab.ts](src/compiler/elab.ts)

1. Add `constructorName` field to `RecordDef`
2. Update `elabRecordToKernel` to handle constructor name
3. Add `TTKRecordDef.constructorName` to kernel representation
4. Update elaboration to default constructor name to `Mk#${name}`

### Phase 3: Namespace System

**File:** [term.ts](src/compiler/term.ts)

1. Add `namespaces: string[]` to `TermDefinition`
2. Update lookup functions to search by namespace chain
3. Add `addDefinitionWithNamespace()` helper
4. Update `createNamedArgLookup` to handle namespaced lookups

### Phase 4: Record Type Checking

**New file:** `src/compiler/record.ts`

Similar to `inductive.ts`:

1. `checkRecordDeclaration()`:
   - Validate record type (must be a valid sort)
   - Check each field type in extended context
   - Verify no unsolved metas
   - Check parameter/extends compatibility

2. Validation steps:
   - Parameters must have valid types
   - Field types must be valid in their context
   - Constructor name must not clash

### Phase 5: Projection Generation

**File:** `src/compiler/record.ts`

1. `generateProjections()`:
   - For each field, generate projection type and body
   - Register in definitions with namespace

2. Projection structure:
   ```typescript
   function generateProjection(
     record: TTKRecordDef,
     fieldIndex: number
   ): { type: TTKTerm, value: TTKTerm }
   ```

### Phase 6: Compilation Integration

**File:** [compile.ts](src/compiler/compile.ts)

1. Add `kind: 'record'` to `ParsedDeclaration`
2. Process records in Phase 2 (alongside inductives)
3. Generate and register:
   - The record type itself (as inductive with one constructor)
   - The constructor
   - All projection functions

### Phase 7: Eta Rule

**Files:** [unify.ts](src/compiler/unify.ts), [normalize.ts](src/compiler/normalize.ts)

1. In unification: when comparing record-typed terms, eta-expand
2. In normalization: recognize record patterns for eta-contraction

### Phase 8: Implicit Fields and Named Args

**Files:** [surface.ts](src/compiler/surface.ts), [elab.ts](src/compiler/elab.ts)

1. Add `implicit` flag to `RecordField`
2. Update constructor type generation for implicit args
3. Generate `namedArgMap` for constructor
4. Parser support for `{field : Type}` syntax

---

## Record as Inductive: Internal Representation

Internally, a record can be represented as an inductive type:

```
record Point where
  x : Nat
  y : Nat

-- Becomes equivalent to:
inductive Point : Type where
| Mk#Point : Nat → Nat → Point
```

The key differences:
1. Fields have names (not just types)
2. Projections are generated automatically
3. Eta rule applies to records

**Option A: Store as separate `recordTypes` map**
```typescript
export type DefinitionsMap = {
  terms: Map<string, TermDefinition>,
  inductiveTypes: Map<string, InductiveDefinition>,
  recordTypes: Map<string, RecordDefinition>,  // NEW
}
```

**Option B: Store records as inductives with extra metadata** (PREFERRED)
```typescript
export type InductiveDefinition = {
  name: string,
  type: TTKTerm,
  constructors: Array<{ name: string; type: TTKTerm; namedArgMap?: NamedArgMap }>,
  indexPositions: number[],
  namedArgMap?: NamedArgMap,
  recordInfo?: RecordInfo,  // NEW: undefined for regular inductives
}

export type RecordInfo = {
  fieldNames: string[],
  projections: string[],  // Names of generated projections
  isEtaExpandable: boolean,
}
```

This approach:
- Reuses existing inductive infrastructure
- Records pattern match the same as inductives
- Extra metadata enables record-specific features (eta, projections)

---

## Example: Full Pipeline

**Input:**
```
record Sigma (A : Type) (B : A → Type) where
  constructor MkSigma
  fst : A
  snd : B fst
```

**Parsed (TT):**
```typescript
{
  kind: 'record',
  name: 'Sigma',
  constructorName: 'MkSigma',
  params: [
    { name: 'A', type: Type_0 },
    { name: 'B', type: Π(A). Type_0 }
  ],
  fields: [
    { name: 'fst', type: Var(1) },  // A is at index 1
    { name: 'snd', type: App(Var(2), Var(0)) }  // B is at 2, fst is at 0
  ]
}
```

**Elaborated (TTK):**
```typescript
// As InductiveDefinition with recordInfo
{
  name: 'Sigma',
  type: Π(A: Type). Π(B: A → Type). Type,
  constructors: [{
    name: 'MkSigma',
    type: Π(A: Type). Π(B: A → Type). Π(fst: A). Π(snd: B fst). Sigma A B
  }],
  indexPositions: [],
  recordInfo: {
    fieldNames: ['fst', 'snd'],
    projections: ['Sigma.fst', 'Sigma.snd'],
    isEtaExpandable: true
  }
}
```

**Generated projections:**
```typescript
// Sigma.fst
{
  name: 'fst',
  namespaces: ['Sigma'],
  type: Π(A: Type). Π(B: A → Type). Sigma A B → A,
  value: λ(A: Type). λ(B: A → Type). λ(s: Sigma A B).
         match s with | MkSigma _ _ fst _ => fst
}

// Sigma.snd
{
  name: 'snd',
  namespaces: ['Sigma'],
  type: Π(A: Type). Π(B: A → Type). Π(s: Sigma A B). B (Sigma.fst A B s),
  value: λ(A: Type). λ(B: A → Type). λ(s: Sigma A B).
         match s with | MkSigma _ _ _ snd => snd
}
```

---

## Open Questions

1. **Parameter compatibility in extends:** How strict should we be? Exact match or unifiable?

2. **Coercion of extended records:** Should `B extends A` allow `B` to be used where `A` is expected?

3. **Multiple inheritance diamond:** If `C extends A, B` and both `A` and `B` extend `D`, what happens to `D`'s fields?

4. **Record update syntax:** Should we support `{ p with x := 5 }`?

5. **Recursive records:** Can a record's field reference the record itself? (Probably yes, via `Const`)

6. **Universe polymorphism:** How do record parameters interact with universe levels?

---

## Testing Plan

1. **Parser tests:**
   - Basic record parsing
   - Records with parameters
   - Records with explicit constructor name
   - Implicit field syntax

2. **Elaboration tests:**
   - Extension inlining (already exists)
   - Constructor type generation
   - Projection type generation

3. **Type checking tests:**
   - Valid record definitions
   - Invalid field types
   - Parameter scope in fields

4. **Projection tests:**
   - Projection applies correctly
   - Projection types are correct
   - Projections work with eta

5. **Eta tests:**
   - Two records equal if fields equal
   - Eta expansion in unification

6. **Integration tests:**
   - Sigma type
   - Algebraic structures (Monoid, Group, etc.)
   - Nested records
   - Records extending other records
