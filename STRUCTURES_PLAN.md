# Structures (Records) Implementation Plan

## Overview

This plan builds upon the **existing infrastructure** to create a complete, robust Structure/Record implementation. We already have:
- ✅ Type definitions in TT (`RecordDef`) and TTK (`TTKRecordDef`)
- ✅ Elaboration pipeline with `extends` inlining
- ✅ Helper functions for projections and constructors
- ✅ UI component (`RecordEditor`)
- ✅ Example records (Magma, Semigroup, Monoid, Point, Prod)

What we need to add:
- ❌ Parser support
- ❌ Type checking with proper field dependency ordering
- ❌ Block checker integration
- ❌ Type query support for source ranges
- ❌ Projection function generation and scope management
- ❌ Parameter vs index handling
- ❌ Implicit argument support

**Dependencies**: This plan assumes Named Args and Levels are implemented first.

---

## Architecture: Record Pipeline

```
Source Text
     │
     ▼
┌─────────────────────────────────────────────────────────────┐
│ PARSER                                                       │
│  'structure Name {params} extends Parents where fields'      │
│  → RecordDef (TT) with extends, params, fields              │
└─────────────────────────────────────────────────────────────┘
     │
     ▼
┌─────────────────────────────────────────────────────────────┐
│ EXTENSION INLINING (existing: inlineExtension)              │
│  RecordDef with extends → RecordDef without extends         │
│  (copies inherited fields, validates no clashes)            │
└─────────────────────────────────────────────────────────────┘
     │
     ▼
┌─────────────────────────────────────────────────────────────┐
│ ELABORATION TO KERNEL (existing: elabRecordToKernel)        │
│  RecordDef (TT) → TTKRecordDef (TTK)                        │
│  (elaborates all field types to kernel form)                │
└─────────────────────────────────────────────────────────────┘
     │
     ▼
┌─────────────────────────────────────────────────────────────┐
│ TYPE CHECKING (NEW)                                          │
│  1. Check record type is well-formed (returns Type_u)       │
│  2. Check each field type in growing context                │
│  3. Generate projection functions                           │
│  4. Generate constructor type                               │
└─────────────────────────────────────────────────────────────┘
     │
     ▼
┌─────────────────────────────────────────────────────────────┐
│ SCOPE REGISTRATION                                           │
│  Add to environment:                                        │
│  - RecordName : Type                                        │
│  - RecordName.mk : Constructor type                         │
│  - RecordName.field : Projection type (for each field)      │
└─────────────────────────────────────────────────────────────┘
```

---

## Phase 1: Parser Support

**Files:** `src/parser/tt-parser.ts`, `src/parser/lexer.ts`

### 1.1 Add Tokens

```typescript
// Add to TokenType enum
| 'STRUCTURE'   // 'structure' keyword
| 'EXTENDS'     // 'extends' keyword

// Update keywords map
const keywords: Record<string, TokenType> = {
  // ... existing
  'structure': 'STRUCTURE',
  'extends': 'EXTENDS',
};
```

### 1.2 Update ParsedDeclaration

```typescript
export interface ParsedDeclaration {
  kind: 'def' | 'theorem' | 'axiom' | 'expr' | 'inductive' | 'structure';  // ADD 'structure'
  name?: string;
  type?: TTerm;
  value?: TTerm;
  constructors?: Array<{ name: string; type: TTerm }>;
  // NEW: Structure-specific fields
  params?: Array<{ name: string; type: TTerm; implicit: boolean }>;
  fields?: Array<{ name: string; type: TTerm }>;
  extends?: string[];
}
```

### 1.3 Implement `parseStructureDeclaration()`

```typescript
// Pattern: structure Name (params) extends Parent1, Parent2 where
//            field1 : Type1
//            field2 : Type2

function parseStructureDeclaration(): ParsedDeclaration {
  expect('STRUCTURE');
  const name = expectIdent();

  // Parse optional parameters: (A : Type) {implicit : T}
  const params: RecordParam[] = [];
  while (check('LPAREN') || check('LBRACE')) {
    const implicit = check('LBRACE');
    advance();  // consume ( or {
    const paramName = expectIdent();
    expect('COLON');
    const paramType = parseExpr();
    expect(implicit ? 'RBRACE' : 'RPAREN');
    params.push({ name: paramName, type: paramType, implicit });
  }

  // Parse optional extends clause
  const extendsNames: string[] = [];
  if (match('EXTENDS')) {
    do {
      extendsNames.push(expectIdent());
    } while (match('COMMA'));
  }

  // Expect 'where' keyword
  expect('WHERE');

  // Parse fields (indented block or pipe-separated)
  const fields: RecordField[] = [];
  while (!isAtBlockEnd()) {
    // Optional pipe prefix (like constructors)
    match('PIPE');
    const fieldName = expectIdent();
    expect('COLON');
    const fieldType = parseExpr();
    fields.push({ name: fieldName, type: fieldType });
  }

  return {
    kind: 'structure',
    name,
    params,
    fields,
    extends: extendsNames.length > 0 ? extendsNames : undefined,
  };
}
```

### 1.4 Syntax Examples

```lean
-- Simple structure
structure Point where
  x : Nat
  y : Nat

-- With parameters
structure Pair (A : Type) (B : Type) where
  fst : A
  snd : B

-- With implicit parameters (after Named Args)
structure Magma {A : Type} where
  op : A → A → A

-- With extends
structure Semigroup (A : Type) extends Magma A where
  assoc : (a b c : A) → op a (op b c) = op (op a b) c

-- Multi-level inheritance
structure Monoid (A : Type) extends Semigroup A where
  e : A
  leftId : (a : A) → op e a = a
```

---

## Phase 2: Field Dependency Checking

**Files:** `src/types/tt-typecheck-record.ts` (new), `src/types/tt-typecheck-decl.ts`

### 2.1 The Core Rule

**A field's type can only reference:**
1. Record parameters
2. Fields defined BEFORE it (earlier in the list)
3. Definitions from the global environment

**Example:**
```lean
structure Example (A : Type) where
  x : A                    -- OK: references param A
  y : A                    -- OK: references param A
  z : Equal A x y          -- OK: references param A, earlier fields x, y
  w : Equal A z x          -- ERROR: z is NOT a term of type A, can't use in Equal
```

### 2.2 Implementation: `checkRecordDeclaration()`

```typescript
export function checkRecordDeclaration(
  record: TTKRecordDef,
  env: Environment
): CheckResult<RecordCheckInfo> {
  const errors: CheckError[] = [];

  // 1. Build initial context with record parameters
  let ctx: TTKContext = { bindings: [] };
  for (const param of record.params) {
    // Check parameter type is well-formed
    const paramTypeResult = checkTypeIsType(param.type, ctx, env);
    if (!paramTypeResult.success) {
      errors.push(...paramTypeResult.errors);
    }
    // Add parameter to context
    ctx = extendContext(ctx, param.name, param.type);
  }

  // 2. Check record type is well-formed (should be Type_u for some universe u)
  const recordTypeResult = checkTypeIsType(record.type, ctx, env);
  if (!recordTypeResult.success) {
    errors.push(...recordTypeResult.errors);
  }

  // 3. Add the record type itself to context (for recursive references in fields)
  // Record.mk : (params) → (fields) → Record params
  const selfType = buildRecordType(record);
  ctx = extendContext(ctx, record.name, selfType);

  // 4. Check each field type in growing context
  const fieldTypes: TTKTerm[] = [];
  for (let i = 0; i < record.fields.length; i++) {
    const field = record.fields[i];

    // Check field type is well-formed in current context
    const fieldTypeResult = checkTypeIsType(field.type, ctx, env);
    if (!fieldTypeResult.success) {
      // Error: field type references unavailable binding
      errors.push({
        tag: 'TypeCheckError',
        message: `Field '${field.name}' has invalid type`,
        details: fieldTypeResult.errors,
        path: ['fields', i, 'type'],
      });
    }
    fieldTypes.push(field.type);

    // Add field to context for subsequent fields
    // The field acts like a variable binding: fieldName : fieldType
    ctx = extendContext(ctx, field.name, field.type);
  }

  if (errors.length > 0) {
    return { success: false, errors };
  }

  return {
    success: true,
    value: {
      recordType: selfType,
      constructorType: buildConstructorType(record),
      projectionTypes: buildProjectionTypes(record),
      fieldTypes,
    },
  };
}
```

### 2.3 Error Messages for Dependency Violations

```typescript
// When a field references an unavailable field:
{
  tag: 'UnboundVariable',
  message: `Field 'z' references 'w', but 'w' is defined after 'z'`,
  hint: `Fields can only reference parameters and earlier fields. Consider reordering.`,
  path: ['fields', 2, 'type'],
}

// When a field uses another field incorrectly:
{
  tag: 'TypeMismatch',
  message: `In field 'z': expected type 'A', but 'x' has type 'Nat'`,
  path: ['fields', 2, 'type'],
}
```

---

## Phase 3: Projection Function Generation

**Files:** `src/types/tt-record-projections.ts` (new)

### 3.1 What Projections Do

For each field, we generate a projection function that extracts that field from a record instance:

```lean
structure Point where
  x : Nat
  y : Nat

-- Generates:
Point.x : Point → Nat
Point.y : Point → Nat

-- Implementation (in kernel):
Point.x = λ (p : Point) => p.x   -- or pattern match: Point.x (Point.mk x y) = x
Point.y = λ (p : Point) => p.y
```

### 3.2 Projection Type with Parameters and Dependencies

```lean
structure Sigma (A : Type) (B : A → Type) where
  fst : A
  snd : B fst   -- Note: depends on 'fst'

-- Projection types:
Sigma.fst : {A : Type} → {B : A → Type} → Sigma A B → A
Sigma.snd : {A : Type} → {B : A → Type} → (s : Sigma A B) → B (Sigma.fst s)
--                                         ↑ Named parameter needed for dependency
```

### 3.3 Implementation

```typescript
export function generateProjections(record: TTKRecordDef): ProjectionDef[] {
  const projections: ProjectionDef[] = [];

  for (let i = 0; i < record.fields.length; i++) {
    const field = record.fields[i];

    // Build projection type:
    // {params} → (r : Record params) → field.type[earlier fields ↦ projections]

    let projType: TTKTerm = field.type;

    // Substitute earlier field references with projection applications
    for (let j = i - 1; j >= 0; j--) {
      const earlierField = record.fields[j];
      // Replace reference to earlier field with: Record.earlierField r
      projType = substitute(projType, earlierField.name,
        mkApp(mkConst(`${record.name}.${earlierField.name}`), mkVar('r')));
    }

    // Wrap with Pi for the record argument
    projType = mkPi('r', buildRecordAppliedType(record), projType);

    // Wrap with implicit Pi for each parameter
    for (let p = record.params.length - 1; p >= 0; p--) {
      const param = record.params[p];
      projType = mkPi(param.name, param.type, projType, 'implicit');
    }

    projections.push({
      name: `${record.name}.${field.name}`,
      type: projType,
      fieldIndex: i,
    });
  }

  return projections;
}
```

### 3.4 Putting Projections in Scope

After type-checking a record, register all projections:

```typescript
function registerRecordInEnvironment(
  record: TTKRecordDef,
  checkInfo: RecordCheckInfo,
  env: Environment
): Environment {
  let newEnv = env;

  // Register the record type itself
  newEnv = addToEnvironment(newEnv, record.name, checkInfo.recordType);

  // Register the constructor
  newEnv = addToEnvironment(newEnv, `${record.name}.mk`, checkInfo.constructorType);

  // Register each projection
  for (const proj of checkInfo.projectionTypes) {
    newEnv = addToEnvironment(newEnv, proj.name, proj.type);
  }

  return newEnv;
}
```

---

## Phase 4: Constructor Type Generation

**Files:** `src/types/tt-record-projections.ts`

### 4.1 Constructor Type Structure

```lean
structure Point where
  x : Nat
  y : Nat

-- Constructor:
Point.mk : Nat → Nat → Point

-- With parameters:
structure Pair (A B : Type) where
  fst : A
  snd : B

-- Constructor:
Pair.mk : {A : Type} → {B : Type} → A → B → Pair A B

-- With dependent fields:
structure Sigma (A : Type) (B : A → Type) where
  fst : A
  snd : B fst

-- Constructor:
Sigma.mk : {A : Type} → {B : A → Type} → (fst : A) → B fst → Sigma A B
```

### 4.2 Implementation

```typescript
export function buildConstructorType(record: TTKRecordDef): TTKTerm {
  // Start with return type: Record applied to all params
  let result: TTKTerm = mkConst(record.name);
  for (const param of record.params) {
    result = mkApp(result, mkVar(param.name));
  }

  // Add Pi for each field (right to left to build correct nesting)
  for (let i = record.fields.length - 1; i >= 0; i--) {
    const field = record.fields[i];
    // For dependent fields, the type may reference earlier field names
    // Those names are bound by the Pi binders we're creating
    result = mkPi(field.name, field.type, result, 'explicit');
  }

  // Add implicit Pi for each parameter (right to left)
  for (let i = record.params.length - 1; i >= 0; i--) {
    const param = record.params[i];
    result = mkPi(param.name, param.type, result, 'implicit');
  }

  return result;
}
```

---

## Phase 5: Type Query Support

**Files:** `src/types/tt-type-query.ts`

### 5.1 Requirements

Type queries should work for:
1. Record name → Record type
2. Parameter names → Parameter types
3. Field names → Field types (in context of earlier fields)
4. Constructor → Constructor type
5. Projections → Projection types

### 5.2 Source Range Mapping

During parsing, we need to track source positions for:

```typescript
interface RecordSourceMap {
  name: SourceRange;
  type: SourceRange;
  params: Array<{
    name: SourceRange;
    type: SourceRange;
  }>;
  fields: Array<{
    name: SourceRange;
    type: SourceRange;
  }>;
  extends?: SourceRange[];  // Ranges of extended record names
}
```

### 5.3 Type Query Implementation

```typescript
export function queryRecordTypeAtPosition(
  record: TTKRecordDef,
  sourceMap: RecordSourceMap,
  position: SourcePosition,
  env: Environment
): TypeQueryResult | null {

  // Check if position is in record name
  if (containsPosition(sourceMap.name, position)) {
    return {
      kind: 'type',
      type: buildRecordType(record),
      context: 'Record type',
    };
  }

  // Check parameters
  for (let i = 0; i < record.params.length; i++) {
    const paramMap = sourceMap.params[i];
    if (containsPosition(paramMap.name, position)) {
      return {
        kind: 'binding',
        name: record.params[i].name,
        type: record.params[i].type,
        context: 'Record parameter',
      };
    }
    if (containsPosition(paramMap.type, position)) {
      return queryTypeAtPosition(record.params[i].type, ...);
    }
  }

  // Check fields - build growing context
  let ctx = buildParamContext(record.params);
  for (let i = 0; i < record.fields.length; i++) {
    const field = record.fields[i];
    const fieldMap = sourceMap.fields[i];

    if (containsPosition(fieldMap.name, position)) {
      return {
        kind: 'binding',
        name: field.name,
        type: field.type,
        context: `Record field (depends on: ${getDependencies(field.type, ctx)})`,
      };
    }
    if (containsPosition(fieldMap.type, position)) {
      // Query within the field type expression
      return queryTypeAtPosition(field.type, ctx, position, env);
    }

    // Add field to context for next iteration
    ctx = extendContext(ctx, field.name, field.type);
  }

  return null;
}
```

---

## Phase 6: Parameter vs Index Handling

**Files:** `src/types/tt-record-projections.ts`, `src/types/tt-typecheck-record.ts`

### 6.1 The Distinction

**Parameters** are uniform across all fields:
```lean
structure Pair (A B : Type) where  -- A, B are parameters
  fst : A
  snd : B
-- Pair A B is a type for any fixed A, B
```

**Indices** can vary:
```lean
-- This would be weird for a structure, but illustrates the concept:
-- In practice, records don't have indices (unlike inductive types)
```

For **structures**, all type arguments are **parameters** (not indices). This is a key simplification compared to inductive types.

### 6.2 Implicit Parameters

After Named Args is implemented, parameters can be implicit:

```lean
structure Magma {A : Type} where
  op : A → A → A

-- Usage:
example : Magma {Nat}
example := Magma.mk (· + ·)

-- Or with inference:
example : Magma
example := Magma.mk (· + ·)  -- A inferred from op's type
```

### 6.3 Implementation

```typescript
// In RecordParam, add implicit flag
export interface RecordParam {
  name: string;
  type: TTerm;
  implicit: boolean;  // NEW: whether parameter is implicit
}

// During elaboration, handle implicit params
export function buildConstructorType(record: TTKRecordDef): TTKTerm {
  let result = buildReturnType(record);

  // Add field arguments (always explicit)
  for (let i = record.fields.length - 1; i >= 0; i--) {
    result = mkPi(record.fields[i].name, record.fields[i].type, result, 'explicit');
  }

  // Add parameter arguments (respecting implicit flag)
  for (let i = record.params.length - 1; i >= 0; i--) {
    const param = record.params[i];
    const bindInfo = param.implicit ? 'implicit' : 'explicit';
    result = mkPi(param.name, param.type, result, bindInfo);
  }

  return result;
}
```

---

## Phase 7: Block Checker Integration

**Files:** `src/parser/block-checker.ts`

### 7.1 Update BlockCheckResult

```typescript
export interface BlockCheckResult {
  // ... existing fields

  blockType: 'Inductive' | 'Term' | 'Comment' | 'Unknown' | 'Record';  // ADD 'Record'

  // NEW: Record-specific info
  recordParams?: Array<{
    name: string;
    type: TTerm;
    implicit: boolean;
    sourceRange: SourceRange;
  }>;
  recordFields?: Array<{
    name: string;
    type: TTerm;
    sourceRange: SourceRange;
  }>;
  recordExtends?: string[];
}
```

### 7.2 Integrate into `checkSourceBlocks()`

```typescript
function checkSourceBlocks(source: string, env: Environment): BlockCheckResult[] {
  const blocks = parseSourceBlocks(source);
  const results: BlockCheckResult[] = [];

  for (const block of blocks) {
    const parsed = parseBlock(block);

    if (parsed.kind === 'structure') {
      // Build RecordDef from parsed data
      const recordDef: RecordDef = {
        name: parsed.name!,
        type: parsed.type ?? mkType(0),
        params: parsed.params ?? [],
        fields: parsed.fields ?? [],
        extends: parsed.extends,
      };

      // Inline extensions
      const registry = createRecordRegistry([...existingRecords, recordDef]);
      let inlinedRecord: RecordDef;
      try {
        inlinedRecord = inlineExtension(recordDef, registry);
      } catch (e) {
        if (e instanceof RecordExtensionError) {
          results.push({
            ...baseResult,
            checkSuccess: false,
            checkErrors: [{ error: extensionError(e), location: getExtendsLocation(parsed) }],
          });
          continue;
        }
        throw e;
      }

      // Elaborate to kernel
      const kernelRecord = elabRecordToKernel(inlinedRecord);

      // Type check
      const checkResult = checkRecordDeclaration(kernelRecord, env);

      if (!checkResult.success) {
        results.push({
          ...baseResult,
          checkSuccess: false,
          checkErrors: mapErrorsToSource(checkResult.errors, parsed.sourceMap),
        });
      } else {
        // Register in environment for subsequent blocks
        env = registerRecordInEnvironment(kernelRecord, checkResult.value, env);

        results.push({
          ...baseResult,
          blockType: 'Record',
          checkSuccess: true,
          recordParams: parsed.params,
          recordFields: parsed.fields,
          recordExtends: parsed.extends,
        });
      }
    }
    // ... handle other declaration kinds
  }

  return results;
}
```

---

## Phase 8: Error Handling and UI Integration

### 8.1 Error Types for Records

```typescript
export type RecordCheckError =
  | { tag: 'FieldDependencyError'; field: string; referencedField: string; message: string }
  | { tag: 'UnknownExtendedRecord'; recordName: string; unknownParent: string }
  | { tag: 'FieldNameClash'; field: string; fromParent: string }
  | { tag: 'CyclicExtension'; cycle: string[] }
  | { tag: 'InvalidFieldType'; field: string; details: CheckError[] }
  | { tag: 'InvalidParameterType'; param: string; details: CheckError[] };
```

### 8.2 Error to Source Range Mapping

```typescript
function mapRecordErrorToSource(
  error: RecordCheckError,
  sourceMap: RecordSourceMap
): { error: CheckError; location: SourceRange | null } {
  switch (error.tag) {
    case 'FieldDependencyError': {
      const fieldIdx = findFieldIndex(sourceMap, error.field);
      return {
        error: {
          tag: 'TypeCheckError',
          message: `Field '${error.field}' cannot reference '${error.referencedField}': ${error.message}`,
        },
        location: fieldIdx >= 0 ? sourceMap.fields[fieldIdx].type : null,
      };
    }
    case 'UnknownExtendedRecord': {
      const extIdx = findExtendsIndex(sourceMap, error.unknownParent);
      return {
        error: {
          tag: 'UnboundVariable',
          message: `Unknown record '${error.unknownParent}' in extends clause`,
        },
        location: extIdx >= 0 ? sourceMap.extends![extIdx] : null,
      };
    }
    // ... other cases
  }
}
```

### 8.3 UI Error Display

The existing `RecordEditor.tsx` component should display errors inline:

```typescript
// In RecordEditor, show field-level errors
{record.fields.map((field, idx) => (
  <FieldRow key={idx}>
    <FieldName>{field.name}</FieldName>
    <FieldType>{prettyPrint(field.type)}</FieldType>
    {fieldErrors[idx] && (
      <ErrorIndicator error={fieldErrors[idx]} />
    )}
  </FieldRow>
))}
```

---

## Phase 9: Extension Validation Enhancements

**Files:** `src/types/tt-elab.ts`

### 9.1 Current Status

The existing `inlineExtension` function handles:
- ✅ Recursive field copying
- ✅ Field name clash detection
- ✅ Unknown parent detection

### 9.2 Enhancements Needed

```typescript
// Add cycle detection
export function inlineExtension(
  record: RecordDef,
  registry: RecordRegistry,
  visited: Set<string> = new Set()  // NEW: track visited for cycle detection
): RecordDef {
  if (visited.has(record.name)) {
    throw new RecordExtensionError(
      `Cyclic extension detected: ${[...visited, record.name].join(' → ')}`
    );
  }
  visited.add(record.name);

  // ... existing logic
}

// Add parameter compatibility checking
export function checkExtensionCompatibility(
  child: RecordDef,
  parent: RecordDef
): ExtensionError | null {
  // Parent's parameters must be prefix of (or unifiable with) child's applied args
  // e.g., Semigroup (A : Type) extends Magma A
  //       Child has (A : Type), applies (A) to Magma
  //       Must check: Magma's param type matches child's applied arg type

  // This is complex and requires type checking during extension
  // For now, we rely on the type checker catching mismatches later
}
```

---

## Phase 10: Testing Strategy

### 10.1 Parser Tests

```typescript
describe('Structure parsing', () => {
  test('simple structure', () => {
    const input = `structure Point where
      x : Nat
      y : Nat`;
    const result = parseStructure(input);
    expect(result.name).toBe('Point');
    expect(result.fields).toHaveLength(2);
  });

  test('structure with parameters', () => {
    const input = `structure Pair (A : Type) (B : Type) where
      fst : A
      snd : B`;
    const result = parseStructure(input);
    expect(result.params).toHaveLength(2);
  });

  test('structure with extends', () => {
    const input = `structure Semigroup (A : Type) extends Magma A where
      assoc : (a b c : A) → op a (op b c) = op (op a b) c`;
    const result = parseStructure(input);
    expect(result.extends).toEqual(['Magma']);
  });

  test('structure with implicit params', () => {
    const input = `structure Magma {A : Type} where
      op : A → A → A`;
    const result = parseStructure(input);
    expect(result.params[0].implicit).toBe(true);
  });
});
```

### 10.2 Type Checking Tests

```typescript
describe('Structure type checking', () => {
  test('field dependency ordering - valid', () => {
    // z depends on x, y which come before
    const record = mkRecord('Example', [
      { name: 'x', type: mkNat() },
      { name: 'y', type: mkNat() },
      { name: 'z', type: mkEqual(mkNat(), mkVar('x'), mkVar('y')) },
    ]);
    const result = checkRecordDeclaration(record, env);
    expect(result.success).toBe(true);
  });

  test('field dependency ordering - invalid forward reference', () => {
    // x references y which comes after - should fail
    const record = mkRecord('Bad', [
      { name: 'x', type: mkEqual(mkNat(), mkVar('y'), mkZero()) },
      { name: 'y', type: mkNat() },
    ]);
    const result = checkRecordDeclaration(record, env);
    expect(result.success).toBe(false);
    expect(result.errors[0].tag).toBe('UnboundVariable');
  });

  test('projection types are correct', () => {
    const record = mkRecord('Point', [
      { name: 'x', type: mkNat() },
      { name: 'y', type: mkNat() },
    ]);
    const result = checkRecordDeclaration(record, env);
    expect(result.value.projectionTypes).toContainEqual({
      name: 'Point.x',
      type: mkPi('p', mkConst('Point'), mkNat()),
    });
  });
});
```

### 10.3 Integration Tests

```typescript
describe('Structure integration', () => {
  test('Magma → Semigroup → Monoid hierarchy', () => {
    const source = `
      structure Magma (A : Type) where
        op : A → A → A

      structure Semigroup (A : Type) extends Magma A where
        assoc : (a b c : A) → op a (op b c) = op (op a b) c

      structure Monoid (A : Type) extends Semigroup A where
        e : A
        leftId : (a : A) → op e a = a
    `;
    const results = checkSourceBlocks(source, emptyEnv);
    expect(results.every(r => r.checkSuccess)).toBe(true);

    // Monoid should have all inherited fields
    const monoidFields = results[2].recordFields!;
    expect(monoidFields.map(f => f.name)).toEqual(['op', 'assoc', 'e', 'leftId']);
  });

  test('type queries work in structure fields', () => {
    const source = `structure Point where
      x : Nat
      y : Nat`;
    const results = checkSourceBlocks(source, emptyEnv);

    // Query at 'x' in first field type
    const query = queryTypeAtPosition(results[0], { line: 1, col: 6 });
    expect(query?.type).toEqual(mkType(0));  // Nat : Type
  });
});
```

### 10.4 Error Case Tests

```typescript
describe('Structure error handling', () => {
  test('unknown parent in extends', () => {
    const source = `structure Foo extends NonExistent where
      x : Nat`;
    const results = checkSourceBlocks(source, emptyEnv);
    expect(results[0].checkSuccess).toBe(false);
    expect(results[0].checkErrors[0].error.message).toContain('NonExistent');
  });

  test('field name clash with parent', () => {
    const source = `
      structure Parent where
        x : Nat

      structure Child extends Parent where
        x : Bool  -- Clash!
    `;
    const results = checkSourceBlocks(source, emptyEnv);
    expect(results[1].checkSuccess).toBe(false);
    expect(results[1].checkErrors[0].error.message).toContain('x');
  });

  test('cyclic extension', () => {
    // This would require modifying the registry mid-check
    // Test at the inlineExtension level
    const A = mkRecord('A', [], ['B']);
    const B = mkRecord('B', [], ['A']);
    const registry = new Map([['A', A], ['B', B]]);

    expect(() => inlineExtension(A, registry)).toThrow(/[Cc]yclic/);
  });
});
```

---

## Phase 11: Future Enhancements

### 11.1 Default Field Values

```lean
structure Config where
  timeout : Nat := 30
  retries : Nat := 3
  verbose : Bool := false

-- Constructor becomes:
Config.mk : (timeout : Nat := 30) → (retries : Nat := 3) → (verbose : Bool := false) → Config

-- Usage:
Config.mk              -- all defaults
Config.mk 60           -- timeout = 60, others default
Config.mk { retries := 5 }  -- named, others default
```

### 11.2 Anonymous Constructor Syntax

```lean
-- Instead of:
let p := Point.mk 1 2

-- Allow:
let p : Point := ⟨1, 2⟩
-- or
let p : Point := { x := 1, y := 2 }
```

### 11.3 Coercion from Child to Parent

```lean
-- Automatic coercion: Monoid → Semigroup → Magma
-- When expecting Magma A, can pass Monoid A

instance : Coe (Monoid A) (Semigroup A) := ⟨fun m => ⟨m.op, m.assoc⟩⟩
instance : Coe (Semigroup A) (Magma A) := ⟨fun s => ⟨s.op⟩⟩
```

### 11.4 Record Update Syntax

```lean
let p := { x := 1, y := 2 }
let q := { p with x := 10 }  -- q.x = 10, q.y = 2
```

---

## Implementation Order Summary

| Phase | Description | Dependencies | Effort |
|-------|-------------|--------------|--------|
| 1 | Parser support | Named Args (for implicit params) | Medium |
| 2 | Field dependency checking | Phase 1 | Medium |
| 3 | Projection generation | Phase 2 | Medium |
| 4 | Constructor type generation | Phase 2 | Low |
| 5 | Type query support | Phase 2, 3 | Medium |
| 6 | Parameter vs index handling | Named Args | Low |
| 7 | Block checker integration | Phase 1-4 | Medium |
| 8 | Error handling & UI | Phase 7 | Medium |
| 9 | Extension validation enhancements | Phase 1 | Low |
| 10 | Testing | All phases | High |
| 11 | Future enhancements | All phases | Future |

**Total Estimated Phases**: 10 core phases + testing

**Critical Path**: Parser → Field Checking → Projections → Block Integration → Testing

---

## Key Files to Create/Modify

| File | Action | Description |
|------|--------|-------------|
| `src/parser/tt-parser.ts` | MODIFY | Add structure parsing |
| `src/types/tt-typecheck-record.ts` | CREATE | Record type checking |
| `src/types/tt-record-projections.ts` | CREATE | Projection/constructor generation |
| `src/types/tt-typecheck-decl.ts` | MODIFY | Integrate record checking |
| `src/types/tt-type-query.ts` | MODIFY | Add record type queries |
| `src/parser/block-checker.ts` | MODIFY | Add 'Record' block type |
| `src/types/tt-elab.ts` | MODIFY | Enhance extension validation |
| `src/types/tt-typecheck-record.test.ts` | CREATE | Record checking tests |
| `src/parser/structure-parser.test.ts` | CREATE | Parser tests |

---

## Relationship to Other Features

### Named Args (Prerequisite)
- Implicit parameters in structures: `structure Magma {A : Type}`
- Named field syntax in constructors: `Point.mk { x := 1, y := 2 }`

### Levels (Prerequisite)
- Universe-polymorphic structures: `structure Container (A : Type u) : Type u`
- Proper universe checking for field types

### Type Classes (Future)
- Structures are the foundation for type classes
- Add `class` keyword as sugar for `structure` + instance mechanism
