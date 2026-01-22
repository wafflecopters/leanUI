# Pattern Elaboration Algorithm

## Overview

`elaboratePatternsToPositionalArguments` is a single function that transforms surface-level clause patterns into fully positional kernel patterns, ready for LHS type checking.

## Goals

1. **Slot-based placement**: Place named/positional patterns into parameter slots
2. **Implicit filling**: Fill unfilled implicit slots with `PWild`
3. **Constructor resolution**: For leaf patterns, determine if they're constructors or variables
4. **RHS adjustment**: Compute a mapping so the RHS de Bruijn indices can be adjusted

## Function Signature

```typescript
type PatternElabResult = {
  // Fully positional kernel patterns (one per parameter)
  patterns: TTKPattern[];

  // Maps parser de Bruijn index → elaborated de Bruijn index
  // For phantom bindings (parser var that's actually a ctor), value is { ctor: string }
  // For regular vars, value is the new index
  varMapping: Map<number, number | { ctor: string }>;

  // Names of bound variables in elaborated order (for RHS context)
  boundNames: string[];
}

function elaboratePatternsToPositionalArguments(
  // Surface patterns from the clause (positional)
  surfacePatterns: TPattern[],

  // Named patterns from clause-level syntax {name := pattern}
  namedPatterns: Array<{ name: string; pattern: TPattern }> | undefined,

  // Parameter info from the function type
  params: ParamInfo[],

  // Set of known constructor names (for ctor vs var resolution)
  constructorNames: Set<string>
): PatternElabResult | { error: string }
```

## Algorithm Steps

### Step 1: Create Slots

```typescript
const slots: (TPattern | null)[] = new Array(params.length).fill(null);
```

### Step 2: Place Named Patterns

For each named pattern `{name := pattern}`:
1. Find the parameter with that name
2. Place the pattern in that slot
3. Error if name not found or slot already filled

```typescript
for (const { name, pattern } of namedPatterns ?? []) {
  const idx = params.findIndex(p => p.name === name);
  if (idx === -1) throw error(`Unknown parameter: ${name}`);
  if (slots[idx] !== null) throw error(`${name} already filled`);
  slots[idx] = pattern;
}
```

### Step 3: Place Positional Patterns

Place positional patterns into unfilled EXPLICIT slots (left to right):

```typescript
let patternIdx = 0;
for (let i = 0; i < params.length && patternIdx < surfacePatterns.length; i++) {
  if (params[i].implicitness === 'explicit' && slots[i] === null) {
    slots[i] = surfacePatterns[patternIdx++];
  }
}
if (patternIdx < surfacePatterns.length) {
  throw error('Too many positional patterns');
}
```

### Step 4: Fill Implicit Slots

For each unfilled implicit slot, insert a wildcard:

```typescript
for (let i = 0; i < params.length; i++) {
  if (slots[i] === null && params[i].implicitness === 'implicit') {
    slots[i] = { tag: 'PWild' };
  }
}
```

### Step 5: Check for Missing Explicits

```typescript
for (let i = 0; i < params.length; i++) {
  if (slots[i] === null && params[i].implicitness === 'explicit') {
    throw error(`Missing pattern for explicit parameter ${params[i].name}`);
  }
}
```

### Step 6: Elaborate Patterns to Kernel + Build Var Mapping

Now convert each surface pattern to kernel pattern, handling constructor resolution:

```typescript
function elaboratePattern(
  pattern: TPattern,
  constructorNames: Set<string>,
  varList: string[]  // accumulates bound variable names
): TTKPattern {
  switch (pattern.tag) {
    case 'PVar':
      varList.push(pattern.name);
      return { tag: 'PVar', name: pattern.name };

    case 'PWild':
      varList.push('_');  // wildcards also bind
      return { tag: 'PWild', name: freshWildcardName() };

    case 'PCtor': {
      const hasArgs = pattern.args.length > 0 || pattern.namedArgs?.length > 0;

      if (!hasArgs) {
        // Leaf PCtor - check if it's a known constructor
        if (constructorNames.has(pattern.name)) {
          // It's a constructor - keep as PCtor
          return { tag: 'PCtor', name: pattern.name, args: [] };
        } else {
          // Not a constructor - treat as pattern variable
          varList.push(pattern.name);
          return { tag: 'PVar', name: pattern.name };
        }
      }

      // PCtor with args - must be a constructor
      if (!constructorNames.has(pattern.name)) {
        throw error(`Unknown constructor: ${pattern.name}`);
      }

      // Recursively elaborate arguments
      // (Handle named args within constructor patterns too)
      const elabArgs = pattern.args.map(arg =>
        elaboratePattern(arg, constructorNames, varList)
      );

      return { tag: 'PCtor', name: pattern.name, args: elabArgs };
    }
  }
}
```

### Step 7: Compute Var Mapping

The parser's `collectPatternVars` produces variables in a certain order.
The elaborator produces variables in a (potentially different) order.

We need to map: `parserIndex → elaboratorIndex | { ctor: name }`

This requires simulating what the parser does vs what the elaborator does:

```typescript
// Simulate parser's collectPatternVars
function collectParserVars(pattern: TPattern): string[] {
  switch (pattern.tag) {
    case 'PVar': return [pattern.name];
    case 'PWild': return ['_'];
    case 'PCtor': {
      const hasArgs = pattern.args.length > 0 || pattern.namedArgs?.length > 0;
      if (!hasArgs) {
        // Parser heuristic: lowercase = variable
        const firstChar = pattern.name[0];
        if (firstChar === firstChar.toLowerCase()) {
          return [pattern.name];
        }
        return [];
      }
      // Recursively collect from args
      return [...pattern.args, ...(pattern.namedArgs?.map(na => na.pattern) ?? [])]
        .flatMap(collectParserVars);
    }
  }
}

// Compare parser vars to elaborator vars to build mapping
function buildVarMapping(
  parserVars: string[],
  elaboratorVars: string[],
  constructorNames: Set<string>
): Map<number, number | { ctor: string }> {
  const mapping = new Map();

  // For each parser var, find its position in elaborator vars
  // or mark it as a constructor if it became one
  for (let i = 0; i < parserVars.length; i++) {
    const name = parserVars[i];

    // Check if this name became a constructor
    if (constructorNames.has(name)) {
      mapping.set(i, { ctor: name });
    } else {
      // Find position in elaborator vars
      const elabIdx = elaboratorVars.indexOf(name);
      if (elabIdx >= 0) {
        mapping.set(i, elabIdx);
      }
    }
  }

  return mapping;
}
```

## RHS Adjustment

After calling `elaboratePatternsToPositionalArguments`, use the `varMapping` to transform the RHS:

```typescript
function adjustRhs(
  rhs: TTerm,
  varMapping: Map<number, number | { ctor: string }>,
  totalParserVars: number
): TTerm {
  // Transform Var(i) based on mapping
  // If mapping[i] is { ctor: name }, replace with Const(name)
  // If mapping[i] is a number, update the index
}
```

## Example

```
-- Function type: {A : Type} -> (x : A) -> {B : Type} -> (y : B) -> C
-- Clause: foo x {B := MyType} y = ...

Surface patterns: [x, y]  (positional)
Named patterns: [{name: 'B', pattern: MyType}]
Params: [{A, implicit}, {x, explicit}, {B, implicit}, {y, explicit}]

Step 2: slots = [null, null, MyType, null]
Step 3: slots = [null, x, MyType, y]
Step 4: slots = [PWild, x, MyType, y]
Step 5: all explicits filled ✓

Elaborated patterns: [PWild, PVar(x), PCtor(MyType), PVar(y)]
  (assuming MyType is a constructor; if not, it becomes PVar(MyType))

Parser vars: [x, y]  (from collectParserVars on [x, y])
Elab vars: [_, x, y]  (from elaborating all slots)

Mapping: {0 → 1, 1 → 2}  (parser x at 0 → elab x at 1, etc.)
```

## Benefits

1. **Single function**: All pattern elaboration logic in one place
2. **Testable**: Pure function, easy to unit test with many cases
3. **Clear contract**: Input/output well-defined
4. **Handles all cases**: Named args, implicit filling, ctor resolution
