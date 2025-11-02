# Type Holes and Hole Instantiation

## Problem

When parsing a goal like `a + a = 2 * a`, the system:
1. ✅ Correctly identifies `a` as an unbound variable
2. ✅ Creates hypothesis `a : ?` 
3. ❌ **BUT** assumes `a : ℝ` when building TT terms
4. ❌ Creates type: `(a : Prop) → ((eq ℝ) ((+ a) a)) ((* 2) a))`

This is wrong! The type of `a` is unknown, so we should create a **type hole**.

## Correct Behavior

### Step 1: Parse Goal with Unbound Variables

Goal: `a + a = 2 * a`
Unbound: `{a}`

### Step 2: Create Type Holes

For each unbound variable, create:
- A type hole: `?type_a : Type`
- A term variable: `a : ?type_a`

TT Structure:
```
?type_a : Type
a : ?type_a
_root : ((a : ?type_a) → ((eq ?type_a) ((+ a) a)) ((* 2) a)))
```

### Step 3: User Instantiates Type Hole

User action: "Set `?type_a` to `ℝ`"

The engine propagates this instantiation throughout the term.

### Step 4: Simplification After Instantiation

After instantiation with a concrete type, if the Pi-binder becomes redundant (no polymorphism), it could be eliminated. However, we still need `a` as a free variable, so:

```
_root : ((a : ℝ) → ((eq ℝ) ((+ a) a)) ((* 2) a)))
```

The difference is that `?type_a` is now concrete `ℝ`, not a hole.

## Implementation Plan

### Phase 1: Type Hole Creation

**File: `EnhancedProofWorkspace.tsx`**

When creating hypotheses for unbound variables:

```typescript
// Current (WRONG):
const hypothesis: Assumption = {
  name: varName,
  expression: `${varName} : ?`,
  ...
};

// New (CORRECT):
const typeHoleId = `type_${varName}`;
const hypothesis: Assumption = {
  name: varName,
  expression: `${varName} : ?${typeHoleId}`,
  typeHoleId,  // NEW: track the type hole
  ...
};
```

**File: `types/enhanced-focus.ts`**

Add `typeHoleId` to `Assumption`:

```typescript
export interface Assumption {
  id: string;
  name: string;
  expression: string;
  description?: string;
  introducedBy?: 'user' | 'auto';
  typeHoleId?: string;  // NEW: ID of the type hole for this variable
}
```

### Phase 2: TT Term Construction with Type Holes

**File: `EnhancedProofWorkspace.tsx`** (lines 298-311)

```typescript
// Current (WRONG):
if (typeStr === '?') {
  typeTerm = mkProp();  // ❌ Assumes Prop
}

// New (CORRECT):
if (typeStr === '?') {
  // Create a type hole
  const typeHoleId = `type_${h.name}`;
  typeTerm = mkHole(typeHoleId, mkSort(1), []);  // Type : Type_1
} else if (typeStr.startsWith('?')) {
  // Explicit type hole reference
  const typeHoleId = typeStr.substring(1);
  typeTerm = mkHole(typeHoleId, mkSort(1), []);
}
```

**File: `tt-core.ts`**

Add `mkSort` helper:

```typescript
export function mkSort(level: number): TTerm {
  return { tag: 'Sort', level };
}
```

### Phase 3: Expression Conversion with Type Context

**File: `tt-bridge.ts`** (`expressionNodeToTTerm`)

Currently assumes all variables are `ℝ`:

```typescript
// Current (WRONG):
case 'variable':
  return {
    tag: 'Const',
    name: varName,
    type: TT_CONSTANTS.Real  // ❌ Hardcoded
  };
```

Need to pass type information:

```typescript
// New (CORRECT):
export function expressionNodeToTTerm(
  expr: ExpressionNode, 
  context: Map<string, number> = new Map(),
  typeContext: Map<string, TTerm> = new Map()  // NEW: variable types
): TTerm {
  switch (expr.type) {
    case 'variable':
      const varName = String(expr.value);
      if (context.has(varName)) {
        return mkVar(context.get(varName)!);
      }
      // Get type from type context
      const varType = typeContext.get(varName) || TT_CONSTANTS.Real;
      return { tag: 'Const', name: varName, type: varType };
    // ...
  }
}
```

**Update call sites** to pass `typeContext`:

```typescript
// In EnhancedProofWorkspace.tsx:
const typeContext = new Map<string, TTerm>();
ttHypotheses.forEach(([name, type]) => {
  typeContext.set(name, type);
});

const goalTerm = goal 
  ? expressionNodeToTTerm(goal, new Map(), typeContext) 
  : mkProp();
```

### Phase 4: Hole Instantiation Engine (Future)

**File: `tt-typecheck.ts` (new functions)**

```typescript
/**
 * Instantiate a hole throughout a term
 * 
 * @param term - The term containing holes
 * @param holeId - ID of the hole to instantiate
 * @param value - The value to replace the hole with
 * @returns New term with hole instantiated
 */
export function instantiateHole(
  term: TTerm, 
  holeId: string, 
  value: TTerm
): TTerm {
  // Recursively replace all occurrences of the hole
  function go(t: TTerm): TTerm {
    if (t.tag === 'Hole' && t.id === holeId) {
      return value;
    }
    // Recurse into subterms
    return mapTTerm(t, {
      Var: (t) => t,
      Sort: (t) => t,
      Binder: (t) => ({
        ...t,
        domain: go(t.domain),
        body: go(t.body),
        binderKind: t.binderKind.tag === 'BLet' 
          ? { tag: 'BLet', defVal: go(t.binderKind.defVal) }
          : t.binderKind
      }),
      App: (t) => ({ ...t, fn: go(t.fn), arg: go(t.arg) }),
      Const: (t) => ({ ...t, type: go(t.type) }),
      Hole: (t) => t,  // Already handled above
      Annot: (t) => ({ ...t, term: go(t.term), type: go(t.type) })
    });
  }
  return go(term);
}
```

## Testing Plan

### Test 1: Type Hole Creation

```typescript
// test file: types/tt-core.test.ts

it('creates type holes for unbound variables', () => {
  const typeHoleId = 'type_a';
  const typeHole = mkHole(typeHoleId, mkSort(1), []);
  
  expect(typeHole.tag).toBe('Hole');
  expect(typeHole.id).toBe('type_a');
  expect(typeHole.type.tag).toBe('Sort');
  expect((typeHole.type as any).level).toBe(1);
});

it('builds goal with type holes', () => {
  const typeHole = mkHole('type_a', mkSort(1), []);
  const hypotheses: Array<[string, TTerm]> = [['a', typeHole]];
  const goalExpr = mkEq(
    mkApp(mkApp(mkConst('+', mkProp()), mkConst('a', typeHole)), mkConst('a', typeHole)),
    mkApp(mkApp(mkConst('*', mkProp()), mkConst('2', TT_CONSTANTS.Real)), mkConst('a', typeHole))
  );
  
  const termDef = createRootTermDefinition('_root', hypotheses, goalExpr, 'proof', []);
  
  // Should have Pi binder with type hole
  const printed = prettyPrint(termDef.type);
  expect(printed).toContain('?type_a');
});
```

### Test 2: Hole Instantiation

```typescript
// test file: types/tt-typecheck.test.ts

it('instantiates type holes throughout term', () => {
  const typeHole = mkHole('type_a', mkSort(1), []);
  const term = mkPi(
    typeHole,
    mkEq(mkConst('a', typeHole), mkConst('b', typeHole)),
    'a'
  );
  
  const instantiated = instantiateHole(term, 'type_a', TT_CONSTANTS.Real);
  
  // All occurrences of ?type_a should be replaced with ℝ
  const printed = prettyPrint(instantiated);
  expect(printed).not.toContain('?type_a');
  expect(printed).toContain('ℝ');
});
```

## Migration Path

1. ✅ Phase 1: Add `typeHoleId` to `Assumption` (minimal change)
2. ✅ Phase 2: Create type holes when building TT terms
3. ✅ Phase 3: Pass type context to `expressionNodeToTTerm`
4. ⏸️ Phase 4: Implement `instantiateHole` (future - when user UI for instantiation exists)

## Key Principles

- **Type holes are first-class**: Just like proof holes, type holes are explicit in the term
- **Propagation is automatic**: When a hole is instantiated, the engine updates all references
- **No assumptions**: Never assume `ℝ` or any other type - always explicit
- **User control**: User instantiates type holes when they want to specialize

## Status

📝 Design complete
🚧 Implementation in progress

