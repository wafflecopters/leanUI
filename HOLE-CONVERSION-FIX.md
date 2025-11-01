# Hole Conversion Fix

## Problem

After adding the 'hole' type to ExpressionNode, the system threw an error when creating let-bindings:

```
Error creating let-binding: Error: Unsupported expression type: hole
```

This happened because `expressionNodeToTTerm()` in `tt-bridge.ts` didn't know how to convert 'hole' nodes to TT terms.

## Solution

Added a 'hole' case to the `expressionNodeToTTerm()` conversion function.

### Change in tt-bridge.ts

**Before:**
```typescript
switch (expr.type) {
  case 'variable': ...
  case 'literal': ...
  case 'binop': ...
  case 'equality': ...
  case 'unop': ...
  case 'application': ...
  case 'inequality': ...
  default:
    throw new Error(`Unsupported expression type: ${expr.type}`); // ❌ 'hole' not handled!
}
```

**After:**
```typescript
switch (expr.type) {
  case 'variable': ...
  case 'literal': ...
  case 'binop': ...
  case 'equality': ...
  case 'unop': ...
  case 'application': ...
  case 'inequality': ...
  
  case 'hole':  // ✅ New case added!
    // A hole in the UI AST represents a proof hole
    // Convert to a TT Hole term
    const holeId = String(expr.value || 'unknown_hole');
    
    // Create a hole with Prop type
    return mkHole(holeId, mkProp(), Array.from(context.entries()).map(([name]) => ({
      name,
      type: TT_CONSTANTS.Real
    })));
  
  default:
    throw new Error(`Unsupported expression type: ${expr.type}`);
}
```

## How It Works

### Input (ExpressionNode with type 'hole')
```typescript
{
  type: 'hole',
  value: 'eq_proof_hole',
  children: [
    { type: 'binop', operator: '+', children: [...] }
  ]
}
```

### Output (TTerm Hole)
```typescript
{
  tag: 'Hole',
  id: 'eq_proof_hole',
  type: { tag: 'Const', name: 'Prop', type: { tag: 'Sort', level: 1 } },
  context: [...]
}
```

## Key Points

1. **Hole Identifier**: Taken from `expr.value` (e.g., 'eq_proof_hole')
2. **Hole Type**: Currently `mkProp()` (could be refined later to infer from expression)
3. **Context**: Converts the variable context map to TT context format
4. **Children**: The expression inside (like `a + a`) is stored in `expr.children[0]` but NOT used in the TT term conversion (it's for UI display only)

## Bonus Fix

Also fixed an unrelated error where `mkConst` was being used but not properly defined:

**Before:**
```typescript
const ruleProof = mkConst(ruleName, mkEq(state.currentExpr, newExpr)); // ❌ mkConst doesn't exist
```

**After:**
```typescript
const ruleProof: TTerm = {
  tag: 'Const',
  name: ruleName,
  type: mkEq(state.currentExpr, newExpr)
}; // ✅ Direct construction
```

## Testing

Now when you create a "proof left" let-binding:

1. **UI creates:** `{ type: 'hole', value: 'eq_proof_hole', children: [...] }`
2. **Conversion succeeds:** Creates `{ tag: 'Hole', id: 'eq_proof_hole', ... }`
3. **No error:** Let-binding created successfully
4. **TT system:** Has proper hole term to work with

## Success Criteria

✅ No more "Unsupported expression type: hole" error  
✅ Let-bindings with holes create successfully  
✅ TT terms have proper Hole structure  
✅ Linter clean (no errors)  

## Files Changed

- `src/types/tt-bridge.ts` - Added 'hole' case to conversion function, fixed mkConst usage

**Status:** ✅ COMPLETE - Hole conversion working!

