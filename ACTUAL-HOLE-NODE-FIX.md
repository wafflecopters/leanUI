# Actual Hole Node Fix

## Problem

When creating an equality proof with "proof left"/"proof right", the system was creating a **fake** hole - just a variable node with value 'HOLE'. This meant:
- The AST didn't have a proper hole type
- Rules couldn't distinguish between a real hole and a constant named "HOLE"
- The structure was wrong: `application(variable("HOLE"), expr)` instead of `hole(expr)`

## Solution

Added a proper 'hole' type to the ExpressionNode AST and updated all relevant code.

### 1. Added 'hole' Type to ExpressionNode (enhanced-focus.ts)

**Before:**
```typescript
type: 'equality' | 'inequality' | 'binop' | 'unop' | 'literal' | 'variable' | 'application';
```

**After:**
```typescript
type: 'equality' | 'inequality' | 'binop' | 'unop' | 'literal' | 'variable' | 'application' | 'hole';
```

### 2. Create Proper Hole Nodes (LetManager.tsx)

**Before (WRONG):**
```typescript
expr = {
  id: crypto.randomUUID(),
  type: 'application',           // ❌ Application, not hole
  raw: `HOLE ${mode.startExpr.raw}`,
  children: [
    { type: 'variable', value: 'HOLE', ... },  // ❌ Variable named "HOLE"
    mode.startExpr
  ]
};
```

**After (CORRECT):**
```typescript
expr = {
  id: crypto.randomUUID(),
  type: 'hole',                  // ✅ Actual hole type
  raw: `HOLE(${mode.startExpr.raw})`,
  value: 'eq_proof_hole',        // ✅ Hole identifier
  children: [mode.startExpr]     // ✅ Expression we're working on
};
```

**Structure:**
- **Type:** `'hole'` (not application or variable)
- **Value:** Identifier for this specific hole
- **Children:** The expression being transformed (e.g., `a + a`)

### 3. Render Hole Nodes (FocusedExpressionRenderer.tsx)

Added a case to display hole nodes as bright yellow badges:

```typescript
case 'hole':
  return (
    <span style={{
      backgroundColor: focused ? '#ffc107' : '#ffeb3b',
      color: '#000',
      padding: '4px 8px',
      borderRadius: '4px',
      fontWeight: 'bold',
      border: '2px solid #ffc107'
    }}>
      HOLE(
      {renderNode(node.children[0], [...currentPath, 0])}
      )
    </span>
  );
```

**Visual appearance:** Yellow badge with `HOLE(a + a)` showing the expression inside.

## How It Works Now

### Creating Equality Proof

1. **User action:** Click "proof left"
2. **LetManager creates:**
   ```
   {
     type: 'hole',
     value: 'eq_proof_hole',
     children: [{ type: 'binop', operator: '+', children: [a, a] }]
   }
   ```
3. **Displayed as:** `HOLE(a + a)` in yellow badge
4. **AST structure:** Proper hole node, not fake application

### Applying Rules

1. **User clicks** on `a` inside `HOLE(a + a)`
2. **Focus path:** `[0, 0]` (first child of hole, first child of binop)
3. **Rule applied** to `children[0]` of the hole
4. **Hole persists**, child updates: `HOLE(1 + a)`
5. **TT system** sees the hole and builds proper proof term

### AST Structure Comparison

**Old (WRONG):**
```
application
├─ variable: "HOLE"  ← Just a string!
└─ binop: "+"
   ├─ variable: "a"
   └─ variable: "a"
```

**New (CORRECT):**
```
hole: "eq_proof_hole"  ← Actual hole type!
└─ binop: "+"
   ├─ variable: "a"
   └─ variable: "a"
```

## Key Differences

| Aspect | Old (Wrong) | New (Correct) |
|--------|-------------|---------------|
| **Node Type** | `'application'` | `'hole'` |
| **Structure** | `app(var("HOLE"), expr)` | `hole(expr)` |
| **Identifier** | String constant | Proper hole ID in `value` |
| **AST Check** | `node.type === 'application' && node.children[0].value === 'HOLE'` | `node.type === 'hole'` |
| **Rendering** | Could be confused with actual application | Distinct yellow badge |

## Benefits

✅ **Proper AST Type:** Hole is a first-class node type  
✅ **Clear Semantics:** No confusion with constants or applications  
✅ **Easy Checking:** `node.type === 'hole'` instead of string matching  
✅ **Visual Clarity:** Bright yellow badge makes holes obvious  
✅ **Extensible:** Can add hole-specific properties (context, type, etc.)  

## Testing

1. **Create equality proof let**
2. **Check console:** Should see `[ADD-LET]` logs
3. **Check UI:** Should see `HOLE(a + a)` in bright yellow badge
4. **Check AST Debug Panel:** Should show `type: 'hole'` not `type: 'application'`
5. **Apply rule:** Click on expression inside hole, apply transformation
6. **Verify:** Hole persists, expression inside changes

## Success Criteria

🎯 **AST shows:** `type: 'hole'` with proper structure  
🎯 **UI shows:** Yellow badge `HOLE(expression)`  
🎯 **Rules work:** Transform expression inside hole  
🎯 **No confusion:** Clear distinction from applications/variables  

## Files Changed

- `src/types/enhanced-focus.ts` - Added 'hole' to type union
- `src/components/LetManager.tsx` - Create proper hole nodes
- `src/components/FocusedExpressionRenderer.tsx` - Render hole nodes

**Status:** ✅ COMPLETE - Proper hole nodes in AST!

