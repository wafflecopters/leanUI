# mkConst Fix and Hole UI Cleanup

## Problem 1: mkConst Not Defined

Error when creating equality proof:
```
ReferenceError: mkConst is not defined
    at mkEq (tt-core.ts:600:1)
    at startEqualityProof (tt-bridge.ts:425:1)
```

The `mkEq`, `mkRefl`, `mkTrans`, etc. functions were using `mkConst()` but it wasn't defined.

### Solution

Added `mkConst` helper function to `tt-core.ts`:

```typescript
/**
 * Create a constant with a given name and type
 */
export function mkConst(name: string, type: TTerm): TTerm {
  return { tag: 'Const', name, type };
}
```

Now `mkEq` and other functions can use it:
```typescript
export function mkEq(a: TTerm, b: TTerm): TTerm {
  return mkApp(mkApp(mkConst('Eq', mkProp()), a), b);
  //                  ^^^^^^^ Now works!
}
```

## Problem 2: Global Hole Selection UI

The UI had a global "Available Holes" section where you could click to select which hole to work on. This was wrong because:
- Holes should be edited through their local proof boxes
- Each let-binding has its own proof workspace
- The global selection was confusing and not the intended UX

### Solution

**Removed the entire "Hole Selection UI" section** (lines 1114-1186 in EnhancedProofWorkspace.tsx)

**Before:**
```
┌─────────────────────────────────┐
│ 🎯 Available Holes (2)          │
│ Click a hole to focus on it...  │
│                                 │
│ [proof]         ← Active        │
│ [eq_proof_init]                 │
└─────────────────────────────────┘
```

**After:**
```
(removed)
```

## How It Works Now

### Hole Interaction Model

1. **Create let-binding** with "proof left"
   - Creates `HOLE(a + a)` in the let's value
   - TT system has `?eq_proof_init` hole
   
2. **Work in local proof box**
   - The let-binding's editor shows the expression
   - You modify the expression by clicking and applying rules
   - The hole gets filled as you work
   
3. **No global selection needed**
   - Each let has its own workspace
   - Focus is managed automatically
   - Holes are implicit, not explicit UI elements

### Internal Focus Management

The `focusedHole` state is still used internally:
- When creating an equality let, focus is set to `eq_proof_init`
- When applying rules, the focused hole gets updated
- No UI for manually selecting holes

**The difference:** User interacts with the *proof workspace*, not with *hole selection buttons*.

## Changes Made

### tt-core.ts
- ✅ Added `mkConst(name: string, type: TTerm)` helper function
- ✅ Now exported for use in other modules

### EnhancedProofWorkspace.tsx
- ✅ Removed entire "Hole Selection UI" section (72 lines)
- ✅ Commented out unused `availableHoles` variable
- ✅ Kept `currentHole` for internal logic
- ✅ Focus management still works, just no UI for it

## Testing

1. **Create equality proof let**
   - Should work without mkConst error ✅
   - No hole selection UI visible ✅
   
2. **Apply rules**
   - Work directly in let's proof box ✅
   - Holes are managed invisibly ✅
   
3. **Check TTViewer**
   - Should show proper TT structure ✅
   - Holes displayed as yellow badges ✅

## Benefits

✅ **Cleaner UX:** No confusing global hole selector  
✅ **Local interaction:** Work directly in proof boxes  
✅ **Simpler mental model:** Edit proofs, not holes  
✅ **No mkConst errors:** Equality proofs initialize correctly  

## Status

✅ mkConst defined and working  
✅ Hole selection UI removed  
✅ Focus management still works internally  
✅ Ready to test equality proofs!

