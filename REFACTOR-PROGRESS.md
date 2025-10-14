# Let-Binding Refactor - Progress Report

## Completed ✅

### 1. Type System Updates
- ✅ Added `TermEditorMode` type with 4 modes:
  - `value`: Hand-written term
  - `equality-left`: Equality chain from left side
  - `equality-right`: Equality chain from right side
  - `cases`: Case split (nat/bool eliminator)

- ✅ Updated `LetElement` interface:
  - Added `editorMode: TermEditorMode`
  - Added `editorExpanded?: boolean`
  - Added `equalityChain?: ProofElement[]`
  - Kept legacy fields as deprecated (for backward compatibility)

- ✅ Updated `createLetElement()` helper:
  - Added optional `editorMode` parameter
  - Defaults to `{ tag: 'value' }`
  - Maintains backward compatibility

### 2. Utility Functions
- ✅ `generateLetName(existingNames)`:
  - Returns `_val0`, `_val1`, etc.
  - Finds lowest available number

- ✅ `parseGoalEquality(goal)`:
  - Detects if goal is `A = B` form
  - Returns `{ left, right }` or `null`
  - Uses `type === 'equality'` check

### 3. Documentation
- ✅ Created [LET-BINDING-REFACTOR.md](LET-BINDING-REFACTOR.md)
  - Full architecture vision
  - Examples and use cases
  - Implementation phases

## In Progress 🚧

### 4. UI Updates (Next Step)
Need to update `LetManager.tsx` "Add Let" form:

**Current UI:**
```
Name: [input]
Expression: [input]
Type: [input]
[x] This is a claim to be proved
Proof method: [dropdown]
```

**Target UI:**
```
Name: [input] (optional, auto-generates _val0 if empty)

[Button Row based on goal type]
```

**Button Logic:**
- If goal is `A = B`: Show all 4 buttons
  - `[goal left = ?]` - Creates equality chain from A
  - `[goal right = ?]` - Creates equality chain from B
  - `[cases]` - Case split UI
  - `[value]` - Text input

- If goal is NOT equality: Show only 2 buttons
  - `[cases]` - Case split UI
  - `[value]` - Text input

## Remaining Work 📋

### Phase 1: Update Add Let Form (Currently Working)
1. Import utility functions (`generateLetName`, `parseGoalEquality`)
2. Remove old form fields (isClaim checkbox, proof method dropdown)
3. Add mode selection button row
4. Conditional rendering based on goal type
5. Handle button clicks to create appropriate LetElement

### Phase 2: Update Let Display
1. Remove proof status badges
2. Remove "Start Proof" button
3. Add expandable term editor to each let

### Phase 3: Term Editor Component
1. Create `TermEditor.tsx` component
2. Switch between editors based on `editorMode`:
   - Value editor: Text input
   - Equality editor: Reuse existing equality chain UI
   - Cases editor: Stub for now

### Phase 4: Integration
1. Wire up term editors to let-bindings
2. Move equality chain from centralized proof area to per-let
3. Handle expand/collapse state

### Phase 5: Cleanup
1. Remove deprecated fields once everything works
2. Remove old proof area code
3. Update tests if any exist

## Key Design Decisions

1. **Backward Compatibility**: Kept deprecated fields to avoid breaking existing code during transition

2. **Auto-naming**: Use `_val{i}` pattern, not `x`, `y`, `z` sequence (simpler algorithm)

3. **Goal Parsing**: Parse at UI creation time, not at type level (keeps types simple)

4. **Term Editors**: Each let has its own editor, not a central proof area

5. **Type Inference**: When using `goal left/right` buttons, type annotation is optional/inferred

## Testing Strategy

### Manual Testing Steps:
1. Create let with each button mode
2. Verify auto-name generation
3. Test with equality goal
4. Test with non-equality goal
5. Verify backward compatibility with existing lets

### Edge Cases to Test:
- Empty name field → should auto-generate
- Goal is not an equality → buttons adjust
- Multiple lets → names should be `_val0`, `_val1`, `_val2`
- Existing lets with old structure → should still render

## Current State

**Files Modified:**
- `src/types/enhanced-focus.ts` - Types and utilities ✅
- `LET-BINDING-REFACTOR.md` - Architecture doc ✅

**Files To Modify:**
- `src/components/LetManager.tsx` - Add Let UI (next)
- `src/components/EnhancedProofWorkspace.tsx` - Integration
- Create `src/components/TermEditor.tsx` - New component

**Build Status:** ✅ Compiling successfully

## Next Immediate Steps

1. Open `LetManager.tsx`
2. Import new utilities
3. Update Add Let form UI
4. Test in browser
5. Iterate

---

*This is a living document. Update as progress continues.*
