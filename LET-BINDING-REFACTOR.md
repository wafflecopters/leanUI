# Let-Binding Architecture Refactor

## Vision

Every let-binding is a term with a type and value. The value is edited through specialized **term editor UIs** based on the mode of construction.

## Old Model (Before)

```typescript
interface LetElement {
  name: string;
  value: ExpressionNode;
  typeAnnotation?: string;
  isClaim?: boolean;              // ❌ Remove
  proofMethod?: ProofMethod;      // ❌ Remove
  proofStatus?: string;           // ❌ Remove
  goal?: ExpressionNode;          // ❌ Remove
  proofElements?: ProofElement[]; // ❌ Remove
}
```

**Problems:**
- Special "claim" vs "let" distinction
- Centralized proof area
- Proof status tracking separate from term

## New Model (After)

```typescript
type TermEditorMode =
  | { tag: 'value' }                          // Hand-written term
  | { tag: 'equality-left'; startExpr: ExpressionNode }   // refl A, chain from left
  | { tag: 'equality-right'; startExpr: ExpressionNode }  // refl B, chain from right
  | { tag: 'cases'; eliminator: 'nat' | 'bool' }         // Case split

interface LetElement {
  name: string;                    // Auto-generated if not provided (_val0, _val1, etc.)
  value: ExpressionNode;           // The term (can be complex proof term)
  typeAnnotation?: string;         // Optional type, inferred if omitted
  editorMode: TermEditorMode;      // How to edit this term
  editorExpanded?: boolean;        // Is the term editor UI visible?

  // For equality chaining mode:
  equalityChain?: ProofElement[];  // The chain of steps (refl, sym, trans, cong)
}
```

## Let-Binding Creation Flow

### Step 1: Name (Optional)
- Input field for name
- If empty, auto-generate: `_val0`, `_val1`, etc. (find lowest unused)

### Step 2: Mode Selection (Buttons)

**If goal is `A = B`:**
```
[goal left = ?]  [goal right = ?]  [cases]  [value]
```

**If goal is NOT equality:**
```
[cases]  [value]
```

### Step 3: Term Editor Opens

Based on mode:

#### `[goal left = ?]`
- Extract `A` from goal `A = B`
- Create let with:
  - `name: _val0` (auto)
  - `typeAnnotation: undefined` (inferred)
  - `editorMode: { tag: 'equality-left', startExpr: A }`
  - `value: refl A` (initial)
  - `equalityChain: [{ type: 'equation', expression: A }]`
- Open equality-chaining UI

#### `[goal right = ?]`
- Extract `B` from goal `A = B`
- Create let with:
  - `name: _val0` (auto)
  - `typeAnnotation: undefined` (inferred)
  - `editorMode: { tag: 'equality-right', startExpr: B }`
  - `value: refl B` (initial)
  - `equalityChain: [{ type: 'equation', expression: B }]`
- Open equality-chaining UI

#### `[cases]`
- Create let with:
  - `name: _val0` (auto)
  - `editorMode: { tag: 'cases', eliminator: 'nat' }` (for now)
  - Open case split UI (stub for now)

#### `[value]`
- Create let with:
  - `name: _val0` (auto)
  - `editorMode: { tag: 'value' }`
  - Open text input for term

## Term Editors

### Equality-Chaining Editor
- Reuse existing equality chain UI
- Each step builds proof terms: refl, sym, trans, cong
- Lives inline within the let-binding display
- Can expand/collapse

### Value Editor
- Simple text input
- For hand-written terms like `5` or `(foo bar)`

### Case Split Editor (Future)
- UI for nat_elim: base case + inductive case
- UI for bool_elim: true case + false case

## UI Changes

### Remove:
- ❌ "This is a claim to be proved" checkbox
- ❌ Proof method dropdown
- ❌ Proof status badges
- ❌ "Start Proof" button
- ❌ Centralized proof area

### Add:
- ✅ Mode selection buttons in "Add Let" form
- ✅ Per-let expandable term editor
- ✅ Auto-name generation
- ✅ Goal parsing for equality detection

## Implementation Phases

### Phase 1: Type Updates
1. Update `LetElement` interface
2. Add `TermEditorMode` type
3. Update `createLetElement` helper

### Phase 2: Name Auto-Generation
1. Create `generateLetName(existingNames)` function
2. Returns `_val0`, `_val1`, etc. (lowest unused)

### Phase 3: Goal Parsing
1. Create `parseGoalEquality(goal)` function
2. Returns `{ left: ExpressionNode, right: ExpressionNode } | null`

### Phase 4: UI Updates
1. Update "Add Let" form with mode buttons
2. Remove isClaim checkbox
3. Add expandable term editor to let-binding display

### Phase 5: Term Editor Integration
1. Move equality-chaining UI into per-let editor
2. Add value text input editor
3. Add case split stub

## Example Usage

### Example 1: Proof by Chaining from Left

**Goal:** `a + b = b + a`

**User Action:**
1. Click "+ Add Let"
2. Leave name empty (will become `_val0`)
3. Click `[goal left = ?]`

**Result:**
```
let _val0 : a + b = ? := refl (a + b)
  [Equality chain editor opens]
  a + b
  = ... [user adds steps]
```

### Example 2: Intermediate Lemma

**Goal:** `A = B`

**User Action:**
1. Click "+ Add Let"
2. Enter name: `lemma1`
3. Click `[goal left = ?]`
4. Chain to get `A = C`

**Result:**
```
let lemma1 : A = C := trans (refl A) ... [chain steps]
```

Later:
1. Create another let from goal right
2. Get `B = C`
3. Combine them to prove `A = B`

## Benefits

1. **Unified Model**: Everything is just a term
2. **Flexible Proof**: Not forced to chain A→B directly
3. **Compositional**: Build lemmas, combine them
4. **Type Inference**: Types inferred when using goal buttons
5. **Per-Let Editors**: Each let has its own workspace
6. **No Special Cases**: No distinction between "claim" and "let"
