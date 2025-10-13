# TT Layer Design and Implementation

## Overview

The TT (Typed Terms) layer is the foundational formal proof representation that sits beneath the UI. When you create a let-binding claim and prove it, we now construct proper TT proof terms with De Bruijn indices, types, and holes.

## What Was Wrong

Previously, when you created a let binding like:
```
claim thm: a+a = 2*a
```

The system would:
1. ✅ Store this in the UI layer (`LetElement`)
2. ❌ **Never create a corresponding TT proof term**
3. ❌ The TT Viewer would show "No proof term constructed yet"

The UI proof steps and the formal TT layer were completely disconnected.

## What's Fixed Now

### Architecture

```
┌─────────────────────────────────────────────────────┐
│                    UI Layer                         │
│  (ExpressionNode, LetElement, proof steps)          │
└──────────────────┬──────────────────────────────────┘
                   │
                   │ tt-bridge.ts
                   │ (translation layer)
                   │
┌──────────────────▼──────────────────────────────────┐
│                   TT Layer                          │
│  (TTerm, De Bruijn indices, type checking)          │
└─────────────────────────────────────────────────────┘
```

### Key Files

1. **[tt-core.ts](src/types/tt-core.ts)** - Core TT language
   - TTerm type (Var, Lambda, Pi, App, Let, Hole, etc.)
   - De Bruijn indices for variable binding
   - Substitution and shifting operations
   - Pretty printing

2. **[tt-bridge.ts](src/types/tt-bridge.ts)** - NEW! Translation layer
   - `expressionNodeToTTerm()` - Convert UI AST to TT terms
   - `createEqualityProofTerm()` - Initialize proof terms for equality claims
   - `LetProofTerm` - Track proof term state (type, term, holes, completion)
   - `buildFullProofTerm()` - Combine multiple let-bindings into nested structure

3. **[tt-typecheck.ts](src/types/tt-typecheck.ts)** - Type checking
   - `inferType()` - Type inference for TT terms
   - `extractHoles()` - Find unfilled holes in proof

4. **[EnhancedProofWorkspace.tsx](src/components/EnhancedProofWorkspace.tsx)** - Integration
   - Maintains `letProofTerms` map (let ID → LetProofTerm)
   - Creates TT proof terms when starting a proof
   - Updates TT terms as rules are applied (stub for now)
   - Rebuilds combined proof term for display

5. **[TTViewer.tsx](src/components/TTViewer.tsx)** - Display
   - Shows the TT proof term with pretty printing
   - Displays holes and type information
   - Raw AST view for debugging

## Example: Creating and Proving `thm: a+a = 2*a`

### Step 1: Create the Let-Binding (UI)

User creates:
```
let thm: a+a = 2*a
```
With proof method: "Equality Chaining"

### Step 2: TT Term Initialization

When user clicks "Start Proof", we call `createEqualityProofTerm()`:

```typescript
// Create TT representation of left side (a+a)
leftTT = App(App(+, Const("a")), Const("a"))

// Create TT representation of goal (2*a)
goalTT = App(App(*, Const("2")), Const("a"))

// Create proposition type: (a+a = 2*a)
propType = App(App(App(Eq, Real), leftTT), goalTT)

// Create initial proof term: hole with expected type
proofTerm = Hole("proof_thm_id", propType, [])
```

**Result stored in `letProofTerms` map:**
```typescript
{
  letId: "thm_id",
  letName: "thm",
  propType: ((((eq ℝ) ((+ a) a)) ((* 2) a))),
  proofTerm: ?proof_thm_id,
  holes: ["proof_thm_id"],
  completed: false
}
```

### Step 3: TT Viewer Display

The TT Viewer now shows:

```
TT Proof Term

Type: ((((eq ℝ) ((+ a) a)) ((* 2) a)))

Holes (1):
  ?proof_thm_id : ((((eq ℝ) ((+ a) a)) ((* 2) a)))

Pretty-Printed Term:
  ?proof_thm_id

⚠️ Proof incomplete: 1 hole remaining
```

### Step 4: Full Let-Binding Structure (When Complete)

Once the proof is done (goal reached), the full TT term would be:

```lean
let thm : ((a+a) = (2*a)) := proof_term in thm
```

Where `proof_term` is the filled-in proof (built from equality chain steps).

## How Proof Steps Work (Equality Chaining)

When user applies a rule (e.g., "Factor out 'a'"), we:

1. **UI Layer**: Transform the expression
   - `a+a` → `2*a`
   - Create `EquationElement` showing the step
   - Update `currentExpression`

2. **TT Layer** (via `applyProofStep()`): **[TODO - Currently Stub]**
   - Create proof term for this specific step
   - Combine with existing proof using transitivity
   - Update holes

The full implementation would build proof terms like:
```
trans (step1) (trans (step2) (trans (step3) refl))
```

Where each `step` is a justified transformation (axiom or derived rule).

## What You Get Right Now

✅ **Working:**
- Let-bindings create TT proof terms
- Proof terms show type information
- Holes are tracked
- Pretty printing works
- Type checking integration
- TTViewer displays the formal proof structure

🚧 **Stub (but architected):**
- `applyProofStep()` - Currently just returns current state
  - Full implementation would build proof term constructors
  - Chain steps with transitivity
  - Fill holes progressively

## Expected TT Term Output

For `thm: a+a = 2*a` with proof by equality chaining:

### Initial State
```
thm : (a+a = 2*a)
thm = ?proof_id : (a+a = 2*a)
```

### After Starting Proof (Current)
```
thm : ((((eq ℝ) ((+ a) a)) ((* 2) a)))
thm = ?proof_thm_id
```

### After Proof Complete (Future)
```
thm : ((((eq ℝ) ((+ a) a)) ((* 2) a)))
thm = trans (factor_rule a) refl
```

## Next Steps for Full TT Integration

1. **Implement `applyProofStep()` properly:**
   - Map UI rules to TT axioms/theorems
   - Build proof term constructors
   - Use transitivity to chain steps

2. **Add axioms for common rules:**
   - `add_both_sides : ∀ a b c, a = b → a + c = b + c`
   - `factor : ∀ a, a + a = 2 * a`
   - etc.

3. **Proof completion detection:**
   - Check when expression matches goal
   - Mark proof as complete
   - Verify type checking passes

4. **Induction support:**
   - Implement `createInductionProofTerm()`
   - Build nat_elim applications
   - Handle base case and inductive step

## Testing

To test the TT layer:

1. Create a let-binding: `let thm: a+a = 2*a` (as a claim)
2. Choose proof method: "Equality Chaining"
3. Click "Start Proof"
4. Scroll down to "TT Proof Term" section
5. You should see:
   - Type: the equality proposition
   - Holes: one hole with ID
   - Pretty-printed term showing the hole
   - "Proof incomplete: 1 hole remaining"

## Key Design Decisions

1. **Separation of Concerns**: UI layer handles user interaction, TT layer handles formal proof
2. **De Bruijn Indices**: Variables referenced by binding depth, not names (proper for formal systems)
3. **Holes as First-Class**: Incomplete proofs are represented explicitly as holes with types
4. **Type-Driven**: Every term has a type, checked via type inference
5. **Bidirectional Translation**: UI → TT for construction, TT → Pretty for display

## Benefits

- **Formal Correctness**: Proof terms can be type-checked
- **Export to Lean/Coq**: TT layer is close to Lean's internal representation
- **Debugging**: Can see exactly what proof is being constructed
- **Trust**: The "ground truth" is the TT term, not the UI
