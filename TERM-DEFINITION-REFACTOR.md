# Term Definition Architecture Refactor

## Problem Statement

Currently, the proof system uses:
1. **Wrapper let-binding at top level**: `let _root : A := HOLE-proof in _root`
2. **ActiveProofContext with IDs**: Tracks which let-binding's proof we're working on
3. **Separate proof contexts**: Each let-binding has its own isolated proof workspace

This is wrong. We should have:
1. **Term definitions at top level**: `_root : A` and `_root = HOLE-proof`
2. **Hole-based focus**: Just focus on whichever hole you're working on
3. **Nested let-bindings**: Let-bindings should be inside the proof term as you add them

## Current Architecture

### Top Level
```typescript
// In createRootProofTerm()
let _root : (hypotheses...) → Goal 
          = ?HOLE-proof
in _root  // <-- This wrapper is wrong!
```

### Let-Bindings
```typescript
// Separate UI elements with proof context IDs
activeProofContext = "let-binding-id-123"
letBindings[id].proofElements = [...]
```

### Focus System
- Tracks `activeProofContext` string ID
- Maps ID to specific let-binding's proof workspace
- Complex state management with multiple proof contexts

## New Architecture

### Top Level: Term Definitions

Instead of a let-binding wrapping everything, we have a **term definition**:

```lean
-- Declaration
_root : (a: ℝ) → (b: ℝ) → (a + b = b + a)

-- Definition (initially a hole)
_root = ?proof
```

In TT terms:
```typescript
interface TermDefinition {
  name: string;           // "_root"
  type: TTerm;           // The full proposition type
  value: TTerm;          // The proof term (starts as hole, fills in)
}
```

### Let-Bindings: Nested Inside

When you add a let-binding, it goes **inside** the proof term:

```lean
_root : (a: ℝ) → (b: ℝ) → (a + b = b + a)
_root = 
  let foo : a + b = b + a := ?proof-foo in
    ?proof-rest
```

Or with multiple lets:
```lean
_root =
  let step1 : a + b = b + a := ... in
  let step2 : ... := ... in
    ?final-proof
```

### Focus System: Hole-Based

No more `activeProofContext` IDs. Just:
```typescript
focusedHole: string | null;  // The ID of the hole we're working on
```

The system:
1. Extracts all holes from the term using `extractHoles()`
2. User selects which hole to work on
3. UI shows the context and type for that hole
4. User applies rules, filling in the hole

## Implementation Plan

### Phase 1: Create Term Definition Type

```typescript
// In tt-core.ts
export interface TermDefinition {
  name: string;
  type: TTerm;
  value: TTerm;
}

// Replace createRootProofTerm with:
export function createRootTermDefinition(
  name: string,
  hypotheses: Array<[string, TTerm]>,
  goal: TTerm,
  proofHoleId: string = 'proof'
): TermDefinition {
  const theoremType = hypothesesToPi(hypotheses, goal);
  const proofHole = mkHole(proofHoleId, theoremType, []);
  
  return {
    name,
    type: theoremType,
    value: proofHole
  };
}
```

### Phase 2: Update State Management

In `EnhancedProofWorkspace.tsx`:

```typescript
// REMOVE:
const [activeProofContext, setActiveProofContext] = useState<string | null>(null);
const [letProofTerms, setLetProofTerms] = useState<Map<string, LetProofTerm>>(new Map());
const [structuredProof, setStructuredProof] = useState<StructuredProof>({...});

// REPLACE WITH:
const [rootDefinition, setRootDefinition] = useState<TermDefinition>(() => 
  createRootTermDefinition('_root', [], mkProp(), 'proof')
);
const [focusedHole, setFocusedHole] = useState<string | null>('proof');
```

### Phase 3: Hole Selection UI

```typescript
// Extract all holes from current term
const holes = extractHoles(rootDefinition.value);

// UI to select which hole to work on
<div>
  <h3>Available Holes:</h3>
  {holes.map(hole => (
    <button
      key={hole.id}
      onClick={() => setFocusedHole(hole.id)}
      style={{ 
        fontWeight: focusedHole === hole.id ? 'bold' : 'normal' 
      }}
    >
      {hole.id}: {ttermToString(hole.type)}
    </button>
  ))}
</div>
```

### Phase 4: Update Let-Binding Addition

When adding a let-binding, instead of creating a separate proof context:

```typescript
function addLetBinding(letName: string, letType: TTerm, letValue: TTerm) {
  // Find the focused hole in the term
  const newValue = fillHole(
    rootDefinition.value,
    focusedHole,
    (holeType, holeContext) => {
      // Replace hole with: let letName : letType := letValue in ?new-hole
      return mkLet(
        letName,
        letType,
        letValue,
        mkHole(`after-${letName}`, holeType, holeContext)
      );
    }
  );
  
  setRootDefinition({ ...rootDefinition, value: newValue });
  setFocusedHole(`after-${letName}`);
}
```

### Phase 5: Update Rule Application

When applying a rule to transform an expression:

```typescript
function applyRule(rule: Rule, params: any) {
  // Get the focused hole
  const hole = findHole(rootDefinition.value, focusedHole);
  if (!hole) return;
  
  // Apply the transformation
  const newProofTerm = buildProofStep(
    rule,
    params,
    hole.type,
    hole.context
  );
  
  // Fill the hole with the new proof term
  const newValue = fillHole(
    rootDefinition.value,
    focusedHole,
    () => newProofTerm
  );
  
  setRootDefinition({ ...rootDefinition, value: newValue });
}
```

### Phase 6: Update UI Components

#### Remove:
- `activeProofContext` state
- `letProofTerms` map
- Global vs. local proof distinction
- Proof context switching logic

#### Update:
- `LetManager`: No longer manages separate proof workspaces
- `TTViewer`: Display the `TermDefinition` structure
- `EnhancedProofWorkspace`: Single proof workspace for focused hole

## Benefits

1. **Simpler State**: No more complex context switching and ID management
2. **True Representation**: The UI matches the actual TT term structure
3. **Natural Nesting**: Let-bindings are naturally nested in the term
4. **Hole-Based Focus**: Clear what you're working on (a hole), not abstract "contexts"
5. **Lean Compatibility**: Matches how Lean actually works

## Migration Strategy

1. Create new types alongside old ones
2. Add new state management parallel to existing
3. Gradually migrate UI components
4. Remove old code once new system works
5. Clean up and refactor

## Files to Modify

### Core Types
- `src/types/tt-core.ts` - Add `TermDefinition`, update constructors
- `src/types/tt-typecheck.ts` - Add `findHole()`, `fillHole()` helpers

### Bridge Layer  
- `src/types/tt-bridge.ts` - Update proof term construction

### UI Components
- `src/components/EnhancedProofWorkspace.tsx` - Major refactor
- `src/components/LetManager.tsx` - Simplify (no proof workspaces)
- `src/components/TTViewer.tsx` - Display term definitions

### Types
- `src/types/enhanced-focus.ts` - Remove proof context types
- `src/types/let-system.ts` - Simplify let-binding types

## Open Questions

1. **Multiple term definitions?** Should we support multiple top-level definitions?
2. **Let-binding editor modes?** How do equality-chaining and cases fit in?
3. **Proof completion?** How do we know when a term is fully proven (no holes)?
4. **UI for hole selection?** Best way to visualize and select holes?

## Next Steps

1. Review this design document
2. Get feedback on architecture
3. Start with Phase 1: Create basic `TermDefinition` type
4. Iterate through phases incrementally
5. Test thoroughly at each step

