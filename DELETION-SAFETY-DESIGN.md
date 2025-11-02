# Deletion Safety System

## Problem

When a hypothesis like `a : ?type_a` is deleted, but `a` is used in the goal (`a + a = 2 * a`), the system becomes inconsistent. We need to:
1. Check if the variable is used before allowing deletion
2. Block deletion with helpful error if used
3. Provide general machinery for safe deletion

## Design

### Core Usage Checking (TT Layer)

**File: `tt-core.ts`**

```typescript
/**
 * Check if a constant/variable name is referenced in a term
 * 
 * This traverses the entire term tree looking for:
 * - Const nodes with matching name
 * - Binders that bind the name (shadows it, so stops searching in body)
 * 
 * @param name - Variable/constant name to search for
 * @param term - Term to search in
 * @returns true if name is referenced
 */
export function isNameUsed(name: string, term: TTerm): boolean {
  switch (term.tag) {
    case 'Var':
      // De Bruijn index - can't directly check by name
      return false;
      
    case 'Const':
      // Direct name match
      return term.name === name;
      
    case 'Sort':
    case 'Hole':
      // No names to check
      return false;
      
    case 'Binder':
      // Check domain
      if (isNameUsed(name, term.domain)) return true;
      
      // Check let-binding value if present
      if (term.binderKind.tag === 'BLet') {
        if (isNameUsed(name, term.binderKind.defVal)) return true;
      }
      
      // Check body - BUT if this binder binds our name, it shadows it
      if (term.name === name) {
        // Name is shadowed in the body, don't search there
        return false;
      }
      return isNameUsed(name, term.body);
      
    case 'App':
      return isNameUsed(name, term.fn) || isNameUsed(name, term.arg);
      
    case 'Annot':
      return isNameUsed(name, term.term) || isNameUsed(name, term.type);
  }
}
```

### Hypothesis Deletion Safety

**File: `EnhancedProofWorkspace.tsx`**

```typescript
const handleDeleteHypothesis = useCallback((hypothesisId: string) => {
  const hypothesis = context.assumptions.find(h => h.id === hypothesisId);
  if (!hypothesis) return;
  
  // Check if this variable is used in the goal
  const goalTerm = goal ? expressionNodeToTTerm(goal, new Map(), typeContext) : null;
  if (goalTerm && isNameUsed(hypothesis.name, goalTerm)) {
    alert(`Cannot delete hypothesis "${hypothesis.name}": it is used in the goal`);
    return;
  }
  
  // Check if used in root definition
  if (isNameUsed(hypothesis.name, rootDefinition.type) || 
      isNameUsed(hypothesis.name, rootDefinition.value)) {
    alert(`Cannot delete hypothesis "${hypothesis.name}": it is used in the proof`);
    return;
  }
  
  // Safe to delete
  context.setAssumptions(prev => prev.filter(h => h.id !== hypothesisId));
}, [context, goal, rootDefinition]);
```

### Let-Binding Deletion Safety

**File: `EnhancedProofWorkspace.tsx`**

```typescript
const handleDeleteLet = useCallback((letId: string) => {
  const letBinding = letBindings.find(l => l.id === letId);
  if (!letBinding) return;
  
  // Check if this let-binding is used in subsequent let-bindings
  for (const otherLet of letBindings) {
    if (otherLet.id === letId) continue; // Skip self
    
    // Check if otherLet's value uses this let's name
    const otherValue = expressionNodeToTTerm(otherLet.value, new Map(), typeContext);
    if (isNameUsed(letBinding.name, otherValue)) {
      alert(`Cannot delete let-binding "${letBinding.name}": it is used in "${otherLet.name}"`);
      return;
    }
  }
  
  // Check if used in root definition
  if (isNameUsed(letBinding.name, rootDefinition.type) || 
      isNameUsed(letBinding.name, rootDefinition.value)) {
    alert(`Cannot delete let-binding "${letBinding.name}": it is used in the proof`);
    return;
  }
  
  // Safe to delete
  setLetBindings(prev => prev.filter(l => l.id !== letId));
  // Also remove from structured proof, TT term, etc.
  // ... cleanup code ...
}, [letBindings, rootDefinition]);
```

## Enhanced Error Messages

Instead of simple alerts, provide detailed feedback:

```typescript
interface DeletionResult {
  allowed: boolean;
  reason?: string;
  usageLocations?: Array<{
    type: 'goal' | 'hypothesis' | 'let-binding' | 'proof';
    description: string;
  }>;
}

function checkHypothesisDeletion(
  hypothesisName: string,
  goal: TTerm | null,
  rootDefinition: TermDefinition,
  letBindings: LetElement[]
): DeletionResult {
  const usages: Array<{ type: any; description: string }> = [];
  
  // Check goal
  if (goal && isNameUsed(hypothesisName, goal)) {
    usages.push({
      type: 'goal',
      description: `Used in goal expression`
    });
  }
  
  // Check proof
  if (isNameUsed(hypothesisName, rootDefinition.value)) {
    usages.push({
      type: 'proof',
      description: `Used in proof term`
    });
  }
  
  // Check let-bindings
  for (const let of letBindings) {
    const letValue = expressionNodeToTTerm(let.value, new Map(), typeContext);
    if (isNameUsed(hypothesisName, letValue)) {
      usages.push({
        type: 'let-binding',
        description: `Used in let-binding "${let.name}"`
      });
    }
  }
  
  if (usages.length > 0) {
    return {
      allowed: false,
      reason: `Variable "${hypothesisName}" is still in use`,
      usageLocations: usages
    };
  }
  
  return { allowed: true };
}
```

Then display nicely:
```typescript
const result = checkHypothesisDeletion(...);
if (!result.allowed) {
  const message = [
    result.reason,
    '',
    'Used in:',
    ...result.usageLocations.map(loc => `  • ${loc.description}`)
  ].join('\n');
  alert(message);
  return;
}
```

## Future Enhancements

### Visual Feedback
- Disable delete button when variable is used
- Highlight usages when hovering over delete button
- Show dependency graph

### Cascade Deletion
- "Also delete dependent let-bindings?" prompt
- Topological sort of dependencies
- Safe cascade with confirmation

### Undo Stack
- Track deletion operations
- Allow undo
- Preserve deleted items temporarily

## Testing

### Test Cases

```typescript
describe('Deletion Safety', () => {
  it('blocks deletion of hypothesis used in goal', () => {
    const hypothesis = { name: 'a', type: mkHole('type_a', Type_1, []) };
    const goal = parseGoal('a + a = 2 * a');
    
    const result = checkHypothesisDeletion(hypothesis.name, goal, ...);
    
    expect(result.allowed).toBe(false);
    expect(result.usageLocations).toContainEqual({
      type: 'goal',
      description: expect.stringContaining('goal')
    });
  });
  
  it('allows deletion of unused hypothesis', () => {
    const hypothesis = { name: 'b', type: Real };
    const goal = parseGoal('a + a = 2 * a'); // 'b' not used
    
    const result = checkHypothesisDeletion(hypothesis.name, goal, ...);
    
    expect(result.allowed).toBe(true);
  });
  
  it('blocks deletion of let-binding used by another let', () => {
    const let1 = { name: 'x', value: parse('1 + 1') };
    const let2 = { name: 'y', value: parse('x * 2') }; // uses x
    
    const result = checkLetDeletion(let1.name, [let1, let2], ...);
    
    expect(result.allowed).toBe(false);
    expect(result.usageLocations).toContainEqual({
      type: 'let-binding',
      description: expect.stringContaining('y')
    });
  });
  
  it('handles shadowing correctly', () => {
    const hypothesis = { name: 'a', type: Real };
    // Goal: ∀ a, a + a = 2 * a
    // The 'a' in the body is bound by the ∀, not by hypothesis
    const goal = mkPi(Real, parseGoal('a + a = 2 * a'), 'a');
    
    const result = checkHypothesisDeletion(hypothesis.name, goal, ...);
    
    // Should be allowed because 'a' is shadowed
    expect(result.allowed).toBe(true);
  });
});
```

## Implementation Plan

1. ✅ Design complete
2. **Phase 1**: Implement `isNameUsed` in `tt-core.ts`
3. **Phase 2**: Add basic deletion checks to `handleDeleteHypothesis`
4. **Phase 3**: Add deletion checks to `handleDeleteLet`
5. **Phase 4**: Enhanced error messages with usage locations
6. **Phase 5**: Tests
7. **Phase 6**: Visual feedback (disable buttons, etc.)

## Status

📝 Design complete  
🚧 Implementation starting

