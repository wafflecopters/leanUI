# Migration Guide: Old → New Architecture

This guide helps you migrate from the old workspace architecture to the new EditableTerm-based system.

## Quick Reference

| Old Approach | New Approach |
|-------------|-------------|
| Multiple state variables | Single `EditableTerm` |
| `setHypotheses()`, `setGoal()`, `setBody()` | `dispatch({ type: 'addHypothesis', ... })` |
| `FocusPath` (array of indices) | `DefinitionFocus` (section + path) |
| Manual state synchronization | Immutable updates |
| Navigation context + metadata | `useDefinitionNavigation` |

## Step-by-Step Migration

### Step 1: Replace State with EditableTerm

**Before:**
```typescript
const [hypotheses, setHypotheses] = useState<Assumption[]>([]);
const [goal, setGoal] = useState<ExpressionNode | null>(null);
const [body, setBody] = useState<TTerm | null>(null);
const [letBindings, setLetBindings] = useState<LetElement[]>([]);
```

**After:**
```typescript
import { useEditableTerm } from '../hooks/useEditableTerm';
import { EditableTerm, createRootTermDefinition } from '../types/tt-core';

// Create initial term
const initialTerm = useMemo(() => {
  const def = createRootTermDefinition(
    'workspace',
    [], // initial hypotheses
    mkHole('goal', mkProp(), []),
    mkHole('proof', mkProp(), [])
  );
  return EditableTerm.fromTermDefinition(def);
}, []);

const { term, dispatch } = useEditableTerm(initialTerm);

// Access parts
const hypotheses = term.hypotheses;
const goal = term.goal;
const body = term.body;
```

### Step 2: Replace State Updates with Dispatch

**Before:**
```typescript
const addHypothesis = (name: string, type: TTerm) => {
  setHypotheses([...hypotheses, { id: uuid(), name, type }]);
};

const updateGoal = (newGoal: ExpressionNode) => {
  setGoal(newGoal);
};

const updateBody = (newBody: TTerm) => {
  setBody(newBody);
};
```

**After:**
```typescript
const addHypothesis = (name: string, type: TTerm) => {
  dispatch({
    type: 'addHypothesis',
    index: term.hypotheses.length, // append
    name,
    hypothesisType: type
  });
};

const updateGoal = (newGoal: TTerm) => {
  dispatch({ type: 'updateGoal', goal: newGoal });
};

const updateBody = (newBody: TTerm) => {
  dispatch({ type: 'updateBody', body: newBody });
};
```

### Step 3: Replace Focus with DefinitionFocus

**Before:**
```typescript
const [focusPath, setFocusPath] = useState<FocusPath>([]);
const [focusedSection, setFocusedSection] = useState<string | null>(null);

// Focus on hypothesis
setFocusedSection('hypotheses');
// ... complex logic to track which hypothesis
```

**After:**
```typescript
import { useDefinitionNavigation } from '../hooks/useDefinitionNavigation';

const navigation = useDefinitionNavigation({
  numHypotheses: term.hypotheses.length,
  onFocusChange: (focus) => {
    console.log('Focus changed:', focus);
  }
});

// Focus on hypothesis
navigation.focusHypothesis(0);

// Check current focus
if (navigation.focus?.tag === 'hypothesis') {
  const index = navigation.focus.hypothesisIndex;
  // ... render focused hypothesis
}
```

### Step 4: Update Commands

**Before:**
```typescript
const hypothesisCommands: Command[] = [
  {
    key: 'a',
    label: 'Add hypothesis',
    execute: () => {
      const name = prompt('Name:');
      if (name) {
        setHypotheses([...hypotheses, { id: uuid(), name, type: mkProp() }]);
      }
    }
  }
];
```

**After:**
```typescript
const hypothesisCommands: Command[] = [
  {
    key: 'a',
    label: 'Add hypothesis',
    execute: () => {
      const name = prompt('Name:');
      if (name) {
        dispatch({
          type: 'addHypothesis',
          index: term.hypotheses.length,
          name,
          hypothesisType: mkProp()
        });
      }
    }
  }
];
```

### Step 5: Update Rendering

**Before:**
```typescript
{hypotheses.map((hyp, i) => (
  <div key={hyp.id}>
    {hyp.name}: {prettyPrint(hyp.type)}
  </div>
))}
```

**After:**
```typescript
{term.hypotheses.map((hyp, i) => {
  const [name, type] = hyp;
  const isFocused = navigation.focus?.tag === 'hypothesis'
                 && navigation.focus.hypothesisIndex === i;

  return (
    <div
      key={i}
      style={{ border: isFocused ? '2px solid blue' : 'none' }}
      onClick={() => navigation.focusHypothesis(i)}
    >
      {name}: {prettyPrint(type)}
    </div>
  );
})}
```

## Common Patterns

### Pattern 1: Adding a Hypothesis

**Before:**
```typescript
const newHyp: Assumption = {
  id: crypto.randomUUID(),
  name: 'h',
  expression: 'a > 0',
  description: 'a is positive',
};
setHypotheses([...hypotheses, newHyp]);
```

**After:**
```typescript
dispatch({
  type: 'addHypothesis',
  index: term.hypotheses.length,
  name: 'h',
  hypothesisType: parseExpression('a > 0')  // Convert to TTerm
});
```

### Pattern 2: Removing a Hypothesis

**Before:**
```typescript
setHypotheses(hypotheses.filter((_, i) => i !== indexToRemove));
```

**After:**
```typescript
try {
  dispatch({ type: 'removeHypothesis', index: indexToRemove });
} catch (error) {
  // EditableTerm checks if hypothesis is used
  alert(error.message);
}
```

### Pattern 3: Updating the Goal

**Before:**
```typescript
setGoal(parseExpressionToAST('a + b = b + a'));
```

**After:**
```typescript
dispatch({
  type: 'updateGoal',
  goal: expressionNodeToTTerm(parseExpressionToAST('a + b = b + a'))
});
```

### Pattern 4: Checking if Hypothesis is Focused

**Before:**
```typescript
const isFocused = focusedSection === 'hypotheses' &&
                 metadata?.focusedItemIndex === i;
```

**After:**
```typescript
const isFocused = navigation.focus?.tag === 'hypothesis' &&
                 navigation.focus.hypothesisIndex === i;
```

### Pattern 5: Cycling Through Sections

**Before:**
```typescript
const sections = ['hypotheses', 'goal', 'body'];
const currentIndex = sections.indexOf(focusedSection);
const nextIndex = (currentIndex + 1) % sections.length;
setFocusedSection(sections[nextIndex]);
```

**After:**
```typescript
navigation.cycleNext();
```

## Converting Between UI and TT

You'll still need to convert between `ExpressionNode` (UI) and `TTerm` (TT engine):

```typescript
import { expressionNodeToTTerm } from '../types/tt-bridge';
import { parseExpressionToAST } from '../types/enhanced-focus';

// UI string → ExpressionNode → TTerm
const uiString = 'a + b = b + a';
const exprNode = parseExpressionToAST(uiString);
const ttTerm = expressionNodeToTTerm(exprNode);

// Update goal with TT term
dispatch({ type: 'updateGoal', goal: ttTerm });
```

## Handling Let-Bindings

The body now contains let-bindings as a TTerm structure:

**Before:**
```typescript
const [letBindings, setLetBindings] = useState<LetElement[]>([]);

const addLetBinding = (name: string, value: ExpressionNode) => {
  setLetBindings([...letBindings, {
    id: uuid(),
    type: 'let',
    name,
    value,
    // ... many other fields
  }]);
};
```

**After:**
```typescript
// Body is a TTerm with let-bindings
const addLetBinding = (name: string, valueTerm: TTerm, typeTerm: TTerm) => {
  const currentBody = term.body;

  // Wrap current body in a new let-binding
  const newBody = mkLet(name, typeTerm, valueTerm, currentBody);

  dispatch({ type: 'updateBody', body: newBody });
};

// Extract let-bindings from body
import { flattenLetBindings } from '../types/tt-core';
const letBindings = flattenLetBindings(term.body);
// Returns: Array<[name, type, value, innerBody]>
```

## Keyboard Navigation

**Before:**
```typescript
// Complex setup with NavigationContext, metadata, etc.
useEffect(() => {
  const handler = (e: KeyboardEvent) => {
    // ... lots of manual key handling
  };
  window.addEventListener('keydown', handler);
  return () => window.removeEventListener('keydown', handler);
}, [/* many dependencies */]);
```

**After:**
```typescript
// Just enable keyboard in the hook
const navigation = useDefinitionNavigation({
  numHypotheses: term.hypotheses.length,
  enableKeyboard: true,  // Automatically handles ↑↓jk and 0-9
});
```

## Undo/Redo

**Before:**
```typescript
const [history, setHistory] = useState<State[]>([]);
const [historyIndex, setHistoryIndex] = useState(0);

// Manual history management
const undo = () => {
  if (historyIndex > 0) {
    const prevState = history[historyIndex - 1];
    setHypotheses(prevState.hypotheses);
    setGoal(prevState.goal);
    // ... restore all state
    setHistoryIndex(historyIndex - 1);
  }
};
```

**After:**
```typescript
const { term, dispatch, undo, redo, canUndo, canRedo } = useEditableTerm(
  initialTerm,
  { enableHistory: true }
);

// Undo/redo automatically managed
<button onClick={undo} disabled={!canUndo}>Undo</button>
<button onClick={redo} disabled={!canRedo}>Redo</button>
```

## Complete Example: Migrating a Command

**Before:**
```typescript
const addHypothesisCommand: Command = {
  key: 'a',
  label: 'Add hypothesis',
  execute: (ctx: CommandContext) => {
    return {
      navigationPath: [...ctx.navigationPath, 'add-hypothesis'],
      mode: 'edit',
      metadata: {
        ...ctx.metadata,
        promptForInput: true,
        inputType: 'hypothesis',
      }
    };
  }
};

// Later in component:
if (metadata.promptForInput && metadata.inputType === 'hypothesis') {
  // Show input form
  const handleSubmit = (name: string, expr: string) => {
    setHypotheses([...hypotheses, {
      id: uuid(),
      name,
      expression: expr,
      description: '',
    }]);
    clearNavigation();
  };
}
```

**After:**
```typescript
const addHypothesisCommand: Command = {
  key: 'a',
  label: 'Add hypothesis',
  execute: () => {
    const name = prompt('Hypothesis name:');
    if (!name) return;

    const typeStr = prompt('Type:');
    if (!typeStr) return;

    const typeTerm = expressionNodeToTTerm(
      parseExpressionToAST(typeStr)
    );

    dispatch({
      type: 'addHypothesis',
      index: term.hypotheses.length,
      name,
      hypothesisType: typeTerm
    });
  }
};
```

## Testing

**Before:**
```typescript
test('adds hypothesis', () => {
  const { result } = renderHook(() => {
    const [hypotheses, setHypotheses] = useState([]);
    return { hypotheses, setHypotheses };
  });

  act(() => {
    result.current.setHypotheses([...result.current.hypotheses, newHyp]);
  });

  expect(result.current.hypotheses).toHaveLength(1);
});
```

**After:**
```typescript
test('adds hypothesis', () => {
  const initialTerm = EditableTerm.fromTermDefinition(
    createRootTermDefinition('test', [], mkProp(), mkHole('proof', mkProp(), []))
  );

  const { result } = renderHook(() => useEditableTerm(initialTerm));

  act(() => {
    result.current.dispatch({
      type: 'addHypothesis',
      index: 0,
      name: 'h',
      hypothesisType: mkProp()
    });
  });

  expect(result.current.term.hypotheses).toHaveLength(1);
  expect(result.current.term.hypotheses[0][0]).toBe('h');
});
```

## Checklist

- [ ] Replace multiple state variables with single `EditableTerm`
- [ ] Replace `setX()` calls with `dispatch({ type: ... })`
- [ ] Replace `FocusPath` with `DefinitionFocus`
- [ ] Update command handlers to use dispatch
- [ ] Update rendering to use `term.hypotheses`, `term.goal`, `term.body`
- [ ] Replace manual navigation with `useDefinitionNavigation`
- [ ] Convert between ExpressionNode and TTerm where needed
- [ ] Test all functionality
- [ ] Remove old state management code
- [ ] Update tests to use new hooks

## Resources

- [New Architecture Overview](NEW_ARCHITECTURE.md)
- [Architecture Diagrams](ARCHITECTURE_DIAGRAM.md)
- [SimpleWorkspace Example](../src/components/SimpleWorkspace.tsx)
- [EditableTerm Source](../src/types/tt-core.ts#L1865-L2055)
- [DefinitionFocus Source](../src/types/definition-focus.ts)
