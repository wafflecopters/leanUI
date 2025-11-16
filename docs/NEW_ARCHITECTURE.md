# New Workspace Architecture

This document describes the refactored workspace and navigation system for LeanUI.

## Overview

The workspace is now modeled as a **single term definition** with a clean separation between:
1. **Type signature** (hypotheses + goal)
2. **Body** (proof term)

This provides a simpler, more principled approach to editing proofs.

## Core Concepts

### 1. EditableTerm (tt-core.ts)

The `EditableTerm` class provides an immutable, structured interface for editing term definitions.

**Structure:**
```typescript
class EditableTerm {
  readonly name: string;                           // Term name
  readonly hypotheses: ReadonlyArray<[string, TTerm]>;  // Pi-binders from type
  readonly goal: TTerm;                            // Final return type
  readonly body: TTerm;                            // Proof term (definition value)
}
```

**Example:**
```
Term definition:
  theorem : (a: ℝ) → (b: ℝ) → (a + b = b + a)
  theorem = ?proof

Becomes EditableTerm:
  name: "theorem"
  hypotheses: [["a", ℝ], ["b", ℝ]]
  goal: (a + b = b + a)
  body: ?proof
```

**API:**
- `fromTermDefinition(def)` - Create from a TermDefinition
- `toTermDefinition()` - Convert back to TermDefinition
- `addHypothesis(index, name, type)` - Add a hypothesis
- `removeHypothesis(index)` - Remove a hypothesis (with safety checks)
- `updateHypothesis(index, name?, type?)` - Update a hypothesis
- `updateGoal(newGoal)` - Update the goal
- `updateBody(newBody)` - Update the body
- `updateBodyAt(path, newTerm)` - Update body at a specific path

All methods return a **new** EditableTerm instance (immutable).

### 2. DefinitionFocus (definition-focus.ts)

The focus system is now unified and simple:

```typescript
type DefinitionFocus =
  | { tag: 'hypothesis', hypothesisIndex: number, path: TermPath }
  | { tag: 'goal', path: TermPath }
  | { tag: 'body', path: TermPath }
```

**Focus Structure:**
- **Section**: Which part (hypothesis, goal, or body)
- **Index**: Which hypothesis (if applicable)
- **Path**: Deep path within that section (using TermPath from tt-core)

**Examples:**
```typescript
// Focus on first hypothesis
{ tag: 'hypothesis', hypothesisIndex: 0, path: [] }

// Focus on the type of second hypothesis
{ tag: 'hypothesis', hypothesisIndex: 1, path: ['domain'] }

// Focus on the goal
{ tag: 'goal', path: [] }

// Focus on body, nested into a let-binding
{ tag: 'body', path: ['body', 'defVal'] }
```

### 3. NavigationController (definition-focus.ts)

Manages focus navigation with immutable updates:

```typescript
class NavigationController {
  getFocus(): DefinitionFocus | null
  setFocus(focus): NavigationController
  focusHypothesisAt(index, path?): NavigationController
  focusGoal(path?): NavigationController
  focusBody(path?): NavigationController
  cycleNext(): NavigationController
  cyclePrevious(): NavigationController
  navigateInto(step): NavigationController
  navigateUp(): NavigationController
}
```

**Navigation order:**
```
hypotheses[0] → hypotheses[1] → ... → hypotheses[n] → goal → body → [wrap to hypotheses[0]]
```

## React Integration

### useEditableTerm Hook

Manages EditableTerm state with a flux-like dispatch pattern:

```typescript
const { term, dispatch, toTermDefinition } = useEditableTerm(initialTerm);

// Add hypothesis
dispatch({
  type: 'addHypothesis',
  index: 0,
  name: 'a',
  hypothesisType: Real
});

// Update goal
dispatch({
  type: 'updateGoal',
  goal: newGoalTerm
});

// Update body
dispatch({
  type: 'updateBody',
  body: newBodyTerm
});
```

**Actions:**
- `addHypothesis` - Add a hypothesis at index
- `removeHypothesis` - Remove hypothesis at index
- `updateHypothesis` - Update hypothesis name/type
- `updateGoal` - Update the goal
- `updateBody` - Replace entire body
- `updateBodyAt` - Update body at path
- `replaceAll` - Replace entire term

**Optional features:**
- `enableHistory: true` - Enable undo/redo
- `onChange` - Callback on term changes

### useDefinitionNavigation Hook

Manages focus and keyboard navigation:

```typescript
const navigation = useDefinitionNavigation({
  numHypotheses: term.hypotheses.length,
  onFocusChange: (focus) => { ... },
  enableKeyboard: true,
});

// Current focus
navigation.focus  // DefinitionFocus | null

// Methods
navigation.focusHypothesis(0)
navigation.focusGoal()
navigation.focusBody()
navigation.cycleNext()
navigation.cyclePrevious()
navigation.selectByNumber(3)  // Numeric selection

// State
navigation.currentSection  // 'hypothesis' | 'goal' | 'body' | null
navigation.currentHypothesisIndex  // number | null
```

**Keyboard shortcuts:**
- `↑/↓` or `j/k` - Cycle between sections
- `0-9` - Select by number
- `Escape` - Clear focus

## Usage Example

```typescript
import { SimpleWorkspace } from './components/SimpleWorkspace';

function App() {
  return <SimpleWorkspace />;
}
```

See `SimpleWorkspace.tsx` for a complete working example.

## Architecture Benefits

### 1. Clear Separation of Concerns

**TT Engine (`tt-core.ts`):**
- Term representation (TTerm, TermDefinition)
- Term manipulation (path navigation, updates)
- EditableTerm class (structured editing)
- Pure functions, no UI dependencies

**Navigation (`definition-focus.ts`):**
- Focus representation (DefinitionFocus)
- Navigation logic (NavigationController)
- No UI dependencies, just state management

**React Layer (`hooks/`, `components/`):**
- State management (useEditableTerm, useDefinitionNavigation)
- UI rendering
- Minimal React state (just term + focus)

### 2. Immutable, Flux-like Updates

**Old approach:**
```typescript
// Scattered state
const [hypotheses, setHypotheses] = useState(...)
const [goal, setGoal] = useState(...)
const [body, setBody] = useState(...)
const [focusPath, setFocusPath] = useState(...)
const [focusedSection, setFocusedSection] = useState(...)
// ... many more pieces of state
```

**New approach:**
```typescript
// Single source of truth
const { term, dispatch } = useEditableTerm(initialTerm);
const navigation = useDefinitionNavigation({ numHypotheses: term.hypotheses.length });

// All updates through dispatch
dispatch({ type: 'addHypothesis', ... });
```

### 3. Type Safety

- EditableTerm enforces valid term structures
- DefinitionFocus ensures valid focus states
- TypeScript catches errors at compile time
- Immutable updates prevent accidental mutations

### 4. Testability

Each layer can be tested independently:
- TT engine: Pure functions, easy to test
- Navigation: Immutable state transitions
- React hooks: Can test with React Testing Library

### 5. Reduced Complexity

**Lines of code comparison:**
- Old workspace component: ~1000+ lines
- New SimpleWorkspace: ~200 lines
- Core logic: Moved to reusable, testable modules

**State management:**
- Old: ~15+ pieces of React state
- New: 2 pieces (term + navigation controller)

## Migration Path

### Phase 1: Core Infrastructure ✅
- [x] EditableTerm class
- [x] DefinitionFocus types
- [x] NavigationController
- [x] React hooks
- [x] SimpleWorkspace example

### Phase 2: Integration (TODO)
- [ ] Update EnhancedProofWorkspace to use new architecture
- [ ] Migrate hypothesis commands
- [ ] Migrate goal commands
- [ ] Migrate body/let-binding commands

### Phase 3: Cleanup (TODO)
- [ ] Remove old FocusPath system
- [ ] Remove old navigation state
- [ ] Simplify NavigationContext
- [ ] Remove deprecated code

### Phase 4: Enhancement (TODO)
- [ ] Add deep term editing within each section
- [ ] Integrate with term editor
- [ ] Add more keyboard shortcuts
- [ ] Improve visual feedback

## API Reference

### EditableTerm

```typescript
class EditableTerm {
  // Static factories
  static fromTermDefinition(def: TermDefinition): EditableTerm

  // Conversions
  toTermDefinition(): TermDefinition

  // Hypothesis operations
  addHypothesis(index: number, name: string, type: TTerm): EditableTerm
  removeHypothesis(index: number): EditableTerm
  updateHypothesis(index: number, name?: string, type?: TTerm): EditableTerm
  getHypothesis(index: number): [string, TTerm] | undefined
  getHypothesisByName(name: string): [string, TTerm] | undefined
  getHypothesisIndex(name: string): number

  // Goal operations
  updateGoal(newGoal: TTerm): EditableTerm

  // Body operations
  updateBody(newBody: TTerm): EditableTerm
  updateBodyAt(path: TermPath, newTerm: TTerm): EditableTerm
}
```

### DefinitionFocus

```typescript
type DefinitionFocus = HypothesisFocus | GoalFocus | BodyFocus

interface HypothesisFocus {
  tag: 'hypothesis'
  hypothesisIndex: number
  path: TermPath
}

interface GoalFocus {
  tag: 'goal'
  path: TermPath
}

interface BodyFocus {
  tag: 'body'
  path: TermPath
}

// Utilities
function focusHypothesis(index: number, path?: TermPath): HypothesisFocus
function focusGoal(path?: TermPath): GoalFocus
function focusBody(path?: TermPath): BodyFocus
function describeFocus(focus: DefinitionFocus): string
function focusEquals(a: DefinitionFocus, b: DefinitionFocus): boolean
```

### NavigationController

```typescript
class NavigationController {
  constructor(numHypotheses: number, initialFocus?: DefinitionFocus | null)

  getFocus(): DefinitionFocus | null
  setFocus(focus: DefinitionFocus | null): NavigationController
  setNumHypotheses(num: number): NavigationController

  focusHypothesisAt(index: number, path?: TermPath): NavigationController
  focusGoal(path?: TermPath): NavigationController
  focusBody(path?: TermPath): NavigationController

  cycleNext(): NavigationController
  cyclePrevious(): NavigationController
  navigateInto(step: TermPath[number]): NavigationController
  navigateUp(): NavigationController
  clearFocus(): NavigationController

  getCurrentSection(): 'hypothesis' | 'goal' | 'body' | null
  getCurrentHypothesisIndex(): number | null
}
```

### useEditableTerm

```typescript
function useEditableTerm(
  initialTerm: EditableTerm,
  options?: {
    enableHistory?: boolean
    maxHistorySize?: number
    onChange?: (term: EditableTerm) => void
  }
): {
  term: EditableTerm
  dispatch: (action: EditableTermAction) => void
  toTermDefinition: () => TermDefinition
  setTerm: (term: EditableTerm) => void
  undo?: () => void
  redo?: () => void
  canUndo?: boolean
  canRedo?: boolean
}
```

### useDefinitionNavigation

```typescript
function useDefinitionNavigation(options: {
  numHypotheses: number
  initialFocus?: DefinitionFocus | null
  onFocusChange?: (focus: DefinitionFocus | null) => void
  enableKeyboard?: boolean
  shouldHandleKeyboard?: () => boolean
}): {
  focus: DefinitionFocus | null
  setFocus: (focus: DefinitionFocus | null) => void
  focusHypothesis: (index: number) => void
  focusGoal: () => void
  focusBody: () => void
  cycleNext: () => void
  cyclePrevious: () => void
  navigateInto: (step: any) => void
  navigateUp: () => void
  clearFocus: () => void
  getFocusDescription: () => string
  selectByNumber: (num: number) => void
  currentSection: 'hypothesis' | 'goal' | 'body' | null
  currentHypothesisIndex: number | null
}
```

## Design Principles

1. **Single Source of Truth**: EditableTerm is the canonical representation
2. **Immutability**: All updates return new instances
3. **Separation of Concerns**: TT engine, navigation, and UI are independent
4. **Type Safety**: Leverage TypeScript for correctness
5. **Testability**: Pure functions and simple state machines
6. **Minimal React State**: Only EditableTerm and NavigationController
7. **Flux-like Updates**: Dispatch actions, not direct mutations
8. **Progressive Enhancement**: Can add features without breaking existing code

## Future Enhancements

1. **Deep Term Editing**: Navigate into term structure with paths
2. **Term Editor Integration**: Edit terms at any path
3. **Rule Application**: Apply rules at focused locations
4. **Undo/Redo**: Full history with branching
5. **Serialization**: Save/load workspace state
6. **Collaboration**: Multiple cursors/focuses
7. **Accessibility**: Screen reader support, keyboard-only navigation
8. **Performance**: Memoization, virtualization for large proofs
