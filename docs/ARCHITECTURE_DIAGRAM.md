# Architecture Diagram

## System Overview

```
┌─────────────────────────────────────────────────────────────┐
│                         React UI Layer                       │
│                                                               │
│  ┌──────────────────┐      ┌──────────────────┐            │
│  │  SimpleWorkspace │      │ EnhancedWorkspace│            │
│  │   (new example)  │      │  (to be updated) │            │
│  └────────┬─────────┘      └────────┬─────────┘            │
│           │                          │                       │
│           ├──────────────────────────┤                       │
│           │                          │                       │
│  ┌────────▼──────────┐      ┌────────▼─────────┐           │
│  │ useEditableTerm   │      │useDefinitionNav  │           │
│  │                   │      │                  │           │
│  │ - term: EditableTerm    │ - focus          │           │
│  │ - dispatch()      │      │ - cycleNext()    │           │
│  └────────┬──────────┘      └────────┬─────────┘           │
└───────────┼──────────────────────────┼──────────────────────┘
            │                          │
            │                          │
┌───────────▼──────────────────────────▼──────────────────────┐
│                    Domain Layer (Pure TS)                    │
│                                                               │
│  ┌──────────────────────┐   ┌──────────────────────┐        │
│  │   EditableTerm       │   │  NavigationController│        │
│  │   (tt-core.ts)       │   │  (definition-focus)  │        │
│  │                      │   │                      │        │
│  │  hypotheses: [name,  │   │  focus: Definition   │        │
│  │              type][] │   │         Focus        │        │
│  │  goal: TTerm         │   │                      │        │
│  │  body: TTerm         │   │  Methods:            │        │
│  │                      │   │  - cycleNext()       │        │
│  │  Methods:            │   │  - focusHypothesis() │        │
│  │  - addHypothesis()   │   │  - navigateInto()    │        │
│  │  - updateGoal()      │   │                      │        │
│  │  - updateBody()      │   │                      │        │
│  └──────────┬───────────┘   └──────────────────────┘        │
│             │                                                 │
│             │                                                 │
│  ┌──────────▼─────────────────────────────────────────┐     │
│  │              TT Engine (tt-core.ts)                 │     │
│  │                                                      │     │
│  │  - TTerm (term representation)                      │     │
│  │  - TermPath (path into terms)                       │     │
│  │  - getAtPath(), updateAtPath()                      │     │
│  │  - flattenPiBinders(), getFinalReturnType()         │     │
│  └──────────────────────────────────────────────────────┘     │
└───────────────────────────────────────────────────────────────┘
```

## Data Flow

### 1. Initialization

```
TermDefinition
    ↓
EditableTerm.fromTermDefinition()
    ↓
useEditableTerm(initialTerm)
    ↓
Component receives { term, dispatch }
```

### 2. User Actions

```
User Action (e.g., "Add Hypothesis")
    ↓
dispatch({
  type: 'addHypothesis',
  index: 0,
  name: 'a',
  hypothesisType: Real
})
    ↓
EditableTerm.addHypothesis()
    ↓
New EditableTerm instance
    ↓
React re-renders with new term
```

### 3. Navigation

```
Keyboard Input (↓ or j)
    ↓
useDefinitionNavigation.cycleNext()
    ↓
NavigationController.cycleNext()
    ↓
New focus: DefinitionFocus
    ↓
React re-renders with focus highlight
```

## State Structure

### Old Architecture (Complex)

```
Component State:
├── hypotheses: Assumption[]
├── goal: ExpressionNode | null
├── body: LetElement[]
├── focusPath: FocusPath
├── focusedSectionId: string | null
├── navigationPath: string[]
├── mode: InputMode
├── metadata: Record<string, any>
├── modalStack: string[]
├── activeLetId: string | null
├── proofElements: ProofElement[]
├── history: ProofStep[]
├── historyIndex: number
└── ... ~10 more pieces of state
```

### New Architecture (Simple)

```
Component State:
├── term: EditableTerm
│   ├── hypotheses: [name, type][]
│   ├── goal: TTerm
│   └── body: TTerm
└── navigation: NavigationController
    └── focus: DefinitionFocus | null
        ├── tag: 'hypothesis' | 'goal' | 'body'
        ├── hypothesisIndex?: number
        └── path: TermPath
```

## DefinitionFocus Structure

```
DefinitionFocus =
  | HypothesisFocus
  | GoalFocus
  | BodyFocus

┌─────────────────────────────────────┐
│        HypothesisFocus              │
│                                     │
│  tag: 'hypothesis'                  │
│  hypothesisIndex: number            │
│  path: TermPath                     │
│                                     │
│  Example:                           │
│  { tag: 'hypothesis',               │
│    hypothesisIndex: 0,              │
│    path: ['domain'] }               │
│  → Focus on type of first hypothesis│
└─────────────────────────────────────┘

┌─────────────────────────────────────┐
│           GoalFocus                 │
│                                     │
│  tag: 'goal'                        │
│  path: TermPath                     │
│                                     │
│  Example:                           │
│  { tag: 'goal',                     │
│    path: [] }                       │
│  → Focus on entire goal             │
└─────────────────────────────────────┘

┌─────────────────────────────────────┐
│           BodyFocus                 │
│                                     │
│  tag: 'body'                        │
│  path: TermPath                     │
│                                     │
│  Example:                           │
│  { tag: 'body',                     │
│    path: ['body', 'defVal'] }       │
│  → Focus on let-binding value       │
└─────────────────────────────────────┘
```

## Term Structure

```
EditableTerm:
  name: "theorem"

  hypotheses: [
    ["a", TTerm(Real)],
    ["b", TTerm(Real)],
    ["h", TTerm(a > 0)]
  ]

  goal: TTerm(a + b = b + a)

  body: TTerm(
    let proof1 = ... in
    let proof2 = ... in
    ...
  )

Converts to/from:

TermDefinition:
  name: "theorem"
  type: (a: R) → (b: R) → (h: a > 0) → (a + b = b + a)
  value: let proof1 = ... in let proof2 = ... in ...
```

## Navigation Flow

```
                    ┌───────────┐
                    │   Start   │
                    └─────┬─────┘
                          │
                    ┌─────▼─────┐
                    │ Hypothesis│
                    │     0     │
                    └─────┬─────┘
                          │ cycleNext()
                    ┌─────▼─────┐
                    │ Hypothesis│
                    │     1     │
                    └─────┬─────┘
                          │ cycleNext()
                    ┌─────▼─────┐
                    │ Hypothesis│
                    │     2     │
                    └─────┬─────┘
                          │ cycleNext()
                    ┌─────▼─────┐
                    │   Goal    │
                    └─────┬─────┘
                          │ cycleNext()
                    ┌─────▼─────┐
                    │   Body    │
                    └─────┬─────┘
                          │ cycleNext()
                          │ (wraps)
                    ┌─────▼─────┐
                    │ Hypothesis│
                    │     0     │
                    └───────────┘
```

## Benefits

### Before (Old Architecture)

```
15+ pieces of React state
↓
Complex synchronization
↓
Hard to test
↓
Bugs from state inconsistencies
↓
~1000+ lines of code
```

### After (New Architecture)

```
2 pieces of state (EditableTerm + NavigationController)
↓
Immutable updates
↓
Easy to test (pure functions)
↓
Type-safe, no inconsistencies possible
↓
~200 lines of code
```

## Extensibility

The new architecture makes it easy to add features:

```
Future Features:
├── Undo/Redo
│   └── Already built into useEditableTerm
│       with enableHistory: true
│
├── Deep Term Navigation
│   └── navigateInto(step) already supports
│       arbitrary TermPath navigation
│
├── Multiple Cursors
│   └── Just maintain multiple DefinitionFocus
│       instances
│
├── Serialization
│   └── term.toTermDefinition() → JSON
│       JSON → EditableTerm.fromTermDefinition()
│
└── Collaboration
    └── Operational transforms on
        EditableTermAction
```

## Testing

```
TT Engine Tests:
├── test EditableTerm methods
├── test path navigation
└── test term reconstruction

Navigation Tests:
├── test NavigationController.cycleNext()
├── test focus transitions
└── test path updates

React Tests:
├── test useEditableTerm dispatch
├── test useDefinitionNavigation hooks
└── test SimpleWorkspace rendering
```
