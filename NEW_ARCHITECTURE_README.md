# New Workspace Architecture - Complete Guide

## 🎯 What This Is

A complete refactoring of the LeanUI workspace system based on the principle:

> **The entire workspace is a single term with a type signature and implementation.**

## 📦 What Was Delivered

### Core Infrastructure

1. **[EditableTerm](src/types/tt-core.ts#L1865-L2055)** - Immutable class for editing term definitions
   - Destructures type into hypotheses + goal
   - Provides safe, immutable methods for editing
   - Automatically reconstructs valid term definitions

2. **[DefinitionFocus](src/types/definition-focus.ts)** - Unified focus system
   - `{ tag: 'hypothesis' | 'goal' | 'body', path: TermPath }`
   - Replaces scattered focus state
   - Uses same TermPath as TT engine

3. **[NavigationController](src/types/definition-focus.ts#L126-L243)** - Immutable navigation state
   - Clean API for focus management
   - Keyboard navigation built-in
   - No UI dependencies

### React Layer

4. **[useEditableTerm](src/hooks/useEditableTerm.ts)** - State management hook
   - Flux-like dispatch pattern
   - Optional undo/redo
   - Type-safe actions

5. **[useDefinitionNavigation](src/hooks/useDefinitionNavigation.ts)** - Navigation hook
   - Keyboard shortcuts (↑↓jk, 0-9)
   - Focus management
   - Change notifications

6. **[SimpleWorkspace](src/components/SimpleWorkspace.tsx)** - Working example
   - Demonstrates all features
   - Only ~200 lines vs ~1000+ old code
   - Minimal React state

### Documentation

7. **[NEW_ARCHITECTURE.md](docs/NEW_ARCHITECTURE.md)** - Comprehensive overview
8. **[ARCHITECTURE_DIAGRAM.md](docs/ARCHITECTURE_DIAGRAM.md)** - Visual diagrams
9. **[MIGRATION_GUIDE.md](docs/MIGRATION_GUIDE.md)** - Step-by-step migration
10. **[REFACTORING_SUMMARY.md](REFACTORING_SUMMARY.md)** - What was done

## 🚀 Quick Start

### Try the New System

```bash
npm run dev
```

Then import and use `SimpleWorkspace` to see the new architecture in action.

### Use in Your Code

```typescript
import { EditableTerm, createRootTermDefinition, mkProp, mkHole } from './types/tt-core';
import { useEditableTerm } from './hooks/useEditableTerm';
import { useDefinitionNavigation } from './hooks/useDefinitionNavigation';

function MyWorkspace() {
  // Create initial term
  const initialTerm = useMemo(() => {
    const def = createRootTermDefinition(
      'myTheorem',
      [['a', Real], ['b', Real]],
      parseGoal('a + b = b + a'),
      mkHole('proof', mkProp(), [])
    );
    return EditableTerm.fromTermDefinition(def);
  }, []);

  // State management
  const { term, dispatch } = useEditableTerm(initialTerm);

  // Navigation
  const nav = useDefinitionNavigation({
    numHypotheses: term.hypotheses.length
  });

  // Add hypothesis
  const addHyp = () => {
    dispatch({
      type: 'addHypothesis',
      index: term.hypotheses.length,
      name: 'h',
      hypothesisType: Real
    });
  };

  // Render
  return (
    <div>
      <h2>Hypotheses</h2>
      {term.hypotheses.map(([name, type], i) => (
        <div
          key={i}
          style={{
            border: nav.focus?.tag === 'hypothesis' &&
                   nav.focus.hypothesisIndex === i
                   ? '2px solid blue' : 'none'
          }}
          onClick={() => nav.focusHypothesis(i)}
        >
          {name}: {prettyPrint(type)}
        </div>
      ))}

      <h2>Goal</h2>
      <div onClick={() => nav.focusGoal()}>
        {prettyPrint(term.goal)}
      </div>

      <h2>Body</h2>
      <div onClick={() => nav.focusBody()}>
        {prettyPrint(term.body)}
      </div>
    </div>
  );
}
```

## 📊 Benefits

| Aspect | Before | After |
|--------|--------|-------|
| React state | 15+ pieces | 2 pieces |
| Lines of code | ~1000+ | ~200 |
| State updates | Direct mutations | Immutable dispatch |
| Focus system | Scattered state | Unified DefinitionFocus |
| Testability | Hard | Easy (pure functions) |
| Type safety | Partial | Complete |

## 🏗️ Architecture Layers

```
┌─────────────────────────────────┐
│     React Components            │  UI layer
│  (SimpleWorkspace, etc.)        │
└────────────┬────────────────────┘
             │
┌────────────▼────────────────────┐
│     React Hooks                 │  State management
│  (useEditableTerm,              │
│   useDefinitionNavigation)      │
└────────────┬────────────────────┘
             │
┌────────────▼────────────────────┐
│     Domain Layer                │  Pure TypeScript
│  (EditableTerm,                 │  No UI dependencies
│   NavigationController)         │
└────────────┬────────────────────┘
             │
┌────────────▼────────────────────┐
│     TT Engine                   │  Core term representation
│  (TTerm, TermPath,              │
│   path navigation)              │
└─────────────────────────────────┘
```

## 📚 Documentation Index

### Getting Started
- **[REFACTORING_SUMMARY.md](REFACTORING_SUMMARY.md)** - Start here! Overview of what was done

### Understanding the Architecture
- **[NEW_ARCHITECTURE.md](docs/NEW_ARCHITECTURE.md)** - Detailed architecture documentation
- **[ARCHITECTURE_DIAGRAM.md](docs/ARCHITECTURE_DIAGRAM.md)** - Visual diagrams and data flow

### Using the New System
- **[MIGRATION_GUIDE.md](docs/MIGRATION_GUIDE.md)** - How to migrate existing code
- **[SimpleWorkspace.tsx](src/components/SimpleWorkspace.tsx)** - Working example

### API Reference
All types, classes, and functions are documented in:
- [src/types/tt-core.ts](src/types/tt-core.ts#L1865-L2055) - EditableTerm
- [src/types/definition-focus.ts](src/types/definition-focus.ts) - DefinitionFocus, NavigationController
- [src/hooks/useEditableTerm.ts](src/hooks/useEditableTerm.ts) - State hook
- [src/hooks/useDefinitionNavigation.ts](src/hooks/useDefinitionNavigation.ts) - Navigation hook

## 🎯 Design Principles

1. **Single Source of Truth** - EditableTerm is the canonical state
2. **Immutability** - All updates return new instances
3. **Separation of Concerns** - TT engine ↔ Navigation ↔ UI
4. **Type Safety** - Leverage TypeScript
5. **Testability** - Pure functions, simple state machines
6. **Minimal React State** - Just EditableTerm + NavigationController
7. **Flux-like** - Dispatch actions, not direct mutations

## 🧪 Testing

All core functionality can be tested without React:

```typescript
// Test EditableTerm
const term = EditableTerm.fromTermDefinition(def);
const updated = term.addHypothesis(0, 'a', Real);
expect(updated.hypotheses).toHaveLength(1);

// Test NavigationController
const nav = new NavigationController(3);
const next = nav.cycleNext();
expect(next.getFocus()?.tag).toBe('hypothesis');

// Test with React hooks
const { result } = renderHook(() => useEditableTerm(initialTerm));
act(() => result.current.dispatch({ type: 'addHypothesis', ... }));
```

## 🔄 Migration Status

- ✅ Core infrastructure complete
- ✅ Documentation complete
- ✅ Example component complete
- ✅ Type checking passing
- ⏳ Migration of EnhancedProofWorkspace (next step)
- ⏳ Command system integration (next step)
- ⏳ Full test coverage (next step)

## 🛠️ Next Steps

### Phase 1: Integration (TODO)
1. Update EnhancedProofWorkspace to use EditableTerm
2. Migrate hypothesis commands
3. Migrate goal commands
4. Migrate body/let-binding commands

### Phase 2: Cleanup (TODO)
1. Remove old FocusPath system
2. Remove old navigation state
3. Simplify NavigationContext
4. Remove deprecated code

### Phase 3: Enhancement (TODO)
1. Deep term editing within sections
2. Integrate with term editor
3. Add more keyboard shortcuts
4. Improve visual feedback

## 🤝 Contributing

When adding new features:

1. **TT Engine** - Add to `tt-core.ts` if it's pure term manipulation
2. **Navigation** - Add to `definition-focus.ts` if it's focus-related
3. **State Management** - Add actions to `EditableTermAction` type
4. **UI** - Keep React components minimal, delegate to hooks

## 📝 Key Files

### Must Read
- [src/types/tt-core.ts](src/types/tt-core.ts) - EditableTerm class (lines 1865-2055)
- [src/types/definition-focus.ts](src/types/definition-focus.ts) - Focus system
- [src/hooks/useEditableTerm.ts](src/hooks/useEditableTerm.ts) - State management
- [src/components/SimpleWorkspace.tsx](src/components/SimpleWorkspace.tsx) - Example

### Reference
- [docs/NEW_ARCHITECTURE.md](docs/NEW_ARCHITECTURE.md) - Architecture details
- [docs/MIGRATION_GUIDE.md](docs/MIGRATION_GUIDE.md) - Migration help

## ❓ FAQ

**Q: Can I still use the old workspace?**
A: Yes! The old system is untouched. The new architecture exists alongside it.

**Q: How do I convert between ExpressionNode and TTerm?**
A: Use `expressionNodeToTTerm()` from `tt-bridge.ts`.

**Q: What about undo/redo?**
A: Built-in! Just use `useEditableTerm(term, { enableHistory: true })`.

**Q: Can I have multiple focuses?**
A: Yes, just maintain multiple `NavigationController` instances.

**Q: How do I navigate deep into terms?**
A: Use `navigateInto(step)` to append to the TermPath.

## 📞 Support

- Read the [docs/NEW_ARCHITECTURE.md](docs/NEW_ARCHITECTURE.md)
- Check the [MIGRATION_GUIDE.md](docs/MIGRATION_GUIDE.md)
- Look at [SimpleWorkspace.tsx](src/components/SimpleWorkspace.tsx) for examples
- Review the inline documentation in source files

## ✨ Summary

This refactoring provides:
- ✅ Clean, principled architecture
- ✅ Minimal React state
- ✅ Immutable, flux-like updates
- ✅ Unified focus system
- ✅ Full type safety
- ✅ Easy testing
- ✅ Comprehensive documentation
- ✅ Working example

The foundation is solid and ready to build on. The old system remains intact, so you can migrate gradually or start new features with the new architecture right away.
