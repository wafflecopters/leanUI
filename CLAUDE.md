# Claude Code Guidelines for LeanUI

## Language Specification

The file `language-spec.md` documents the surface syntax of the LeanUI language. **When making changes to the parser or surface syntax, update `language-spec.md` to reflect those changes.**

This includes:
- Adding new syntax forms (e.g., new binder types, operators)
- Changing existing syntax (e.g., modifying how multi-parameter binders work)
- Removing deprecated syntax

---

## Term Representation Layers (TT vs TTK)

This project has multiple layers of term representation. Understanding these is critical:

### The Pipeline

```
Source Text --parse--> TT --elaborate--> TTK --future--> ULT
                       ↑                  ↑              ↑
                   Surface            Kernel        Untyped
                   Syntax             Terms         Lambda Terms
```

### TT (Typed Terms - Surface)

- **Location**: `src/types/tt-core.ts`
- **Purpose**: Surface-level representation, may include syntactic sugar
- **Types**: `TTerm`, `TPattern`, `TClause`, `BinderKind`
- **Used by**: Parser output, UI display

### TTK (Typed Terms - Kernel)

- **Location**: `src/types/tt-kernel.ts`
- **Purpose**: Elaborated/desugared form - the "ground truth" for verification
- **Types**: `TTKTerm`, `TTKClause`, `TTKBinderKind`, `TTKContext`
- **Used by**: Type checker, recursion checker, all verification passes

### Key Rule: All Checking Happens in TTK

**Type checking, unification, termination checking, and any other verification
must operate on `TTKTerm`, not `TTerm`.**

The kernel is designed to be simple and trustworthy. Surface syntax conveniences
are elaborated away before checking.

### ULT (Untyped Lambda Terms) - Future

Will be the compilation target for interpretation. Types are erased at this stage.

---

## React Hooks: Keep Them Simple

React hooks should be **thin wrappers** that delegate to pure helper/utility functions. Avoid putting complex logic directly inside hooks.

### Why?

1. **Testability**: Pure functions are easier to unit test than hooks
2. **Debuggability**: When logic is in a pure function, you can trace through it step-by-step without React's batching/timing complications
3. **Reusability**: Pure functions can be used in multiple hooks or outside React entirely
4. **Readability**: Hooks become a clear "glue layer" between React and business logic

### Bad: Logic inside hooks

```typescript
const executeCommand = useCallback((key: string): boolean => {
  // 50+ lines of complex navigation logic here
  setState(prev => {
    let newPath: string[];
    let newTransientIndices = new Set(prev.transientSegmentIndices);

    if (result.navigationPath !== undefined) {
      newPath = result.navigationPath;
      newTransientIndices = NavigationUtils.pruneTransientIndices(newTransientIndices, newPath.length);

      if (command.transient && newPath.length > prev.navigationPath.length) {
        newTransientIndices.add(newPath.length - 1);
      }
      // ... more complex logic
    }
    // ... etc
  });
}, [commandTree, state, popModal]);
```

### Good: Delegate to pure functions

```typescript
// Pure function - easy to test and debug
function computeNextNavigationState(
  prevState: NavigationState,
  command: Command,
  result: CommandResult
): NavigationState {
  // All the complex logic here, fully testable
}

// Hook is a thin wrapper
const executeCommand = useCallback((key: string): boolean => {
  const command = commandTree.findCommand(key, state.navigationPath);
  if (!command) return false;

  const result = command.execute(context);
  if (result) {
    setState(prev => computeNextNavigationState(prev, command, result));
  }
  return true;
}, [commandTree, state]);
```

### Apply This To:

- `useCallback` handlers
- `useEffect` side effects
- `useState` setter functions
- Any hook with more than ~10 lines of logic

Extract the logic into a pure function in a `utils/` file, then call it from the hook.

## Architectural Principles: Avoid Duplication Through Abstraction

### Recognize Patterns Early

When implementing a feature for one context (e.g., editing an inductive type's signature), ask: "Will this same operation be needed elsewhere?" If yes, build the abstraction immediately.

### The Duplication Anti-Pattern

**Bad**: Copy-pasting code with slightly different variable names.

```typescript
// In InductiveTypeEditor.tsx
function createTypeEditingCommands(): Command[] {
  return [
    createCommand('wrap-arg', 'a', 'Arg (Pi)', (context) => {
      const type = context.metadata?.inductiveType;        // Different key
      const setType = context.metadata?.setInductiveType;  // Different key
      // ... exact same logic ...
    }),
  ];
}

// In ConstructorsSection.tsx - COPY-PASTED with different keys!
function createConstructorTypeEditingCommands(): Command[] {
  return [
    createCommand('ctor-wrap-arg', 'a', 'Arg (Pi)', (context) => {
      const type = context.metadata?.selectedConstructorType;  // Different key
      const setType = context.metadata?.setSelectedConstructorType;  // Different key
      // ... exact same logic ...
    }),
  ];
}
```

This leads to:
1. **Divergent bugs**: Fix a bug in one copy, forget the other
2. **Maintenance burden**: Every change must be made N times
3. **Inconsistent behavior**: Copies drift apart over time

### The Abstraction Solution

**Good**: Create a standardized interface that any context can implement.

```typescript
// utils/typeEditingCommands.ts

// 1. Define a standard context interface
export interface TypeEditingContext {
  term: TTerm;
  focusPath: TermFocusPath;
  setTerm: (t: TTerm) => void;
  setFocusPath: (p: TermFocusPath) => void;
  returnPath: string[];          // Where to navigate after actions
  editBinderNamePath: string[];  // Where to navigate for binder renaming
}

// 2. Define standard metadata keys
export const TYPE_EDITING_KEYS = {
  term: 'typeEditing.term',
  focusPath: 'typeEditing.focusPath',
  setTerm: 'typeEditing.setTerm',
  // ...
} as const;

// 3. Create ONE set of commands that reads from the standard keys
export function createTypeEditingCommands(): Command[] {
  return [
    createCommand('type-wrap-arg', 'a', 'Arg (Pi)', (context) => {
      const ctx = getTypeEditingContext(context);  // Read standard keys
      if (!ctx) return { preventDefault: true };
      // ... single implementation of the logic ...
      return { navigationPath: ctx.returnPath, preventDefault: true };
    }),
  ];
}
```

Then each consumer just populates the standard metadata keys:

```typescript
// InductiveTypeEditor
navigation.updateMetadata({
  [TYPE_EDITING_KEYS.term]: inductiveDef.type,
  [TYPE_EDITING_KEYS.setTerm]: (t) => setInductiveDef(prev => ({ ...prev, type: t })),
  [TYPE_EDITING_KEYS.returnPath]: ['Type'],
  // ...
});

// ConstructorsSection
navigation.updateMetadata({
  [TYPE_EDITING_KEYS.term]: selectedConstructor.type,
  [TYPE_EDITING_KEYS.setTerm]: (t) => updateConstructor(id, { ...ctor, type: t }),
  [TYPE_EDITING_KEYS.returnPath]: ['Constructors', idx, 'Type'],
  // ...
});
```

### When Building New Features, Ask:

1. **"Is this a generic operation?"** - Type editing, name editing, list management, etc.
2. **"Will multiple contexts need this?"** - Inductive types, constructors, hypotheses, let bindings, etc.
3. **"Can I define a standard interface?"** - What data/callbacks does this operation need?

If yes to all three: Build the abstraction in `utils/` FIRST, then use it.

---

## Type Checker Error Philosophy

Errors should be **semantic and user-friendly** at the top level, with technical details available for those who want to dig deeper.

### Structure

```
PRIMARY MESSAGE: What went wrong in terms the user understands
↳ CAUSE: Technical details about why it failed
↳ DEEPER CAUSE: Even lower-level details if applicable
```

### Example

**Good** (semantic primary, technical detail):
```
'Succ' expects Nat but was applied to (Nat -> Nat -> Nat)
↳ unification failed: (Nat -> Nat -> Nat) vs Nat
```

**Bad** (technical primary, semantic context):
```
Unification failed (conflicting heads): (Nat -> Nat -> Nat) vs Nat
• while checking argument to 'Succ'
```

### Implementation

When catching low-level errors (like unification failures), higher-level code uses `wrappedBy()` to provide a semantic message that becomes the new primary:

```typescript
try {
  argEnv = checkType(argEnv.inAppArg(), expectedType);
} catch (e) {
  if (e instanceof TCEnvError) {
    // Semantic error becomes primary, original error becomes cause
    throw e.wrappedBy(`'Succ' expects Nat but was applied to (Nat -> Nat -> Nat)`);
  }
  throw e;
}
```

### Guidelines

1. **Primary messages** should answer: "What did the user do wrong?"
2. **Cause messages** should answer: "Why did the system reject it?"
3. The further down the cause stack, the more technical it can be
4. Users should be able to understand the primary message without knowing type theory

---

## File Creation: Use Write Tool, Not Bash

**IMPORTANT**: When creating new files, always use the `Write` tool directly instead of `cat` heredocs or `echo` redirection via `Bash`. The `Write` tool:
1. Doesn't require user permission for each file creation
2. Is cleaner and more reliable
3. Avoids shell quoting issues

**Bad**:
```typescript
// Using Bash with cat/echo - requires permission, error-prone
cat > /tmp/test.ts << 'EOF'
const x = 1;
EOF
```

**Good**:
```typescript
// Using Write tool directly
Write({ file_path: '/tmp/test.ts', content: 'const x = 1;' })
```
