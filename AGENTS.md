# Codex Guidelines for LeanUI

## IMPORTANT: Read This First

**This is a dependent type theory implementation.** Before making ANY changes, you MUST understand the context:

### 1. Read the Documentation

The following files provide essential context. Read them BEFORE diving into code:

| File | Purpose |
|------|---------|
| `SYSTEM_OVERVIEW.md` | **START HERE.** Comprehensive guide to the architecture, type checking rules, and key algorithms |
| `language-spec.md` | Surface syntax specification for the language |
| `TODO.md` | Current project status and what's already implemented |
| `RECORDS.md` | Design document for record types |
| `IMPLICITS-DESIGN.md` | Design for implicit argument handling |
| `ALGORITHMS/*.md` | Detailed algorithm documentation (pattern matching, totality, etc.) |

**Do NOT start coding until you understand:**
- The TT → TTK elaboration pipeline
- How type checking works (bidirectional, with metas and constraints)
- The de Bruijn index convention used throughout
- What has already been implemented vs. what's planned

### 2. Fix Bugs, Never Skip Tests

**CRITICAL**: When you encounter a bug or failing test, your job is to FIX it, not document it as a limitation.

**DO:**
- Write focused unit tests that reproduce the bug at the lowest possible level
- Research the root cause systematically, layer by layer
- Fix the underlying issue, even if it requires architectural changes
- Verify the fix with tests before claiming completion
- Add regression tests to prevent the bug from recurring

**DON'T:**
- Document bugs as "known limitations" without attempting to fix them
- Skip failing tests or mark them as "todo"
- Make superficial fixes that mask symptoms without addressing root causes
- Claim a task is complete without running `npx tsc --noEmit && npm test`

**Testing is non-negotiable**: Every bug fix MUST include tests. Every feature MUST have tests. Never skip tests because "they'll probably pass" or "it looks right". Always verify.

### 3. This is Type Theory - Favor Proven Algorithms

This project implements a dependently-typed language similar to Lean, Idris, and Agda. **Type theory has 50+ years of research behind it.** When implementing features:

**DO:**
- Research how Lean/Idris/Agda/Coq solve the same problem
- Look up the relevant type theory papers (e.g., "Elaboration in Dependent Type Theory", "A Tutorial Implementation of a Dependently Typed Lambda Calculus")
- Use established algorithms: bidirectional type checking, pattern unification, structural recursion checking
- Understand WHY the algorithms work, not just WHAT they do

**DON'T:**
- Invent ad-hoc solutions for well-studied problems
- Assume "this seems reasonable" - type theory has many subtle interactions
- Skip the research phase because you think you understand the problem

**Example - Record Eta:**
The eta rule `MkR (R.f1 r) ... (R.fN r) ≃ r` isn't arbitrary - it's a standard definitional equality in type theory. The implementation checks this BEFORE whnf normalization because projections unfold during δ-reduction. This is how Lean/Agda do it.

### 3. When in Doubt, Research First

If you're unsure about:
- **How to implement a feature**: Check how Lean or Idris does it
- **Whether an approach is sound**: Look for type theory literature
- **Why existing code does something a certain way**: Ask, or read the git history/comments

Common research resources:
- The Lean 4 source code (especially the type checker)
- "Elaboration in Dependent Type Theory" (thesis)
- "Typing Haskell in Haskell" (for basic inference concepts)
- Agda's documentation and source

### 4. Understand the Big Picture

This codebase has clear architectural layers. Respect them:

```
Source Text → Parser → TT (surface) → Elaboration → TTK (kernel) → Type Checker
```

- **All verification happens on TTK, never TT**
- **Elaboration converts named vars to de Bruijn indices**
- **Metas and constraints track unknowns during type checking**
- **WHNF normalization handles β, δ, ι, ζ reductions**

If you don't understand what layer you're working in, STOP and read `SYSTEM_OVERVIEW.md`.

### 5. Immutability

**All major data structures are immutable**, except the parser (which uses mutable state for tokenization and source map building). In particular:

- **`TCEnv`** is immutable. Every method (e.g., `withValue`, `extendTTKContext`, `inAppFn`) returns a **new** `TCEnv` instance. Never mutate a `TCEnv`.
- **`TTKTerm`** and **`TTerm`** are immutable. Term transformations produce new terms.
- **`TTKContext`** is an immutable array. Extending it creates a new array.
- The only mutable maps are explicitly shared ones (e.g., `TypeInfoMap`, which is a shared collector passed through immutable envs via constructor parameter).

---

## PURE KERNEL / ENGINE — No Domain Knowledge in Generic Layers

**The kernel, type checker, parser, tactic engine, suggestion system, and goal computation MUST NOT contain hard-coded knowledge about specific domains (Reals, Naturals, etc.) or specific definitions (`rone`, `rzero`, `rtwo`, `rneg`, `Zero`, `Succ`, etc.).**

These layers are GENERIC — they work with any user-supplied preset. Hard-coded names create:
- Tight coupling: changing the preset breaks the kernel
- Inconsistency: rules apply to one preset but not others
- Maintenance burden: every new domain requires kernel edits

### What goes WHERE:

| Layer | Allowed |
|-------|---------|
| **Kernel/Engine/Parser** | Term shapes (`App`, `Const`, `Var`), generic algorithms (WHNF, unification, pattern matching), generic protocols (`@syntax`, namedArgMap) |
| **Preset (.tt or preset .ts)** | Domain definitions, `@syntax` annotations, `@unfold` markers, custom notation entries |
| **`syntax-registry.ts`** | Generic registry data structures (NotationEntry, symbolMap), NOT domain-specific entries |

### Examples of VIOLATIONS to avoid:

**BAD** — kernel knows about `rone`/`rtwo`:
```typescript
// In goal-computation.ts (kernel-level code):
const numericAliases = { '1': ['rone'], '2': ['rtwo'] };
if (name === '-1') return rneg(rone(R));  // ← shame!
```

**GOOD** — preset defines `@syntax`, kernel reads registry:
```typescript
// In real-analysis.ts (preset):
@syntax 1
rone : (R : Real) -> Carrier R

// In parser (kernel-level):
const sourceFromSymbol = registry.symbolMap.get('1')?.source;  // generic lookup
```

### When you find yourself writing hard-coded names:

**STOP.** Ask: "Should this work for Naturals too? For my own preset?" If yes (it should), put it in the preset via `@syntax` and have the kernel read the registry.

If `@syntax` doesn't support what you need, **extend the protocol**, don't hard-code names.

---

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

## Debugging Strategy: Prove Each Layer Before Going Deeper

**CRITICAL**: When debugging issues in this codebase, **prove each layer is correct before diving deeper**.

### The Pipeline Has Distinct Layers

```
Source → Parser → TT → Elaboration → TTK → Type Checker → Result
```

Each layer can have bugs. When something fails end-to-end, **don't immediately dive into the deepest layer**.

### The Anti-Pattern: Deep End-to-End Debugging

**BAD**: "The type checker says 'unsolved metas' so let me add complex level inference logic to the type checker."

This approach:
- Assumes the problem is in the type checker
- May be fixing symptoms, not causes
- Can introduce unnecessary complexity
- May mask earlier bugs

### The Correct Pattern: Layer-by-Layer Verification

**GOOD**: "Let me first verify the elaborated structure is correct. If elaboration is correct, THEN I'll look at type checking."

For example, with record types:
1. **First**: Write tests that verify the ELABORATED constructor type has correct:
   - Field order
   - De Bruijn indices
   - Level references
2. **Then**: If elaboration is proven correct, examine type checking
3. **Only then**: Look at meta solving, constraint propagation, etc.

### Practical Example: Record Extends with ULevel

When `record Monoid {u : ULevel} (A : Type u) extends Semigroup A` fails:

**Step 1**: Verify elaboration produces the correct inductive type
```typescript
// Test the STRUCTURE, not checkSuccess
const ctorType = monoidDecl?.kernelConstructors?.[0]?.type;
expect(countPiBinders(ctorType)).toBe(7);  // u, A, op, assoc, e, identLeft, identRight
```

**Step 2**: If structure is correct, check specific field types
```typescript
// At op's position, is A referenced correctly?
expect(opDomain.domain.tag).toBe('Var');
expect((opDomain.domain as any).index).toBe(0);  // A should be at index 0
```

**Step 3**: Only if elaboration is correct, debug type checking
- Now you know: "Elaboration is correct, so the bug is in how level metas get solved"

### Why This Matters

Records elaborate to inductives. If elaboration produces the right inductive, the type checker should "just work" - it's the same type checking code used for all inductives.

If you find yourself adding special cases to the type checker for records, **STOP** and ask: "Is this really a type checker bug, or did elaboration produce the wrong structure?"

### Test Structure for Layer Verification

```typescript
// Good: Tests that verify elaboration structure
describe('Record elaboration structure', () => {
  test('constructor has correct fields', () => {
    // Examine kernelConstructors, not checkSuccess
  });
});

// Separate: Tests for end-to-end behavior
describe('Record type checking', () => {
  test('record type checks successfully', () => {
    expect(decl.checkSuccess).toBe(true);
  });
});
```

---

## Fix With Unit Tests, Not Whack-a-Mole

**Always write focused unit tests first when debugging or fixing bugs.** Don't make a change and then run the full suite hoping it works — that's whack-a-mole debugging.

### The Process

1. **Write a unit test** that reproduces the bug at the lowest possible level (e.g., test `solveConstraints` directly, not the full compiler pipeline)
2. **Verify the test fails** before the fix
3. **Make the fix**
4. **Verify the unit test passes**
5. **Run the full suite** to check for regressions

### Why?

- Unit tests catch the exact bug and prevent it from recurring
- They run in milliseconds, giving fast feedback
- They document the bug for future developers
- If the full suite regresses, you know the unit test is right and can investigate why the regression occurs

### Example

**Bad**: "The type checker accepts wrong code. Let me tweak `areTermsDefinitelyDifferent` and run all 1200 tests to see what happens."

**Good**: "Let me write a test in `meta.test.ts` that verifies `solveConstraints` throws on conflicting constraints `?m := Zero` then `?m := Succ x`. Then I'll fix the function and verify just that test. Then run the full suite."

---

## Smoke Testing: Verify Before Claiming Complete

**CRITICAL**: Before claiming any task is complete, ALWAYS verify the build works:

```bash
# Run both TypeScript compilation AND tests
npx tsc --noEmit && npm test
```

**Why both?**
- `npm test` runs tests but may not catch all TypeScript errors (tests run via ts-node/vitest which can be more lenient)
- `npx tsc --noEmit` performs full TypeScript type checking without emitting files
- A task is NOT done if either command fails

**Common mistake**: Adding code that passes tests but has TypeScript errors (e.g., accessing properties that don't exist on a type). The tests might pass because the runtime behavior is correct, but the build will fail.

**Never claim "done" without seeing both commands succeed.**

---

## Prefer `.tt` File Tests for Compile-and-Check

When testing whether source code compiles successfully or produces expected errors, **prefer `.tt` file tests** over inline string tests in TypeScript.

### The `.tt` Test System

Test programs live in `src/test-programs/` as `.tt` files with header directives:

```
@test success
@name "sym: Equal u v -> Equal v u"
@import preambles/equality.tt

sym : {A : Type} -> {u v : A} -> Equal u v -> Equal v u
sym refl = refl
```

The runner (`src/test-programs/tt-runner.test.ts`) discovers these files, resolves imports, compiles, and asserts.

### Running a Single `.tt` Test

To run one test by name (useful for debugging):

```bash
npx vitest run src/test-programs/tt-runner.test.ts -t "sym: Equal u v"
```

The `-t` flag matches test names by substring, so you don't need the full name. To run all tests in a directory group:

```bash
npx vitest run src/test-programs/tt-runner.test.ts -t "tt-programs/with"
```

### Directives

| Directive | Required | Description |
|-----------|----------|-------------|
| `@test success\|failure` | Yes | What to assert |
| `@name "..."` | Yes | Test name shown in vitest output |
| `@import path.tt` | No | Prepend contents of another `.tt` file (relative to `test-programs/`) |
| `@error "substring"` | No | Assert error message contains this substring |

### When to Use `.tt` Files

- **Any test that compiles source and checks success/failure** — put it in a `.tt` file
- **Exploratory debugging** — if you write `compileTTFromText(\`...\`)` to test something, keep it as a `.tt` file instead of throwing it away
- **Regression tests** — when a bug is found, add a `.tt` file that reproduces it

### When NOT to Use `.tt` Files

- Tests that inspect internal structure (kernel terms, de Bruijn indices, elaboration output)
- Tests that call individual functions directly (unit tests for `whnf`, `solveConstraints`, etc.)
- Tests that need to manipulate state between steps

### Shared Preambles

Common type definitions live in `src/test-programs/preambles/`:
- `nat.tt` — Nat (Zero, Succ)
- `bool.tt` — Bool (True, False)
- `equality.tt` — Universe-polymorphic Equal with refl
- `equal-simple.tt` — Non-polymorphic Equal
- `list.tt` — List (Nil, Cons)
- `maybe.tt` — Maybe (Nothing, Just)
- `either.tt` — Either (Left, Right)
- `pair.tt` — Pair (MkPair)

### Keep Explorations as Tests

When debugging or exploring (e.g., "let me try compiling this to see what happens"), **don't throw away the source code**. Save it as a `.tt` file instead. Every `compileTTFromText(\`...\`)` one-off you'd write in a scratch file or REPL should become a permanent `.tt` test. These explorations often catch regressions later.

This applies to **any** temporary experiment:
- "Let me check if this type-checks" → save as a `.tt` file
- "Does this pattern match compile?" → save as a `.tt` file
- "I wonder if this edge case works" → save as a `.tt` file
- Debugging a user report → save the minimal repro as a `.tt` file

```
@test success
@name "nested with on equality proof (debug exploration)"
@import preambles/nat.tt
@import preambles/equal-simple.tt

-- Found while debugging issue #42
myProof : ...
```

Then run it in isolation while debugging:

```bash
npx vitest run src/test-programs/tt-runner.test.ts -t "nested with on equality"
```

Once the bug is fixed, the `.tt` file stays as a regression test — zero extra effort.

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

---

## Status Tracking

The file `status.md` at the project root is read by **Conductor** (a project manager dashboard) to generate project summaries and progress tracking.

**After completing any significant feature, bug fix, or refactor, update `status.md`:**
- Move completed work from "Up Next" to "Recent Progress"
- Update "Current Focus" to reflect what you're working on now
- Add/remove blockers as they arise or resolve
- Keep each section concise (3-5 bullet points max for Recent Progress, prioritized list for Up Next)
- Trim old items from "Recent Progress" — keep only the ~5 most recent

**This is not optional.** If you just finished a task and are about to report completion, check whether `status.md` needs updating. When in doubt, update it.
