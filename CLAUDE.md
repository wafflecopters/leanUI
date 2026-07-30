# Claude Code Guidelines for LeanUI

## IMPORTANT: Read This First

**LeanUI is a WYSIWYG editor for Lean 4 proofs.** You write and manipulate real
Lean; the editor renders it as mathematical prose you can click, and every
suggestion it offers has been tried against real Lean before you see it. The
goal is two things at once: math you can poke and prod at, and a document that
reads like a rigorous paper.

**There is no type checker in this repo.** Lean is the engine — type checking,
elaboration, unification, tactics, `simp`, `exact?`, all of it. M5 deleted the
custom dependent-type-theory implementation (parser, elaborator, TTK kernel,
checker, tactic engine — ~129k lines). If you find yourself about to implement
type theory, stop: ask Lean instead.

### 1. Read the Documentation

| File | Purpose |
|------|---------|
| `status.md` | **START HERE.** Current state, focus, recent progress |
| `LEAN_WYSIWYG_PORT.md` | The Lean-backend architecture and the port's design |
| `LIMIT-DESIGN.md` | The limit/ε-δ design the milestone proofs use |
| `docs/tt-archive/` | Design docs for the DELETED TT engine — history only. Do not implement against these. |

### 2. The Architecture

```
Lean source ──► server/lean-bridge.ts ──► lean/Extract.lean ──► Lean 4
    ▲                (resident workers,        (InfoTree walk:
    │                 prefix-olean cache)       goals, messages,
    │                                           declarations, tagged pp)
    │                                                   │
    └──── src/controller/ (headless ProofSession) ◄──────┘
                    │
              src/components/ (thin React view)
```

- **`lean/Extract.lean`** is a Lean meta-program: it elaborates a file and emits
  JSON — diagnostics, per-tactic goal states (hypotheses + target as
  `CodeWithInfos` tagged pretty-print, with subexpression positions), and the
  user's declarations.
- **`server/lean-bridge.ts`** runs it. Performance is a product feature here:
  resident `extract --serve` workers keep the environment loaded, a prefix-olean
  cache avoids re-elaborating imports, and a priority queue keeps the visible
  goal ahead of background trials. See the memory note on pool sizing — a
  Mathlib-loaded worker is 4–7GB.
- **`src/controller/`** is the editor's brain, headless and framework-free:
  `ProofSession` owns tree + cursor + selection + history, the goal round-trip,
  candidate generation, validation and write-back. Lean arrives through an
  injected `LeanAnalyzer`, so the same session runs in a browser, under Node, or
  against a scripted fake.
- **`src/proof-tree/`** is the proof MODEL and its prose rendering. It holds no
  engine — the `*-types.ts` modules (`goal-types`, `suggestion-types`,
  `term-builder-types`, `interactive-goal-types`, `tactic-command`) are the
  vocabulary the Lean layer fills in.
- **`src/lean/`** is the seam: `proofTreeToLean` prints the tree as a Lean tactic
  block with per-node source ranges; `leanGoalMapping` maps Lean's range-keyed
  goal states back onto nodes. That round-trip is the whole trick.

**Drive it without a browser:**
`npx tsx scripts/proof-repl.ts --decl limitAdd` (interactive), or
`--run "constructor; intros ε epsPos; have h1 : 0 < ε / 2; take apply divTwoPos"`.

### 3. Lean Owns the Semantics — Never Reimplement It

The recurring mistake in this codebase's history was doing in TypeScript what
Lean already does. Concretely:

- **Never parse Lean.** A tactic argument is Lean source text; pass it through
  verbatim. (`TacticCommand.args` used to be parsed terms, and re-printing them
  turned `ε / 2` into `div ε 2`, which Lean rejects.)
- **Never decide whether a tactic applies.** Propose it and let validation trial
  it at the real cursor (`src/controller/validate.ts`). An unavailable tactic
  errors on its own line and is dropped by the same code that drops a lemma that
  fails to apply — which is why Mathlib and from-scratch files need no mode flag.
- **Never compute a goal.** Ask for the round-trip and read Lean's answer.
- **Prefer asking Lean a NEW question** over inferring from what you already
  have. `Extract.lean` is ours to extend — when the UI needed to know which goal
  was a value to choose, the fix was to record the dependency in the extractor,
  not to pattern-match pretty-printed text.

### 4. Fix Bugs, Never Skip Tests

**CRITICAL**: When you encounter a bug or failing test, your job is to FIX it,
not document it as a limitation.

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

**Testing is non-negotiable**: Every bug fix MUST include tests. Every feature
MUST have tests. Never skip tests because "they'll probably pass". Always verify.

### 5. Research Before Inventing

This is still dependent type theory, with 50+ years of research behind it — the
difference is that Lean is the implementation. When designing a feature, look at
how Lean's own InfoView, `Widget.goalToInteractive`, `SubExpr.Pos`, and the
tactic framework solve it, and use their vocabulary. Reach for the Lean 4 source
and the Mathlib source; they answer most questions faster than guessing does.

### 6. Immutability

**All major data structures are immutable.** `ProofNode`/`ProofTreeState` are
immutable — transformations produce new trees. `ProofSession` holds mutable
state, but every value it hands out via `getState()` is plain serializable data.

---

## PURE ENGINE — No Domain Knowledge in Generic Layers

**The bridge, the controller, the proof model, and the suggestion/goal layers
MUST NOT contain hard-coded knowledge about specific domains (Reals, Naturals)
or specific definitions (`rone`, `rtwo`, `rneg`, `Zero`, `Succ`).**

These layers are GENERIC — they work with any preset, and with Mathlib. Hard-coded
names create tight coupling, inconsistency between presets, and a maintenance
burden on every new domain.

| Layer | Allowed |
|-------|---------|
| **Bridge / controller / proof-tree** | Generic algorithms and protocols: goal round-trip, candidate ranking by overlap, validation, prose generation |
| **Preset (`src/lean/presets.ts`, the `.lean` source)** | Domain definitions, notation, `@[simp]` lemmas, `@[app_unexpander]`s |
| **`lean/Extract.lean`** | Generic extraction (Lean's own predicates), NOT domain-specific names |

**BAD** — the engine knows about `rone`/`rtwo`:
```typescript
const numericAliases = { '1': ['rone'], '2': ['rtwo'] };
if (name === '-1') return rneg(rone(R));  // ← shame!
```

**GOOD** — the preset states the fact, the engine runs a generic tactic:
```lean
-- in the preset:
@[simp] theorem twoAddNegOne : (2 : Carrier R) + -1 = 1 := by ...
```
```typescript
// in the engine: offer `simp`, let the file's @[simp] set define "compute"
```

When you find yourself writing hard-coded names, **STOP.** Ask: "should this
work for Naturals too? For Mathlib? For my own preset?" If yes, it belongs in
the preset — and Lean's attribute system (`@[simp]`, `@[app_unexpander]`) is
usually the protocol you want.

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

---

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

---

## Error Philosophy

Errors should be **semantic and user-friendly** at the top level, with technical
details available for those who want to dig deeper. Lean's own messages are the
technical layer; our job is to say what the user did and scope it to the step
they did it on.

```
PRIMARY MESSAGE: What went wrong in terms the user understands
↳ CAUSE: Lean's own message
```

Guidelines:
1. **Primary messages** answer: "what did the user do wrong?"
2. **Cause messages** answer: "why did Lean reject it?"
3. Scope an error to the tactic's OWN line. A broken tactic also produces a
   knock-on `unsolved goals` at the `by` — blaming the whole declaration for it
   is how a proof looks broken everywhere at once. This is load-bearing in
   `validateOne` and covered by tests.
4. Never let a broken proof look fine. A hole below a failed step is NOT solved
   just because Lean reported no goal there (see `unsolveAfterErrors`).

---

## Debugging Strategy: Prove Each Layer Before Going Deeper

**CRITICAL**: prove each layer is correct before diving deeper.

```
proof tree → proofTreeToLean → assembled source → Lean → goals → leanGoalMapping → prose
```

When something is wrong end-to-end, don't start at the deepest layer. Check, in
order:

1. **What did we print?** `session.proofSource()` / `assembleProofInSource` —
   is the Lean source what you intended? Most "Lean is wrong" bugs are "we
   printed the wrong thing".
2. **What did Lean say?** Run the assembled source through the bridge directly
   and read the raw JSON. Lean is almost never wrong.
3. **Did we map it back correctly?** `mapLeanGoalsToNodes` matches by source
   RANGE; a printer that shifts a line breaks the mapping silently.
4. **Only then** look at the prose/render layer.

A concrete example of why the order matters: "the goal chain stops after the
Compute step" looked like a rendering bug. It was the PARSER — `conv in (p) =>
simp` fell into the unrecognized-tactic fallback, which is terminal, so the
hole that carried the chain was swallowed. Two layers up from where it showed.

**Save every exploration as a test.** If you write a one-off script to check
what Lean does with some tactic, turn it into a unit test (scripted-fake Lean,
in `src/controller/testing.ts`) or an `*.e2e.test.ts` case. These catch
regressions later for zero extra effort.

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

---

## Smoke Testing: Verify Before Claiming Complete

**CRITICAL**: Before claiming any task is complete, ALWAYS verify the build:

```bash
npx tsc --noEmit && npm test
```

**Why both?** `npm test` may not catch all TypeScript errors (vitest is more
lenient); `npx tsc --noEmit` type-checks fully without emitting. A task is NOT
done if either fails. **Never claim "done" without seeing both succeed.**

`npm test` is the fast gate (~1s, real-Lean e2e excluded). It excludes
`*.e2e.test.ts`.

### Running Lean-heavy suites — MEMORY DANGER

A Lean process that has imported Mathlib holds **4–7GB resident**. Stacking them
took the machine down twice (see the memory note). ALWAYS run Lean-touching
commands under the watchdog, which kills the whole process tree past a limit:

```bash
scripts/guarded-run.sh -l 14 -- env E2E=1 npx vitest run src/controller/session.e2e.test.ts
scripts/guarded-run.sh -l 14 -- npm test
```

Run e2e suites foreground and watched, never in the background, never stacked,
and never auto-resumed. When sampling memory, walk the process TREE — filtering
for `extract --serve` misses the one-shot processes that actually cause the
blowup.

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
