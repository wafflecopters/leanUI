# TacticSession: Unified Tactic Execution

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace the duplicated tactic execution paths (compile.ts + goal-computation.ts) with a single `TacticSession` that both compilation and the proof tree UI share.

**Architecture:** Extract the elaboration logic (`surfaceToKernel`) from `compile.ts` into a standalone module. Create `TacticSession` — a stateful wrapper around `TacticEngine` that can elaborate and apply tactic commands, recording a trace of intermediate states. Both `elaborateTacticBlock()` in compile.ts and the proof tree rendering in goal-computation.ts call the same `TacticSession.applyCommand()`.

**Tech Stack:** TypeScript, existing TacticEngine + Tactic classes (unchanged), vitest for testing.

---

## File Structure

| File | Action | Responsibility |
|------|--------|---------------|
| `src/tactics/elaborate-tactic-arg.ts` | **Create** | Standalone `surfaceToKernel()` and `tacticCommandToTactic()` extracted from compile.ts |
| `src/tactics/tactic-session.ts` | **Create** | `TacticSession` class: wraps engine + elaboration, applies commands, records trace |
| `src/tactics/tactic-session.test.ts` | **Create** | Unit tests for TacticSession |
| `src/compiler/compile.ts` | **Modify** | Replace inline elaboration in `elaborateTacticBlock()` with `TacticSession` |
| `src/proof-tree/goal-computation.ts` | **Modify** | Replace `replayProofTree`/`walk` tactic re-execution with trace consumption |
| `src/proof-tree/goal-computation.test.ts` | **Modify** | Add regression tests verifying identical rendering output |

## Key Interfaces

```typescript
// src/tactics/tactic-session.ts

interface TacticStepTrace {
  tacticName: string;
  engineAfter: TacticEngine;
  goalId: string;           // focused goal ID after this step
  error?: string;
  branchPath: string[];     // nesting: ['Left'], ['Right', 'Succ']
}

class TacticSession {
  readonly engine: TacticEngine;
  readonly definitions: DefinitionsMap;
  readonly trace: readonly TacticStepTrace[];

  static create(goalType: TTKTerm, definitions: DefinitionsMap, context?: TTKContext): TacticSession;

  /** Apply a single tactic command. Returns new session with updated engine and trace. */
  applyCommand(cmd: TacticCommand, branchPath?: string[]): TacticSession;

  /** Apply a sequence of tactic commands. */
  applyCommands(cmds: readonly TacticCommand[], branchPath?: string[]): TacticSession;

  /** Get the focused goal. */
  get goal(): MetaVar | null;
  get goalId(): string | null;
}
```

```typescript
// src/tactics/elaborate-tactic-arg.ts

/** Convert a surface term to a kernel term in the given goal context. */
function elaborateTacticArg(
  term: TTerm,
  goalCtx: TTKContext,
  definitions: DefinitionsMap,
  depth?: number
): TTKTerm;

/** Convert a tactic command (with elaborated args) to a Tactic instance. */
function tacticCommandToTactic(
  cmd: { name: string; args: Array<TTerm | TTKTerm>; focusedTactics?: Tactic[] }
): Tactic | 'sorry';
```

---

### Task 1: Extract `elaborateTacticArg` from compile.ts

**Files:**
- Create: `src/tactics/elaborate-tactic-arg.ts`
- Create: `src/tactics/elaborate-tactic-arg.test.ts`
- Read: `src/compiler/compile.ts:1818-1950` (the `surfaceToKernel` closure)

The `surfaceToKernel` function inside `elaborateTacticBlock()` is a closure that captures `goal`, `definitions`, and the `namedArgLookup`. Extract it into a standalone function that takes these as parameters.

- [ ] **Step 1: Write failing tests for elaborateTacticArg**

Test cases:
- `Const("x")` in context → `Var(correct_index)`
- `Const("Succ")` not in context → `Const("Succ")` with implicit holes
- `App(Const("f"), Const("x"))` → application with correct indices
- `Binder(BLamTT, "y", body_with_y)` → lambda with shifted indices
- Name shadowing: inner binder shadows outer context entry

```typescript
// src/tactics/elaborate-tactic-arg.test.ts
import { describe, test, expect } from 'vitest';
import { elaborateTacticArg } from './elaborate-tactic-arg';
import { createDefinitionsMap } from '../compiler/term';

describe('elaborateTacticArg', () => {
  test('resolves context variable to Var', () => {
    const ctx = [{ name: 'x', type: { tag: 'Const' as const, name: 'Nat' } }];
    const term = { tag: 'Const' as const, name: 'x' };
    const result = elaborateTacticArg(term, ctx, createDefinitionsMap());
    expect(result.tag).toBe('Var');
    expect((result as any).index).toBe(0);
  });

  test('keeps unknown constant as Const', () => {
    const ctx = [{ name: 'x', type: { tag: 'Const' as const, name: 'Nat' } }];
    const term = { tag: 'Const' as const, name: 'Succ' };
    const result = elaborateTacticArg(term, ctx, createDefinitionsMap());
    expect(result.tag).toBe('Const');
  });

  test('lambda body resolves binder variable', () => {
    const ctx: any[] = [];
    const term = {
      tag: 'Binder' as const,
      name: 'y',
      binderKind: { tag: 'BLamTT' as const },
      domain: { tag: 'Const' as const, name: 'Nat' },
      body: { tag: 'Const' as const, name: 'y' },
    };
    const result = elaborateTacticArg(term, ctx, createDefinitionsMap());
    expect(result.tag).toBe('Binder');
    expect((result as any).body.tag).toBe('Var');
    expect((result as any).body.index).toBe(0);
  });
});
```

- [ ] **Step 2: Run tests, verify they fail** (function doesn't exist yet)

Run: `npx vitest run src/tactics/elaborate-tactic-arg.test.ts`

- [ ] **Step 3: Extract `elaborateTacticArg` from compile.ts**

Copy the `surfaceToKernel` logic from `compile.ts:1838-1950` into a standalone exported function. Replace the closure captures (`goal`, `definitions`, `namedArgLookup`) with explicit parameters.

Key changes from the closure version:
- `goal.ctx` → parameter `goalCtx: TTKContext`
- `definitions` → parameter `definitions: DefinitionsMap`
- `namedArgLookup` → computed internally from `definitions`
- `insertImplicitHolesForApp` → import or inline

- [ ] **Step 4: Run tests, verify they pass**

Run: `npx vitest run src/tactics/elaborate-tactic-arg.test.ts`

- [ ] **Step 5: Extract `tacticCommandToTactic` into same file**

Move the `tacticCommandToTactic` function from `compile.ts:1518-1702` into `elaborate-tactic-arg.ts`. This is a pure function that maps command names to Tactic instances — no closure dependencies.

- [ ] **Step 6: Verify compile.ts still works by importing from the new module**

Update `compile.ts` to import `elaborateTacticArg` and `tacticCommandToTactic` from the new module. Replace the inline `surfaceToKernel` closure with a call to `elaborateTacticArg(term, goal.ctx, definitions, depth)`.

Run: `npx tsc --noEmit && npm test`

- [ ] **Step 7: Commit**

```
feat: extract elaborateTacticArg and tacticCommandToTactic into shared module
```

---

### Task 2: Create TacticSession class

**Files:**
- Create: `src/tactics/tactic-session.ts`
- Create: `src/tactics/tactic-session.test.ts`

- [ ] **Step 1: Write failing tests for TacticSession**

```typescript
// src/tactics/tactic-session.test.ts
import { describe, test, expect } from 'vitest';
import { TacticSession } from './tactic-session';
import { compileTTFromText } from '../compiler/compile';

describe('TacticSession', () => {
  test('create session from goal type', () => {
    const code = `
inductive Nat where
  Zero : Nat
  Succ : Nat -> Nat
`;
    const result = compileTTFromText(code);
    const defs = result.definitions;
    // Goal: Nat -> Nat
    const goalType = { tag: 'Binder' as const, ... }; // Pi Nat Nat
    const session = TacticSession.create(goalType, defs);
    expect(session.goal).not.toBeNull();
    expect(session.trace).toHaveLength(0);
  });

  test('apply intros creates trace entry', () => {
    // ... setup ...
    const s1 = session.applyCommand({ name: 'intros', args: [{ tag: 'Const', name: 'n' }] });
    expect(s1.trace).toHaveLength(1);
    expect(s1.trace[0].tacticName).toBe('intros');
    expect(s1.goal?.ctx.length).toBeGreaterThan(session.goal!.ctx.length);
  });

  test('apply sequence produces cumulative trace', () => {
    const s = session
      .applyCommand({ name: 'intros', args: [...] })
      .applyCommand({ name: 'exact', args: [...] });
    expect(s.trace).toHaveLength(2);
  });
});
```

Use real compilation results from the nat-math or real-analysis presets for realistic tests.

- [ ] **Step 2: Run tests, verify they fail**

- [ ] **Step 3: Implement TacticSession**

```typescript
// src/tactics/tactic-session.ts
import { TacticEngine, createInitialEngine } from './tacticsEngine';
import { elaborateTacticArg, tacticCommandToTactic } from './elaborate-tactic-arg';
import { TacticCommand, TTerm } from '../compiler/surface';
import { TTKTerm, TTKContext } from '../compiler/kernel';
import { DefinitionsMap, MetaVar } from '../compiler/term';

export interface TacticStepTrace {
  tacticName: string;
  engineAfter: TacticEngine;
  goalId: string;
  error?: string;
  branchPath: string[];
}

export class TacticSession {
  constructor(
    readonly engine: TacticEngine,
    readonly definitions: DefinitionsMap,
    readonly trace: readonly TacticStepTrace[],
  ) {}

  static create(goalType: TTKTerm, definitions: DefinitionsMap, context: TTKContext = []): TacticSession {
    return new TacticSession(createInitialEngine(goalType, context, definitions), definitions, []);
  }

  get goal(): MetaVar | null { return this.engine.getFocusedGoal(); }
  get goalId(): string | null { return this.engine.getFocusedGoalId(); }

  applyCommand(cmd: TacticCommand, branchPath: string[] = []): TacticSession {
    const goal = this.engine.getFocusedGoal();
    const goalId = this.engine.getFocusedGoalId();
    if (!goal || !goalId) return this;

    // 1. Elaborate args
    const elabArgs = cmd.args.map((arg, i) => {
      if (this.shouldKeepAsName(cmd.name, i)) return arg;
      return elaborateTacticArg(arg, goal.ctx, this.definitions);
    });

    // 2. Handle focused tactics (bullets)
    let focusedTactics;
    if (cmd.focusedTactics?.length) {
      focusedTactics = cmd.focusedTactics.map(ft => {
        // Recursively elaborate focused tactic args
        const ftArgs = ft.args.map(a => elaborateTacticArg(a, goal.ctx, this.definitions));
        return tacticCommandToTactic({ ...ft, args: ftArgs });
      }).filter((t): t is Exclude<typeof t, 'sorry'> => t !== 'sorry');
    }

    // 3. Create tactic
    const tactic = tacticCommandToTactic({ name: cmd.name, args: elabArgs, focusedTactics });
    if (tactic === 'sorry') {
      return new TacticSession(this.engine, this.definitions, [
        ...this.trace, { tacticName: 'sorry', engineAfter: this.engine, goalId, branchPath }
      ]);
    }

    // 4. Apply
    const result = tactic.apply(this.engine, goal, goalId);
    const newEngine = result.success ? result.newEngine : this.engine;
    const newGoalId = newEngine.getFocusedGoalId() ?? goalId;
    const entry: TacticStepTrace = {
      tacticName: cmd.name,
      engineAfter: newEngine,
      goalId: newGoalId,
      error: result.success ? undefined : result.error,
      branchPath,
    };

    let session = new TacticSession(newEngine, this.definitions, [...this.trace, entry]);

    // 5. Handle case branches
    if (result.success && cmd.caseBranches?.length) {
      session = this.applyCaseBranches(session, cmd.caseBranches, branchPath);
    }

    return session;
  }

  applyCommands(cmds: readonly TacticCommand[], branchPath: string[] = []): TacticSession {
    let session: TacticSession = this;
    for (const cmd of cmds) {
      session = session.applyCommand(cmd, branchPath);
    }
    return session;
  }

  private shouldKeepAsName(tacticName: string, argIndex: number): boolean {
    // intro/intros/unfold/fold: args are names, not expressions
    if (['intro', 'intros', 'unfold', 'fold'].includes(tacticName)) return true;
    if (tacticName === 'have' && argIndex === 0) return true; // have name
    if (tacticName === 'obtain' && argIndex < /* last */ ) return true;
    if (tacticName === 'suffices' && argIndex === 0) return true;
    return false;
  }

  private applyCaseBranches(session: TacticSession, branches: CaseBranch[], parentPath: string[]): TacticSession {
    // For each branch, focus the matching goal and apply branch tactics
    for (const branch of branches) {
      const branchPath = [...parentPath, branch.constructor];
      // Find goal with matching caseTag
      const engine = session.engine;
      const matchIdx = engine.goals.findIndex(gid => {
        const meta = engine.metaVars.get(gid);
        return meta?.caseTag === branch.constructor;
      });
      if (matchIdx < 0) continue;
      const focused = engine.withUpdates({ focusIndex: matchIdx });
      let branchSession = new TacticSession(focused, this.definitions, session.trace);
      branchSession = branchSession.applyCommands(branch.tactics, branchPath);
      session = new TacticSession(branchSession.engine, this.definitions, branchSession.trace);
    }
    return session;
  }
}
```

- [ ] **Step 4: Run tests, verify they pass**

- [ ] **Step 5: Add integration test with real-analysis preset**

```typescript
test('real-analysis tactic declarations all produce traces', { timeout: 15000 }, () => {
  const result = compileTTFromText(REAL_ANALYSIS_CODE);
  const tacticDecls = result.blocks.flatMap(b => b.declarations)
    .filter(d => d.tacticCommands && d.tacticCommands.length > 0);
  for (const decl of tacticDecls) {
    const session = TacticSession.create(decl.kernelType!, result.definitions);
    const final = session.applyCommands(decl.tacticCommands!);
    expect(final.trace.length).toBeGreaterThan(0);
    // No errors in trace (or expected errors for specific tactics)
  }
});
```

- [ ] **Step 6: Commit**

```
feat: add TacticSession class with shared elaboration and trace
```

---

### Task 3: Wire compile.ts to use TacticSession

**Files:**
- Modify: `src/compiler/compile.ts:1714-2400` (elaborateTacticBlock)

- [ ] **Step 1: Write regression test**

Before changing compile.ts, capture current behavior:

```typescript
test('elaborateTacticBlock produces same results via TacticSession', { timeout: 15000 }, () => {
  const result = compileTTFromText(REAL_ANALYSIS_CODE);
  // All declarations that were checkSuccess=true should still pass
  const failedBefore = result.blocks.flatMap(b => b.declarations)
    .filter(d => d.checkSuccess === false).map(d => d.name);
  // ... recompile and compare ...
});
```

- [ ] **Step 2: Run full test suite to establish baseline**

Run: `npx tsc --noEmit && npm test`
Record pass count. All 2652+ tests must still pass after changes.

- [ ] **Step 3: Replace inline elaboration loop with TacticSession.applyCommands**

In `elaborateTacticBlock()`, replace the manual tactic loop (lines 1809-2400) with:

```typescript
const session = TacticSession.create(expectedType, definitions, context);
const final = session.applyCommands(tacticBlock.tactics);
// Extract proof term
const term = final.engine.zonk();
return { term, trace: final.trace };
```

This is the biggest change. The key challenge: `elaborateTacticBlock` currently does extra things beyond just applying tactics:
- Records source map entries
- Builds the InfoTree
- Handles error recovery and reporting

Strategy: keep the outer loop structure for source map / error reporting, but delegate the actual tactic application to `TacticSession.applyCommand()` for each step.

- [ ] **Step 4: Run full test suite**

Run: `npx tsc --noEmit && npm test`
All tests must pass. If any fail, debug by comparing old vs new behavior for that specific tactic.

- [ ] **Step 5: Store trace on CompiledDeclaration**

Add `tacticTrace?: TacticStepTrace[]` to the `CompiledDeclaration` interface. Populate it from the session's trace when a tactic block is compiled.

- [ ] **Step 6: Commit**

```
refactor: wire elaborateTacticBlock to use TacticSession
```

---

### Task 4: Wire goal-computation.ts to consume traces

**Files:**
- Modify: `src/proof-tree/goal-computation.ts`
- Modify: `src/proof-tree/tactic-to-tree.ts` (add traceIndex to ProofNode)
- Modify: `src/proof-tree/proof-tree.ts` (add traceIndex field)

- [ ] **Step 1: Add traceIndex to ProofNode**

Add an optional `traceIndex?: number` field to every ProofNode interface that represents a tactic step (intros, unfold, fold, rewrite, apply, have, suffices, exact). This maps each tree node to its position in the trace array.

- [ ] **Step 2: Assign traceIndex during tacticCommandsToProofTree**

Pass a mutable counter through `tacticCommandsToProofTree`. Each tactic node gets the next index:

```typescript
export function tacticCommandsToProofTree(
  commands: readonly TacticCommand[],
  traceCounter?: { value: number }
): ProofNode {
  // ... for each command, assign traceIndex: traceCounter?.value++
}
```

- [ ] **Step 3: Add trace-based path to computeWithTacticEngine**

When the declaration has a `tacticTrace`, use it instead of replaying:

```typescript
// In computeWithTacticEngine or replayEntireTree:
if (declaration.tacticTrace) {
  // Walk tree, for each node with traceIndex, look up trace[traceIndex].engineAfter
  // Use that engine to render goals/hypotheses/LaTeX
  // No tactic re-execution needed
} else {
  // Fallback: existing replay logic (for future interactive editing)
}
```

- [ ] **Step 4: Write regression test comparing old vs new rendering**

```typescript
test('trace-based rendering matches replay-based rendering', { timeout: 15000 }, () => {
  // Compile with trace
  // Render all nodes via trace path
  // Render all nodes via replay path (temporarily force fallback)
  // Compare: same goalLatex, same hypotheses, same errors
});
```

- [ ] **Step 5: Run full test suite**

Run: `npx tsc --noEmit && npm test`

- [ ] **Step 6: Commit**

```
feat: goal-computation consumes tactic traces instead of replaying
```

---

### Task 5: Delete duplicated replay code

**Files:**
- Modify: `src/proof-tree/goal-computation.ts`

- [ ] **Step 1: Identify dead code**

With the trace path working, the per-tactic handlers in `replayProofTree` and `walk` (intros, unfold, fold, rewrite, apply, constructor, have, suffices, cases/induction — ~300 lines) are only needed for the fallback path.

- [ ] **Step 2: Extract remaining fallback replay into shared function**

If keeping the fallback, consolidate the per-tactic-type handlers into a single `applyTacticFromNode(node, engine, definitions)` function that uses the shared `TacticSession.applyCommand()`.

- [ ] **Step 3: Delete the old per-tactic handlers**

Remove the duplicated switch cases that manually construct IntrosTactic, ApplyTactic, ConstructorTactic, HaveTactic, etc. Replace with single call to TacticSession.

- [ ] **Step 4: Remove parseExactExpr and resolveExprInGoal (if no longer needed)**

If the trace provides all engine states, these approximate parsers are only needed for the fallback path. Keep them if fallback is wanted, otherwise delete.

- [ ] **Step 5: Run full test suite**

Run: `npx tsc --noEmit && npm test`

- [ ] **Step 6: Commit**

```
refactor: remove duplicated tactic replay code from goal-computation
```

---

### Task 6: End-to-end integration tests

**Files:**
- Create: `src/tactics/tactic-session-integration.test.ts`

- [ ] **Step 1: Test all 46 real-analysis tactic-mode declarations produce valid traces**

```typescript
test('all tactic-mode declarations produce valid traces', { timeout: 20000 }, () => {
  const result = compileTTFromText(REAL_ANALYSIS_CODE);
  const tacticDecls = result.blocks.flatMap(b => b.declarations)
    .filter(d => d.tacticTrace && d.tacticTrace.length > 0);
  expect(tacticDecls.length).toBeGreaterThanOrEqual(40); // we know there are 46
  for (const decl of tacticDecls) {
    expect(decl.tacticTrace!.every(t => t.engineAfter != null)).toBe(true);
  }
});
```

- [ ] **Step 2: Test trace-based rendering produces clean LaTeX (same as existing test)**

The existing "ALL tactic-mode definitions replay with zero errors and clean LaTeX" test should still pass, but now using the trace path.

- [ ] **Step 3: Test TacticSession works for interactive-style usage**

```typescript
test('interactive: apply tactics one at a time', () => {
  // Create session for a simple goal
  // Apply intros → check goal changed
  // Apply exact → check proof complete
  // Verify trace has 2 entries
});
```

- [ ] **Step 4: Commit**

```
test: add end-to-end integration tests for TacticSession
```
