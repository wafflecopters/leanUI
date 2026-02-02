# Tactics Engine Redesign

## Motivation

The current tactics implementation works for basic linear proofs but has limitations:

1. **No branching support**: Can't handle tactics like `cases` that create multiple subgoals
2. **No IDE integration**: Can't inspect goal state at cursor position
3. **Tight coupling**: Elaboration logic mixed with proof state management
4. **Hard to test**: Multi-step proofs only testable end-to-end

This redesign addresses these issues by following Lean 4's proven architecture.

---

## Core Principles

### 1. Goals Are Metavariables

**Current (correct)**: Goals are just unsolved metavariables in the proof term.

**Keep this**: Our existing `TacticEngine` already implements this correctly. A "goal" is simply a metavariable we haven't assigned yet.

### 2. Single-Step Application

**New**: Each tactic application is a pure function:

```typescript
function applyTactic(
  state: ProofState,
  tactic: TacticExpr
): TacticResult
```

This enables:
- Easy unit testing of single steps
- Clear input/output contracts
- Accumulating state after each line for IDE inspection

### 3. Explicit Goal List Management

**Current limitation**: Goals list is implicit in the engine's goal tracking.

**New**: Make the goal list explicit and support multiple goals per step (branching).

---

## Architecture Overview

```
┌─────────────────────────────────────────────────────────────┐
│                      TacticM Monad                          │
│  (Optional future: monadic context for state + errors)      │
└─────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────┐
│                      ProofState                             │
│  - term: TTKTerm (proof with holes)                         │
│  - metaVars: Map<string, MetaVar>                           │
│  - goals: GoalId[]                                          │
│  - focusIndex: number                                       │
│  - constraints: Constraint[]                                │
│  - definitions: DefinitionsMap                              │
└─────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────┐
│                    applyTactic()                            │
│  Input: ProofState + TacticExpr                             │
│  Output: ProofState (with updated goals)                    │
└─────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────┐
│                      InfoTree                               │
│  Records state after each tactic for IDE inspection         │
│  - position: source location                                │
│  - goalsBefore: GoalState[]                                 │
│  - goalsAfter: GoalState[]                                  │
│  - children: InfoTree[]                                     │
└─────────────────────────────────────────────────────────────┘
```

---

## Core Types

### ProofState

The complete proof state at any point in a tactic proof:

```typescript
export interface ProofState {
  /** The proof term being built (contains Meta nodes for unsolved goals) */
  term: TTKTerm;

  /** All metavariables (solved and unsolved) */
  metaVars: Map<string, MetaVar>;

  /** Ordered list of goal IDs (unsolved metas we're working on) */
  goals: GoalId[];

  /** Which goal has focus (index into goals array) */
  focusIndex: number;

  /** Active constraint set */
  constraints: Constraint[];

  /** Global definitions */
  definitions: DefinitionsMap;
}

export type GoalId = string; // Meta ID
```

### GoalState (for display/inspection)

What the IDE shows to the user:

```typescript
export interface GoalState {
  /** Goal ID */
  id: GoalId;

  /** Hypothesis list: name : type */
  hypotheses: Array<{ name: string; type: TTKTerm }>;

  /** Target type we're trying to prove */
  target: TTKTerm;

  /** Optional: tag for case branches ("Zero", "Succ", etc.) */
  caseTag?: string;
}
```

### TacticResult

Result of applying a tactic:

```typescript
export type TacticResult =
  | { success: true; newState: ProofState; info?: TacticInfo }
  | { success: false; error: string; cause?: Error };

export interface TacticInfo {
  /** Human-readable description of what happened */
  message?: string;

  /** New goals created (for branching tactics) */
  newGoals?: GoalId[];
}
```

---

## Core API

### applyTactic

The fundamental operation:

```typescript
/**
 * Apply a tactic to the current proof state.
 *
 * This is the ONLY way tactics modify proof state. All tactics
 * go through this function.
 *
 * @param state - Current proof state
 * @param tactic - Tactic to apply (parsed from surface syntax)
 * @returns New proof state or error
 */
export function applyTactic(
  state: ProofState,
  tactic: TacticExpr
): TacticResult;
```

### TacticExpr (surface syntax)

```typescript
export type TacticExpr =
  | { tag: 'Intro'; name?: string }
  | { tag: 'Intros'; names?: string[] }
  | { tag: 'Exact'; term: TTerm }
  | { tag: 'Apply'; fn: TTerm }
  | { tag: 'Assumption' }
  | { tag: 'Cases'; target: TTerm; withClause?: CasesWithClause }
  | { tag: 'Case'; ctorName: string; tactics: TacticExpr[] };

export interface CasesWithClause {
  /** User-provided names for case branches */
  cases: Array<{ ctor: string; names: string[] }>;
}
```

---

## Branching Support: The `cases` Tactic

### How Cases Works (Lean 4 approach)

When you write:

```lean
cases n with
| Zero => <proof for Zero>
| Succ m => <proof for Succ m>
```

Lean:
1. **Looks up the eliminator** for the inductive type (Nat.rec)
2. **Creates one metavariable per constructor**
3. **Applies the eliminator** to the scrutinee, with metas as branch bodies
4. **Tags each goal** with the constructor name
5. **Extends context** in each goal with constructor parameters

### Implementation Strategy

```typescript
export class CasesTactic implements Tactic {
  name = 'cases';

  constructor(
    public readonly scrutinee: TTKTerm,
    public readonly withClause?: CasesWithClause
  ) {}

  apply(state: ProofState): TacticResult {
    const goal = state.getFocusedGoal();

    // 1. Infer type of scrutinee
    const scrutineeType = inferType(scrutinee, goal.ctx, state.definitions);

    // 2. Ensure it's an inductive type
    const indType = getInductiveType(scrutineeType, state.definitions);
    if (!indType) {
      return { success: false, error: 'cases: not an inductive type' };
    }

    // 3. Create one meta per constructor
    const branchMetas: Array<{ id: GoalId; ctor: string; meta: MetaVar }> = [];

    for (const ctor of indType.constructors) {
      // Extend context with constructor parameters
      const branchCtx = extendContextWithCtorParams(goal.ctx, ctor);

      // Create meta for this branch
      const branchId = freshMetaName();
      const branchMeta: MetaVar = {
        ctx: branchCtx,
        type: goal.type, // Same target type as original goal
        solution: undefined,
        caseTag: ctor.name // Tag for IDE display
      };

      branchMetas.push({ id: branchId, ctor: ctor.name, meta: branchMeta });
    }

    // 4. Build eliminator application
    // Result: IndType.rec (λ params1 => ?meta1) (λ params2 => ?meta2) ... scrutinee
    const elimTerm = buildEliminatorApp(
      indType,
      branchMetas.map(b => ({ tag: 'Meta', id: b.id })),
      scrutinee
    );

    // 5. Assign eliminator to current goal
    const newMetaVars = new Map(state.metaVars);
    newMetaVars.set(goal.id, { ...goal, solution: elimTerm });

    // Add branch metas
    for (const { id, meta } of branchMetas) {
      newMetaVars.set(id, meta);
    }

    // 6. Replace current goal with branch goals
    const newGoalIds = branchMetas.map(b => b.id);
    const newGoals = [
      ...state.goals.slice(0, state.focusIndex),
      ...newGoalIds,
      ...state.goals.slice(state.focusIndex + 1)
    ];

    return {
      success: true,
      newState: {
        ...state,
        metaVars: newMetaVars,
        goals: newGoals,
        focusIndex: state.focusIndex // Focus first new goal
      },
      info: {
        message: `cases: created ${branchMetas.length} subgoals`,
        newGoals: newGoalIds
      }
    };
  }
}
```

### Case-Specific Goal Handling

The `case` syntax focuses on a specific tagged goal:

```typescript
export class CaseTactic implements Tactic {
  name = 'case';

  constructor(
    public readonly ctorName: string,
    public readonly tactics: TacticExpr[]
  ) {}

  apply(state: ProofState): TacticResult {
    // Find goal with matching caseTag
    const goalIdx = state.goals.findIndex(gid => {
      const meta = state.metaVars.get(gid);
      return meta?.caseTag === this.ctorName;
    });

    if (goalIdx === -1) {
      return {
        success: false,
        error: `case: no goal for constructor '${this.ctorName}'`
      };
    }

    // Focus that goal
    let currentState = { ...state, focusIndex: goalIdx };

    // Apply tactics in sequence
    for (const tactic of this.tactics) {
      const result = applyTactic(currentState, tactic);
      if (!result.success) return result;
      currentState = result.newState;
    }

    return { success: true, newState: currentState };
  }
}
```

---

## InfoTree: IDE Integration

### Goal State Recording

After each tactic, record the state for IDE inspection:

```typescript
export interface TacticInfoNode {
  /** Source position of this tactic */
  position: { line: number; col: number };

  /** Goals before applying this tactic */
  goalsBefore: GoalState[];

  /** Goals after applying this tactic */
  goalsAfter: GoalState[];

  /** Tactic that was applied */
  tactic: TacticExpr;

  /** Child nodes (for case branches) */
  children: TacticInfoNode[];
}

export class TacticInfoTree {
  constructor(public root: TacticInfoNode) {}

  /**
   * Find the info node at the given cursor position.
   * Returns the goals that are active at that position.
   */
  findGoalsAtPosition(line: number, col: number): GoalState[] | null {
    return this.searchNode(this.root, line, col);
  }

  private searchNode(
    node: TacticInfoNode,
    line: number,
    col: number
  ): GoalState[] | null {
    // Check if cursor is in this node's range
    if (this.contains(node.position, line, col)) {
      // Search children first (more specific)
      for (const child of node.children) {
        const result = this.searchNode(child, line, col);
        if (result) return result;
      }

      // Cursor is in this tactic's range but not any child
      // Return goalsAfter (the state visible at this point)
      return node.goalsAfter;
    }

    return null;
  }

  private contains(
    pos: { line: number; col: number },
    line: number,
    col: number
  ): boolean {
    // TODO: Track end position as well
    return line >= pos.line && col >= pos.col;
  }
}
```

### Building the InfoTree

```typescript
/**
 * Execute tactics and build info tree for IDE inspection.
 */
export function executeTacticsWithInfo(
  initialState: ProofState,
  tactics: Array<{ expr: TacticExpr; position: SourcePosition }>
): { finalState: ProofState; infoTree: TacticInfoTree; error?: string } {
  const rootNode: TacticInfoNode = {
    position: { line: 0, col: 0 },
    goalsBefore: extractGoalStates(initialState),
    goalsAfter: [],
    tactic: { tag: 'Root' } as any,
    children: []
  };

  let currentState = initialState;

  for (const { expr, position } of tactics) {
    const goalsBefore = extractGoalStates(currentState);

    const result = applyTactic(currentState, expr);
    if (!result.success) {
      return {
        finalState: currentState,
        infoTree: new TacticInfoTree(rootNode),
        error: result.error
      };
    }

    currentState = result.newState;
    const goalsAfter = extractGoalStates(currentState);

    // Record this step
    rootNode.children.push({
      position,
      goalsBefore,
      goalsAfter,
      tactic: expr,
      children: []
    });
  }

  return {
    finalState: currentState,
    infoTree: new TacticInfoTree(rootNode)
  };
}

function extractGoalStates(state: ProofState): GoalState[] {
  return state.goals.map(gid => {
    const meta = state.metaVars.get(gid)!;
    return {
      id: gid,
      hypotheses: meta.ctx.map(b => ({
        name: b.name,
        type: b.type
      })),
      target: meta.type,
      caseTag: meta.caseTag
    };
  });
}
```

---

## Migration Path

### Phase 1: Extract Current Code (No Behavior Change)

1. Keep existing `TacticEngine` class
2. Rename to `LegacyTacticEngine` (mark deprecated)
3. Extract `applyTactic` function that wraps existing tactics
4. Add unit tests for `applyTactic` with each tactic type

**Goal**: Prove we can call tactics through a single function without breaking anything.

### Phase 2: Add ProofState Type (No Behavior Change)

1. Create `ProofState` type that wraps `TacticEngine`
2. Implement `applyTactic(state: ProofState, ...)` that delegates to engine
3. Update `elaborateTacticBlock` to use `ProofState`

**Goal**: New types in place, old code still works.

### Phase 3: Add InfoTree Recording (New Feature)

1. Implement `TacticInfoTree` and `TacticInfoNode`
2. Update `executeTacticsWithInfo` to record state after each tactic
3. Wire into compilation pipeline (store in declaration metadata)

**Goal**: IDE can now inspect goals at cursor position.

### Phase 4: Implement Cases (New Feature)

1. Implement `CasesTactic` with eliminator-based approach
2. Add `case` syntax to parser
3. Add tests for multi-branch proofs

**Goal**: Cases works, enabling structured case-by-case proofs.

### Phase 5: Cleanup (Refactor)

1. Remove `LegacyTacticEngine` if no longer needed
2. Simplify `TacticEngine` to pure immutable state (no methods)
3. Move all logic to standalone functions

**Goal**: Clean, testable, functional architecture.

---

## Testing Strategy

### Unit Tests for Single Tactics

Already implemented in `tactic.test.ts`. These verify each tactic works correctly in isolation.

### Unit Tests for applyTactic

```typescript
describe('applyTactic', () => {
  test('applies intro tactic', () => {
    const state = createInitialState(/* Nat -> Nat */);
    const result = applyTactic(state, { tag: 'Intro', name: 'n' });

    expect(result.success).toBe(true);
    if (!result.success) return;

    // Verify new goal has extended context
    const newGoal = result.newState.getFocusedGoal();
    expect(newGoal.ctx.length).toBe(1);
    expect(newGoal.ctx[0].name).toBe('n');
  });

  test('applies cases tactic', () => {
    const state = createInitialState(/* Nat -> Nat */, withVar('n', Nat));
    const result = applyTactic(state, {
      tag: 'Cases',
      target: { tag: 'Const', name: 'n' }
    });

    expect(result.success).toBe(true);
    if (!result.success) return;

    // Should have two goals (Zero and Succ)
    expect(result.newState.goals.length).toBe(2);
    expect(result.newState.metaVars.get(result.newState.goals[0])?.caseTag).toBe('Zero');
    expect(result.newState.metaVars.get(result.newState.goals[1])?.caseTag).toBe('Succ');
  });
});
```

### Integration Tests for Multi-Step Proofs

```typescript
describe('Multi-step proofs', () => {
  test('proof by cases', () => {
    // Prove: ∀ n : Nat, n = n
    const goalType = mkPi('n', Nat, mkEqual(Var(0), Var(0)));
    let state = createInitialState(goalType);

    // Step 1: intro n
    state = applyTactic(state, { tag: 'Intro', name: 'n' }).newState;

    // Step 2: cases n
    state = applyTactic(state, {
      tag: 'Cases',
      target: { tag: 'Var', index: 0 }
    }).newState;

    // Should have two goals
    expect(state.goals.length).toBe(2);

    // Step 3a: case Zero => exact refl
    state = applyTactic(state, {
      tag: 'Case',
      ctorName: 'Zero',
      tactics: [{ tag: 'Exact', term: mkRefl() }]
    }).newState;

    // Step 3b: case Succ => exact refl
    state = applyTactic(state, {
      tag: 'Case',
      ctorName: 'Succ',
      tactics: [{ tag: 'Exact', term: mkRefl() }]
    }).newState;

    // All goals solved
    expect(state.goals.length).toBe(0);
  });
});
```

### .tt File Tests

Continue using `.tt` files for end-to-end compilation tests:

```
-- @test success
-- @name "Nat cases proof"
-- @import preambles/nat.tt
-- @import preambles/equal-simple.tt

natEqRefl : (n : Nat) -> Equal n n := by
  intro n
  cases n with
  | Zero => exact refl
  | Succ m => exact refl
```

---

## IDE Integration Plan

### Display Goal State

When cursor is inside a tactic block:

1. Parse the file up to cursor position
2. Execute tactics up to that point with `executeTacticsWithInfo`
3. Use `infoTree.findGoalsAtPosition(line, col)` to get goal state
4. Display in sidebar:

```
Goals (2):
────────────────────
Case: Zero
────────────────────
⊢ Equal Zero Zero

────────────────────
Case: Succ
────────────────────
m : Nat
⊢ Equal (Succ m) (Succ m)
```

### Hover Information

When hovering over a tactic:
- Show which goals it affects
- Show resulting goal state
- Show any errors

### Go to Definition

When clicking on a hypothesis name:
- Jump to where it was introduced (intro/intros/cases)

---

## Open Questions

### 1. TacticM Monad?

Lean uses a `TacticM` monad for:
- State threading (ProofState)
- Error handling (MonadExcept)
- IO effects (trace, profiling)

**Decision**: Start without monad, use plain functions. If error handling gets messy, consider adding a Result monad wrapper.

### 2. Constraint Solving Timing

**Current**: Solve constraints after each tactic in `ExactTactic` and `ApplyTactic`.

**Question**: Should `applyTactic` always call `solveConstraints` at the end?

**Proposal**: Yes, but make it explicit:

```typescript
export function applyTactic(
  state: ProofState,
  tactic: TacticExpr,
  options: { solveConstraints?: boolean } = { solveConstraints: true }
): TacticResult {
  const result = applyTacticCore(state, tactic);
  if (!result.success) return result;

  if (options.solveConstraints) {
    const solved = solveAllConstraints(result.newState);
    return { success: true, newState: solved };
  }

  return result;
}
```

### 3. Parallel Proofs?

Lean can work on multiple goals in parallel. Do we need this?

**Decision**: No, not initially. Keep sequential for simplicity. Can add later if needed.

---

## Summary

### Core Changes

1. **ProofState type**: Explicit, immutable proof state
2. **applyTactic function**: Single entry point for all tactic applications
3. **Branching support**: `cases` creates multiple goals, `case` focuses on specific constructor
4. **InfoTree**: Records state after each tactic for IDE inspection

### Unchanged (Good Design)

1. Goals are metavariables (keep this!)
2. TacticEngine immutability (keep this!)
3. Existing tactic implementations (mostly keep, wrap in new API)

### New Capabilities

1. Case-by-case proofs with pattern matching
2. IDE shows goal state at cursor
3. Easy unit testing of single tactic steps
4. Clear separation of concerns

### Next Steps

1. ✅ Write unit tests for existing tactics (DONE)
2. Create `ProofState` type and `applyTactic` wrapper
3. Implement `TacticInfoTree` recording
4. Implement `CasesTactic`
5. Update parser for `cases`/`case` syntax
6. Wire into IDE for goal display
